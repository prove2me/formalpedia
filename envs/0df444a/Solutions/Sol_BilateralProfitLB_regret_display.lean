-- Prove2me | solution 1 for BilateralProfitLB.regret_display
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:21:40.038108+00:00
-- url     : https://prove2.me/submissions/0b320c13-aa9c-45c1-969c-0d4e08b45b9c

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic
import Theorems.Thm_BilateralProfitLB_claim_3_4
import Theorems.Thm_BilateralProfitLB_claim_7_3
import Theorems.Thm_BilateralProfitLB_expected_profit_formula


section BundlePart000



open Set Filter MeasureTheory
open scoped ENNReal

namespace BilateralProfitLB

open MechanismDesign.BilateralTrade

private abbrev HardLawClaim : Prop :=
  ∀ K : ℕ, 1 ≤ K → ∀ j : ℕ, j ≤ K →
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular

private theorem densityEnvironment_integrable {E : Environment} (hE : UnitSupport E) :
    IntegrableOn E.fB (Icc (0 : ℝ) 1) := by
  have hi : IntervalIntegrable E.fB volume 0 1 :=
    hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_intervalIntegrable
  exact (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).2 hi.1

private theorem densityEnvironment_integral {E : Environment} (hE : UnitSupport E) :
    ∫ x in (0 : ℝ)..1, E.fB x = 1 :=
  hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_integral

private theorem densityEnvironment_linIcc {E : Environment} {K j : ℕ}
    (hE : UnitSupport E) (hB : ∀ b ∈ Icc (0 : ℝ) 1, E.fB b = fB K j b)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x in Icc q 1, ENNReal.ofReal (fB K j x) =
      ENNReal.ofReal (∫ x in q..1, E.fB x) := by
  have hsub : Icc q 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left hq.1
  have hi : IntegrableOn E.fB (Icc q 1) :=
    (densityEnvironment_integrable hE).mono_set hsub
  have hnon : 0 ≤ᵐ[volume.restrict (Icc q 1)] E.fB := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply le_of_lt
    apply E.fB_pos
    rw [hE.2.2.1, hE.2.2.2]
    exact hsub hx
  rw [intervalIntegral.integral_of_le hq.2, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [hB x (hsub hx)]

private theorem densityEnvironment_tail {E : Environment} {K j : ℕ} (hE : UnitSupport E)
    (hS : ∀ b ∈ Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫ x in q..1, E.fB x = S K j q := by
  have hi := densityEnvironment_integrable hE
  have hin₁ : IntervalIntegrable E.fB volume 0 q := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.1]
    exact hi.mono_set (Icc_subset_Icc_right hq.2)
  have hin₂ : IntervalIntegrable E.fB volume q 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.2]
    exact hi.mono_set (Icc_subset_Icc_left hq.1)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hin₁ hin₂
  rw [densityEnvironment_integral hE] at hsum
  have hs := hS q hq
  rw [Environment.cdfB, hE.2.2.1] at hs
  linarith

private theorem S_nonneg_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ} (hK : 1 ≤ K)
    (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ S K j q := by
  obtain ⟨E, hE, _, _, hS, _, _⟩ := hClaim K hK j hj
  rw [← densityEnvironment_tail hE hS hq]
  apply intervalIntegral.integral_nonneg hq.2
  intro b hb
  have hb' : b ∈ Icc E.loB E.hiB := by
    rw [hE.2.2.1, hE.2.2.2]
    exact ⟨hq.1.trans hb.1, hb.2⟩
  exact (E.fB_pos b hb').le

private theorem S_continuousOn_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ} (hK : 1 ≤ K)
    (hj : j ≤ K) : ContinuousOn (S K j) (Icc (0 : ℝ) 1) := by
  obtain ⟨E, hE, _, _, hS, _, _⟩ := hClaim K hK j hj
  have hi := densityEnvironment_integrable hE
  have hcont : ContinuousOn (fun b => ∫ x in (0 : ℝ)..b, E.fB x) (Icc (0 : ℝ) 1) := by
    rw [← uIcc_of_le zero_le_one] at hi ⊢
    exact intervalIntegral.continuousOn_primitive_interval hi
  have hdiff : ContinuousOn (fun b => (1 : ℝ) - ∫ x in (0 : ℝ)..b, E.fB x) (Icc 0 1) :=
    continuousOn_const.sub hcont
  refine hdiff.congr fun b hb => ?_
  simpa only [Environment.cdfB, hE.2.2.1] using (hS b hb).symm

private theorem buyerMeasure_Ici_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b))
      (Ici q) = ENNReal.ofReal (S K j q) := by
  obtain ⟨E, hE, _, hB, hS, _, _⟩ := hClaim K hK j hj
  have hh : Ici q ∩ Icc (0 : ℝ) 1 = Icc q 1 := by
    ext b
    exact ⟨fun ⟨h, _, h₁⟩ => ⟨h, h₁⟩, fun ⟨h, h₁⟩ => ⟨h, hq.1.trans h, h₁⟩⟩
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hh, densityEnvironment_linIcc hE hB hq, densityEnvironment_tail hE hS hq]

private theorem buyerMeasure_Ici_real_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)).real
      (Ici q) = S K j q := by
  rw [Measure.real, buyerMeasure_Ici_of_claim_7_3 hClaim hK hj hq,
    ENNReal.toReal_ofReal (S_nonneg_of_claim_7_3 hClaim hK hj hq)]

private theorem buyerMeasure_inUnit_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) :
    ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (fB K j x) = 1 := by
  obtain ⟨E, hE, _, hB, _, _, _⟩ := hClaim K hK j hj
  rw [densityEnvironment_linIcc hE hB (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩),
    densityEnvironment_integral hE, ENNReal.ofReal_one]

private theorem buyerMeasure_isProbabilityMeasure_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) :
    IsProbabilityMeasure
      ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    buyerMeasure_inUnit_of_claim_7_3 hClaim hK hj]

private theorem sellerMeasure_isProbabilityMeasure_unit :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
  constructor
  simp

private theorem law_isProbabilityMeasure_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) : IsProbabilityMeasure (law K j) := by
  letI := sellerMeasure_isProbabilityMeasure_unit
  letI := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK hj
  unfold law
  infer_instance

private theorem law_supported_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) :
    law K j ((Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) = 1 := by
  letI := sellerMeasure_isProbabilityMeasure_unit
  letI := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK hj
  rw [law, Measure.prod_prod]
  have hs : (volume.restrict (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) = 1 := by
    simp [Measure.restrict_apply, measurableSet_Icc]
  have hb : ((volume.restrict (Icc (0 : ℝ) 1)).withDensity
          fun b => ENNReal.ofReal (fB K j b)) (Icc (0 : ℝ) 1) = 1 := by
    rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_self, buyerMeasure_inUnit_of_claim_7_3 hClaim hK hj]
  rw [hs, hb, one_mul]

end BilateralProfitLB
end BundlePart000


section BundlePart001


noncomputable section

namespace BilateralProfitLB

open MeasureTheory ProbabilityTheory Set BilateralProfit
open scoped ProbabilityTheory ENNReal

private abbrev FeedbackPair := Bool × Bool
private abbrev Valuation := ℝ × ℝ
private abbrev Tape (n : ℕ) := Fin n → Valuation
private abbrev PrefixState (Ω : Type) (n : ℕ) := Ω × (Fin n → FeedbackPair)

variable {Ω : Type} [MeasurableSpace Ω]

private theorem measurable_feedback : Measurable (fun x : Valuation × Valuation => feedback x.1 x.2) := by
  classical
  have h {f g : Valuation × Valuation → ℝ} (hf : Measurable f) (hg : Measurable g) :
      Measurable fun x => decide (f x ≤ g x) := by
    have he : (fun x => decide (f x ≤ g x)) =
        (fun x => if x ∈ {z | f z ≤ g z} then true else false) := by
      funext x
      by_cases hx : f x ≤ g x <;> simp [hx]
    rw [he]
    exact measurable_const.ite (measurableSet_le hf hg) measurable_const
  exact (h (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)).prodMk
    (h (measurable_snd.comp measurable_snd) (measurable_snd.comp measurable_fst))

private def protocolPrice (π : Policy Ω) {n : ℕ} (z : PrefixState Ω n) : ℝ × ℝ :=
  π.price z.1 (List.ofFn z.2)

private theorem protocolPrice_measurable (π : Policy Ω) (n : ℕ) :
    Measurable (protocolPrice π : PrefixState Ω n → ℝ × ℝ) :=
  measurable_from_prod_countable_left fun h => π.price_measurable (List.ofFn h)

private theorem protocolPrice_mem (π : Policy Ω) {n : ℕ} (z : PrefixState Ω n) :
    protocolPrice π z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
  π.price_mem z.1 (List.ofFn z.2)

private theorem measurable_feedback_at (π : Policy Ω) (n : ℕ) :
    Measurable fun z : PrefixState Ω n × Valuation => feedback z.2 (protocolPrice π z.1) :=
  measurable_feedback.comp (measurable_snd.prodMk ((protocolPrice_measurable π n).comp measurable_fst))

private def protocolUpdate (n : ℕ) (x : PrefixState Ω n × FeedbackPair) : PrefixState Ω (n + 1) :=
  (x.1.1, Fin.snoc x.1.2 x.2)

private theorem protocolUpdate_measurable (n : ℕ) :
    Measurable (protocolUpdate n : PrefixState Ω n × FeedbackPair → _) := by
  apply (measurable_fst.comp measurable_fst).prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [protocolUpdate] using (measurable_snd :
      Measurable (Prod.snd : PrefixState Ω n × FeedbackPair → FeedbackPair))
  · simpa [protocolUpdate, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

private def protocolHistory (π : Policy Ω) :
    (n : ℕ) → Ω → Tape n → Fin n → FeedbackPair
  | 0, _, _ => Fin.elim0
  | n+1, ω, v =>
      let h := protocolHistory π n ω (Fin.init v)
      Fin.snoc h (feedback (v (Fin.last n)) (protocolPrice π (ω, h)))

private def prefixState (π : Policy Ω) (n : ℕ) (x : Ω × Tape n) : PrefixState Ω n :=
  (x.1, protocolHistory π n x.1 x.2)

private def valuationPrefix {m n : ℕ} (h : m ≤ n) (v : Tape n) : Tape m :=
  fun i => v (i.castLE h)

private theorem valuationPrefix_measurable {m n : ℕ} (h : m ≤ n) :
    Measurable (valuationPrefix h : Tape n → Tape m) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i.castLE h)

private theorem prefixState_measurable (π : Policy Ω) (n : ℕ) :
    Measurable (prefixState π n) := by
  induction n with
  | zero => exact measurable_fst.prodMk measurable_const
  | succ n ih =>
    have hprev : Measurable fun x : Ω × Tape (n+1) => prefixState π n (x.1, Fin.init x.2) :=
      ih.comp (measurable_fst.prodMk ((valuationPrefix_measurable (Nat.le_succ n)).comp measurable_snd))
    have hfresh : Measurable fun x : Ω × Tape (n+1) => x.2 (Fin.last n) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_snd
    exact (protocolUpdate_measurable n).comp (hprev.prodMk
      ((measurable_feedback_at π n).comp (hprev.prodMk hfresh)))

private theorem protocolHistory_eq_hist (π : Policy Ω) {T : ℕ} (ω : Ω) (v : Tape T)
    (n : ℕ) (hn : n ≤ T) :
    List.ofFn (protocolHistory π n ω (valuationPrefix hn v)) = hist π ω v n := by
  induction n with
  | zero => simp [protocolHistory, hist]
  | succ n ih =>
    have hn' := Nat.le_of_succ_le hn
    have ht := Nat.lt_of_succ_le hn
    have hinit : Fin.init (valuationPrefix hn v) = valuationPrefix hn' v := rfl
    rw [hist, dif_pos ht, protocolHistory, hinit, List.ofFn_succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, protocolPrice, ih hn']
    rfl

private theorem protocolPrice_eq_act (π : Policy Ω) {T : ℕ} (x : Ω × Tape T) (t : Fin T) :
    protocolPrice π (prefixState π t (x.1, valuationPrefix t.isLt.le x.2)) = act π x.1 x.2 t := by
  simp only [protocolPrice, prefixState, act, protocolHistory_eq_hist]

private theorem tape_split_preserving (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    MeasurePreserving (fun v : Tape (n+1) => (Fin.init v, v (Fin.last n)))
      (Measure.pi fun _ : Fin (n+1) => D)
      ((Measure.pi fun _ : Fin n => D).prod D) := by
  have h := (Measure.measurePreserving_swap (μ := D) (ν := Measure.pi fun _ : Fin n => D)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) (Fin.last n))
  refine h.congr ((valuationPrefix_measurable (Nat.le_succ n)).prodMk
    (measurable_pi_apply (Fin.last n))) ?_
  filter_upwards with v
  simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply, Fin.init]

private theorem valuationPrefix_preserving (D : Measure Valuation) [IsProbabilityMeasure D]
    {m n : ℕ} (h : m ≤ n) :
    MeasurePreserving (valuationPrefix h)
      (Measure.pi fun _ : Fin n => D) (Measure.pi fun _ : Fin m => D) := by
  induction h with
  | refl =>
    refine (MeasurePreserving.id _).congr (valuationPrefix_measurable _) ?_
    filter_upwards with v
    rfl
  | @step n h ih =>
    have hf : MeasurePreserving Prod.fst ((Measure.pi fun _ : Fin n => D).prod D)
        (Measure.pi fun _ : Fin n => D) :=
      ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    refine (ih.comp (hf.comp (tape_split_preserving D n))).congr
      (valuationPrefix_measurable _) ?_
    filter_upwards with v
    rfl

private theorem run_prefix_preserving (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure Valuation)
    [IsProbabilityMeasure D] {m n : ℕ} (h : m ≤ n) :
    MeasurePreserving (fun x : Ω × Tape n => (x.1, valuationPrefix h x.2))
      (runMeasure P D n) (runMeasure P D m) :=
  (MeasurePreserving.id P).prod (valuationPrefix_preserving D h)

private theorem run_split_preserving (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure Valuation)
    [IsProbabilityMeasure D] (n : ℕ) :
    MeasurePreserving (fun x : Ω × Tape (n+1) => ((x.1, Fin.init x.2), x.2 (Fin.last n)))
      (runMeasure P D (n+1)) ((runMeasure P D n).prod D) := by
  have h := (measurePreserving_prodAssoc P (Measure.pi fun _ : Fin n => D) D).symm
  exact h.comp ((MeasurePreserving.id P).prod (tape_split_preserving D n))

private def prefixLaw (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation) (n : ℕ) :
    Measure (PrefixState Ω n) :=
  (runMeasure P D n).map (prefixState π n)

private theorem prefixState_preserving (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation)
    (n : ℕ) : MeasurePreserving (prefixState π n) (runMeasure P D n) (prefixLaw π P D n) :=
  ⟨prefixState_measurable π n, rfl⟩

private instance prefixLaw_probability (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    IsProbabilityMeasure (prefixLaw π P D n) := by
  letI : IsProbabilityMeasure (runMeasure P D n) := by unfold runMeasure; infer_instance
  exact Measure.isProbabilityMeasure_map (prefixState_measurable π n).aemeasurable

private theorem prefixLaw_zero_same (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D D' : Measure Valuation) [IsProbabilityMeasure D] [IsProbabilityMeasure D'] :
    prefixLaw π P D 0 = prefixLaw π P D' 0 := by
  have he (v : Tape 0) : v = Fin.elim0 := Subsingleton.elim _ _
  have hD (μ : Measure Valuation) [IsProbabilityMeasure μ] :
      Measure.pi (fun _ : Fin 0 => μ) = Measure.dirac (Fin.elim0 : Tape 0) := by
    ext s hs
    by_cases h : (Fin.elim0 : Tape 0) ∈ s
    · have hu : s = univ := by ext v; simp [he v, h]
      simp [hu]
    · have hz : s = ∅ := by ext v; simp [he v, h]
      simp [hz]
  simp only [prefixLaw, runMeasure, hD]

private def feedbackKernel (π : Policy Ω) (D : Measure Valuation) (n : ℕ) :
    Kernel (PrefixState Ω n) FeedbackPair :=
  (Kernel.id ×ₖ Kernel.const _ D).map (fun z => feedback z.2 (protocolPrice π z.1))

private instance feedbackKernel_markov (π : Policy Ω) (D : Measure Valuation) [IsProbabilityMeasure D]
    (n : ℕ) : IsMarkovKernel (feedbackKernel π D n) := by
  exact Kernel.IsMarkovKernel.map _ (measurable_feedback_at π n)

private theorem feedbackKernel_apply (π : Policy Ω) (D : Measure Valuation) [IsProbabilityMeasure D]
    (n : ℕ) (z : PrefixState Ω n) :
    feedbackKernel π D n z = D.map (fun v => feedback v (protocolPrice π z)) := by
  rw [feedbackKernel, Kernel.map_apply _ (measurable_feedback_at π n)]
  ext s hs
  have hsec : Measurable fun v => feedback v (protocolPrice π z) :=
    (measurable_feedback_at π n).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply (measurable_feedback_at π n) hs,
    Kernel.id_prod_apply' _ _ ((measurable_feedback_at π n) hs), Kernel.const_apply,
    Measure.map_apply hsec hs]
  rfl

private theorem prefix_fresh_preserving (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] {n T : ℕ} (hn : n+1 ≤ T) :
    MeasurePreserving
      (fun x : Ω × Tape T =>
        (prefixState π n (x.1, valuationPrefix (Nat.le_of_succ_le hn) x.2),
         x.2 ⟨n, Nat.lt_of_succ_le hn⟩))
      (runMeasure P D T) ((prefixLaw π P D n).prod D) := by
  letI : IsProbabilityMeasure (runMeasure P D n) := by unfold runMeasure; infer_instance
  exact ((prefixState_preserving π P D n).prod (MeasurePreserving.id D)).comp
    ((run_split_preserving P D n).comp (run_prefix_preserving P D hn))

private theorem prefixLaw_succ (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (n : ℕ) :
    prefixLaw π P D (n + 1) =
      ((prefixLaw π P D n) ⊗ₘ (feedbackKernel π D n)).map (protocolUpdate n) := by
  let ν := prefixLaw π P D n
  let F : PrefixState Ω n × Valuation → PrefixState Ω n × FeedbackPair :=
    fun z => (z.1, feedback z.2 (protocolPrice π z.1))
  have hF : Measurable F := measurable_fst.prodMk (measurable_feedback_at π n)
  have hmap : (ν.prod D).map F = ν ⊗ₘ feedbackKernel π D n := by
    ext s hs
    rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro z
    have hsec : Measurable fun v => feedback v (protocolPrice π z) :=
      (measurable_feedback_at π n).comp (measurable_const.prodMk measurable_id)
    rw [feedbackKernel_apply, Measure.map_apply hsec (measurable_prodMk_left hs)]
    rfl
  rw [← hmap, Measure.map_map (protocolUpdate_measurable n) hF]
  have hp := prefix_fresh_preserving π P D (le_refl (n+1))
  rw [← hp.map_eq, Measure.map_map ((protocolUpdate_measurable n).comp hF) hp.measurable]
  rfl

end BilateralProfitLB
end
end BundlePart001


section BundlePart002


namespace BilateralProfitLB

private theorem w_pos {K : ℕ} (hK : 0 < K) : 0 < w K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  positivity

private theorem w_le_quarter {K : ℕ} (hK : 0 < K) : w K ≤ 1 / 4 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold w
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private theorem cast_mul_w {K : ℕ} (hK : 0 < K) : (K : ℝ) * w K = 1 / 4 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  field_simp

private theorem a_ge_quarter {K j : ℕ} (hj : 1 ≤ j) : 1 / 4 ≤ a K j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw : 0 ≤ w K := by unfold w; positivity
  unfold a
  linarith [mul_nonneg (sub_nonneg.mpr hjr) hw]

private theorem endpoint_le_half {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    a K j + w K ≤ 1 / 2 := by
  have hjr : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_right hjr (w_pos hK).le
  unfold a
  linarith [cast_mul_w hK]

private theorem I_subset {K j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) :
    I K j ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
  have hK : 0 < K := lt_of_lt_of_le (by decide : 0 < 1) (hj₁.trans hj₂)
  intro q hq
  exact ⟨(a_ge_quarter hj₁).trans_lt hq.1, hq.2.trans_le (endpoint_le_half hK hj₂)⟩

private theorem qstar_mem {K j : ℕ} (hK : 0 < K) : qstar K j ∈ I K j := by
  have hw := w_pos hK
  change a K j < a K j + w K / 2 ∧ a K j + w K / 2 < a K j + w K
  exact ⟨by linarith, by linarith⟩

private theorem normalized_qstar {K j : ℕ} (hK : 0 < K) : (qstar K j - a K j) / w K = 1 / 2 := by
  unfold qstar
  apply (div_eq_iff (w_pos hK).ne').mpr
  ring

private theorem I_pairwiseDisjoint (K : ℕ) : Pairwise (fun i j => Disjoint (I K i) (I K j)) := by
  intro i j hij
  have hw : 0 ≤ w K := by unfold w; positivity
  suffices ordered : ∀ {k l : ℕ}, k < l → Disjoint (I K k) (I K l) by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ordered h
    · exact (ordered h).symm
  intro k l hkl
  have hcast : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ l - 1 by linarith) hw
  apply Set.disjoint_left.mpr
  intro q hk hl
  have hkq : q < a K k + w K := hk.2
  have hql : a K l < q := hl.1
  unfold a at hkq hql
  nlinarith

open Classical in
private theorem sum_interval_visits_le (K T : ℕ) (s : Finset ℕ) (q : Fin T → ℝ) :
    ∑ j ∈ s, (Finset.univ.filter fun t => q t ∈ I K j).card ≤ T := by
  let visits (j : ℕ) := Finset.univ.filter fun t => q t ∈ I K j
  have hd : (s : Set ℕ).PairwiseDisjoint visits := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun t hi hj => ?_
    exact Set.disjoint_left.mp (I_pairwiseDisjoint K hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  change ∑ j ∈ s, (visits j).card ≤ T
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (s.biUnion visits)

private theorem Delta_eq {K : ℕ} (hK : 0 < K) : Delta K = 1 / (73728 * (K : ℝ) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold Delta w
  field_simp
  ring

private theorem Delta_pos {K : ℕ} (hK : 0 < K) : 0 < Delta K := by
  have hw := w_pos hK
  unfold Delta
  positivity

open Classical in
private theorem sum_outside_interval_gap (K j T : ℕ) (q : Fin T → ℝ) :
    (∑ t : Fin T, Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t)) =
      ((T : ℝ) - ((Finset.univ.filter fun t => q t ∈ I K j).card : ℝ)) * Delta K := by
  have hi (t : Fin T) : Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t) =
      Delta K - if q t ∈ I K j then Delta K else 0 := by
    by_cases ht : q t ∈ I K j
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [nsmul_eq_mul, sub_mul]

end BilateralProfitLB
end BundlePart002


section BundlePart003



open MeasureTheory Set

namespace BilateralProfitLB

variable {Ω : Type} [MeasurableSpace Ω]

private def visitEvent (π : Policy Ω) {T : ℕ} (t : Fin T) (J : Set ℝ) : Set (Ω × Tape T) :=
  {x | (act π x.1 x.2 t).2 ∈ J}

private theorem measurePreserving_before_round (π : Policy Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : Measure Valuation) [IsProbabilityMeasure D]
    {T : ℕ} (t : Fin T) :
    MeasurePreserving
      (fun x : Ω × Tape T => prefixState π t (x.1, valuationPrefix t.isLt.le x.2))
      (runMeasure P D T) (prefixLaw π P D t) :=
  (prefixState_preserving π P D t).comp (run_prefix_preserving P D t.isLt.le)

private theorem visitEvent_measurable (π : Policy Ω) {T : ℕ} (t : Fin T)
    {J : Set ℝ} (hJ : MeasurableSet J) : MeasurableSet (visitEvent π t J) := by
  have hm := (protocolPrice_measurable π t).comp
    ((prefixState_measurable π t).comp
      (measurable_fst.prodMk ((valuationPrefix_measurable t.isLt.le).comp measurable_snd)))
  have he : visitEvent π t J =
      (fun x : Ω × Tape T => (protocolPrice π
        (prefixState π t (x.1, valuationPrefix t.isLt.le x.2))).2) ⁻¹' J := by
    ext x
    simp only [visitEvent, mem_ofPred_eq, mem_preimage, protocolPrice_eq_act]
  rw [he]
  exact hm.snd hJ

private theorem visitEvent_real (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] {T : ℕ} (t : Fin T)
    {J : Set ℝ} (hJ : MeasurableSet J) :
    (runMeasure P D T).real (visitEvent π t J) =
      (prefixLaw π P D t).real {z | (protocolPrice π z).2 ∈ J} := by
  have hp := measurePreserving_before_round π P D t
  have hs : MeasurableSet {z : PrefixState Ω t | (protocolPrice π z).2 ∈ J} :=
    (protocolPrice_measurable π t).snd hJ
  have he : visitEvent π t J =
      (fun x : Ω × Tape T => prefixState π t (x.1, valuationPrefix t.isLt.le x.2)) ⁻¹'
        {z | (protocolPrice π z).2 ∈ J} := by
    ext x
    simp only [visitEvent, mem_ofPred_eq, mem_preimage, protocolPrice_eq_act]
  rw [he, ← hp.map_eq, Measure.real, Measure.real, Measure.map_apply hp.measurable hs]

open Classical in
private noncomputable def visitCount (π : Policy Ω) {T : ℕ} (J : Set ℝ) (x : Ω × Tape T) : ℝ :=
  ((Finset.univ.filter fun t : Fin T => (act π x.1 x.2 t).2 ∈ J).card : ℝ)

private theorem visitCount_eq_sum (π : Policy Ω) {T : ℕ} (J : Set ℝ) (x : Ω × Tape T) :
    visitCount π J x = ∑ t : Fin T, (visitEvent π t J).indicator (fun _ => (1 : ℝ)) x := by
  classical
  unfold visitCount
  rw [← Finset.sum_boole (R := ℝ)]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (act π x.1 x.2 t).2 ∈ J <;> simp [Set.indicator, visitEvent, ht]

private theorem visitCount_integrable (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation)
    {T : ℕ} [IsFiniteMeasure (runMeasure P D T)] {J : Set ℝ} (hJ : MeasurableSet J) :
    Integrable (visitCount π (T := T) J) (runMeasure P D T) := by
  simp only [funext (visitCount_eq_sum π (T := T) J)]
  exact integrable_finsetSum _ fun t _ =>
    (integrable_const (1 : ℝ)).indicator (visitEvent_measurable π t hJ)

private theorem expCount_nonneg (π : Policy Ω) (P : Measure Ω) (D : Measure Valuation) (T : ℕ)
    (J : Set ℝ) : 0 ≤ expCount π P D T J := by
  unfold expCount
  exact integral_nonneg fun _ => Nat.cast_nonneg _

/-- The expected count is the sum of the event probabilities under the pre-round prefix laws. -/
private theorem expCount_eq_sum_prefix (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (T : ℕ) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    expCount π P D T J =
      ∑ t ∈ Finset.range T, (prefixLaw π P D t).real {z | (protocolPrice π z).2 ∈ J} := by
  have hr : IsProbabilityMeasure (runMeasure P D T) := by unfold runMeasure; infer_instance
  change (∫ x, visitCount π J x ∂(runMeasure P D T)) = _
  simp only [visitCount_eq_sum π J, ← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    exact (integral_indicator_one (μ := runMeasure P D T) (visitEvent_measurable π t hJ)).trans
      (visitEvent_real π P D t hJ)
  · intro t _
    exact (integrable_const (1 : ℝ)).indicator (visitEvent_measurable π t hJ)

/-- The disjoint perturbation intervals together receive at most one visit per round. -/
private theorem sum_expCount_le (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] (K T : ℕ) (s : Finset ℕ) :
    ∑ j ∈ s, expCount π P D T (I K j) ≤ (T : ℝ) := by
  have hr : IsProbabilityMeasure (runMeasure P D T) := by unfold runMeasure; infer_instance
  have hi (j : ℕ) : Integrable (visitCount π (T := T) (I K j)) (runMeasure P D T) :=
    visitCount_integrable π P D measurableSet_Ioo
  change (∑ j ∈ s, ∫ x, visitCount π (I K j) x ∂(runMeasure P D T)) ≤ _
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ∫ (_ : Ω × Tape T), (T : ℝ) ∂(runMeasure P D T) := by
      refine integral_mono (integrable_finsetSum _ (fun j _ => hi j)) (integrable_const _) ?_
      intro x
      classical
      simpa only [visitCount, Nat.cast_sum] using
        (show ((∑ j ∈ s, (Finset.univ.filter fun t => (act π x.1 x.2 t).2 ∈ I K j).card : ℕ) : ℝ)
          ≤ (T : ℝ) by exact_mod_cast sum_interval_visits_le K T s (fun t => (act π x.1 x.2 t).2))
    _ = _ := by simp

end BilateralProfitLB
end BundlePart003


section BundlePart004






noncomputable section

namespace BilateralProfitLB

open BilateralProfit MeasureTheory Set
open scoped BigOperators

variable {Ω : Type} [MeasurableSpace Ω]

private theorem profit_measurable_pair :
    Measurable (fun z : Valuation × Valuation => profit z.1 z.2) := by
  have ht : MeasurableSet {z : Valuation × Valuation | Trades z.1 z.2} :=
    (measurableSet_le (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_snd.comp measurable_snd)
        (measurable_snd.comp measurable_fst))
  exact ((measurable_snd.comp measurable_snd).sub (measurable_fst.comp measurable_snd)).mul
    (measurable_const.ite ht measurable_const)

private theorem abs_profit_le_one (v a : Valuation)
    (ha : a ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    |profit v a| ≤ 1 := by
  rcases ha with ⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩⟩
  unfold profit tradeBit
  split <;> simp only [mul_one, mul_zero]
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · norm_num

private theorem profit_at_prefix_measurable (π : Policy Ω) (n : ℕ) :
    Measurable fun z : PrefixState Ω n × Valuation => profit z.2 (protocolPrice π z.1) :=
  profit_measurable_pair.comp
    (measurable_snd.prodMk ((protocolPrice_measurable π n).comp measurable_fst))

private theorem profit_at_prefix_integrable (π : Policy Ω) {n : ℕ}
    (D : Measure Valuation) [IsProbabilityMeasure D] (Q : Measure (PrefixState Ω n))
    [IsProbabilityMeasure Q] :
    Integrable (fun z : PrefixState Ω n × Valuation => profit z.2 (protocolPrice π z.1))
      (Q.prod D) := by
  apply Integrable.of_bound (profit_at_prefix_measurable π n).aestronglyMeasurable 1
  filter_upwards with z
  exact abs_profit_le_one z.2 (protocolPrice π z.1) (protocolPrice_mem π z.1)

private theorem expProfit_eq_prefix_integral (π : Policy Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure Valuation) [IsProbabilityMeasure D] {T : ℕ} (t : Fin T) :
    expProfit π P D T t = ∫ z, (∫ v, profit v (protocolPrice π z) ∂D) ∂(prefixLaw π P D t) := by
  let F := fun z : PrefixState Ω t × Valuation => profit z.2 (protocolPrice π z.1)
  have hF := profit_at_prefix_measurable π t
  have hfresh := prefix_fresh_preserving π P D (Nat.succ_le_of_lt t.isLt)
  have hI := profit_at_prefix_integrable π D (prefixLaw π P D t)
  calc
    _ = ∫ z, F z ∂((prefixLaw π P D t).prod D) := by
      rw [← hfresh.map_eq, integral_map_of_stronglyMeasurable hfresh.measurable hF.stronglyMeasurable]
      unfold expProfit
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg (profit (x.2 t)) (protocolPrice_eq_act π x t).symm
    _ = _ := integral_prod F hI

private theorem comparator_gap {K j : ℕ} (hK : 1 ≤ K) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ∃ a ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ p q,
      p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
        ((I K j)ᶜ).indicator (fun _ => Delta K) q ≤
          (∫ v, profit v a ∂(law K j)) - (∫ v, profit v (p,q) ∂(law K j)) := by
  have hh (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
      h K j q = q ^ 2 / 4 * S K j q :=
    (expected_profit_formula K hK j hjK 0 q (by norm_num) hq).2.2.1
  have hcont : ContinuousOn (h K j) (Icc (0 : ℝ) 1) :=
    ((((continuous_id.pow 2).div_const 4).continuousOn).mul
      (S_continuousOn_of_claim_7_3 claim_7_3 hK hjK)).congr hh
  obtain ⟨qmax, hqmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, by norm_num⟩ hcont
  have hpmax : qmax / 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hqmax.1], by linarith [hqmax.2]⟩
  have hfix : (∫ v, profit v (qmax/2,qmax) ∂(law K j)) = h K j qmax := by
    rw [(expected_profit_formula K hK j hjK _ _ hpmax hqmax).1, hh qmax hqmax]
    ring
  have hmidmem : qstar K j ∈ Icc (0 : ℝ) 1 := by
    have hr := I_subset hj1 hjK (qstar_mem (show 0 < K from hK))
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨(qmax/2,qmax), ⟨hpmax,hqmax⟩, ?_⟩
  intro p q hp hq
  rw [hfix]
  have hupper := (expected_profit_formula K hK j hjK p q hp hq).2.2.2
  by_cases hqI : q ∈ I K j
  · have hqI' : q ∉ (I K j)ᶜ := by simpa using hqI
    rw [indicator_of_notMem hqI']
    have hs : h K j q ≤ h K j qmax := hmax hq
    linarith
  · rw [indicator_of_mem (mem_compl hqI)]
    have hgap := (claim_3_4 K hK).2 j hj1 hjK q hq hqI
    have hs : h K j (qstar K j) ≤ h K j qmax := hmax hmidmem
    linarith

private theorem regret_display_proof (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j)
    (hjK : j ≤ K) (T : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (π : Policy Ω) :
    ∃ a ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ((T : ℝ) - expCount π P (law K j) T (I K j)) * Delta K ≤
        regret π P (law K j) T a := by
  obtain ⟨a, ha, hgap⟩ := comparator_gap hK hj1 hjK
  let D := law K j
  have hD : IsProbabilityMeasure D := law_isProbabilityMeasure_of_claim_7_3 claim_7_3 hK hjK
  refine ⟨a, ha, ?_⟩
  let event (t : ℕ) : Set (PrefixState Ω t) := {z | (protocolPrice π z).2 ∈ I K j}
  let M := ∫ v, profit v a ∂D
  have hround (t : Fin T) :
      (1 - (prefixLaw π P D t).real (event t)) * Delta K ≤ M - expProfit π P D T t := by
    let Q := prefixLaw π P D t
    have hQ : IsProbabilityMeasure Q := prefixLaw_probability π P D t
    let g (z : PrefixState Ω t) := ∫ v, profit v (protocolPrice π z) ∂D
    have hg : Integrable g Q := (profit_at_prefix_integrable π D Q).integral_prod_left
    have he : MeasurableSet (event t) := (protocolPrice_measurable π t).snd measurableSet_Ioo
    rw [expProfit_eq_prefix_integral π P D t]
    change (1 - Q.real (event t)) * Delta K ≤ M - ∫ z, g z ∂Q
    calc
      _ = ∫ z, ((event t)ᶜ).indicator (fun _ => Delta K) z ∂Q := by
        rw [integral_indicator_const _ he.compl, probReal_compl_eq_one_sub he]
        rfl
      _ ≤ ∫ z, M - g z ∂Q := by
        refine integral_mono ((integrable_const _).indicator he.compl)
          ((integrable_const M).sub hg) ?_
        intro z
        have hz := protocolPrice_mem π z
        exact hgap (protocolPrice π z).1 (protocolPrice π z).2 hz.1 hz.2
      _ = _ := by
        rw [integral_sub (integrable_const M) hg]
        simp
  have hcount := expCount_eq_sum_prefix π P D T (I K j) measurableSet_Ioo
  change expCount π P D T (I K j) =
    ∑ t ∈ Finset.range T, (prefixLaw π P D t).real (event t) at hcount
  rw [← Fin.sum_univ_eq_sum_range] at hcount
  change ((T : ℝ) - expCount π P D T (I K j)) * Delta K ≤ regret π P D T a
  rw [hcount]
  calc
    _ = ∑ t : Fin T, (1 - (prefixLaw π P D t).real (event t)) * Delta K := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      simp
    _ ≤ _ := Finset.sum_le_sum fun t _ => hround t

end BilateralProfitLB
end
end BundlePart004

open BilateralProfitLB
open MeasureTheory

theorem solution (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (π : Policy Ω) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ((T : ℝ) - expCount π P (law K j) T (I K j)) * Delta K ≤ regret π P (law K j) T a := by
  exact BilateralProfitLB.regret_display_proof K hK j hj1 hjK T Ω P π
