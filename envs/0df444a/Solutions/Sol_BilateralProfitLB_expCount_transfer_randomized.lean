-- Prove2me | solution 1 for BilateralProfitLB.expCount_transfer_randomized
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:20:54.554623+00:00
-- url     : https://prove2.me/submissions/aaf88f9c-8190-4abb-ad65-c7ccf75a60d9

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic
import Theorems.Thm_BilateralProfitLB_claim_7_2
import Theorems.Thm_BilateralProfitLB_claim_7_3
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral
import Theorems.Thm_RegretBandits_Stochastic_kl_bernoulli_bounds

section InformationPart0

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

end BilateralProfitLB

end InformationPart0

section InformationPart1

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

end InformationPart1

section InformationPart2

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

end BilateralProfitLB

end InformationPart2

section InformationPart3

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

end BilateralProfitLB

end InformationPart3

section InformationPart4

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory unitInterval

namespace BilateralProfitLB

private lemma bernoulliFin_ac (p q : unitInterval) (hq : (q : ℝ) ∈ Set.Ioo 0 1) :
    bernoulliMeasure (1 : Fin 2) 0 p ≪ bernoulliMeasure (1 : Fin 2) 0 q := by
  intro s hzero
  by_cases h1 : (1 : Fin 2) ∈ s <;> by_cases h0 : (0 : Fin 2) ∈ s
  · simp [bernoulliMeasure_apply_of_mem_of_mem _ MeasurableSet.of_discrete h1 h0] at hzero
  · have h : (bernoulliMeasure (1 : Fin 2) 0 q).real s = q :=
      bernoulliMeasure_real_apply_of_mem_of_notMem q MeasurableSet.of_discrete h1 h0
    simp [measureReal_def, hzero] at h
    exact (ne_of_gt hq.1 h.symm).elim
  · have h : (bernoulliMeasure (1 : Fin 2) 0 q).real s = 1 - (q : ℝ) :=
      bernoulliMeasure_real_apply_of_notMem_of_mem q MeasurableSet.of_discrete h1 h0
    simp [measureReal_def, hzero] at h
    linarith [hq.2]
  · exact bernoulliMeasure_apply_of_notMem_of_notMem p MeasurableSet.of_discrete h1 h0

private lemma klDiv_bernoulliFin_toReal (p q : unitInterval)
    (h : bernoulliMeasure (1 : Fin 2) 0 p ≪ bernoulliMeasure (1 : Fin 2) 0 q) :
    (klDiv (bernoulliMeasure (1 : Fin 2) 0 p) (bernoulliMeasure (1 : Fin 2) 0 q)).toReal =
      RegretBandits.Stochastic.klBern p q := by
  rw [categorical_toReal_klDiv_eq_sum _ _ h, Fin.sum_univ_two]
  simp [RegretBandits.Stochastic.klBern, add_comm]

/-- A measurable map with a measurable left inverse preserves relative entropy. -/
private lemma klDiv_map_eq_of_inverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α → β) (g : β → α)
    (hf : Measurable f) (hg : Measurable g) (hgf : Function.LeftInverse g f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν hf)
  have h : g ∘ f = id := funext hgf
  simpa [Measure.map_map hg hf, h] using klDiv_map_le (μ.map f) (ν.map f) hg

private lemma klDiv_bernoulliBool_eq_fin (p q : unitInterval) :
    klDiv (bernoulliMeasure true false p) (bernoulliMeasure true false q) =
      klDiv (bernoulliMeasure (1 : Fin 2) 0 p) (bernoulliMeasure (1 : Fin 2) 0 q) := by
  have hmap (r : unitInterval) :
      (bernoulliMeasure (1 : Fin 2) 0 r).map finTwoEquiv = bernoulliMeasure true false r := by
    rw [map_bernoulliMeasure' (1 : Fin 2) 0 Measurable.of_discrete r]
    rfl
  rw [← hmap p, ← hmap q]
  exact klDiv_map_eq_of_inverse _ _ _ finTwoEquiv.symm Measurable.of_discrete
    Measurable.of_discrete finTwoEquiv.left_inv

/-- Upper Bernoulli KL inequality in the measure-theoretic formulation. -/
private theorem klDiv_bernoulliBool_le (p q : unitInterval) (hq : (q : ℝ) ∈ Set.Ioo 0 1) :
    klDiv (bernoulliMeasure true false p) (bernoulliMeasure true false q) ≤
      ENNReal.ofReal (((p : ℝ) - (q : ℝ)) ^ 2 / ((q : ℝ) * (1 - (q : ℝ)))) := by
  rw [klDiv_bernoulliBool_eq_fin]
  have hac := bernoulliFin_ac p q hq
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hac Integrable.of_finite),
    klDiv_bernoulliFin_toReal p q hac]
  exact ENNReal.ofReal_le_ofReal
    (RegretBandits.Stochastic.kl_bernoulli_bounds p q p.property hq).2

/-- The common independent seller feedback cancels in one-step KL. -/
private theorem klDiv_prod_common_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (seller : Measure α) (μ ν : Measure β) [IsProbabilityMeasure seller] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : klDiv (seller.prod μ) (seller.prod ν) = klDiv μ ν := by
  have hs (τ : Measure β) [IsFiniteMeasure τ] : (seller.prod τ).map Prod.swap = τ.prod seller :=
    Measure.prod_swap
  rw [← klDiv_map_eq_of_inverse (seller.prod μ) (seller.prod ν) Prod.swap Prod.swap
    measurable_swap measurable_swap (fun _ => rfl), hs μ, hs ν,
    ← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_left]

private lemma map_event_bernoulliFin {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    μ.map (fun x => if x ∈ s then (1 : Fin 2) else 0) =
      bernoulliMeasure (1 : Fin 2) 0 ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩ := by
  have hm : Measurable (fun x => if x ∈ s then (1 : Fin 2) else 0) :=
    measurable_const.ite hs measurable_const
  ext u hu
  rw [Measure.map_apply hm hu]
  by_cases h1 : (1 : Fin 2) ∈ u <;> by_cases h0 : (0 : Fin 2) ∈ u
  · have hpre : (fun x => if x ∈ s then (1 : Fin 2) else 0) ⁻¹' u = Set.univ := by
      ext x
      by_cases hxs : x ∈ s <;> simp [hxs, h1, h0]
    rw [hpre, measure_univ, bernoulliMeasure_apply_of_mem_of_mem _ hu h1 h0]
  · have hpre : (fun x => if x ∈ s then (1 : Fin 2) else 0) ⁻¹' u = s := by
      ext x
      by_cases hxs : x ∈ s <;> simp [hxs, h1, h0]
    rw [hpre]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    exact (bernoulliMeasure_real_apply_of_mem_of_notMem
      ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩ hu h1 h0).symm
  · have hpre : (fun x => if x ∈ s then (1 : Fin 2) else 0) ⁻¹' u = sᶜ := by
      ext x
      by_cases hxs : x ∈ s <;> simp [hxs, h1, h0]
    rw [hpre]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    change μ.real sᶜ = (bernoulliMeasure (1 : Fin 2) 0 _).real u
    rw [probReal_compl_eq_one_sub hs, bernoulliMeasure_real_apply_of_notMem_of_mem _ hu h1 h0]
  · have hpre : (fun x => if x ∈ s then (1 : Fin 2) else 0) ⁻¹' u = ∅ := by
      ext x
      by_cases hxs : x ∈ s <;> simp [hxs, h1, h0]
    rw [hpre, measure_empty, bernoulliMeasure_apply_of_notMem_of_notMem _ hu h1 h0]

/-- The pushforward by a Boolean-valued test is its Bernoulli law. -/
private theorem map_bool_eq_bernoulli {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → Bool) (hf : Measurable f) :
    μ.map f = bernoulliMeasure true false
      ⟨μ.real (f ⁻¹' {true}), measureReal_nonneg, measureReal_le_one⟩ := by
  classical
  let s := f ⁻¹' {true}
  have hs : MeasurableSet s := hf (MeasurableSet.singleton _)
  let g := fun x => if x ∈ s then (1 : Fin 2) else 0
  have hg : Measurable g := measurable_const.ite hs measurable_const
  have hcomp : finTwoEquiv ∘ g = f := by
    funext x
    cases hx : f x <;> simp [g, s, hx] <;> rfl
  nth_rw 1 [← hcomp]
  rw [← Measure.map_map Measurable.of_discrete hg]
  change (μ.map g).map finTwoEquiv = _
  rw [map_event_bernoulliFin μ s hs,
    map_bernoulliMeasure' (1 : Fin 2) 0 Measurable.of_discrete]
  rfl

/-- Pinsker for the probability of any measurable event, via its two-point law. -/
private theorem event_difference_le_sqrt {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set α) (hs : MeasurableSet s) {d : ℝ} (hd : 0 ≤ d)
    (hc : klDiv μ ν ≤ ENNReal.ofReal d) :
    |ν.real s - μ.real s| ≤ Real.sqrt (d / 2) := by
  classical
  have hfinite : klDiv μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc
  have hac := (klDiv_ne_top_iff.mp hfinite).1
  by_cases hν0 : ν s = 0
  · simpa [measureReal_def, hν0, hac hν0] using Real.sqrt_nonneg (d / 2)
  by_cases hν1 : ν s = 1
  · have hνc : ν sᶜ = 0 := by rw [measure_compl hs (measure_ne_top ν s), measure_univ, hν1]; simp
    have hμ1 : μ s = 1 := by
      rw [← measure_univ (μ := μ), ← Set.union_compl_self s,
        measure_union disjoint_compl_right hs.compl, hac hνc, add_zero]
    simpa [measureReal_def, hν1, hμ1] using Real.sqrt_nonneg (d / 2)
  let p : unitInterval := ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩
  let q : unitInterval := ⟨ν.real s, measureReal_nonneg, measureReal_le_one⟩
  have hq : (q : ℝ) ∈ Set.Ioo 0 1 := by
    constructor
    · exact ENNReal.toReal_pos hν0 (measure_ne_top ν s)
    · change (ν s).toReal < 1
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top ν s) ENNReal.one_ne_top).2
        (lt_of_le_of_ne (prob_le_one (μ := ν)) hν1)
  have hm : Measurable (fun x => if x ∈ s then (1 : Fin 2) else 0) :=
    measurable_const.ite hs measurable_const
  have hbound := (klDiv_map_le μ ν hm).trans hc
  rw [map_event_bernoulliFin μ s hs, map_event_bernoulliFin ν s hs] at hbound
  change klDiv (bernoulliMeasure (1 : Fin 2) 0 p) (bernoulliMeasure (1 : Fin 2) 0 q) ≤
    ENNReal.ofReal d at hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [klDiv_bernoulliFin_toReal p q (bernoulliFin_ac p q hq), ENNReal.toReal_ofReal hd] at hreal
  have hsquare := (RegretBandits.Stochastic.kl_bernoulli_bounds p q p.property hq).1.trans hreal
  change 2 * (μ.real s - ν.real s) ^ 2 ≤ d at hsquare
  have hsq : (ν.real s - μ.real s) ^ 2 ≤ d / 2 := by nlinarith
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-- Adaptive event counts under two laws obtained by successively appending observations.
The initial measures are equal, and the one-step divergence is charged only where the event
of interest occurs. -/
private theorem adaptive_count_difference_le {A : ℕ → Type*} [mA : ∀ t, MeasurableSpace (A t)]
    {B : Type*} [MeasurableSpace B] [MeasurableSpace.CountablyGenerated B]
    (μ ν : ∀ t, Measure (A t)) [∀ t, IsProbabilityMeasure (μ t)] [∀ t, IsProbabilityMeasure (ν t)]
    (κ η : ∀ t, Kernel (A t) B) [∀ t, IsMarkovKernel (κ t)] [∀ t, IsMarkovKernel (η t)]
    (step : ∀ t, A t × B → A (t + 1)) (hstep : ∀ t, Measurable (step t))
    (hμ : ∀ t, μ (t + 1) = (μ t ⊗ₘ κ t).map (step t))
    (hν : ∀ t, ν (t + 1) = (ν t ⊗ₘ η t).map (step t))
    (hinit : μ 0 = ν 0)
    (event : ∀ t, Set (A t)) (hevent : ∀ t, MeasurableSet (event t))
    {c : ℝ} (hc : 0 ≤ c)
    (hcost : ∀ t x, klDiv (κ t x) (η t x) ≤ ENNReal.ofReal ((event t).indicator (fun _ => c) x))
    (T : ℕ) :
    (∑ t ∈ Finset.range T, (ν t).real (event t)) - (∑ t ∈ Finset.range T, (μ t).real (event t)) ≤
      T * Real.sqrt (c * (∑ t ∈ Finset.range T, (μ t).real (event t)) / 2) := by
  have hac (t : ℕ) (x : A t) : κ t x ≪ η t x :=
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcost t x))).1
  have hdiv (t : ℕ) :
      klDiv (μ t) (ν t) ≤ ENNReal.ofReal (c * (∑ i ∈ Finset.range t, (μ i).real (event i))) := by
    induction t with
    | zero => simp [hinit]
    | succ t ih =>
      rw [hμ t, hν t]
      apply (klDiv_map_le _ _ (hstep t)).trans
      rw [klDiv_compProd_eq_add, klDiv_compProd_self_eq_lintegral (μ t) (κ t) (η t) (hac t)]
      have hi :
          ∫⁻ x, klDiv (κ t x) (η t x) ∂(μ t) ≤ ENNReal.ofReal (c * (μ t).real (event t)) := by
        apply (lintegral_mono (hcost t)).trans
        rw [show (fun x => ENNReal.ofReal ((event t).indicator (fun _ => c) x)) =
          (event t).indicator (fun _ => ENNReal.ofReal c) by
          ext x
          by_cases hx : x ∈ event t <;> simp [Set.indicator, hx]]
        rw [lintegral_indicator_const (hevent t), ENNReal.ofReal_mul hc, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [Finset.sum_range_succ, mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add ih hi
  let d := c * (∑ i ∈ Finset.range T, (μ i).real (event i))
  have hd : 0 ≤ d := by dsimp [d]; positivity
  rw [← Finset.sum_sub_distrib]
  apply le_trans (Finset.sum_le_sum (g := fun _ => Real.sqrt (d / 2)) ?_)
  · simp [d]
  · intro t ht
    have hsub := Finset.range_mono (Finset.mem_range.mp ht).le
    have hbound := (hdiv t).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => measureReal_nonneg)) hc))
    exact (le_abs_self _).trans (event_difference_le_sqrt (μ t) (ν t) _ (hevent t) hd hbound)

end BilateralProfitLB

end InformationPart4

section InformationPart5

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace BilateralProfitLB

private lemma rho_nonneg_for_information (u : ℝ) : 0 ≤ rho u := by
  classical
  unfold rho
  split_ifs <;> positivity

private lemma Sj_eq_outside {K j : ℕ} {q : ℝ} (hq : q ∉ I K j) : S K j q = S0 q := by
  simp [S, hq]

/-- The reciprocal perturbation bounds entering (77). -/
private theorem survival_information_bounds {K j : ℕ} {q : ℝ} (hj : 1 ≤ j) (hjK : j ≤ K)
    (hq : q ∈ I K j) :
    S K j q ∈ Set.Ioo (0 : ℝ) 1 ∧
      (S0 q - S K j q) ^ 2 / (S K j q * (1 - S K j q)) ≤ w K ^ 4 := by
  have hK : 0 < K := by omega
  have hwindow := I_subset hj hjK hq
  have hlow : 1 / 4 < q := hwindow.1
  have hhigh : q < 1 / 2 := hwindow.2
  have hY0 : Y0 q = 48 * q ^ 2 := by
    rw [Y0, S0, if_neg (not_le_of_gt hlow), if_pos hhigh.le, one_div_one_div]
  have hY0lo : 3 ≤ Y0 q := by
    rw [hY0]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hlow.le 2
    nlinarith
  have hY0hi : Y0 q ≤ 12 := by
    rw [hY0]
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ q) hhigh.le 2
    nlinarith
  have hw := (w_pos hK).le
  have hw2 := pow_le_pow_left₀ hw ((w_le_quarter hK).trans (by norm_num : (1/4:ℝ) ≤ 1)) 2
  have hρlo := rho_nonneg_for_information ((q - a K j) / w K)
  have hρhi := claim_7_2.2.1.1 ((q - a K j) / w K)
  have hb : 0 ≤ 1 / 2 * w K ^ 2 * rho ((q - a K j) / w K) := by positivity
  have hb' : 1 / 2 * w K ^ 2 * rho ((q - a K j) / w K) ≤ w K ^ 2 := by
    calc
      _ ≤ 1 / 2 * w K ^ 2 * 1 := mul_le_mul_of_nonneg_left hρhi (by positivity)
      _ ≤ _ := by nlinarith
  have hYlo : 2 ≤ Y K j q := by
    unfold Y
    nlinarith
  have hYhi : Y K j q ≤ 12 := by
    unfold Y
    linarith
  have hYpos : 0 < Y K j q := by linarith
  have hY0pos : 0 < Y0 q := by linarith
  have hSj : S K j q = 1 / Y K j q := by simp [S, hj, hjK, hq]
  have hS0 : S0 q = 1 / Y0 q := by simp [Y0]
  have hSlo : 1 / 12 ≤ S K j q := by
    rw [hSj]
    exact one_div_le_one_div_of_le hYpos hYhi
  have hShi : S K j q ≤ 1 / 2 := by
    rw [hSj]
    exact one_div_le_one_div_of_le (by norm_num) hYlo
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  have hdenom : (1 / 24 : ℝ) ≤ S K j q * (1 - S K j q) := by
    calc
      _ = (1 / 12) * (1 / 2) := by norm_num
      _ ≤ _ := mul_le_mul hSlo (by linarith) (by norm_num) (by linarith)
  have hYmul : (6 : ℝ) ≤ Y0 q * Y K j q := by
    calc
      _ = 3 * 2 := by norm_num
      _ ≤ _ := mul_le_mul hY0lo hYlo (by norm_num) hY0pos.le
  have hdiff : S0 q - S K j q = (Y K j q - Y0 q) / (Y0 q * Y K j q) := by
    rw [hS0, hSj]
    field_simp [hY0pos.ne', hYpos.ne']
  have habs : |S0 q - S K j q| ≤ w K ^ 2 / 6 := by
    rw [hdiff, abs_div, abs_of_pos (mul_pos hY0pos hYpos), Y, sub_sub_cancel_left,
      abs_neg, abs_of_nonneg hb]
    exact div_le_div₀ (sq_nonneg _) hb' (by norm_num) hYmul
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hsq
  apply (div_le_iff₀ (by linarith : 0 < S K j q * (1 - S K j q))).2
  calc
    _ ≤ (w K ^ 2 / 6) ^ 2 := hsq
    _ ≤ w K ^ 4 * (1 / 24) := by nlinarith [sq_nonneg (w K ^ 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdenom (by positivity)

private lemma buyer_acceptance {μ : Measure ℝ} [IsProbabilityMeasure μ] (q : ℝ) :
    μ.map (fun b => decide (q ≤ b)) =
      bernoulliMeasure true false ⟨μ.real (Set.Ici q), measureReal_nonneg, measureReal_le_one⟩ := by
  have hm : Measurable (fun b => decide (q ≤ b)) := by
    change Measurable (fun b => if b ∈ Set.Ici q then true else false)
    exact measurable_const.ite measurableSet_Ici measurable_const
  rw [map_bool_eq_bernoulli μ _ hm]
  congr 1
  apply Subtype.ext
  apply congrArg μ.real
  ext b
  change decide (q ≤ b) = true ↔ q ≤ b
  exact decide_eq_true_iff

/-- One-step information for two independent acceptance bits and a common seller law. -/
private theorem two_bit_kl_le {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K)
    (seller baseline alternative : Measure ℝ) [IsProbabilityMeasure seller]
    [IsProbabilityMeasure baseline] [IsProbabilityMeasure alternative]
    (p q : ℝ) (hbase : baseline.real (Set.Ici q) = S0 q)
    (halt : alternative.real (Set.Ici q) = S K j q) :
    klDiv ((seller.prod baseline).map (fun v => feedback v (p,q)))
      ((seller.prod alternative).map (fun v => feedback v (p,q))) ≤
      ENNReal.ofReal ((I K j).indicator (fun _ => w K ^ 4) q) := by
  classical
  have hms : Measurable (fun s : ℝ => decide (s ≤ p)) := by
    change Measurable (fun s => if s ∈ Set.Iic p then true else false)
    exact measurable_const.ite measurableSet_Iic measurable_const
  have hmb : Measurable (fun b : ℝ => decide (q ≤ b)) := by
    change Measurable (fun b => if b ∈ Set.Ici q then true else false)
    exact measurable_const.ite measurableSet_Ici measurable_const
  change klDiv
    ((seller.prod baseline).map (Prod.map (fun s : ℝ => decide (s ≤ p)) (fun b : ℝ => decide (q ≤ b))))
    ((seller.prod alternative).map (Prod.map
      (fun s : ℝ => decide (s ≤ p)) (fun b : ℝ => decide (q ≤ b)))) ≤ _
  rw [← Measure.map_prod_map seller baseline hms hmb,
    ← Measure.map_prod_map seller alternative hms hmb]
  have : IsProbabilityMeasure (seller.map (fun s => decide (s ≤ p))) :=
    Measure.isProbabilityMeasure_map hms.aemeasurable
  rw [klDiv_prod_common_left, buyer_acceptance q, buyer_acceptance q]
  by_cases hq : q ∈ I K j
  · have hinfo := survival_information_bounds hj hjK hq
    have hqi : alternative.real (Set.Ici q) ∈ Set.Ioo (0 : ℝ) 1 := halt ▸ hinfo.1
    apply (klDiv_bernoulliBool_le _ _ hqi).trans
    apply ENNReal.ofReal_le_ofReal
    change (baseline.real (Set.Ici q) - alternative.real (Set.Ici q)) ^ 2 /
      (alternative.real (Set.Ici q) * (1 - alternative.real (Set.Ici q))) ≤ _
    rw [hbase, halt, Set.indicator_of_mem hq]
    exact hinfo.2
  · have heq :
        (⟨baseline.real (Set.Ici q), measureReal_nonneg, measureReal_le_one⟩ : unitInterval) =
        ⟨alternative.real (Set.Ici q), measureReal_nonneg, measureReal_le_one⟩ :=
      Subtype.ext (hbase.trans (halt.trans (Sj_eq_outside hq)).symm)
    rw [heq, klDiv_self]
    exact bot_le

/-- The one-step bound \(w^4\) implies the coefficient in Claim 3.6. -/
private theorem sqrt_information_cost_le {K : ℕ} (hK : 0 < K) (T : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (T : ℝ) * Real.sqrt (w K ^ 4 * x / 2) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) * Real.sqrt x := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hw : w K ^ 2 = 1 / (16 * (K : ℝ) ^ 2) := by
    unfold w
    field_simp
    ring
  have hroot : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h22 : (22 : ℝ) ≤ 16 * Real.sqrt 2 := by
    have h : (11 / 8 : ℝ) ≤ Real.sqrt 2 := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).2
      norm_num
    linarith
  rw [show w K ^ 4 * x / 2 = (w K ^ 2) ^ 2 * (x / 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _), hw, Real.sqrt_div hx]
  calc
    _ = (T : ℝ) * Real.sqrt x * (1 / ((16 * Real.sqrt 2) * (K : ℝ) ^ 2)) := by
      field_simp
    _ ≤ (T : ℝ) * Real.sqrt x * (1 / (22 * (K : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right h22 (sq_nonneg _))) (by positivity)
    _ = _ := by ring

end BilateralProfitLB

end InformationPart5

section InformationPart6

open MeasureTheory InformationTheory

namespace BilateralProfitLB

/-- The one-step bound from (77) for the registered hard-instance laws. -/
private theorem one_step_kl_le (hClaim : HardLawClaim) {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K)
    (price : ℝ × ℝ) (hq : price.2 ∈ Set.Icc (0 : ℝ) 1) :
    klDiv ((law K 0).map (fun v => feedback v price))
      ((law K j).map (fun v => feedback v price)) ≤
      ENNReal.ofReal ((I K j).indicator (fun _ => w K ^ 4) price.2) := by
  rcases price with ⟨p,q⟩
  have hK := hj.trans hjK
  have := sellerMeasure_isProbabilityMeasure_unit
  have := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK (Nat.zero_le K)
  have := buyerMeasure_isProbabilityMeasure_of_claim_7_3 hClaim hK hjK
  unfold law
  apply two_bit_kl_le hj hjK
  · simpa [S] using buyerMeasure_Ici_real_of_claim_7_3 hClaim hK (Nat.zero_le K) hq
  · exact buyerMeasure_Ici_real_of_claim_7_3 hClaim hK hjK hq

end BilateralProfitLB

end InformationPart6

section InformationPart7

open MeasureTheory ProbabilityTheory InformationTheory

namespace BilateralProfitLB

/-- Claim 3.6 with the policy seed included in the transcript law. -/
private theorem expCount_transfer (hClaim : HardLawClaim) {Ω : Type} [MeasurableSpace Ω] (π : Policy Ω)
    (P : Measure Ω) [IsProbabilityMeasure P] {K j : ℕ} (hK : 1 ≤ K)
    (hj : 1 ≤ j) (hjK : j ≤ K) (T : ℕ) :
    expCount π P (law K j) T (I K j) - expCount π P (law K 0) T (I K j) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) * Real.sqrt (expCount π P (law K 0) T (I K j)) := by
  have hμ := law_isProbabilityMeasure_of_claim_7_3 hClaim hK (Nat.zero_le K)
  have hν := law_isProbabilityMeasure_of_claim_7_3 hClaim hK hjK
  have hI : MeasurableSet (I K j) := measurableSet_Ioo
  let event (t : ℕ) : Set (PrefixState Ω t) := {z | (protocolPrice π z).2 ∈ I K j}
  have hevent (t : ℕ) : MeasurableSet (event t) :=
    (protocolPrice_measurable π t).snd hI
  have hcost (t : ℕ) (z : PrefixState Ω t) :
      klDiv (feedbackKernel π (law K 0) t z) (feedbackKernel π (law K j) t z) ≤
        ENNReal.ofReal ((event t).indicator (fun _ => w K ^ 4) z) := by
    have hs := one_step_kl_le hClaim hj hjK (protocolPrice π z) (protocolPrice_mem π z).2
    by_cases hq : (protocolPrice π z).2 ∈ I K j
    · simpa [event, hq, Set.indicator, feedbackKernel_apply] using hs
    · simpa [event, hq, Set.indicator, feedbackKernel_apply] using hs
  have hbound := adaptive_count_difference_le
    (prefixLaw π P (law K 0)) (prefixLaw π P (law K j))
    (feedbackKernel π (law K 0)) (feedbackKernel π (law K j))
    (protocolUpdate (Ω := Ω)) (protocolUpdate_measurable (Ω := Ω))
    (prefixLaw_succ π P (law K 0)) (prefixLaw_succ π P (law K j))
    (prefixLaw_zero_same π P (law K 0) (law K j)) event hevent
    (c := w K ^ 4) (by positivity) hcost T
  rw [← expCount_eq_sum_prefix π P (law K j) T (I K j) hI,
    ← expCount_eq_sum_prefix π P (law K 0) T (I K j) hI] at hbound
  exact hbound.trans
    (sqrt_information_cost_le hK T (expCount_nonneg π P (law K 0) T (I K j)))

end BilateralProfitLB

open BilateralProfitLB

theorem solution (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (π : Policy Ω) :
    expCount π P (law K j) T (I K j) - expCount π P (law K 0) T (I K j) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) * Real.sqrt (expCount π P (law K 0) T (I K j)) :=
  expCount_transfer claim_7_3 π P hK hj1 hjK T

end InformationPart7
