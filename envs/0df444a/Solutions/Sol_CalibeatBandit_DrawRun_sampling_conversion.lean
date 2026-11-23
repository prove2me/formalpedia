-- Prove2me | solution 1 for CalibeatBandit.DrawRun.sampling_conversion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:57:15.888472+00:00
-- url     : https://prove2.me/submissions/31ce893f-69e7-41d3-a981-3c113698b9ba

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_Supplement_PricingRegretBound
import Definitions.Def_CalibeatBandit_draw_run

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem info_le_info (run : DrawRun K T P) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    run.info a ≤ run.info b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih =>
    exact (ih (by omega)).trans ((run.info_le_preDraw _ (by omega)).trans (run.preDraw_le_succ _ (by omega)))

theorem preDraw_le_ambient (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ mΩ :=
  (run.preDraw_le_succ t ht).trans (run.info_le _ (Nat.succ_le_of_lt ht))

end DrawRun

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- Conditional expectation of a bounded function evaluated at the played action. -/
theorem DrawRun.condExp_select_played {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P) {t : ℕ} (ht : t < T)
    (g : Fin K → Ω → ℝ) (hg : ∀ j, Measurable[run.preDraw t] (g j))
    (B : ℝ) (hb : ∀ j ω, |g j ω| ≤ B) :
    Integrable (fun ω => g (run.I t ω) ω) P ∧
    condExp (run.preDraw t) P (fun ω => g (run.I t ω) ω) =ᵐ[P]
      fun ω => ∑ j, run.played t ω j * g j ω := by
  classical
  let ind (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  have hm := run.preDraw_le_ambient ht
  have im (j : Fin K) : Measurable (ind j) :=
    measurable_const.indicator ((run.I_measurable t ht).mono
      (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have ib (j : Fin K) (ω : Ω) : ind j ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : run.I t ω = j <;> simp [ind, h]
  have ii (j : Fin K) : Integrable (ind j) P :=
    (integrable_const (1 : ℝ)).mono' (im j).aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ib j ω).1] using (ib j ω).2)
  have gi (j : Fin K) : Integrable (g j * ind j) P :=
    (integrable_const B).mono' (((hg j).mono hm le_rfl).mul (im j)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        change ‖g j ω * ind j ω‖ ≤ B
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ib j ω).1]
        exact (mul_le_of_le_one_right (abs_nonneg _) (ib j ω).2).trans (hb j ω))
  have heq : (fun ω => g (run.I t ω) ω) = ∑ j, g j * ind j := by
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, ind, Set.indicator_apply,
      Set.mem_preimage, Set.mem_singleton_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [heq]
  refine ⟨integrable_finsetSum' _ (fun j _ => gi j), (condExp_finsetSum (fun j _ => gi j) _).trans ?_⟩
  have hcoord (j : Fin K) :
      condExp (run.preDraw t) P (g j * ind j) =ᵐ[P] fun ω => g j ω * run.played t ω j := by
    refine (condExp_mul_of_stronglyMeasurable_left (hg j).stronglyMeasurable (gi j) (ii j)).trans ?_
    filter_upwards [run.I_law t ht j] with ω hω
    change condExp (run.preDraw t) P (ind j) ω = run.played t ω j at hω
    change g j ω * condExp (run.preDraw t) P (ind j) ω = _
    rw [hω]
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => (hω j).trans (mul_comm _ _)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl

theorem DrawRun.integral_exp_sum_le_one {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[run.info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (run.preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 :=
  CalibeatBandit.integral_exp_sum_le_one P run.info run.preDraw
    (fun _ _ h => run.info_le_info h) run.info_le
    (fun _ ht => run.preDraw_le_ambient ht) run.info_le_preDraw d hm hb hc

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

/-- A finite maximum is bounded in expectation by the logarithm of the number
of competitors whenever each competitor has an exponential moment at most one. -/
theorem integral_max_le_log_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {η B : ℝ} (hη : 0 < η)
    (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B)
    (he : ∀ i, ∫ ω, Real.exp (η * F i ω) ∂P ≤ 1) :
    ∫ ω, Finset.univ.sup' hne (fun i => F i ω) ∂P ≤ Real.log (Fintype.card ι) / η := by
  classical
  let M (ω : Ω) := Finset.univ.sup' hne (fun i => F i ω)
  let Z (ω : Ω) := ∑ i, Real.exp (η * F i ω)
  let N : ℝ := Fintype.card ι
  let H (ω : Ω) := Real.log N + (Z ω / N - 1)
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hM : Integrable M P := integrable_finset_max hne F hm hb
  have hei (i : ι) : Integrable (fun ω => Real.exp (η * F i ω)) P := by
    refine integrable_of_abs_bound (B := Real.exp (η * B))
      (Real.continuous_exp.measurable.comp ((hm i).const_mul η)) ?_
    intro ω
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb i ω)) hη.le)
  have hZ : Integrable Z P := integrable_finsetSum _ fun i _ => hei i
  have hZi : (∫ ω, Z ω ∂P) ≤ N := by
    rw [show (∫ ω, Z ω ∂P) = ∑ i, ∫ ω, Real.exp (η * F i ω) ∂P from
      integral_finsetSum _ (fun i _ => hei i)]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => he i
      _ = N := by simp [N]
  have hH : Integrable H P := (integrable_const _).add ((hZ.div_const N).sub (integrable_const _))
  have hpoint (ω : Ω) : η * M ω ≤ H ω := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    have hle : Real.exp (η * M ω) ≤ Z ω := by
      change Real.exp (η * Finset.univ.sup' hne (fun i => F i ω)) ≤ Z ω
      rw [hi]
      exact Finset.single_le_sum (fun j _ => Real.exp_nonneg (η * F j ω)) (Finset.mem_univ i)
    have hz : 0 < Z ω := (Real.exp_pos _).trans_le hle
    have hl := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hl
    have hh := Real.log_le_sub_one_of_pos (div_pos hz hN)
    rw [Real.log_div hz.ne' hN.ne'] at hh
    dsimp [H]
    linarith only [hl, hh]
  have hHi : (∫ ω, H ω ∂P) ≤ Real.log N := by
    let W : Ω → ℝ := fun ω => Z ω / N
    change (∫ ω, Real.log N + (W ω - 1) ∂P) ≤ _
    have hW : Integrable W P := hZ.div_const N
    have hdiff : Integrable (fun ω => W ω - 1) P := hW.sub (integrable_const _)
    rw [integral_add (integrable_const _) hdiff, integral_sub hW (integrable_const _)]
    dsimp only [W]
    rw [integral_div]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith only [(div_le_one hN).mpr hZi]
  have hi := (integral_mono (hM.const_mul η) hH hpoint).trans hHi
  have heq : (∫ ω, η * M ω ∂P) = η * ∫ ω, M ω ∂P := integral_const_mul η M
  rw [heq] at hi
  exact (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hi)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- The draw law determines a pre-draw measurable version of the vector of play
probabilities, with a probability vector also on its exceptional null set. -/
theorem DrawRun.exists_played_version {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P) (j₀ : Fin K) {t : ℕ} (ht : t < T) :
    ∃ p : Ω → Fin K → ℝ, Measurable[run.preDraw t] p ∧
      (∀ ω, IsProbVec (p ω)) ∧ p =ᵐ[P] run.played t := by
  classical
  let ind (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  let q (j : Fin K) := condExp (run.preDraw t) P (ind j)
  have hmeas (j : Fin K) : Measurable[run.preDraw t] (q j) := stronglyMeasurable_condExp.measurable
  have hn (j : Fin K) : 0 ≤ᵐ[P] q j := condExp_nonneg (ae_of_all _ fun ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hI := (run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
  have hi (j : Fin K) : Integrable (ind j) P :=
    (integrable_const (1 : ℝ)).indicator (hI (measurableSet_singleton j))
  have hind : (∑ j, ind j) = fun _ => 1 := by
    funext ω
    simp [ind, Set.indicator_apply]
  have hsum : ∀ᵐ ω ∂P, ∑ j, q j ω = 1 := by
    have h := condExp_finsetSum (s := Finset.univ) (fun j _ => hi j) (run.preDraw t)
    rw [hind, condExp_const (run.preDraw_le_ambient ht)] at h
    filter_upwards [h.symm] with ω hw
    simpa only [Finset.sum_apply] using hw
  have haq : ∀ᵐ ω ∂P, IsProbVec (fun j => q j ω) := by
    filter_upwards [ae_all_iff.mpr hn, hsum] with ω h₁ h₂
    exact ⟨h₁, h₂⟩
  have heq : ∀ᵐ ω ∂P, ∀ j, q j ω = run.played t ω j := ae_all_iff.mpr (run.I_law t ht)
  let p (ω : Ω) : Fin K → ℝ := if IsProbVec (fun j => q j ω) then fun j => q j ω else Pi.single j₀ 1
  have hsingle : IsProbVec (Pi.single j₀ (1 : ℝ)) := by
    constructor
    · intro j
      by_cases h : j = j₀ <;> simp [h]
    · simp [Pi.single_apply]
  refine ⟨p, ?_, fun ω => ?_, ?_⟩
  · let : MeasurableSpace Ω := run.preDraw t
    have hs : MeasurableSet {ω | IsProbVec (fun j => q j ω)} := by
      change MeasurableSet ({ω | ∀ j, 0 ≤ q j ω} ∩ {ω | ∑ j, q j ω = 1})
      have hnonneg : MeasurableSet {ω | ∀ j, 0 ≤ q j ω} := by
        have heq : {ω | ∀ j, 0 ≤ q j ω} = ⋂ j, {ω | 0 ≤ q j ω} := by ext ω; simp
        rw [heq]
        exact MeasurableSet.iInter (fun j =>
          measurableSet_le (measurable_const (a := (0 : ℝ))) (hmeas j))
      refine hnonneg.inter ?_
      exact (Finset.measurable_sum _ fun j _ => hmeas j) (measurableSet_singleton 1)
    exact Measurable.ite hs (measurable_pi_iff.mpr hmeas) measurable_const
  · by_cases h : IsProbVec (fun j => q j ω)
    · simpa only [p, if_pos h] using h
    · simpa only [p, if_neg h] using hsingle
  · filter_upwards [haq, heq] with ω h₁ h₂
    exact funext fun j => by simpa only [p, if_pos h₁] using h₂ j

private theorem finite_hoeffding {K : ℕ} (p a : Fin K → ℝ) (hp : IsProbVec p)
    (ha : ∀ j, a j ∈ Set.Icc (-1 : ℝ) 1) (s : ℝ) :
    ∑ j, p j * Real.exp (s * (a j - ∑ i, p i * a i) - s ^ 2 / 2) ≤ 1 := by
  have hsum : ∑ j, ENNReal.ofReal (p j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp.1 j), hp.2, ENNReal.ofReal_one]
  let pm := PMF.ofFintype (fun j => ENNReal.ofReal (p j)) hsum
  have hm (f : Fin K → ℝ) : (∫ j, f j ∂pm.toMeasure) = ∑ j, p j * f j := by
    rw [PMF.integral_eq_sum]
    simp [pm, ENNReal.toReal_ofReal (hp.1 _), smul_eq_mul]
  have hexp := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := pm.toMeasure)
    (Measurable.of_discrete.aemeasurable : AEMeasurable a pm.toMeasure) (ae_of_all _ ha)).mgf_le s
  simp only [ProbabilityTheory.mgf, hm] at hexp
  have hexp' : ∑ j, p j * Real.exp (s * (a j - ∑ i, p i * a i)) ≤ Real.exp (s ^ 2 / 2) := by
    convert hexp using 2
    norm_num
  calc
    _ = Real.exp (-(s ^ 2 / 2)) * ∑ j, p j * Real.exp (s * (a j - ∑ i, p i * a i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (-(s ^ 2 / 2)) * Real.exp (s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hexp' (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

set_option maxHeartbeats 800000 in
/-- Sampling conversion in the proof of Lemma C.1, for any policy satisfying
the protocol's conditional draw law. -/
theorem DrawRun.sampling_conversion {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) (hK : 0 < K) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
      ≤ ∫ ω, pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) ∂P
        + Real.sqrt (2 * T * K * Real.log K) := by
  classical
  by_cases hT : T = 0
  · subst T
    simp [swapRegret, pseudoSwapRegret]
  by_cases hOne : K = 1
  · subst K
    have heq (f : Fin 1 → Fin 1) (j : Fin 1) : f j = j := Subsingleton.elim _ _
    simp [swapRegret, pseudoSwapRegret, heq, dotProduct]
  let j₀ : Fin K := ⟨0, hK⟩
  have chosen (t : ℕ) : ∃ p : Ω → Fin K → ℝ, Measurable[run.preDraw t] p ∧
      (∀ ω, IsProbVec (p ω)) ∧ (t < T → p =ᵐ[P] run.played t) := by
    by_cases ht : t < T
    · obtain ⟨p, hm, hp, heq⟩ := run.exists_played_version P j₀ ht
      exact ⟨p, hm, hp, fun _ => heq⟩
    · have hi : IsProbVec (Pi.single j₀ (1 : ℝ)) := by
        constructor
        · intro j
          by_cases h : j = j₀ <;> simp [h]
        · simp [Pi.single_apply]
      exact ⟨fun _ => Pi.single j₀ 1, measurable_const, fun _ => hi, fun h => (ht h).elim⟩
  choose p hpM hp hpEq using chosen
  have hpAE : ∀ᵐ ω ∂P, ∀ t ∈ Finset.range T, p t ω = run.played t ω :=
    (ae_all_iff.mpr fun (t : Fin T) => hpEq t t.isLt).mono fun ω h t ht =>
      h ⟨t, Finset.mem_range.mp ht⟩
  let a (t : ℕ) (f : Fin K → Fin K) (j : Fin K) (ω : Ω) :=
    run.y t ω (f j) - run.y t ω j
  let b (t : ℕ) (f : Fin K → Fin K) (ω : Ω) := ∑ j, p t ω j * a t f j ω
  let v (t : ℕ) (f : Fin K → Fin K) (ω : Ω) := a t f (run.I t ω) ω
  let d (t : ℕ) (f : Fin K → Fin K) (ω : Ω) := v t f ω - b t f ω
  have haM (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (j : Fin K) :
      Measurable[run.preDraw t] (a t f j) := by
    have hy := run.y_measurable t ht
    exact ((measurable_pi_apply (f j)).comp hy).sub ((measurable_pi_apply j).comp hy)
  have ha (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (j : Fin K) (ω : Ω) :
      a t f j ω ∈ Set.Icc (-1 : ℝ) 1 := by
    have h₁ := run.y_mem t ht ω (f j)
    have h₂ := run.y_mem t ht ω j
    exact ⟨by dsimp [a]; linarith [h₁.1, h₂.2], by dsimp [a]; linarith [h₁.2, h₂.1]⟩
  have hbM (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      Measurable[run.preDraw t] (b t f) :=
    Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp (hpM t)).mul (haM t ht f j)
  have hb (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (ω : Ω) : |b t f ω| ≤ 1 := by
    calc
      _ ≤ ∑ j, |p t ω j * a t f j ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, p t ω j := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg ((hp t ω).1 j)]
        exact mul_le_of_le_one_right ((hp t ω).1 j) (abs_le.mpr (ha t ht f j ω))
      _ = 1 := (hp t ω).2
  have hvM (t : ℕ) (ht : t < T) (f : Fin K → Fin K) : Measurable[run.info (t + 1)] (v t f) :=
    @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ (run.I_measurable t ht)
      (a t f) (fun j => (haM t ht f j).mono (run.preDraw_le_succ t ht) le_rfl)
  have hdM (t : ℕ) (ht : t < T) (f : Fin K → Fin K) : Measurable[run.info (t + 1)] (d t f) :=
    (hvM t ht f).sub ((hbM t ht f).mono (run.preDraw_le_succ t ht) le_rfl)
  have hd (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (ω : Ω) : |d t f ω| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith [abs_le.mpr (ha t ht f (run.I t ω) ω), hb t ht f ω])
  have hstep (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (s : ℝ) :
      condExp (run.preDraw t) P (fun ω => Real.exp (s * d t f ω - s ^ 2 / 2))
        ≤ᵐ[P] fun _ => 1 := by
    let g (j : Fin K) (ω : Ω) := Real.exp (s * (a t f j ω - b t f ω) - s ^ 2 / 2)
    have gm (j : Fin K) : Measurable[run.preDraw t] (g j) :=
      Real.continuous_exp.measurable.comp
        ((((haM t ht f j).sub (hbM t ht f)).const_mul s).sub measurable_const)
    have gb (j : Fin K) (ω : Ω) : |g j ω| ≤ Real.exp (|s| * 2) := by
      rw [show g j ω = Real.exp (s * (a t f j ω - b t f ω) - s ^ 2 / 2) from rfl,
        abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ s * (a t f j ω - b t f ω) := sub_le_self _ (by positivity)
        _ ≤ |s| * |a t f j ω - b t f ω| := le_trans (le_abs_self _) (by rw [abs_mul])
        _ ≤ |s| * 2 := mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
          (by linarith [abs_le.mpr (ha t ht f j ω), hb t ht f ω])) (abs_nonneg s)
    obtain ⟨_, h⟩ := run.condExp_select_played P ht g gm _ gb
    filter_upwards [h, hpEq t ht] with ω hω eqω
    rw [show condExp (run.preDraw t) P (fun ω => Real.exp (s * d t f ω - s ^ 2 / 2)) ω =
      condExp (run.preDraw t) P (fun ω => g (run.I t ω) ω) ω from rfl, hω, ← eqω]
    exact finite_hoeffding _ (fun j => a t f j ω) (hp t ω) (fun j => ha t ht f j ω) s
  let maxSum (g : ℕ → (Fin K → Fin K) → Ω → ℝ) (ω : Ω) :=
    Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => ∑ t ∈ Finset.range T, g t f ω)
  have sumBound (g : ℕ → (Fin K → Fin K) → Ω → ℝ) (B : ℝ)
      (hb : ∀ t < T, ∀ f ω, |g t f ω| ≤ B) (f : Fin K → Fin K) (ω : Ω) :
      |∑ t ∈ Finset.range T, g t f ω| ≤ T * B := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |g t f ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, B := Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) f ω
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have maxInt (g : ℕ → (Fin K → Fin K) → Ω → ℝ) {B : ℝ}
      (hm : ∀ t < T, ∀ f, Measurable[run.info (t + 1)] (g t f))
      (hb : ∀ t < T, ∀ f ω, |g t f ω| ≤ B) :
      Integrable (maxSum g) P :=
    integrable_finset_max ⟨id, Finset.mem_univ _⟩ _
      (fun f => Finset.measurable_sum _ fun t ht =>
        (hm t (Finset.mem_range.mp ht) f).mono (run.info_le _ (Finset.mem_range.mp ht)) le_rfl)
      (sumBound g B hb)
  have hiD := maxInt d hdM hd
  have hiV := maxInt v hvM (B := 1) (fun t ht f ω => abs_le.mpr (ha t ht f (run.I t ω) ω))
  have hiB := maxInt b (B := 1) (fun t ht f => (hbM t ht f).mono (run.preDraw_le_succ t ht) le_rfl) hb
  have hcompare : (∫ ω, maxSum v ω ∂P) ≤ (∫ ω, maxSum b ω ∂P) + ∫ ω, maxSum d ω ∂P := by
    rw [← integral_add hiB hiD]
    refine integral_mono hiV (hiB.add hiD) fun ω => Finset.sup'_le _ _ fun f hf => ?_
    have heq : (∑ t ∈ Finset.range T, v t f ω) =
        (∑ t ∈ Finset.range T, b t f ω) + (∑ t ∈ Finset.range T, d t f ω) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by dsimp [d]; ring
    rw [heq]
    exact add_le_add (Finset.le_sup' (fun g => ∑ t ∈ Finset.range T, b t g ω) hf)
      (Finset.le_sup' (fun g => ∑ t ∈ Finset.range T, d t g ω) hf)
  have hchange : (∫ ω, maxSum b ω ∂P) = ∫ ω,
      pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hpAE] with ω hω
    unfold maxSum pseudoSwapRegret
    congr 1
    funext f
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [b, a, mul_sub, Finset.sum_sub_distrib, hω t ht, dotProduct]
  change (∫ ω, maxSum v ω ∂P) ≤ _
  rw [← hchange]
  refine hcompare.trans (add_le_add_right ?_ _)
  let L : ℝ := K * Real.log K
  have hL : 0 < L := mul_pos (by exact_mod_cast hK) (Real.log_pos (by exact_mod_cast (show 1 < K by omega)))
  have ht : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  let R := Real.sqrt (2 * T * L)
  have hrad : 0 < 2 * T * L := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr hrad
  let s := R / T
  have hs : 0 < s := div_pos hR ht
  let F (f : Fin K → Fin K) (ω : Ω) := ∑ t ∈ Finset.range T, (d t f ω - s / 2)
  have hfm (f : Fin K → Fin K) : Measurable (F f) :=
    Finset.measurable_sum _ fun t ht =>
      ((hdM t (Finset.mem_range.mp ht) f).mono (run.info_le _ (Finset.mem_range.mp ht)) le_rfl).sub
        measurable_const
  have hfb (f : Fin K → Fin K) (ω : Ω) : |F f ω| ≤ T * (2 + |s / 2|) :=
    sumBound (fun t f ω => d t f ω - s / 2) _ (fun t ht f ω =>
      (abs_sub _ _).trans (add_le_add_left (hd t ht f ω) _)) f ω
  have hfe (f : Fin K → Fin K) : (∫ ω, Real.exp (s * F f ω) ∂P) ≤ 1 := by
    have h := run.integral_exp_sum_le_one P (fun t ω => s * d t f ω - s ^ 2 / 2)
      (B := |s| * 2 + |s ^ 2 / 2|)
      (fun t ht => ((hdM t ht f).const_mul s).sub measurable_const)
      (fun t ht ω => (abs_sub _ _).trans (by
        rw [abs_mul]
        gcongr
        exact hd t ht f ω))
      (fun t ht => hstep t ht f s)
    have eq (ω : Ω) : s * F f ω = ∑ t ∈ Finset.range T, (s * d t f ω - s ^ 2 / 2) := by
      simp only [F, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    simpa only [eq] using h
  have hF := integral_max_le_log_card P ⟨id, Finset.mem_univ _⟩ F hs hfm hfb hfe
  have hshift (ω : Ω) :
      Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => F f ω) = maxSum d ω - T * (s / 2) := by
    have heq (f : Fin K → Fin K) : F f ω = (∑ t ∈ Finset.range T, d t f ω) - T * (s / 2) := by
      simp only [F, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    obtain ⟨f, hf, he⟩ := Finset.exists_mem_eq_sup' ⟨id, Finset.mem_univ _⟩
      (fun f : Fin K → Fin K => ∑ t ∈ Finset.range T, d t f ω)
    apply le_antisymm
    · apply Finset.sup'_le
      intro g hg
      rw [heq]
      exact sub_le_sub_right (Finset.le_sup' (fun g => ∑ t ∈ Finset.range T, d t g ω) hg) _
    · rw [show maxSum d ω = ∑ t ∈ Finset.range T, d t f ω from he, ← heq]
      exact Finset.le_sup' (fun g => F g ω) hf
  simp_rw [hshift, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] at hF
  rw [integral_sub hiD (integrable_const (T * (s / 2)))] at hF
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hF
  have hRsq : R ^ 2 = 2 * T * L := Real.sq_sqrt hrad.le
  have hhalf : L / s = R / 2 := by
    apply (div_eq_iff hs.ne').mpr
    dsimp [s]
    field_simp [ht.ne']
    nlinarith only [hRsq]
  have hother : (T : ℝ) * (s / 2) = R / 2 := by
    dsimp [s]
    field_simp [ht.ne']
  change (∫ ω, maxSum d ω ∂P) - T * (s / 2) ≤ L / s at hF
  rw [hhalf, hother] at hF
  have htarget : Real.sqrt (2 * T * K * Real.log K) = R := by
    unfold R L
    congr 1
    ring
  rw [htarget]
  linarith

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.DrawRun.sampling_conversion := @CalibeatBandit.DrawRun.sampling_conversion
