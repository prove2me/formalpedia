-- Prove2me | solution 3 for CalibeatBandit.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:57:19.159413+00:00
-- url     : https://prove2.me/submissions/842a7074-dfd7-41aa-8968-c67a5a8ae096

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
import Theorems.Thm_CalibeatBandit_eq_C_3
import Theorems.Thm_CalibeatBandit_eq_C_5
import Definitions.Def_CalibeatBandit_draw_run
import Theorems.Thm_CalibeatBandit_DrawRun_sampling_conversion
import Theorems.Thm_CalibeatBandit_correction_loss_of_played_eq
import Theorems.Thm_CalibeatBandit_estimation_loss_of_played_eq
import Theorems.Thm_CalibeatBandit_secondMoment_of_played_eq

section

set_option autoImplicit false

open Matrix
open Filter
open scoped BigOperators Topology

namespace CalibeatBandit

private theorem sum_mulVec_stochastic {K : ℕ} {M : Matrix (Fin K) (Fin K) ℝ}
    (hM : IsColStochastic M) (x : Fin K → ℝ) :
    ∑ i, (M *ᵥ x) i = ∑ i, x i :=
  Matrix.sum_mulVec_of_mem_colStochastic <|
    Matrix.mem_colStochastic_iff_sum.mpr ⟨fun i j => (hM j).1 i, fun j => (hM j).2⟩

/-- The affine fixed point used by the algorithm is a probability vector when
the weight on swap regret is strictly less than one. -/
theorem fixedPointSol_spec {K : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (hlt : lam < 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) :
    IsProbVec (fixedPointSol lam MSR MRec J) ∧
      (1 - lam • MSR) *ᵥ fixedPointSol lam MSR MRec J =
        (1 - lam) • (MRec *ᵥ Pi.single J 1) := by
  let A : Matrix (Fin K) (Fin K) ℝ := 1 - lam • MSR
  have affine (x b : Fin K → ℝ) (heq : A *ᵥ x = b) (i : Fin K) :
      x i = lam * (MSR *ᵥ x) i + b i := by
    have hi := congrFun heq i
    simp only [A, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    linarith
  have neg_contraction (x b : Fin K → ℝ) (heq : A *ᵥ x = b) (hb : ∀ i, 0 ≤ b i) :
      ∀ i, 0 ≤ x i := by
    let n : Fin K → ℝ := fun i => max (-x i) 0
    have hn (i : Fin K) : 0 ≤ n i := le_max_right _ _
    have hMn (i : Fin K) : 0 ≤ (MSR *ᵥ n) i := by
      change 0 ≤ ∑ j, MSR i j * n j
      exact Finset.sum_nonneg fun j _ => mul_nonneg ((hSR j).1 i) (hn j)
    have hdom (i : Fin K) : n i ≤ lam * (MSR *ᵥ n) i := by
      apply max_le
      · have hsum : -(MSR *ᵥ x) i ≤ (MSR *ᵥ n) i := by
          simp only [mulVec, dotProduct, ← Finset.sum_neg_distrib, ← mul_neg]
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (le_max_left (-x j) 0) ((hSR j).1 i)
        linarith [affine x b heq i, hb i, mul_le_mul_of_nonneg_left hsum hlam]
      · exact mul_nonneg hlam (hMn i)
    have htotal : ∑ i, n i ≤ lam * ∑ i, n i := by
      simpa only [← Finset.mul_sum, sum_mulVec_stochastic hSR n] using
        (Finset.sum_le_sum (s := Finset.univ) fun i _ => hdom i)
    have hzero : ∑ i, n i = 0 := by
      by_contra! h
      have hpos : 0 < ∑ i, n i := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hn i) (Ne.symm h)
      exact (not_lt_of_ge htotal) (mul_lt_of_lt_one_left hpos hlt)
    intro i
    have hi := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    rw [hzero] at hi
    linarith [le_trans (le_max_left (-x i) 0) hi]
  have hA : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    have hzero : A *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
    have hzero' : A *ᵥ (y - x) = 0 := by rw [mulVec_sub, hxy, sub_self]
    ext i
    have h₁ := neg_contraction (x - y) 0 hzero (fun _ => le_rfl) i
    have h₂ := neg_contraction (y - x) 0 hzero' (fun _ => le_rfl) i
    exact le_antisymm (sub_nonneg.mp h₂) (sub_nonneg.mp h₁)
  let x := fixedPointSol lam MSR MRec J
  let b := (1 - lam) • (MRec *ᵥ Pi.single J (1 : ℝ))
  have heq : A *ᵥ x = b := by
    unfold x fixedPointSol
    change A *ᵥ ((1 - lam) • (A⁻¹ *ᵥ (MRec *ᵥ Pi.single J 1))) = b
    rw [mulVec_smul, mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA),
      one_mulVec]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    simp only [b, mulVec_single_one, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (sub_nonneg.mpr hlt.le) ((hRec J).1 i)
  refine ⟨⟨neg_contraction x b heq hb, ?_⟩, heq⟩
  have hsum := congrArg (fun q : Fin K → ℝ => ∑ i, q i) heq
  simp only [A, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    b, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mulVec_stochastic hSR x, mulVec_single_one] at hsum
  change (∑ i, x i) - lam * ∑ i, x i = (1 - lam) * ∑ i, MRec i J at hsum
  rw [(hRec J).2] at hsum
  apply (mul_right_inj' (sub_pos.mpr hlt).ne').mp
  linarith

end CalibeatBandit

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

private theorem hedge_prob {K : ℕ} (j : Fin K) (η : ℝ) (g : Fin K → ℝ) :
    IsProbVec (FewExperts.hedgeWeights η g) := by
  have hpos : 0 < ∑ i, Real.exp (η * g i) :=
    (Real.exp_pos _).trans_le (Finset.single_le_sum (fun i _ => Real.exp_nonneg (η * g i)) (Finset.mem_univ j))
  constructor
  · intro i
    exact div_nonneg (Real.exp_nonneg _) hpos.le
  · simp only [FewExperts.hedgeWeights, ← Finset.sum_div, div_self hpos.ne']

theorem LearnerState.lam_mem {K : ℕ} (s : LearnerState K) (η : ℝ) :
    s.lam η ∈ Set.Ioo (0 : ℝ) 1 := by
  have hmix := hedge_prob (0 : Fin 2) η ![s.cumHSR, s.cumHRec]
  have hpos (i : Fin 2) : 0 < FewExperts.hedgeWeights η ![s.cumHSR, s.cumHRec] i := by
    unfold FewExperts.hedgeWeights
    apply div_pos (Real.exp_pos _)
    exact (Real.exp_pos _).trans_le
      (Finset.single_le_sum (fun k _ => Real.exp_nonneg _) (Finset.mem_univ i))
  have hsum := hmix.2
  rw [Fin.sum_univ_two] at hsum
  have hlt : s.lam η < 1 := by
    unfold LearnerState.lam
    linarith [hpos 1]
  exact ⟨hpos 0, hlt⟩

theorem LearnerState.matSR_stochastic {K : ℕ} (s : LearnerState K) (η : ℝ) (J : Fin K) :
    IsColStochastic (s.matSR η) :=
  fun i => hedge_prob J η (s.cumSR i)

theorem LearnerState.matRec_stochastic {K : ℕ} (s : LearnerState K) (η : ℝ) (J : Fin K) :
    IsColStochastic (s.matRec η) :=
  fun i => hedge_prob J η (s.cumRec i)

theorem LearnerState.roundX_spec {K : ℕ} (s : LearnerState K) (η : ℝ) (J : Fin K) :
    IsProbVec (s.roundX η J) ∧
      (1 - s.lam η • s.matSR η) *ᵥ s.roundX η J =
        (1 - s.lam η) • (s.matRec η *ᵥ Pi.single J 1) :=
  fixedPointSol_spec _ (s.lam_mem η).1.le (s.lam_mem η).2 _ _
    (s.matSR_stochastic η J) (s.matRec_stochastic η J) J

theorem explore_prob {K : ℕ} (hK : 0 < K) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    {x : Fin K → ℝ} (hx : IsProbVec x) : IsProbVec (explore μ x) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hμ₁) (hx.1 i)) (by positivity)
  · simp only [explore, Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

local instance matrixMeasurableSpace (K : ℕ) : MeasurableSpace (Matrix (Fin K) (Fin K) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin K → Fin K → ℝ))

local instance matrixBorelSpace (K : ℕ) : BorelSpace (Matrix (Fin K) (Fin K) ℝ) :=
  inferInstanceAs (BorelSpace (Fin K → Fin K → ℝ))

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

@[fun_prop] theorem measurable_hedge {g : Ω → Fin K → ℝ} (hg : Measurable g)
    (η : ℝ) (j : Fin K) : Measurable fun ω => FewExperts.hedgeWeights η (g ω) j := by
  unfold FewExperts.hedgeWeights
  exact (Real.continuous_exp.measurable.comp ((measurable_pi_iff.mp hg j).const_mul η)).div
    (Finset.measurable_sum _ fun i _ =>
      Real.continuous_exp.measurable.comp ((measurable_pi_iff.mp hg i).const_mul η))

theorem measurable_fixedPointSol {lam : Ω → ℝ}
    {M N : Ω → Matrix (Fin K) (Fin K) ℝ} (hlam : Measurable lam)
    (hM : Measurable M) (hN : Measurable N) {J : Ω → Fin K} (hJ : Measurable J) :
    Measurable fun ω => fixedPointSol (lam ω) (M ω) (N ω) (J ω) := by
  let A : Ω → Matrix (Fin K) (Fin K) ℝ := fun ω => 1 - lam ω • M ω
  have hA : Measurable A := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => by
    change Measurable fun ω => (1 : Matrix (Fin K) (Fin K) ℝ) i j - lam ω * M ω i j
    exact measurable_const.sub (hlam.mul (measurable_pi_iff.mp (measurable_pi_iff.mp hM i) j))
  have hdet : Measurable fun ω => (A ω).det :=
    (continuous_id.matrix_det : Continuous fun a : Matrix (Fin K) (Fin K) ℝ => a.det).measurable.comp hA
  have hadj : Measurable fun ω => (A ω).adjugate :=
    (continuous_id.matrix_adjugate : Continuous fun a : Matrix (Fin K) (Fin K) ℝ => a.adjugate).measurable.comp hA
  have hcol (i : Fin K) : Measurable fun ω => N ω i (J ω) :=
    measurable_select hJ fun j => measurable_pi_iff.mp (measurable_pi_iff.mp hN i) j
  refine measurable_pi_iff.mpr fun i => ?_
  change Measurable fun ω => ((1 - lam ω) • ((A ω)⁻¹ *ᵥ (N ω *ᵥ Pi.single (J ω) 1))) i
  simp only [mulVec_single_one, Matrix.inv_def, Ring.inverse_eq_inv, Pi.smul_apply,
    smul_eq_mul, mulVec, dotProduct, col_apply, Matrix.smul_apply]
  exact (measurable_const.sub hlam).mul
    (Finset.measurable_sum _ fun j _ =>
      (hdet.inv.mul (measurable_pi_iff.mp (measurable_pi_iff.mp hadj i) j)).mul (hcol j))

end Measurability

theorem estimate_scaled_mem {K : ℕ} {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    (x : Fin K → ℝ) (hx : IsProbVec x) (I j : Fin K) (obs : ℝ)
    (hobs : obs ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ η * estimate η (explore μ x) I obs j ∧
      η * estimate η (explore μ x) I obs j ≤ 1 := by
  let p := explore μ x j
  let d := (Real.exp 1 - 2) * η
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₈ : η ≤ 1 / 8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hp : 4 * η ≤ p := by
    change 4 * η ≤ (1 - μ) * x j + μ / K
    have hle := (le_div_iff₀ hk).mpr (show 4 * η * K ≤ μ by linarith only [hKη])
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by linarith) (hx.1 j)))
  have hp₀ : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hd₀ : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hd₁ : d ≤ η := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three]) hη.le]
  let r := if I = j then obs else 0
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [r]
    split
    · exact hobs
    · exact ⟨le_rfl, zero_le_one⟩
  have hv : estimate η (explore μ x) I obs j = (r + d) / p := by
    change (if I = j then obs / p else 0) + d / p = _
    dsimp [r]
    split <;> simp [add_div]
  rw [hv]
  refine ⟨mul_nonneg hη.le (div_nonneg (add_nonneg hr.1 hd₀) hp₀.le), ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hp₀).mpr
  nlinarith [mul_nonneg hη.le (show 0 ≤ 4 - (r + d) by linarith [hr.2])]

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

theorem obs_measurable (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    Measurable[run.info (t + 1)] (run.obs t) :=
  @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ (run.I_measurable t ht)
    (fun j ω => run.y t ω j) fun j => (measurable_pi_apply j).comp
      ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl)

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

/-- The conditional mean reward is the dot product of the played strategy and
the current reward vector. This identity holds for every policy in the protocol. -/
theorem DrawRun.condExp_obs {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    Integrable (run.obs t) P ∧
    condExp (run.preDraw t) P (run.obs t) =ᵐ[P]
      fun ω => run.played t ω ⬝ᵥ run.y t ω := by
  have h := run.condExp_select_played P ht (fun j ω => run.y t ω j)
    (fun j => (measurable_pi_apply j).comp (run.y_measurable t ht)) 1
    (fun j ω => by
      have hj := run.y_mem t ht ω j
      exact (abs_of_nonneg hj.1).trans_le hj.2)
  exact h

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

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Matrix
open scoped BigOperators

/-- Remapping benchmark with a distribution over reference labels and a
possibly different distribution over the baseline actions. -/
noncomputable def comparisonMax {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty (ι → Fin N)] (T : ℕ) (w : ℕ → ι → ℝ)
    (p y : ℕ → Fin N → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun f : ι → Fin N => ∑ t ∈ Finset.range T,
    ((∑ i, w t i * y t (f i)) - p t ⬝ᵥ y t))

theorem abs_weighted_sum {ι : Type*} [Fintype ι] {w a : ι → ℝ} {B : ℝ}
    (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (ha : ∀ i, |a i| ≤ B) :
    |∑ i, w i * a i| ≤ B := by
  calc
    _ ≤ ∑ i, |w i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * B := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_nonneg (hw₀ i)]
      exact mul_le_mul_of_nonneg_left (ha i) (hw₀ i)
    _ = B := by rw [← Finset.sum_mul, hw, one_mul]

set_option maxHeartbeats 950000 in
/-- Combine a pathwise corrected comparison bound with sampling, estimation,
and correction terms. Reference labels can be actions or recommendations. -/
theorem DrawRun.expected_comparison {N T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty (ι → Fin N)] {η μ : ℝ} (hN : 0 < N) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hNη : 4 * N * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun N T P)
    (x : ℕ → Ω → Fin N → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω))
    (w W : ℕ → Ω → ι → ℝ)
    (hw₀ : ∀ t < T, ∀ ω i, 0 ≤ w t ω i) (hw : ∀ t < T, ∀ ω, ∑ i, w t ω i = 1)
    (hwm : ∀ t < T, Measurable[run.preDraw t] (w t))
    (hW₀ : ∀ t < T, ∀ ω i, 0 ≤ W t ω i) (hW : ∀ t < T, ∀ ω, ∑ i, W t ω i = 1)
    (hWm : ∀ t < T, Measurable[run.preDraw t] (W t))
    (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hδ : ∀ t < T, ∀ ω (f : ι → Fin N),
      (∑ i, W t ω i * run.y t ω (f i)) - explore μ (x t ω) ⬝ᵥ run.y t ω
        ≤ μ + a * ((∑ i, w t ω i * run.y t ω (f i)) - x t ω ⬝ᵥ run.y t ω))
    (C : ℝ) (hC₀ : 0 ≤ C) :
    let v (t : ℕ) (ω : Ω) := estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    (∀ ω (f : ι → Fin N),
      (∑ t ∈ Finset.range T, ((∑ i, w t ω i * v t ω (f i)) - x t ω ⬝ᵥ v t ω))
        ≤ C + (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t ω j * v t ω j ^ 2) →
    ∫ ω, comparisonMax T (fun t => W t ω) (fun t => run.played t ω) (fun t => run.y t ω) ∂P
      ≤ μ * T + C + Fintype.card ι * Real.log N / η + 5 * η * N * T / (1 - μ) := by
  intro v hc
  classical
  let p (t : ℕ) (ω : Ω) := explore μ (x t ω)
  let y := run.y
  let d := (Real.exp 1 - 2) * η
  let Q (t : ℕ) (ω : Ω) := ∑ j, x t ω j * v t ω j ^ 2
  let L (ω : Ω) := ∑ t ∈ Finset.range T, x t ω ⬝ᵥ (v t ω - y t ω)
  let E (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty (fun f : ι → Fin N =>
    ∑ t ∈ Finset.range T, ∑ i, w t ω i * (y t ω (f i) - v t ω (f i)))
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hp (t : ℕ) (ht : t < T) (ω : Ω) : IsProbVec (p t ω) :=
    explore_prob hN hμ₀.le (by linarith) (hx t ht ω)
  have hm (t : ℕ) (ht : t < T) {A : Ω → ℝ}
      (ha : Measurable[run.preDraw t] A) : Measurable A :=
    ha.mono (run.preDraw_le_ambient ht) le_rfl
  have hxm' (t : ℕ) (ht : t < T) (j : Fin N) : Measurable (fun ω => x t ω j) :=
    hm t ht ((measurable_pi_apply j).comp (hxm t ht))
  have hym (t : ℕ) (ht : t < T) (j : Fin N) : Measurable (fun ω => y t ω j) :=
    hm t ht ((measurable_pi_apply j).comp (run.y_measurable t ht))
  have hpm (t : ℕ) (ht : t < T) (j : Fin N) : Measurable (fun ω => p t ω j) :=
    ((hxm' t ht j).const_mul _).add measurable_const
  have hvm (t : ℕ) (ht : t < T) (j : Fin N) : Measurable (fun ω => v t ω j) := by
    have hi := (run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
    have hr := (run.obs_measurable ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
    exact (Measurable.ite (hi (measurableSet_singleton j)) (hr.div (hpm t ht j))
      measurable_const).add (measurable_const.div (hpm t ht j))
  have hvB (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin N) : |v t ω j| ≤ 1 / η := by
    obtain ⟨h₀, h₁⟩ := estimate_scaled_mem hN hη hμ hNη (x t ω) (hx t ht ω)
      (run.I t ω) j (run.obs t ω) (run.y_mem t ht ω (run.I t ω))
    rw [abs_of_nonneg (nonneg_of_mul_nonneg_right h₀ hη)]
    exact (le_div_iff₀ hη).mpr (by simpa [mul_comm] using h₁)
  have hyB (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin N) : |y t ω j| ≤ 1 :=
    (abs_of_nonneg (run.y_mem t ht ω j).1).trans_le (run.y_mem t ht ω j).2
  have hQm (t : ℕ) (ht : t < T) : Integrable (Q t) P := by
    refine integrable_of_abs_bound (B := (1 / η) ^ 2)
      (Finset.measurable_sum _ fun j _ => (hxm' t ht j).mul ((hvm t ht j).pow_const 2)) ?_
    intro ω
    apply abs_weighted_sum (hx t ht ω).1 (hx t ht ω).2
    intro j
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hvB t ht ω j) 2
  have hLossM (t : ℕ) (ht : t < T) (j : Fin N) :
      Measurable (fun ω => v t ω j - y t ω j) := (hvm t ht j).sub (hym t ht j)
  have hLossB (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin N) :
      |v t ω j - y t ω j| ≤ 1 / η + 1 :=
    (abs_sub _ _).trans (add_le_add (hvB t ht ω j) (hyB t ht ω j))
  have hL : Integrable L P := by
    apply integrable_finsetSum
    intro t ht
    have ht' := Finset.mem_range.mp ht
    apply integrable_of_abs_bound (B := 1 / η + 1)
    · exact Finset.measurable_sum _ fun j _ => (hxm' t ht' j).mul (hLossM t ht' j)
    · exact fun ω => abs_weighted_sum (hx t ht' ω).1 (hx t ht' ω).2 (hLossB t ht' ω)
  have maxInt (F : ℕ → (ι → Fin N) → Ω → ℝ) (B : ℝ)
      (hFm : ∀ t < T, ∀ f, Measurable (F t f)) (hFb : ∀ t < T, ∀ f ω, |F t f ω| ≤ B) :
      Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun f => ∑ t ∈ Finset.range T, F t f ω)) P := by
    apply integrable_finset_max Finset.univ_nonempty _ (B := T * B)
    · exact fun f => Finset.measurable_sum _ fun t ht => hFm t (Finset.mem_range.mp ht) f
    · intro f ω
      calc
        _ ≤ ∑ t ∈ Finset.range T, |F t f ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, B := Finset.sum_le_sum fun t ht => hFb t (Finset.mem_range.mp ht) f ω
        _ = _ := by simp
  have hE : Integrable E P := by
    apply maxInt (fun t f ω => ∑ i, w t ω i * (y t ω (f i) - v t ω (f i))) (1 / η + 1)
    · intro t ht f
      exact Finset.measurable_sum _ fun i _ => (hm t ht ((measurable_pi_apply i).comp
        (hwm t ht))).mul ((hym t ht (f i)).sub (hvm t ht (f i)))
    · intro t ht f ω
      exact abs_weighted_sum (hw₀ t ht ω) (hw t ht ω) fun i => by
        rw [abs_sub_comm]
        exact hLossB t ht ω (f i)
  let F (ω : Ω) := comparisonMax T (fun t => W t ω) (fun t => p t ω) (fun t => y t ω)
  have hF : Integrable F P := by
    apply maxInt (fun t f ω => (∑ i, W t ω i * y t ω (f i)) - p t ω ⬝ᵥ y t ω) 2
    · intro t ht f
      exact (Finset.measurable_sum _ fun i _ => (hm t ht ((measurable_pi_apply i).comp
        (hWm t ht))).mul (hym t ht (f i))).sub
        (Finset.measurable_sum _ fun j _ => (hpm t ht j).mul (hym t ht j))
    · intro t ht f ω
      have h₁ := abs_weighted_sum (hW₀ t ht ω) (hW t ht ω) (fun i => hyB t ht ω (f i))
      have h₂ := abs_weighted_sum (hp t ht ω).1 (hp t ht ω).2 (hyB t ht ω)
      simpa only [dotProduct, one_add_one_eq_two] using
        (abs_sub _ _).trans (add_le_add h₁ h₂)
  let B (ω : Ω) := C + d * ∑ t ∈ Finset.range T, Q t ω
  have hB : Integrable B P := (integrable_const _).add
    ((integrable_finsetSum _ (fun t ht => hQm t (Finset.mem_range.mp ht))).const_mul d)
  have hpoint (ω : Ω) : F ω ≤ μ * T + a * (B ω + E ω + L ω) := by
    unfold F comparisonMax
    apply Finset.sup'_le
    intro f hf
    have hEmax := Finset.le_sup' (fun f : ι → Fin N => ∑ t ∈ Finset.range T,
      ∑ i, w t ω i * (y t ω (f i) - v t ω (f i))) hf
    have hsplit (t : ℕ) : ((∑ i, w t ω i * y t ω (f i)) - x t ω ⬝ᵥ y t ω) =
        ((∑ i, w t ω i * v t ω (f i)) - x t ω ⬝ᵥ v t ω) +
          (∑ i, w t ω i * (y t ω (f i) - v t ω (f i))) + x t ω ⬝ᵥ (v t ω - y t ω) := by
      simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    have htotal : (∑ t ∈ Finset.range T,
        ((∑ i, w t ω i * y t ω (f i)) - x t ω ⬝ᵥ y t ω)) ≤ B ω + E ω + L ω := by
      simp_rw [hsplit, Finset.sum_add_distrib]
      exact add_le_add_left (add_le_add (hc ω f) hEmax) _
    calc
      _ ≤ ∑ t ∈ Finset.range T, (μ + a * ((∑ i, w t ω i * y t ω (f i)) - x t ω ⬝ᵥ y t ω)) :=
        Finset.sum_le_sum fun t ht => hδ t (Finset.mem_range.mp ht) ω f
      _ = μ * T + a * (∑ t ∈ Finset.range T, ((∑ i, w t ω i * y t ω (f i)) - x t ω ⬝ᵥ y t ω)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left htotal ha₀) _
  have hQi (t : ℕ) (ht : t < T) : (∫ ω, Q t ω ∂P) ≤ 2 * N / (1 - μ) := by
    obtain ⟨heq, hbound, hsum⟩ := secondMoment_of_played_eq hN hη hμ₀ hμ hNη P run t ht
      (x t) (hx t ht) (hxm t ht) (hplay t ht)
    rw [← integral_condExp (m := run.preDraw t) (run.preDraw_le_ambient ht)]
    calc
      _ ≤ ∫ _ : Ω, (2 * (N : ℝ) / (1 - μ)) ∂P := by
        apply integral_mono_ae integrable_condExp (integrable_const _)
        change condExp (run.preDraw t) P (Q t) ≤ᵐ[P] _
        filter_upwards [heq] with ω hω
        rw [show condExp (run.preDraw t) P (Q t) ω = _ from hω]
        exact (hbound ω).trans (hsum ω)
      _ = _ := by simp
  have hBi : (∫ ω, B ω ∂P) ≤ C + 2 * d * N * T / (1 - μ) := by
    unfold B
    rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun t ht =>
      hQm t (Finset.mem_range.mp ht)).const_mul d), integral_const_mul,
      integral_finsetSum _ (fun t ht => hQm t (Finset.mem_range.mp ht))]
    simp only [integral_const, probReal_univ, one_smul]
    have hs := Finset.sum_le_sum (s := Finset.range T) fun t ht => hQi t (Finset.mem_range.mp ht)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    calc
      _ ≤ C + d * ((T : ℝ) * (2 * N / (1 - μ))) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hs hd) _
      _ = _ := by ring
  have hEi := estimation_loss_of_played_eq Finset.univ_nonempty hN hη hμ₀ hμ hNη P
    run x hx hxm hplay w hw₀ hw hwm
  have hLi := correction_loss_of_played_eq hN hη hμ₀ hμ hNη P run x hx hxm hplay
  have hA := ((hB.add hE).add hL).const_mul a
  have hmain := integral_mono hF ((integrable_const _).add hA) hpoint
  rw [integral_add' (integrable_const _) hA] at hmain
  have hAeq : (∫ ω, a * (B + E + L) ω ∂P) =
      a * ((∫ ω, B ω ∂P) + (∫ ω, E ω ∂P) + ∫ ω, L ω ∂P) := by
    rw [integral_const_mul, integral_add' (hB.add hE) hL, integral_add' hB hE]
  rw [hAeq] at hmain
  simp only [integral_const, probReal_univ, one_smul] at hmain
  have hC : 2 * d * N * T / (1 - μ) + d * N * T / (1 - μ)
      ≤ 5 * η * N * T / (1 - μ) := by
    have hfactor : 0 ≤ η * N * T / (1 - μ) := div_nonneg (by positivity) (by linarith)
    calc
      _ = 3 * (Real.exp 1 - 2) * (η * N * T / (1 - μ)) := by dsimp [d]; ring
      _ ≤ 5 * (η * N * T / (1 - μ)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_three]) hfactor
      _ = _ := by ring
  have heq : (fun ω => comparisonMax T (fun t => W t ω) (fun t => run.played t ω)
      (fun t => y t ω)) =ᵐ[P] F := by
    have hpAE : ∀ᵐ ω ∂P, ∀ t : Fin T, run.played t ω = p t ω :=
      ae_all_iff.mpr fun t => hplay t t.isLt
    filter_upwards [hpAE] with ω he
    unfold F comparisonMax
    congr 1
    funext f
    exact Finset.sum_congr rfl fun t ht => by
      have ht' : run.played t ω = p t ω := he ⟨t, Finset.mem_range.mp ht⟩
      simp only [ht']
  rw [integral_congr_ae heq]
  change (∫ ω, E ω ∂P) ≤ _ at hEi
  change (∫ ω, L ω ∂P) ≤ d * N * T / (1 - μ) at hLi
  let U := C + Fintype.card ι * Real.log N / η + 5 * η * N * T / (1 - μ)
  have hU : 0 ≤ U := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hden : 0 < 1 - μ := by linarith
    dsimp [U]
    positivity
  have hbig : (∫ ω, B ω ∂P) + (∫ ω, E ω ∂P) + (∫ ω, L ω ∂P) ≤ U := by
    dsimp [U]
    linarith only [hBi, hEi, hLi, hC]
  have hfinal := add_le_add_right ((mul_le_mul_of_nonneg_left hbig ha₀).trans
    (mul_le_of_le_one_left hU ha₁)) (μ * T)
  exact hmain.trans (hfinal.trans_eq (by dsimp [U]; ring))

end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit

private noncomputable def logPartition {K : ℕ} (η : ℝ) (G : Fin K → ℝ) : ℝ :=
  Real.log (1 / K * ∑ j, Real.exp (η * G j))

private theorem logPartition_step {K : ℕ} (i : Fin K) (η : ℝ) (G z : Fin K → ℝ) :
    Real.log (∑ j, FewExperts.hedgeWeights η G j * Real.exp (η * z j)) =
      logPartition η (fun j => G j + z j) - logPartition η G := by
  have hK : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have pos (G : Fin K → ℝ) : 0 < ∑ j, Real.exp (η * G j) :=
    (Real.exp_pos _).trans_le (Finset.single_le_sum (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i))
  have hsum : ∑ j, FewExperts.hedgeWeights η G j * Real.exp (η * z j) =
      (∑ j, Real.exp (η * (G j + z j))) / (∑ j, Real.exp (η * G j)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      rw [FewExperts.hedgeWeights, mul_add, Real.exp_add, div_mul_eq_mul_div]
  rw [hsum, Real.log_div (pos _).ne' (pos _).ne']
  unfold logPartition
  rw [Real.log_mul (by positivity) (pos _).ne', Real.log_mul (by positivity) (pos _).ne']
  ring

private theorem gain_le_logPartition {K : ℕ} (i : Fin K) {η : ℝ} (hη : 0 < η)
    (G : Fin K → ℝ) : G i ≤ (logPartition η G + Real.log K) / η := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hs : Real.exp (η * G i) ≤ ∑ j, Real.exp (η * G j) :=
    Finset.single_le_sum (fun j _ => Real.exp_nonneg (η * G j)) (Finset.mem_univ i)
  have hl := Real.log_le_log (Real.exp_pos _) hs
  rw [Real.log_exp] at hl
  apply (le_div_iff₀ hη).mpr
  unfold logPartition
  rw [Real.log_mul (by positivity) ((Real.exp_pos _).trans_le hs).ne', one_div,
    Real.log_inv]
  linarith

/-- Independent internal learners indexed by an arbitrary finite reference set.
Every learner uses exponential weights over the same set of output actions. -/
theorem rectangular_potential_bound {K T : ℕ} {ι : Type*} [Fintype ι]
    {η : ℝ} (hη : 0 < η) (f : ι → Fin K) (g : ℕ → ι → Fin K → ℝ) :
    (∑ t ∈ Finset.range T, ∑ i, g t i (f i)) ≤
      Fintype.card ι * Real.log K / η +
        ∑ t ∈ Finset.range T, (1 / η) * ∑ i, Real.log
          (∑ j, FewExperts.hedgeWeights η (fun j => ∑ s ∈ Finset.range t, g s i j) j *
            Real.exp (η * g t i j)) := by
  let G (t : ℕ) (i : ι) (j : Fin K) := ∑ s ∈ Finset.range t, g s i j
  let L (t : ℕ) (i : ι) := Real.log
    (∑ j, FewExperts.hedgeWeights η (G t i) j * Real.exp (η * g t i j))
  have hstep (t : ℕ) (i : ι) : L t i = logPartition η (G (t + 1) i) - logPartition η (G t i) := by
    simpa only [L, G, Finset.sum_range_succ] using
      logPartition_step (f i) η (G t i) (g t i)
  have htel (k : ℕ) (i : ι) : (∑ t ∈ Finset.range k, L t i) = logPartition η (G k i) := by
    induction k with
    | zero =>
      have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt (f i).isLt).ne'
      simp [G, logPartition, one_div, inv_mul_cancel₀ hK]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hstep]
      ring
  have hrows : (∑ t ∈ Finset.range T, ∑ i, g t i (f i)) ≤
      ∑ i, (logPartition η (G T i) + Real.log K) / η := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => gain_le_logPartition (f i) hη (G T i)
  refine hrows.trans_eq ?_
  change (∑ i, (logPartition η (G T i) + Real.log K) / η) =
    _ + ∑ t ∈ Finset.range T, (1 / η) * ∑ i, L t i
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range T), show (∑ i, ∑ t ∈ Finset.range T, L t i) =
      ∑ i, logPartition η (G T i) from Finset.sum_congr rfl fun i _ => htel T i]
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

/-- A finite-grid learner with K posted prices and a separate type of
recommendation labels. New labels have zero cumulative reward. -/
structure PricingLearnerState (K : ℕ) (ι : Type*) where
  cumSR : Fin K → Fin K → ℝ
  cumRec : ι → Fin K → ℝ
  cumHSR : ℝ
  cumHRec : ℝ

namespace PricingLearnerState

variable {K : ℕ} {ι : Type*}

noncomputable def core (s : PricingLearnerState K ι) (j : ι) : LearnerState K :=
  ⟨s.cumSR, fun _ => s.cumRec j, s.cumHSR, s.cumHRec⟩

/-- The square solver only uses the selected recommendation column. The other
columns in this representation are copies of that column. -/
noncomputable def x (s : PricingLearnerState K ι) (η : ℝ) (j : ι) (anchor : Fin K) :
    Fin K → ℝ :=
  (s.core j).roundX η anchor

noncomputable def feedback (s : PricingLearnerState K ι) (η : ℝ) (j : ι) (anchor : Fin K)
    (v : Fin K → ℝ) : Fin 2 → ℝ :=
  ![HSRof η ((s.core j).matSR η) (s.x η j anchor) v,
    HRecOf η ((s.core j).matRec η) anchor v]

noncomputable def step [DecidableEq ι] (s : PricingLearnerState K ι) (η : ℝ) (j : ι) (anchor : Fin K)
    (v : Fin K → ℝ) : PricingLearnerState K ι :=
  { cumSR := fun i k => s.cumSR i k + s.x η j anchor i * v k
    cumRec := fun i k => s.cumRec i k + if j = i then v k else 0
    cumHSR := s.cumHSR + s.feedback η j anchor v 0
    cumHRec := s.cumHRec + s.feedback η j anchor v 1 }

noncomputable def along [DecidableEq ι] (η : ℝ) (j : ℕ → ι) (anchor : Fin K)
    (v : ℕ → Fin K → ℝ) : ℕ → PricingLearnerState K ι
  | 0 => ⟨0, 0, 0, 0⟩
  | t + 1 => (along η j anchor v t).step η (j t) anchor (v t)

end PricingLearnerState

/-- The grid policy uses only recommendation labels, its past actions, and
the revenues it observed at those actions. -/
noncomputable def pricingLearnerState {K : ℕ} {ι : Type*} [DecidableEq ι]
    (η μ : ℝ) (J : ℕ → ι) (I : ℕ → Fin K) (r : ℕ → ℝ) (anchor : Fin K) :
    ℕ → PricingLearnerState K ι
  | 0 => ⟨0, 0, 0, 0⟩
  | t + 1 =>
    let s := pricingLearnerState η μ J I r anchor t
    let p := explore μ (s.x η (J t) anchor)
    s.step η (J t) anchor (estimate η p (I t) (r t))

noncomputable def pricingGridPolicy {K : ℕ} {ι : Type*} [DecidableEq ι]
    (η μ : ℝ) (anchor : Fin K) (t : ℕ) (J : ℕ → ι) (I : ℕ → Fin K) (r : ℕ → ℝ) :
    Fin K → ℝ :=
  explore μ ((pricingLearnerState η μ J I r anchor t).x η (J t) anchor)

theorem pricingGridPolicy_prob {K : ℕ} {ι : Type*} [DecidableEq ι]
    (η : ℝ) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (anchor : Fin K)
    (t : ℕ) (J : ℕ → ι) (I : ℕ → Fin K) (r : ℕ → ℝ) :
    IsProbVec (pricingGridPolicy η μ anchor t J I r) :=
  explore_prob (Nat.zero_lt_of_lt anchor.isLt) hμ.1 hμ.2
    (((pricingLearnerState η μ J I r anchor t).core (J t)).roundX_spec η anchor).1

theorem pricingLearnerState_eq_along {K : ℕ} {ι : Type*} [DecidableEq ι]
    (η μ : ℝ) (J : ℕ → ι) (I : ℕ → Fin K) (r : ℕ → ℝ) (anchor : Fin K) (t : ℕ) :
    pricingLearnerState η μ J I r anchor t = PricingLearnerState.along η J anchor
      (fun u => estimate η (pricingGridPolicy η μ anchor u J I r) (I u) (r u)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (pricingLearnerState η μ J I r anchor t).step η (J t) anchor _ = _
    rw [PricingLearnerState.along, ← ih]
    rfl

theorem pricingGridPolicy_eq_of_history {K : ℕ} {ι : Type*} [DecidableEq ι]
    (η μ : ℝ) (anchor : Fin K) (t : ℕ)
    (J J' : ℕ → ι) (I I' : ℕ → Fin K) (r r' : ℕ → ℝ)
    (hJ : ∀ s ≤ t, J s = J' s) (hI : ∀ s < t, I s = I' s)
    (hr : ∀ s < t, r s = r' s) :
    pricingGridPolicy η μ anchor t J I r = pricingGridPolicy η μ anchor t J' I' r' := by
  have hstate (s : ℕ) (hs : s ≤ t) :
      pricingLearnerState η μ J I r anchor s = pricingLearnerState η μ J' I' r' anchor s := by
    induction s with
    | zero => rfl
    | succ s ih =>
      have hs' : s < t := Nat.lt_of_succ_le hs
      simp only [pricingLearnerState, ih hs'.le, hJ s hs'.le, hI s hs', hr s hs']
  unfold pricingGridPolicy
  rw [hstate t le_rfl, hJ t le_rfl]

/-- Only equality of recommendation prices matters to the learner. Relabeling
an injective representation of those prices leaves every play distribution unchanged. -/
theorem pricingGridPolicy_relabel {N : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (η μ : ℝ) (anchor : Fin N) (label : ι → κ) (hlabel : Function.Injective label)
    (J : ℕ → ι) (I : ℕ → Fin N) (r : ℕ → ℝ) (t : ℕ) :
    pricingGridPolicy η μ anchor t (label ∘ J) I r =
      pricingGridPolicy η μ anchor t J I r := by
  let s := pricingLearnerState η μ J I r anchor
  let s' := pricingLearnerState η μ (label ∘ J) I r anchor
  have hcore (u : ℕ) (j : ι) :
      (s' u).core (label j) = (s u).core j := by
    induction u generalizing j with
    | zero => rfl
    | succ u ih =>
      have he : (s' u).x η (label (J u)) anchor = (s u).x η (J u) anchor := by
        unfold PricingLearnerState.x
        rw [ih (J u)]
      let v := estimate η (explore μ ((s u).x η (J u) anchor)) (I u) (r u)
      change ((s' u).step η (label (J u)) anchor
        (estimate η (explore μ ((s' u).x η (label (J u)) anchor)) (I u) (r u))).core (label j) =
          ((s u).step η (J u) anchor v).core j
      rw [he]
      change ((s' u).step η (label (J u)) anchor v).core (label j) =
        ((s u).step η (J u) anchor v).core j
      have h := ih j
      have hs := congrArg LearnerState.cumSR h
      have hr := congrArg (fun c : LearnerState N => c.cumRec anchor) h
      have hsr := congrArg LearnerState.cumHSR h
      have hrec := congrArg LearnerState.cumHRec h
      have hf : (s' u).feedback η (label (J u)) anchor v = (s u).feedback η (J u) anchor v := by
        unfold PricingLearnerState.feedback
        rw [he, ih (J u)]
      simp only [PricingLearnerState.core, PricingLearnerState.step] at hs hr hsr hrec ⊢
      rw [hs, hr, hsr, hrec, hf, he]
      simp only [hlabel.eq_iff]
  unfold pricingGridPolicy
  congr 1
  unfold PricingLearnerState.x
  exact congrArg (fun s : LearnerState N => s.roundX η anchor) (hcore t (J t))

section Measurability

local instance pricingMatrixMeasurableSpace (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin N → Fin N → ℝ))

variable {Ω ι : Type*} {N : ℕ} [MeasurableSpace Ω]
  [DecidableEq ι] [MeasurableSpace ι] [MeasurableEq ι]

omit [DecidableEq ι] [MeasurableEq ι] in
private theorem measurable_pricingCore {s : Ω → PricingLearnerState N ι} {J : Ω → ι}
    (η : ℝ) (hJ : Measurable J)
    (hsr : ∀ i k, Measurable (fun ω => (s ω).cumSR i k))
    (hrec : ∀ (L : Ω → ι), Measurable L → ∀ k,
      Measurable (fun ω => (s ω).cumRec (L ω) k))
    (hHSR : Measurable (fun ω => (s ω).cumHSR))
    (hHRec : Measurable (fun ω => (s ω).cumHRec)) :
    let C := fun ω => (s ω).core (J ω)
    Measurable (fun ω => (C ω).matSR η) ∧ Measurable (fun ω => (C ω).matRec η) ∧
      Measurable (fun ω => (C ω).lam η) := by
  intro C
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
      measurable_hedge (measurable_pi_iff.mpr (hsr i)) η j
  · exact measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun _ =>
      measurable_hedge (measurable_pi_iff.mpr fun k =>
        hrec J hJ k) η j
  · exact measurable_hedge (measurable_pi_iff.mpr (Fin.forall_fin_two.mpr ⟨hHSR, hHRec⟩)) η 0

private theorem measurable_pricing_history (η μ : ℝ) (anchor : Fin N)
    (J : ℕ → Ω → ι) (I : ℕ → Ω → Fin N) (r : ℕ → Ω → ℝ)
    (t : ℕ) (hJ : ∀ u < t, Measurable (J u)) (hI : ∀ u < t, Measurable (I u))
    (hr : ∀ u < t, Measurable (r u)) :
    let s := fun ω => pricingLearnerState η μ (fun u => J u ω) (fun u => I u ω)
      (fun u => r u ω) anchor t
    (∀ i k, Measurable (fun ω => (s ω).cumSR i k)) ∧
    (∀ (L : Ω → ι), Measurable L → ∀ k, Measurable (fun ω => (s ω).cumRec (L ω) k)) ∧
    Measurable (fun ω => (s ω).cumHSR) ∧ Measurable (fun ω => (s ω).cumHRec) := by
  induction t with
  | zero => exact ⟨fun _ _ => measurable_const, fun _ _ _ => measurable_const,
      measurable_const, measurable_const⟩
  | succ t ih =>
    let s := fun ω => pricingLearnerState η μ (fun u => J u ω) (fun u => I u ω)
      (fun u => r u ω) anchor t
    obtain ⟨hsr, hrec, hHSR, hHRec⟩ := ih (fun u hu => hJ u (by omega))
      (fun u hu => hI u (by omega)) (fun u hu => hr u (by omega))
    have hj := hJ t (Nat.lt_succ_self _)
    have hi := hI t (Nat.lt_succ_self _)
    have ht := hr t (Nat.lt_succ_self _)
    obtain ⟨hmSR, hmRec, hlam⟩ := measurable_pricingCore η hj hsr hrec hHSR hHRec
    let x (ω : Ω) := (s ω).x η (J t ω) anchor
    have hx : Measurable x := measurable_fixedPointSol hlam hmSR hmRec measurable_const
    have hp (k : Fin N) : Measurable (fun ω => explore μ (x ω) k) :=
      (((measurable_pi_apply k).comp hx).const_mul (1 - μ)).add measurable_const
    let v (ω : Ω) := estimate η (explore μ (x ω)) (I t ω) (r t ω)
    have hv (k : Fin N) : Measurable (fun ω => v ω k) :=
      (Measurable.ite (hi (measurableSet_singleton k)) (ht.div (hp k)) measurable_const).add
        (measurable_const.div (hp k))
    let C (ω : Ω) := (s ω).core (J t ω)
    have hm (k i : Fin N) : Measurable (fun ω => (C ω).matSR η k i) :=
      measurable_pi_iff.mp (measurable_pi_iff.mp hmSR k) i
    have hmr (k : Fin N) : Measurable (fun ω => (C ω).matRec η k anchor) :=
      measurable_pi_iff.mp (measurable_pi_iff.mp hmRec k) anchor
    have hmSRgain : Measurable (fun ω => HSRof η ((C ω).matSR η) (x ω) (v ω)) := by
      unfold HSRof
      refine (Finset.measurable_sum _ fun i _ => Real.measurable_log.comp ?_).const_mul (1 / η)
      exact Finset.measurable_sum _ fun k _ => (hm k i).mul (Real.continuous_exp.measurable.comp
        ((((measurable_pi_apply i).comp hx).const_mul η).mul (hv k)))
    have hmRecGain : Measurable (fun ω => HRecOf η ((C ω).matRec η) anchor (v ω)) := by
      unfold HRecOf
      refine (Real.measurable_log.comp ?_).const_mul (1 / η)
      exact Finset.measurable_sum _ fun k _ => (hmr k).mul
        (Real.continuous_exp.measurable.comp ((hv k).const_mul η))
    exact ⟨fun i k => (hsr i k).add (((measurable_pi_apply i).comp hx).mul (hv k)),
      fun L hL k => (hrec L hL k).add
        (Measurable.ite (measurableSet_eq_fun hj hL) (hv k) measurable_const),
      hHSR.add hmSRgain, hHRec.add hmRecGain⟩

theorem measurable_pricingX (η μ : ℝ) (anchor : Fin N)
    (J : ℕ → Ω → ι) (I : ℕ → Ω → Fin N) (r : ℕ → Ω → ℝ)
    (t : ℕ) (hJ : ∀ u ≤ t, Measurable (J u)) (hI : ∀ u < t, Measurable (I u))
    (hr : ∀ u < t, Measurable (r u)) :
    Measurable (fun ω =>
      (pricingLearnerState η μ (fun u => J u ω) (fun u => I u ω) (fun u => r u ω) anchor t).x
        η (J t ω) anchor) := by
  obtain ⟨hsr, hrec, hHSR, hHRec⟩ :=
    measurable_pricing_history η μ anchor J I r t (fun u hu => hJ u hu.le) hI hr
  obtain ⟨hmSR, hmRec, hlam⟩ :=
    measurable_pricingCore η (hJ t le_rfl) hsr hrec hHSR hHRec
  exact measurable_fixedPointSol hlam hmSR hmRec measurable_const

end Measurability

/-- Corrected payoff comparisons for separate posted and recommendation
sets. The only dependence on the recommendation support is its cardinality
in the potential term. -/
theorem rectangular_corrected_regret {K T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : ℝ} (hη : 0 < η) (anchor : Fin K) (J : ℕ → ι) (v : ℕ → Fin K → ℝ)
    (hrange : ∀ t < T, ∀ j, 0 ≤ η * v t j ∧ η * v t j ≤ 1)
    (f : Fin K → Fin K) (g : ι → Fin K) :
    let s := PricingLearnerState.along η J anchor v
    let x := fun t => (s t).x η (J t) anchor
    let q := (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t j * v t j ^ 2
    (∑ t ∈ Finset.range T, ((∑ j, x t j * v t (f j)) - x t ⬝ᵥ v t))
      ≤ (K * Real.log K + Real.log 2) / η + q ∧
    (∑ t ∈ Finset.range T, (v t (g (J t)) - x t ⬝ᵥ v t))
      ≤ (Fintype.card ι * Real.log K + Real.log 2) / η + q := by
  intro s x q
  let C (t : ℕ) := (s t).core (J t)
  let M (t : ℕ) := (C t).lam η
  let H (t : ℕ) := (s t).feedback η (J t) anchor (v t)
  let L (t : ℕ) := 1 / η * Real.log
    (M t * Real.exp (η * H t 0) + (1 - M t) * Real.exp (η * H t 1))
  let zSR (t : ℕ) (i j : Fin K) := x t i * v t j
  let zRec (t : ℕ) (i : ι) (j : Fin K) := if J t = i then v t j else 0
  have hSRstate (t : ℕ) (i j : Fin K) :
      (s t).cumSR i j = ∑ u ∈ Finset.range t, zSR u i j := by
    induction t with
    | zero => simp [s, PricingLearnerState.along]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  have hRecstate (t : ℕ) (i : ι) (j : Fin K) :
      (s t).cumRec i j = ∑ u ∈ Finset.range t, zRec u i j := by
    induction t with
    | zero => simp [s, PricingLearnerState.along]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  let G (t : ℕ) : Fin 2 → ℝ := ![(s t).cumHSR, (s t).cumHRec]
  have hG (t : ℕ) (a : Fin 2) : G t a = ∑ u ∈ Finset.range t, H u a := by
    induction t with
    | zero =>
      rw [Finset.sum_range_zero]
      fin_cases a <;> rfl
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      fin_cases a <;> rfl
  have hSR : (∑ t ∈ Finset.range T, ∑ i, x t i * v t (f i)) ≤
      K * Real.log K / η + ∑ t ∈ Finset.range T, H t 0 := by
    have h := rectangular_potential_bound (T := T) hη f zSR
    rw [Fintype.card_fin] at h
    simp_rw [← hSRstate] at h
    simpa only [zSR, H, PricingLearnerState.feedback, HSRof, C, PricingLearnerState.core,
      LearnerState.matSR, Matrix.of_apply, Matrix.cons_val_zero, mul_assoc] using h
  have hRec : (∑ t ∈ Finset.range T, v t (g (J t))) ≤
      Fintype.card ι * Real.log K / η + ∑ t ∈ Finset.range T, H t 1 := by
    have h := rectangular_potential_bound (T := T) hη g zRec
    simp_rw [← hRecstate] at h
    have he (t : ℕ) : (1 / η) * ∑ i, Real.log
        (∑ j, FewExperts.hedgeWeights η ((s t).cumRec i) j * Real.exp (η * zRec t i j)) =
        H t 1 := by
      have hnorm (i : ι) :
          (∑ j, FewExperts.hedgeWeights η ((s t).cumRec i) j) = 1 := by
        have hz : 0 < ∑ j, Real.exp (η * (s t).cumRec i j) :=
          (Real.exp_pos _).trans_le (Finset.single_le_sum (fun _ _ => Real.exp_nonneg _)
            (Finset.mem_univ anchor))
        simp [FewExperts.hedgeWeights, ← Finset.sum_div, hz.ne']
      have hrow (i : ι) : (Real.log
          (∑ j, FewExperts.hedgeWeights η ((s t).cumRec i) j * Real.exp (η * zRec t i j))) =
          if J t = i then Real.log
            (∑ j, FewExperts.hedgeWeights η ((s t).cumRec (J t)) j * Real.exp (η * v t j)) else 0 := by
        by_cases hi : J t = i
        · subst i
          simp [zRec]
        · simp [zRec, hi, hnorm]
      simp_rw [hrow]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rfl
    simp_rw [he, zRec, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)] at h
    exact h
  have hmaster (a : Fin 2) : (∑ t ∈ Finset.range T, H t a) ≤
      Real.log 2 / η + ∑ t ∈ Finset.range T, L t := by
    let z (t : ℕ) (_ : Unit) := H t
    let p : Unit → Fin 2 := fun _ => a
    have h := rectangular_potential_bound (T := T) hη p z
    have hw (t : ℕ) : FewExperts.hedgeWeights η (G t) 1 = 1 - M t := by
      have hz : 0 < Real.exp (η * G t 0) + Real.exp (η * G t 1) := by positivity
      change FewExperts.hedgeWeights η (G t) 1 = 1 - FewExperts.hedgeWeights η (G t) 0
      simp only [FewExperts.hedgeWeights, Fin.sum_univ_two]
      field_simp [hz.ne']
      ring
    have hsum (t : ℕ) : (fun a => ∑ u ∈ Finset.range t, H u a) = G t :=
      funext fun a => (hG t a).symm
    simp only [z, p, Fintype.card_unit, Nat.cast_one, one_mul, Fintype.sum_unique] at h
    simp_rw [hsum, Fin.sum_univ_two, hw] at h
    exact h
  have hround (t : ℕ) (ht : t < T) :
      L t - x t ⬝ᵥ v t ≤ (Real.exp 1 - 2) * η * ∑ j, x t j * v t j ^ 2 := by
    have hx := (C t).roundX_spec η anchor
    have hlam := (C t).lam_mem η
    have h := eq_C_3 η (M t) hη hlam.1.le hlam.2.le ((C t).matSR η) ((C t).matRec η)
      ((C t).matSR_stochastic η anchor) ((C t).matRec_stochastic η anchor) anchor (x t) (v t) hx.1 hx.2
    have hpos : 0 < M t * Real.exp (η * H t 0) + (1 - M t) * Real.exp (η * H t 1) :=
      add_pos (mul_pos hlam.1 (Real.exp_pos _)) (mul_pos (sub_pos.mpr hlam.2) (Real.exp_pos _))
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log hpos (h.1.trans_eq h.2))
      (show 0 ≤ 1 / η by positivity)
    have hm := eq_C_5 η hη (x t) (v t) hx.1 (hrange t ht)
    exact (sub_le_sub_right hlog _).trans (hm.1.trans hm.2)
  have hs : (∑ t ∈ Finset.range T, (L t - x t ⬝ᵥ v t)) ≤ q := by
    unfold q
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hround t (Finset.mem_range.mp ht)
  rw [Finset.sum_sub_distrib] at hs
  constructor
  · rw [Finset.sum_sub_distrib, add_div]
    linarith only [hSR, hmaster 0, hs]
  · rw [Finset.sum_sub_distrib, add_div]
    linarith only [hRec, hmaster 1, hs]

end CalibeatBandit

end

section

set_option autoImplicit false

open scoped BigOperators

namespace CalibeatBandit.Pricing

abbrev Price := Set.Icc (0 : ℝ) 1

structure Demand where
  toFun : Price → Price
  antitone : Antitone toFun

instance : CoeFun Demand (fun _ => Price → Price) := ⟨Demand.toFun⟩

def revenue (cost : Price) (demand : Demand) (p : Price) : ℝ :=
  ((p : ℝ) - cost) * demand p

theorem abs_revenue_le_one (cost : Price) (demand : Demand) (p : Price) :
    |revenue cost demand p| ≤ 1 := by
  rw [revenue, abs_mul, abs_of_nonneg (demand p).property.1]
  apply (mul_le_of_le_one_right (abs_nonneg _) (demand p).property.2).trans
  exact abs_le.mpr ⟨by linarith [p.property.1, cost.property.2],
    by linarith [p.property.2, cost.property.1]⟩

/-- The best cumulative payoff improvement obtained by a measurable remapping
of the reference prices. Use the posted prices as the reference for swap regret
and the recommended prices for recommendation loss. -/
noncomputable def benchmark (T : ℕ) (cost : Price) (demand : ℕ → Demand)
    (reference posted : ℕ → Price) : ℝ :=
  sSup {g | ∃ f : Price → Price, Measurable f ∧
    g = ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
      revenue cost (demand t) (posted t))}

theorem benchmark_bddAbove (T : ℕ) (cost : Price) (demand : ℕ → Demand)
    (reference posted : ℕ → Price) :
    BddAbove {g | ∃ f : Price → Price, Measurable f ∧
      g = ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
        revenue cost (demand t) (posted t))} := by
  refine ⟨(T : ℝ) * 2, ?_⟩
  rintro _ ⟨f, _, rfl⟩
  calc
    _ ≤ ∑ _ ∈ Finset.range T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
      have h₁ := abs_le.mp (abs_revenue_le_one cost (demand t) (f (reference t)))
      have h₂ := abs_le.mp (abs_revenue_le_one cost (demand t) (posted t))
      linarith
    _ = _ := by simp

theorem benchmark_le_horizon_of_ge_cost (T : ℕ) (cost : Price) (demand : ℕ → Demand)
    (reference posted : ℕ → Price) (hp : ∀ t < T, cost ≤ posted t) :
    benchmark T cost demand reference posted ≤ (T : ℝ) := by
  apply csSup_le
  · exact ⟨_, id, measurable_id, rfl⟩
  · rintro _ ⟨f, _, rfl⟩
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have hc : (cost : ℝ) ≤ posted t := hp t (Finset.mem_range.mp ht)
        have h₀ : 0 ≤ revenue cost (demand t) (posted t) :=
          mul_nonneg (sub_nonneg.mpr hc) (demand t (posted t)).property.1
        have h₁ := (le_abs_self _).trans (abs_revenue_le_one cost (demand t) (f (reference t)))
        linarith only [h₀, h₁]
      _ = _ := by simp

theorem comparison_le_benchmark {T : ℕ} {cost : Price} {demand : ℕ → Demand}
    {reference posted : ℕ → Price} {f : Price → Price} (hf : Measurable f) :
    ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
      revenue cost (demand t) (posted t)) ≤ benchmark T cost demand reference posted :=
  le_csSup (benchmark_bddAbove T cost demand reference posted) ⟨f, hf, rfl⟩

theorem exists_measurable_price_remapping {ι : Type*} [Fintype ι]
    (price : ι → Price) (hprice : Function.Injective price) (target : ι → Price) :
    ∃ f : Price → Price, Measurable f ∧ f ∘ price = target := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hEmbed : MeasurableEmbedding price :=
    ⟨hprice, measurable_of_finite price, fun s _ => (s.toFinite.image price).measurableSet⟩
  exact hEmbed.exists_measurable_extend (measurable_of_finite target) (fun p => ⟨p⟩)

/-- A price at or above cost loses at most the price difference when rounded
down, since the demand at the lower price is at least as large. -/
theorem revenue_le_of_round_down (cost : Price) (demand : Demand) {p q : Price}
    (hcq : cost ≤ q) (hqp : q ≤ p) :
    revenue cost demand p ≤ revenue cost demand q + ((p : ℝ) - q) := by
  have hmono : (demand p : ℝ) ≤ demand q := demand.antitone hqp
  have hcq' : (cost : ℝ) ≤ q := hcq
  have hqp' : (q : ℝ) ≤ p := hqp
  unfold revenue
  calc
    _ = ((q : ℝ) - cost) * demand p + ((p : ℝ) - q) * demand p := by ring
    _ ≤ ((q : ℝ) - cost) * demand q + ((p : ℝ) - q) :=
      add_le_add (mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hcq'))
        (mul_le_of_le_one_right (sub_nonneg.mpr hqp') (demand p).property.2)

theorem revenue_le_of_le_cost (cost : Price) (demand : Demand) {p : Price}
    (hp : p ≤ cost) : revenue cost demand p ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (demand p).property.1

/-- The uniform grid on the interval from cost to one, with n subdivisions. -/
noncomputable def gridPrice (cost : Price) {n : ℕ} (i : Fin (n + 1)) : Price :=
  ⟨(cost : ℝ) + (1 - cost) * ((i : ℕ) / (n : ℝ)), by
    have hc : 0 ≤ 1 - (cost : ℝ) := sub_nonneg.mpr cost.property.2
    have hd : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hratio : (i : ℕ) / (n : ℝ) ≤ 1 := by
      by_cases hn : n = 0
      · simp [hn]
      · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr (by exact_mod_cast hd)
    constructor
    · exact add_nonneg cost.property.1 (mul_nonneg hc (by positivity))
    · linarith [mul_le_of_le_one_right hc hratio]⟩

theorem gridPrice_ge_cost (cost : Price) {n : ℕ} (i : Fin (n + 1)) :
    cost ≤ gridPrice cost i := by
  change (cost : ℝ) ≤ (cost : ℝ) + (1 - (cost : ℝ)) * ((i : ℕ) / (n : ℝ))
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr cost.property.2) (by positivity))

theorem gridPrice_eq_cost_of_unit_cost (cost : Price) (hc : (cost : ℝ) = 1)
    {n : ℕ} (i : Fin (n + 1)) : gridPrice cost i = cost :=
  le_antisymm (show (gridPrice cost i : ℝ) ≤ cost by
    rw [hc]
    exact (gridPrice cost i).property.2) (gridPrice_ge_cost cost i)

theorem gridPrice_injective (cost : Price) (hc : (cost : ℝ) < 1)
    {n : ℕ} (hn : 0 < n) : Function.Injective (@gridPrice cost n) := by
  intro i j h
  have he := congrArg Subtype.val h
  change (cost : ℝ) + (1 - (cost : ℝ)) * ((i : ℕ) / (n : ℝ)) =
    (cost : ℝ) + (1 - (cost : ℝ)) * ((j : ℕ) / (n : ℝ)) at he
  have h₁ : 1 - (cost : ℝ) ≠ 0 := (sub_pos.mpr hc).ne'
  have h₂ : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h₃ := (mul_left_cancel₀ h₁ (add_left_cancel he))
  have h₄ := (div_left_inj' h₂).mp h₃
  apply Fin.ext
  exact_mod_cast h₄

theorem benchmark_eq_zero_at_unit_cost (cost : Price) (hc : (cost : ℝ) = 1)
    (T : ℕ) (demand : ℕ → Demand) (reference : ℕ → Price) :
    benchmark T cost demand reference (fun _ => cost) = 0 := by
  have hz (t : ℕ) : revenue cost (demand t) cost = 0 := by simp [revenue]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, fun _ => cost, measurable_const, rfl⟩
    · rintro _ ⟨f, _, rfl⟩
      apply Finset.sum_nonpos
      intro t _
      rw [hz, sub_zero]
      exact revenue_le_of_le_cost cost (demand t) (show (f (reference t) : ℝ) ≤ cost by
        rw [hc]
        exact (f (reference t)).property.2)
  · simpa only [hz, sub_self, Finset.sum_const_zero] using
      comparison_le_benchmark (T := T) (cost := cost) (demand := demand)
        (reference := reference) (posted := fun _ => cost) (f := fun _ => cost) measurable_const

/-- A grid comparator for any price. The same index works against every
non-increasing demand curve, so it can be chosen once per reference price. -/
theorem exists_grid_comparison (cost p : Price) {n : ℕ} (hn : 0 < n) :
    ∃ i : Fin (n + 1), ∀ d : Demand,
      revenue cost d p ≤ revenue cost d (gridPrice cost i) + 1 / (n : ℝ) := by
  by_cases hp : p ≤ cost
  · refine ⟨0, fun d => (revenue_le_of_le_cost cost d hp).trans ?_⟩
    change 0 ≤ ((↑(gridPrice cost (0 : Fin (n + 1))) : ℝ) - cost) * d (gridPrice cost 0) + _
    simp [gridPrice]
  have hc : 0 < 1 - (cost : ℝ) := by
    have h : (cost : ℝ) < p := lt_of_not_ge hp
    linarith [p.property.2]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let x : ℝ := (n : ℝ) * ((p : ℝ) - cost) / (1 - cost)
  have hx : 0 ≤ x := by
    have h : (cost : ℝ) ≤ p := (lt_of_not_ge hp).le
    exact div_nonneg (mul_nonneg hn'.le (sub_nonneg.mpr h)) hc.le
  have hxn : x ≤ n := by
    apply (div_le_iff₀ hc).mpr
    apply mul_le_mul_of_nonneg_left _ hn'.le
    linarith [p.property.2]
  have hf := Nat.floor_le hx
  have hnext := Nat.lt_floor_add_one x
  have hi : ⌊x⌋₊ ≤ n := by exact_mod_cast hf.trans hxn
  let i : Fin (n + 1) := ⟨⌊x⌋₊, Nat.lt_succ_of_le hi⟩
  let q := gridPrice cost i
  have hq : (q : ℝ) = cost + (1 - cost) * ((⌊x⌋₊ : ℝ) / n) := rfl
  have cost_le_q : cost ≤ q := by
    change (cost : ℝ) ≤ q
    rw [hq]
    exact le_add_of_nonneg_right (by positivity)
  have q_le_p : q ≤ p := by
    change (q : ℝ) ≤ p
    rw [hq]
    have h := (le_div_iff₀ hc).mp hf
    apply (le_of_mul_le_mul_right ?_ hn')
    field_simp
    nlinarith only [h]
  have hgap : (p : ℝ) - q ≤ 1 / (n : ℝ) := by
    rw [hq]
    have h := (div_lt_iff₀ hc).mp hnext
    apply (le_div_iff₀ hn').mpr
    field_simp
    nlinarith only [h, cost.property.1]
  refine ⟨i, fun d => (revenue_le_of_round_down cost d cost_le_q q_le_p).trans ?_⟩
  exact add_le_add_right hgap _

/-- Payoff improvement by the best remapping into the chosen output grid. -/
noncomputable def gridBenchmark {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : ℕ) (cost : Price) (demand : ℕ → Demand) (reference : ℕ → ι)
    (posted : ℕ → Price) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun g : ι → Fin (n + 1) =>
    ∑ t ∈ Finset.range T, (revenue cost (demand t) (gridPrice cost (g (reference t))) -
      revenue cost (demand t) (posted t)))

theorem abs_gridBenchmark_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : ℕ) (cost : Price) (demand : ℕ → Demand) (reference : ℕ → ι)
    (posted : ℕ → Price) (n : ℕ) :
    |gridBenchmark T cost demand reference posted n| ≤ (T : ℝ) * 2 := by
  have h (g : ι → Fin (n + 1)) :
      |∑ t ∈ Finset.range T, (revenue cost (demand t) (gridPrice cost (g (reference t))) -
        revenue cost (demand t) (posted t))| ≤ (T : ℝ) * 2 := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |revenue cost (demand t) (gridPrice cost (g (reference t))) -
          revenue cost (demand t) (posted t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
        simpa only [one_add_one_eq_two] using
          (abs_sub _ _).trans (add_le_add (abs_revenue_le_one _ _ _) (abs_revenue_le_one _ _ _))
      _ = _ := by simp
  unfold gridBenchmark
  obtain ⟨g, _, hg⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun g : ι → Fin (n + 1) => ∑ t ∈ Finset.range T,
      (revenue cost (demand t) (gridPrice cost (g (reference t))) - revenue cost (demand t) (posted t)))
  rw [hg]
  exact h g

/-- The comparator-rounding step in Appendix E.1 for any posted prices. -/
theorem benchmark_le_gridBenchmark {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : ℕ) (cost : Price) (demand : ℕ → Demand) (reference : ℕ → ι)
    (price : ι → Price) {n : ℕ} (hn : 0 < n) (posted : ℕ → Price) :
    benchmark T cost demand (fun t => price (reference t)) posted
      ≤ gridBenchmark T cost demand reference posted n + (T : ℝ) / n := by
  classical
  apply csSup_le
  · exact ⟨_, id, measurable_id, rfl⟩
  rintro _ ⟨f, _, rfl⟩
  choose g hg using fun i => exists_grid_comparison cost (f (price i)) hn
  calc
    _ ≤ ∑ t ∈ Finset.range T, ((revenue cost (demand t) (gridPrice cost (g (reference t))) -
          revenue cost (demand t) (posted t)) + 1 / (n : ℝ)) :=
      Finset.sum_le_sum fun t _ => by linarith [hg (reference t) (demand t)]
    _ = (∑ t ∈ Finset.range T, (revenue cost (demand t) (gridPrice cost (g (reference t))) -
          revenue cost (demand t) (posted t))) + (T : ℝ) / n := by
      simp [Finset.sum_add_distrib, div_eq_mul_inv]
    _ ≤ _ := by
      exact add_le_add_left (Finset.le_sup' (fun g : ι → Fin (n + 1) =>
        ∑ t ∈ Finset.range T, (revenue cost (demand t) (gridPrice cost (g (reference t))) -
          revenue cost (demand t) (posted t))) (Finset.mem_univ g)) _

theorem gridBenchmark_le_benchmark {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : ℕ) (cost : Price) (demand : ℕ → Demand) (reference : ℕ → ι)
    (price : ι → Price) (hprice : Function.Injective price) (posted : ℕ → Price) (n : ℕ) :
    gridBenchmark T cost demand reference posted n ≤
      benchmark T cost demand (fun t => price (reference t)) posted := by
  unfold gridBenchmark
  apply Finset.sup'_le
  intro g _
  let f : ι → Price := fun i => gridPrice cost (g i)
  obtain ⟨extension, he, h⟩ := exists_measurable_price_remapping price hprice f
  have heq (i : ι) : extension (price i) = f i := congrFun h i
  simpa only [heq, f] using
    comparison_le_benchmark (T := T) (cost := cost) (demand := demand)
      (reference := fun t => price (reference t)) (posted := posted) he

/-- Finer output grids recover the continuous benchmark. The reference labels
are fixed and have distinct prices. -/
theorem benchmark_eq_iSup_gridBenchmark {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : ℕ) (cost : Price) (demand : ℕ → Demand) (reference : ℕ → ι)
    (price : ι → Price) (hprice : Function.Injective price) (posted : ℕ → Price) :
    benchmark T cost demand (fun t => price (reference t)) posted =
      ⨆ n : ℕ, gridBenchmark T cost demand reference posted (n + 1) := by
  have hb : BddAbove (Set.range fun n : ℕ => gridBenchmark T cost demand reference posted (n + 1)) := by
    refine ⟨(T : ℝ) * 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (abs_le.mp (abs_gridBenchmark_le T cost demand reference posted (n + 1))).2
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((T : ℝ) / ε)
    have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hgap : (T : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ ε := by
      apply (div_le_iff₀ hden).mpr
      have h := (div_lt_iff₀ hε).mp hn
      push_cast
      linarith
    exact (benchmark_le_gridBenchmark T cost demand reference price (Nat.succ_pos n) posted).trans
      (add_le_add (le_ciSup hb n) hgap)
  · exact ciSup_le fun n => gridBenchmark_le_benchmark T cost demand reference price hprice posted (n + 1)

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

namespace CalibeatBandit.Pricing

open MeasureTheory
open scoped BigOperators

/-- The finite-grid bound in Appendix E.1. There are N posted prices
and K possible recommended prices. -/
noncomputable def gridRegretBound (N K T : ℕ) (η μ : ℝ) : ℝ :=
  μ * T + (2 * (max N K : ℕ) * Real.log N + Real.log 2) / η +
    5 * η * N * T / (1 - μ)

noncomputable def gridLogBudget (N K : ℕ) : ℝ :=
  2 * (max N K : ℕ) * Real.log N + Real.log 2

/-- The grid and learning parameters in the sample-complexity bound.
The horizon condition covers the second-order and sampling terms. -/
theorem gridRegretBound_with_rounding {n K T : ℕ} {ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hgrid : 2 / ε ≤ (n : ℝ))
    (hT : 1024 * ((n + 1 : ℕ) : ℝ) * gridLogBudget (n + 1) K / ε ^ 2 ≤ T) :
    let N := n + 1
    let η := ε / (64 * N)
    let μ := ε / 16
    0 < η ∧ 0 < μ ∧ μ ≤ 1 / 2 ∧ 4 * N * η ≤ μ ∧
      gridRegretBound N K T η μ + Real.sqrt (2 * T * N * Real.log N) + (T : ℝ) / n
        ≤ ε * T := by
  intro N η μ
  let A : ℝ := gridLogBudget N K
  let S : ℝ := Real.sqrt (2 * T * N * Real.log N)
  have hN : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hη : 0 < η := by dsimp [η]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμ₁ : μ ≤ 1 / 2 := by dsimp [μ]; linarith
  have hηN : η * N = ε / 64 := by
    dsimp [η]
    field_simp
  have hμN : 4 * N * η = μ := by
    dsimp [μ]
    nlinarith only [hηN]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hmax : (1 : ℝ) ≤ (max N K : ℕ) := by
    exact_mod_cast (show 1 ≤ max N K from le_trans (Nat.succ_le_succ (Nat.zero_le n)) (le_max_left N K))
  have hA : 0 ≤ A := by
    unfold A gridLogBudget
    have hlo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hlogA : Real.log N ≤ A := by
    unfold A gridLogBudget
    have hlo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) hlog]
  have hbudget : 1024 * (N : ℝ) * A ≤ T * ε ^ 2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp hT
  have hfirst : A / η ≤ ε * T / 16 := by
    apply (div_le_iff₀ hη).mpr
    dsimp [η]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 64 * (N : ℝ) by positivity)).mpr
    nlinarith only [hbudget]
  refine ⟨hη, hμ, hμ₁, hμN.le, ?_⟩
  have hsecond : 5 * η * N * T / (1 - μ) ≤ 5 * ε * T / 32 := by
    have hden : 0 < 1 - μ := by linarith
    apply (div_le_iff₀ hden).mpr
    rw [mul_assoc (5 : ℝ) η, hηN]
    nlinarith only [mul_nonneg (show 0 ≤ 5 * ε * (T : ℝ) by positivity)
      (show 0 ≤ 1 / 2 - μ by linarith)]
  have hthird : S ≤ ε * T / 16 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h₁ : 512 * (N : ℝ) * Real.log N ≤ T * ε ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hlogA (show 0 ≤ 512 * (N : ℝ) by positivity)
      nlinarith only [h, hbudget, mul_nonneg (show 0 ≤ (N : ℝ) by positivity) hA]
    have h := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg T)
    nlinarith only [h]
  have hround : (T : ℝ) / n ≤ ε * T / 2 := by
    apply (div_le_iff₀ hn').mpr
    have hg := (div_le_iff₀ hε).mp hgrid
    nlinarith only [mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg T)]
  change μ * T + A / η + 5 * η * N * T / (1 - μ) + S + (T : ℝ) / n ≤ ε * T
  dsimp [μ] at *
  linarith [show 0 ≤ ε * (T : ℝ) by positivity]

/-- Choosing the grid size explicitly gives the advertised sample complexity,
conditional on the rectangular finite-grid regret bound. -/
theorem grid_parameters_for_accuracy {K T : ℕ} {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T) :
    let n := ⌈2 / ε⌉₊
    let N := n + 1
    let η := ε / (64 * N)
    let μ := ε / 16
    0 < n ∧ 0 < η ∧ 0 < μ ∧ μ ≤ 1 / 2 ∧ 4 * N * η ≤ μ ∧
      gridRegretBound N K T η μ + Real.sqrt (2 * T * N * Real.log N) + (T : ℝ) / n
        ≤ ε * T := by
  intro n N η μ
  let x : ℝ := ε⁻¹
  have hx : 0 < x := inv_pos.mpr hε
  have hx₁ : 1 ≤ x := by
    dsimp [x]
    rw [← one_div]
    exact (le_div_iff₀ hε).mpr (by simpa using hε₁)
  have h2 : 2 / ε = 2 * x := by rw [div_eq_mul_inv]
  have hg : 2 / ε ≤ (n : ℝ) := Nat.le_ceil _
  have hn : 0 < n := by exact_mod_cast (lt_of_lt_of_le (div_pos (by norm_num) hε) hg)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN : (N : ℝ) ≤ 4 * x := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 / ε by positivity)
    change (n : ℝ) < 2 / ε + 1 at h
    dsimp [N]
    push_cast
    linarith
  have hlog : 0 ≤ Real.log (4 / ε) := by
    rw [show 4 / ε = 4 * x by rw [div_eq_mul_inv]]
    exact Real.log_nonneg (by linarith)
  have hlogN : Real.log N ≤ Real.log (4 / ε) := by
    apply Real.log_le_log (by positivity)
    simpa only [div_eq_mul_inv] using hN
  have hlog2 : Real.log 2 ≤ Real.log (4 / ε) := by
    apply Real.log_le_log (by norm_num)
    rw [show 4 / ε = 4 * x by rw [div_eq_mul_inv]]
    linarith
  have hmax : ((max N K : ℕ) : ℝ) ≤ 4 * x + K := by
    push_cast
    exact max_le (hN.trans (le_add_of_nonneg_right (by positivity)))
      (le_add_of_nonneg_left (by positivity))
  have hA : gridLogBudget N K ≤ (9 * x + 2 * K) * Real.log (4 / ε) := by
    unfold gridLogBudget
    have h₁ := mul_le_mul_of_nonneg_left hlogN (show 0 ≤ (2 : ℝ) * ((max N K : ℕ) : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hmax hlog
    have h₃ := mul_le_mul_of_nonneg_right hx₁ hlog
    nlinarith only [h₁, h₂, h₃, hlog2]
  have hbudget : 1024 * (N : ℝ) * gridLogBudget N K / ε ^ 2 ≤ T := by
    calc
      _ = 1024 * (N : ℝ) * gridLogBudget N K * x ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
      _ ≤ 1024 * (4 * x) * ((9 * x + 2 * K) * Real.log (4 / ε)) * x ^ 2 := by
        have ha : 0 ≤ gridLogBudget N K := by
          unfold gridLogBudget
          have := Real.log_nonneg hN₁
          have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
          positivity
        gcongr
      _ ≤ 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) := by
        change _ ≤ 2 ^ 17 * (x ^ 4 + (K : ℝ) * x ^ 3) * Real.log (4 / ε)
        have ha : 0 ≤ x ^ 4 * Real.log (4 / ε) := by positivity
        have hb : 0 ≤ (K : ℝ) * x ^ 3 * Real.log (4 / ε) := by positivity
        nlinarith only [ha, hb]
      _ ≤ _ := hT
  exact ⟨hn, gridRegretBound_with_rounding hn hε hε₁ hg hbudget⟩

/-- The accuracy budget can be met at a rate comparable to the expression
in Theorem 5.1. An accuracy exceeding one can use the trivial bound. -/
theorem pricing_accuracy_budget (K T : ℕ) (hT : 2 ≤ T) :
    let x := (T : ℝ) ^ (-(1 / 4) : ℝ)
    let y := ((K : ℝ) / T) ^ (1 / 3 : ℝ)
    let ε := 64 * Real.log (4 * T) * (x + y)
    0 < ε ∧ (ε ≤ 1 →
      2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T) := by
  intro x y ε
  have hT₀ : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hT₁ : 1 ≤ (T : ℝ) := by exact_mod_cast (show 1 ≤ T by omega)
  have hx : 0 < x := Real.rpow_pos_of_pos hT₀ _
  have hy : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  let L := Real.log (4 * T)
  have hL : 1 ≤ L := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    linarith [Real.exp_one_lt_three]
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨hε, fun hε₁ => ?_⟩
  have hx4 : x ^ 4 = (T : ℝ)⁻¹ := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hT₀.le]
    norm_num [Real.rpow_neg_one]
  have hy3 : y ^ 3 = (K : ℝ) / T := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast (show 0 ≤ (K : ℝ) / T by positivity)]
    norm_num
  have hεx : 64 * L * x ≤ ε := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hy) (by positivity)
  have hεy : 64 * L * y ≤ ε := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx.le) (by positivity)
  have hεinv : (T : ℝ)⁻¹ ≤ ε := by
    have hxT : (T : ℝ)⁻¹ ≤ x := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hT₁ (by norm_num)
    exact hxT.trans ((le_mul_of_one_le_left hx.le (by linarith)).trans hεx)
  have hlog : Real.log (4 / ε) ≤ L := by
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ hε).mpr
    have hh := (inv_le_iff_one_le_mul₀ hT₀).mp hεinv
    nlinarith only [hh]
  have h₄ := pow_le_pow_left₀ (show 0 ≤ 64 * L * x by positivity) hεx 4
  have h₃ := pow_le_pow_left₀ (show 0 ≤ 64 * L * y by positivity) hεy 3
  rw [mul_pow, hx4] at h₄
  rw [mul_pow, hy3] at h₃
  have h₄' : (64 * L) ^ 4 ≤ T * ε ^ 4 := by
    exact ((div_le_iff₀ hT₀).mp (by simpa only [div_eq_mul_inv] using h₄)).trans_eq (mul_comm _ _)
  have h₃' : (64 * L) ^ 3 * K ≤ T * ε ^ 3 := by
    rw [← mul_div_assoc] at h₃
    have h := (div_le_iff₀ hT₀).mp h₃
    exact h.trans_eq (mul_comm _ _)
  have h4L : 2 ^ 18 * L ≤ (64 * L) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL 3
    have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ L by positivity)
    norm_num at hh ⊢
    nlinarith only [hh, show 0 ≤ L by positivity]
  have h3L : 2 ^ 18 * L ≤ (64 * L) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL 2
    have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ L by positivity)
    norm_num at hh ⊢
    nlinarith only [hh]
  have hA : 2 ^ 17 * (ε⁻¹ ^ 4) * Real.log (4 / ε) ≤ T / 2 := by
    rw [inv_pow, show 2 ^ 17 * (ε ^ 4)⁻¹ * Real.log (4 / ε) =
      (2 ^ 17 * Real.log (4 / ε)) / ε ^ 4 by ring]
    apply (div_le_iff₀ (pow_pos hε 4)).mpr
    nlinarith only [hlog, h4L, h₄']
  have hB : 2 ^ 17 * ((K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T / 2 := by
    rw [inv_pow]
    have hc := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg K)
    have hc' := mul_le_mul_of_nonneg_right h3L (Nat.cast_nonneg K)
    rw [show 2 ^ 17 * ((K : ℝ) * (ε ^ 3)⁻¹) * Real.log (4 / ε) =
      (2 ^ 17 * K * Real.log (4 / ε)) / ε ^ 3 by ring]
    apply (div_le_iff₀ (pow_pos hε 3)).mpr
    nlinarith only [hc, hc', h₃']
  linarith only [hA, hB]

/-- Lift an expected finite-grid comparison bound to the continuous benchmark.
The reference indices can encode either the posted prices or the recommendations. -/
theorem integral_benchmark_le_grid {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (cost : Price) (demand : Ω → ℕ → Demand) (reference : Ω → ℕ → ι)
    (price : ι → Price) {n : ℕ} (hn : 0 < n) (posted : Ω → ℕ → Fin (n + 1))
    (hm : ∀ t < T, ∀ g : ι → Fin (n + 1), Measurable (fun ω =>
      revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
        revenue cost (demand ω t) (gridPrice cost (posted ω t)))) :
    let continuous (ω : Ω) := benchmark T cost (demand ω)
      (fun t => price (reference ω t)) (fun t => gridPrice cost (posted ω t))
    let finite (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty (fun g : ι → Fin (n + 1) =>
      ∑ t ∈ Finset.range T, (revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
        revenue cost (demand ω t) (gridPrice cost (posted ω t))))
    Integrable continuous P →
    (∫ ω, continuous ω ∂P) ≤ (∫ ω, finite ω ∂P) + (T : ℝ) / n := by
  intro continuous finite hcontinuous
  have hfinite : Integrable finite P := by
    apply integrable_finset_max Finset.univ_nonempty _ (B := (T : ℝ) * 2)
    · intro g
      exact Finset.measurable_sum _ fun t ht => hm t (Finset.mem_range.mp ht) g
    · intro g ω
      calc
        _ ≤ ∑ t ∈ Finset.range T, |revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
            revenue cost (demand ω t) (gridPrice cost (posted ω t))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (2 : ℝ) := Finset.sum_le_sum fun t _ => by
          have h₁ := abs_revenue_le_one cost (demand ω t) (gridPrice cost (g (reference ω t)))
          have h₂ := abs_revenue_le_one cost (demand ω t) (gridPrice cost (posted ω t))
          exact (abs_sub _ _).trans (by linarith)
        _ = _ := by simp
  have hconst : Integrable (fun _ : Ω => (T : ℝ) / n) P := integrable_const _
  have hpoint (ω : Ω) : continuous ω ≤ finite ω + (T : ℝ) / n :=
    benchmark_le_gridBenchmark T cost (demand ω) (reference ω) price hn
      (fun t => gridPrice cost (posted ω t))
  have h := integral_mono hcontinuous (hfinite.add hconst) hpoint
  have he : (∫ ω, finite ω + (T : ℝ) / n ∂P) = (∫ ω, finite ω ∂P) + (T : ℝ) / n := by
    rw [integral_add hfinite hconst]
    simp
  exact h.trans_eq he

/-- Measurability at the finite output grids suffices to integrate the
continuous benchmark for a fixed set of reference prices. -/
theorem integrable_benchmark_of_grids {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℕ) (cost : Price) (demand : Ω → ℕ → Demand) (reference : Ω → ℕ → ι)
    (price : ι → Price) (hprice : Function.Injective price) (posted : Ω → ℕ → Price)
    (hm : ∀ n, ∀ t < T, ∀ g : ι → Fin (n + 1), Measurable (fun ω =>
      revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
        revenue cost (demand ω t) (posted ω t))) :
    Integrable (fun ω => benchmark T cost (demand ω)
      (fun t => price (reference ω t)) (posted ω)) P := by
  let B (n : ℕ) (ω : Ω) := gridBenchmark T cost (demand ω) (reference ω) (posted ω) (n + 1)
  have hmB (n : ℕ) : Measurable (B n) := by
    unfold B gridBenchmark
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup fun g => Finset.measurable_sum _ fun t ht => hm (n + 1) t
      (Finset.mem_range.mp ht) g
  have hEq (ω : Ω) := benchmark_eq_iSup_gridBenchmark T cost (demand ω) (reference ω)
    price hprice (posted ω)
  simp_rw [hEq]
  apply integrable_of_abs_bound (Measurable.iSup hmB) (B := (T : ℝ) * 2)
  intro ω
  have hbound (n : ℕ) : |B n ω| ≤ (T : ℝ) * 2 :=
    abs_gridBenchmark_le T cost (demand ω) (reference ω) (posted ω) (n + 1)
  have hUpper : BddAbove (Set.range fun n : ℕ => B n ω) := by
    refine ⟨(T : ℝ) * 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (abs_le.mp (hbound n)).2
  exact abs_le.mpr ⟨(abs_le.mp (hbound 0)).1.trans (le_ciSup hUpper 0),
    ciSup_le fun n => (abs_le.mp (hbound n)).2⟩

/-- The reduction in Theorem 5.1 for either choice of reference prices.
An expected grid-regret bound at the chosen parameters implies the
corresponding continuous benchmark is at most εT. -/
theorem pricing_accuracy_of_grid_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {K T : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T)
    (cost : Price) (demand : Ω → ℕ → Demand) (reference : Ω → ℕ → ι)
    (price : ι → Price) :
    let n := ⌈2 / ε⌉₊
    let N := n + 1
    let η := ε / (64 * N)
    let μ := ε / 16
    ∀ posted : Ω → ℕ → Fin N,
      (∀ t < T, ∀ g : ι → Fin N, Measurable (fun ω =>
        revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
          revenue cost (demand ω t) (gridPrice cost (posted ω t)))) →
      (Integrable (fun ω => benchmark T cost (demand ω)
        (fun t => price (reference ω t)) (fun t => gridPrice cost (posted ω t))) P) →
      (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun g : ι → Fin N =>
        ∑ t ∈ Finset.range T, (revenue cost (demand ω t) (gridPrice cost (g (reference ω t))) -
          revenue cost (demand ω t) (gridPrice cost (posted ω t)))) ∂P)
        ≤ gridRegretBound N K T η μ + Real.sqrt (2 * T * N * Real.log N) →
      ∫ ω, benchmark T cost (demand ω)
        (fun t => price (reference ω t)) (fun t => gridPrice cost (posted ω t)) ∂P ≤ ε * T := by
  intro n N η μ posted hm hi hgrid
  obtain ⟨hn, _, _, _, _, hbudget⟩ := grid_parameters_for_accuracy hε hε₁ hT
  have h := integral_benchmark_le_grid P T cost demand reference price hn posted hm hi
  exact h.trans ((add_le_add_left hgrid _).trans hbudget)

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Matrix
open scoped BigOperators

private theorem explore_weighted {N : ℕ} (μ : ℝ) (x z : Fin N → ℝ) :
    explore μ x ⬝ᵥ z = (1 - μ) * (x ⬝ᵥ z) + ∑ i, μ / N * z i := by
  simp only [explore, dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem explore_swap_le {N : ℕ} (hN : 0 < N) {μ : ℝ} (hμ : 0 ≤ μ)
    (x y : Fin N → ℝ) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) (f : Fin N → Fin N) :
    (∑ i, explore μ x i * y (f i)) - explore μ x ⬝ᵥ y
      ≤ μ + (1 - μ) * ((∑ i, x i * y (f i)) - x ⬝ᵥ y) := by
  change explore μ x ⬝ᵥ (fun i => y (f i)) - explore μ x ⬝ᵥ y ≤ _
  rw [explore_weighted, explore_weighted]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) fun i _ =>
    mul_le_of_le_one_right (show 0 ≤ μ / (N : ℝ) by positivity)
      (show y (f i) - y i ≤ 1 by linarith [(hy (f i)).2, (hy i).1])
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℝ) * (μ / N) = μ by field_simp] at h
  change (1 - μ) * (∑ i, x i * y (f i)) + (∑ i : Fin N, μ / N * y (f i)) -
    ((1 - μ) * (x ⬝ᵥ y) + ∑ i, μ / N * y i) ≤ _
  linarith only [h]

theorem explore_baseline_le {N : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (x y : Fin N → ℝ) (hx : IsProbVec x) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    x ⬝ᵥ y ≤ μ + explore μ x ⬝ᵥ y := by
  have hupper : x ⬝ᵥ y ≤ 1 := by
    unfold dotProduct
    exact (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hx.1 i) (hy i).2).trans_eq hx.2
  have hnonneg : 0 ≤ ∑ i : Fin N, μ / N * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hy i).1
  rw [explore_weighted]
  nlinarith only [hnonneg, mul_nonneg hμ (sub_nonneg.mpr hupper)]

private lemma sum_single_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (a : ι → ℝ) :
    ∑ i, (@Pi.single ι (fun _ => ℝ) _ _ j 1) i * a i = a j := by
  simp [Pi.single_apply, ite_mul]

/-- The recommendation benchmark with a finite label set and a realized
baseline action. -/
noncomputable def recommendationMax {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty (ι → Fin N)] (T : ℕ) (J : ℕ → ι) (I : ℕ → Fin N) (y : ℕ → Fin N → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun f : ι → Fin N =>
    ∑ t ∈ Finset.range T, (y t (f (J t)) - y t (I t)))

set_option maxHeartbeats 500000 in
/-- Sampling changes the baseline in every recommendation comparison by
the same random variable of mean zero. -/
theorem DrawRun.integral_recommendationMax {N T : ℕ} {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty (ι → Fin N)] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun N T P) (J : ℕ → Ω → ι) (hJ : ∀ t < T, Measurable[run.preDraw t] (J t)) :
    (∫ ω, recommendationMax T (fun t => J t ω) (fun t => run.I t ω) (fun t => run.y t ω) ∂P) =
      ∫ ω, comparisonMax T (fun t => Pi.single (J t ω) 1) (fun t => run.played t ω)
        (fun t => run.y t ω) ∂P := by
  classical
  let A (t : ℕ) (ω : Ω) := run.played t ω ⬝ᵥ run.y t ω - run.obs t ω
  let R (ω : Ω) := recommendationMax T (fun t => J t ω) (fun t => run.I t ω) (fun t => run.y t ω)
  have hA (t : ℕ) (ht : t < T) : Integrable (A t) P ∧ (∫ ω, A t ω ∂P) = 0 := by
    obtain ⟨hi, heq⟩ := run.condExp_obs P ht
    have hp : Integrable (fun ω => run.played t ω ⬝ᵥ run.y t ω) P :=
      integrable_condExp.congr heq
    refine ⟨hp.sub hi, ?_⟩
    dsimp [A]
    rw [integral_sub hp hi, ← integral_congr_ae heq, integral_condExp (run.preDraw_le_ambient ht), sub_self]
  have hR : Integrable R P := by
    unfold R recommendationMax
    apply integrable_finset_max Finset.univ_nonempty _ (B := T)
    · intro f
      refine Finset.measurable_sum _ fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      have hm := run.preDraw_le_ambient ht'
      have hm' := run.info_le _ (Nat.succ_le_of_lt ht')
      exact (measurable_select ((hJ t ht').mono hm le_rfl) fun j =>
        (measurable_pi_apply (f j)).comp ((run.y_measurable t ht').mono hm le_rfl)).sub
          ((run.obs_measurable ht').mono hm' le_rfl)
    · intro f ω
      calc
        _ ≤ ∑ t ∈ Finset.range T, |run.y t ω (f (J t ω)) - run.y t ω (run.I t ω)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
          have hy₁ := run.y_mem t (Finset.mem_range.mp ht) ω (f (J t ω))
          have hy₂ := run.y_mem t (Finset.mem_range.mp ht) ω (run.I t ω)
          exact abs_le.mpr ⟨by linarith [hy₁.1, hy₂.2], by linarith [hy₁.2, hy₂.1]⟩
        _ = _ := by simp
  have hEq (ω : Ω) : comparisonMax T (fun t => Pi.single (J t ω) 1)
      (fun t => run.played t ω) (fun t => run.y t ω) = R ω - ∑ t ∈ Finset.range T, A t ω := by
    unfold comparisonMax R recommendationMax
    simp only [sum_single_mul]
    have h (f : ι → Fin N) : (∑ t ∈ Finset.range T,
        (run.y t ω (f (J t ω)) - run.played t ω ⬝ᵥ run.y t ω)) =
        (∑ t ∈ Finset.range T, (run.y t ω (f (J t ω)) - run.y t ω (run.I t ω))) -
          ∑ t ∈ Finset.range T, A t ω := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by dsimp [A, DrawRun.obs]; ring
    simp_rw [h]
    simp only [Finset.sup'_univ_eq_ciSup]
    let F (f : ι → Fin N) := ∑ t ∈ Finset.range T, (run.y t ω (f (J t ω)) - run.y t ω (run.I t ω))
    let c := ∑ t ∈ Finset.range T, A t ω
    change (⨆ f, F f - c) = (⨆ f, F f) - c
    apply le_antisymm
    · exact ciSup_le fun f => sub_le_sub_right (le_ciSup (Finite.bddAbove_range F) f) _
    · apply sub_le_iff_le_add.mpr
      apply ciSup_le
      intro f
      exact (sub_le_iff_le_add.mp (le_ciSup (Finite.bddAbove_range (fun f => F f - c)) f))
  simp_rw [hEq]
  rw [integral_sub hR (integrable_finsetSum _ (fun t ht => (hA t (Finset.mem_range.mp ht)).1)),
    integral_finsetSum _ (fun t ht => (hA t (Finset.mem_range.mp ht)).1)]
  simp only [Finset.sum_congr rfl (fun t ht => (hA t (Finset.mem_range.mp ht)).2), Finset.sum_const_zero,
    sub_zero]
  rfl

set_option maxHeartbeats 1000000 in
/-- Expected finite-grid regret of the pricing learner, allowing separate
finite sets for actions and recommendation labels. The current label and
reward vector are fixed before the action draw. -/
theorem pricingGrid_expected_regret {N T : ℕ} {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] {η μ : ℝ} (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hNη : 4 * N * η ≤ μ) (anchor : Fin N)
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun N T P)
    (J : ℕ → Ω → ι) (hJ : ∀ t < T, Measurable[run.preDraw t] (J t))
    (hpolicy : ∀ t < T, run.played t =ᵐ[P] fun ω =>
      pricingGridPolicy η μ anchor t (fun u => J u ω) (fun u => run.I u ω) (fun u => run.obs u ω)) :
    let _ : Nonempty (ι → Fin N) := ⟨fun _ => anchor⟩
    (∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P)
      ≤ Pricing.gridRegretBound N (Fintype.card ι) T η μ + Real.sqrt (2 * T * N * Real.log N) ∧
    (∫ ω, recommendationMax T (fun t => J t ω) (fun t => run.I t ω) (fun t => run.y t ω) ∂P)
      ≤ Pricing.gridRegretBound N (Fintype.card ι) T η μ := by
  let _ : Nonempty (ι → Fin N) := ⟨fun _ => anchor⟩
  let _ : Nonempty (Fin N → Fin N) := ⟨id⟩
  let x (t : ℕ) (ω : Ω) :=
    (pricingLearnerState η μ (fun u => J u ω) (fun u => run.I u ω)
      (fun u => run.obs u ω) anchor t).x η (J t ω) anchor
  let v (t : ℕ) (ω : Ω) := estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
  let w (t : ℕ) (ω : Ω) : ι → ℝ := Pi.single (J t ω) 1
  have hN : 0 < N := Nat.zero_lt_of_lt anchor.isLt
  have hx (t : ℕ) (_ht : t < T) (ω : Ω) : IsProbVec (x t ω) := by
    exact (((pricingLearnerState η μ (fun u => J u ω) (fun u => run.I u ω)
      (fun u => run.obs u ω) anchor t).core (J t ω)).roundX_spec η anchor).1
  have hxm (t : ℕ) (ht : t < T) : Measurable[run.preDraw t] (x t) := by
    have past (u : ℕ) (hu : u < t) : run.info (u + 1) ≤ run.preDraw t :=
      (run.info_le_info (Nat.succ_le_of_lt hu) ht.le).trans (run.info_le_preDraw t ht)
    refine @measurable_pricingX Ω ι N (run.preDraw t) _ _ _ η μ anchor J run.I run.obs t ?_ ?_ ?_
    · intro u hu
      rcases lt_or_eq_of_le hu with hlt | rfl
      · exact (hJ u (hlt.trans ht)).mono ((run.preDraw_le_succ u (hlt.trans ht)).trans (past u hlt)) le_rfl
      · exact hJ u ht
    · exact fun u hu => (run.I_measurable u (hu.trans ht)).mono (past u hu) le_rfl
    · exact fun u hu => (run.obs_measurable (hu.trans ht)).mono (past u hu) le_rfl
  have hplay (t : ℕ) (ht : t < T) : run.played t =ᵐ[P] fun ω => explore μ (x t ω) := hpolicy t ht
  have hwm (t : ℕ) (ht : t < T) : Measurable[run.preDraw t] (w t) := by
    let : MeasurableSpace Ω := run.preDraw t
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun ω => (Pi.single (J t ω) 1 : ι → ℝ) i)
    have hset : MeasurableSet {ω | i = J t ω} := by
      have hh := hJ t ht (measurableSet_singleton i)
      simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hh
    simpa only [Pi.single_apply, Pi.zero_apply] using
      (Measurable.ite hset measurable_const measurable_const :
        Measurable (fun ω => if i = J t ω then (1 : ℝ) else 0))
  have hw₀ (t : ℕ) (_ht : t < T) (ω : Ω) (i : ι) : 0 ≤ w t ω i := by
    simp only [w, Pi.single_apply]
    split <;> norm_num
  have hw (t : ℕ) (_ht : t < T) (ω : Ω) : ∑ i, w t ω i = 1 := by
    simpa only [mul_one] using sum_single_mul (J t ω) (fun _ => 1)
  have hpath (ω : Ω) (f : Fin N → Fin N) (g : ι → Fin N) :
      (∑ t ∈ Finset.range T, ((∑ i, x t ω i * v t ω (f i)) - x t ω ⬝ᵥ v t ω))
        ≤ (N * Real.log N + Real.log 2) / η +
          (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t ω j * v t ω j ^ 2 ∧
      (∑ t ∈ Finset.range T, (v t ω (g (J t ω)) - x t ω ⬝ᵥ v t ω))
        ≤ (Fintype.card ι * Real.log N + Real.log 2) / η +
          (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t ω j * v t ω j ^ 2 := by
    have h (t : ℕ) (ht : t < T) (j : Fin N) : 0 ≤ η * v t ω j ∧ η * v t ω j ≤ 1 :=
      estimate_scaled_mem hN hη hμ hNη (x t ω) (hx t ht ω) (run.I t ω) j
        (run.obs t ω) (run.y_mem t ht ω (run.I t ω))
    have he (t : ℕ) : (PricingLearnerState.along η (fun u => J u ω) anchor (fun u => v u ω) t).x
        η (J t ω) anchor = x t ω := by
      unfold x
      rw [pricingLearnerState_eq_along]
      rfl
    simpa only [he] using rectangular_corrected_regret hη anchor (fun t => J t ω)
      (fun t => v t ω) h f g
  have hnlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbudget (k : ℕ) (hk : k ≤ max N (Fintype.card ι)) :
      μ * T + (k * Real.log N + Real.log 2) / η + k * Real.log N / η +
        5 * η * N * T / (1 - μ) ≤ Pricing.gridRegretBound N (Fintype.card ι) T η μ := by
    have hk' : (k : ℝ) ≤ (max N (Fintype.card ι) : ℕ) := by exact_mod_cast hk
    have hlo := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk' hnlog) hη.le
    unfold Pricing.gridRegretBound
    simp only [add_div, mul_div_assoc, two_mul]
    simp only [mul_div_assoc] at hlo
    linarith only [hlo]
  have hpM (t : ℕ) (ht : t < T) :
      Measurable[run.preDraw t] (fun ω => explore μ (x t ω)) := by
    let : MeasurableSpace Ω := run.preDraw t
    refine measurable_pi_iff.mpr ?_
    intro j
    exact (((measurable_pi_apply j).comp (hxm t ht)).const_mul (1 - μ)).add measurable_const
  have hsr := run.expected_comparison hN hη hμ₀ hμ hNη P x hx hxm hplay x
    (fun t ω => explore μ (x t ω)) (fun t ht ω => (hx t ht ω).1)
    (fun t ht ω => (hx t ht ω).2) hxm
    (fun t ht ω => (explore_prob hN hμ₀.le (by linarith) (hx t ht ω)).1)
    (fun t ht ω => (explore_prob hN hμ₀.le (by linarith) (hx t ht ω)).2)
    hpM
    (1 - μ) (by linarith) (by linarith) (fun t ht ω f =>
      explore_swap_le hN hμ₀.le (x t ω) (run.y t ω) (run.y_mem t ht ω) f)
    ((N * Real.log N + Real.log 2) / η) (by positivity)
    (fun ω f => (hpath ω f (fun _ => anchor)).1)
  have heq : (fun ω => comparisonMax T (fun t => explore μ (x t ω)) (fun t => run.played t ω)
      (fun t => run.y t ω)) =ᵐ[P] fun ω =>
        pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) := by
    have hp : ∀ᵐ ω ∂P, ∀ t : Fin T, run.played t ω = explore μ (x t ω) :=
      ae_all_iff.mpr fun t => hplay t t.isLt
    filter_upwards [hp] with ω eqω
    unfold comparisonMax pseudoSwapRegret
    congr 1
    funext f
    exact Finset.sum_congr rfl fun t ht => by
      have ht' : run.played t ω = explore μ (x t ω) := eqω ⟨t, Finset.mem_range.mp ht⟩
      simp only [← ht']
  rw [integral_congr_ae heq] at hsr
  simp only [Fintype.card_fin] at hsr
  have hre := run.expected_comparison hN hη hμ₀ hμ hNη P x hx hxm hplay w w hw₀ hw hwm hw₀ hw hwm
    1 zero_le_one le_rfl (fun t ht ω g => by
      have h := explore_baseline_le hμ₀.le (x t ω) (run.y t ω) (hx t ht ω) (run.y_mem t ht ω)
      linarith only [h]) ((Fintype.card ι * Real.log N + Real.log 2) / η) (by positivity)
    (fun ω g => by simpa only [w, sum_single_mul] using (hpath ω id g).2)
  refine ⟨(run.sampling_conversion P hN).trans (add_le_add_left
    (hsr.trans (hbudget N (le_max_left _ _))) _), ?_⟩
  rw [run.integral_recommendationMax P J hJ]
  exact hre.trans (hbudget _ (le_max_right _ _))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Pricing

open MeasureTheory
open scoped BigOperators

private theorem integral_grid_transfer {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] {K T : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : ε < 1 → 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T)
    (cost : Price) (demand : Ω → ℕ → Demand)
    (I : ℕ → Ω → Fin (⌈2 / ε⌉₊ + 1)) (hI : ∀ t < T, Measurable (I t))
    (ref : ℕ → Ω → α) (hRef : ∀ t < T, Measurable (ref t))
    (price : α → Price) (hprice : Function.Injective price)
    (hrev : ∀ t < T, ∀ p : Price, Measurable (fun ω => revenue cost (demand ω t) p)) :
    let n := ⌈2 / ε⌉₊
    let N := n + 1
    let η := ε / (64 * N)
    let μ := ε / 16
    let posted (ω : Ω) (t : ℕ) := gridPrice cost (I t ω)
    (ε < 1 →
      (∫ ω, gridBenchmark T cost (demand ω) (fun t => ref t ω) (posted ω) n ∂P)
        ≤ gridRegretBound N K T η μ + Real.sqrt (2 * T * N * Real.log N)) →
    (∫ ω, benchmark T cost (demand ω) (fun t => price (ref t ω)) (posted ω) ∂P) ≤ ε * T := by
  intro n N η μ posted hb
  have hm (m : ℕ) (t : ℕ) (ht : t < T) (g : α → Fin (m + 1)) :
      Measurable (fun ω => revenue cost (demand ω t) (gridPrice cost (g (ref t ω))) -
        revenue cost (demand ω t) (posted ω t)) :=
    (measurable_select (hRef t ht) fun j => hrev t ht (gridPrice cost (g j))).sub
      (measurable_select (hI t ht) fun j => hrev t ht (gridPrice cost j))
  have hi := integrable_benchmark_of_grids P T cost demand (fun ω t => ref t ω) price hprice posted hm
  rcases lt_or_eq_of_le hε₁ with hlt | heq
  · exact pricing_accuracy_of_grid_bound P hε hε₁ (hT hlt) cost demand
      (fun ω t => ref t ω) price (fun ω t => I t ω) (hm n) hi (hb hlt)
  · rw [heq, one_mul]
    calc
      _ ≤ ∫ _ : Ω, (T : ℝ) ∂P := integral_mono hi (integrable_const _) fun ω =>
        benchmark_le_horizon_of_ge_cost T cost (demand ω) _ _ fun t _ => gridPrice_ge_cost cost (I t ω)
      _ = _ := by simp

set_option maxHeartbeats 1800000 in
/-- The finite-grid implementation attains both continuous benchmarks at
accuracy ε for any bandit run with a fixed finite recommendation support. -/
theorem theorem_5_1_accuracy {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : ε < 1 → 2 ^ 17 * (ε⁻¹ ^ 4 + (Fintype.card ι : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T)
    (cost : Price) (demand : Ω → ℕ → Demand)
    (price : ι → Price) (hprice : Function.Injective price)
    (hrev : ∀ t < T, ∀ p : Price, Measurable (fun ω => revenue cost (demand ω t) p)) :
    let n := ⌈2 / ε⌉₊
    let N := n + 1
    let η := ε / (64 * N)
    let μ := ε / 16
    ∀ (run : DrawRun N T P) (J : ℕ → Ω → ι),
      (∀ t < T, Measurable[run.preDraw t] (J t)) →
      (∀ t < T, ∀ ω i, run.y t ω i = revenue cost (demand ω t) (gridPrice cost i)) →
      (∀ t < T, run.played t =ᵐ[P] fun ω =>
        pricingGridPolicy η μ (0 : Fin N) t (fun u => price (J u ω))
          (fun u => run.I u ω) (fun u => run.obs u ω)) →
      let posted (ω : Ω) (t : ℕ) := gridPrice cost (run.I t ω)
      (∫ ω, benchmark T cost (demand ω) (posted ω) (posted ω) ∂P) ≤ ε * T ∧
        (∫ ω, benchmark T cost (demand ω) (fun t => price (J t ω)) (posted ω) ∂P) ≤ ε * T := by
  intro n N η μ run J hJ hy hpolicy posted
  rcases lt_or_eq_of_le cost.property.2 with hcost | hcost
  swap
  · have hp (ω : Ω) : posted ω = fun _ => cost := by
      funext t
      exact gridPrice_eq_cost_of_unit_cost cost hcost (run.I t ω)
    have hz (ω : Ω) (ref : ℕ → Price) : benchmark T cost (demand ω) ref (posted ω) = 0 := by
      rw [hp, benchmark_eq_zero_at_unit_cost cost hcost]
    simp only [hz, integral_zero]
    exact ⟨by positivity, by positivity⟩
  have hmI (t : ℕ) (ht : t < T) : Measurable (run.I t) :=
    (run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
  have hmJ (t : ℕ) (ht : t < T) : Measurable (J t) :=
    (hJ t ht).mono (run.preDraw_le_ambient ht) le_rfl
  have hn : 0 < n := by
    have h := (div_pos (show (0 : ℝ) < 2 by norm_num) hε).trans_le (Nat.le_ceil (2 / ε))
    exact_mod_cast h
  have hinj : Function.Injective (@gridPrice cost n) := gridPrice_injective cost hcost hn
  refine ⟨integral_grid_transfer P hε hε₁ hT cost demand run.I hmI run.I hmI
      (gridPrice cost) hinj hrev (fun hlt => ?_),
    integral_grid_transfer P hε hε₁ hT cost demand run.I hmI J hmJ price hprice hrev (fun hlt => ?_)⟩
  all_goals
    have hbudget := hT hlt
    obtain ⟨_, hη, hμ₀, hμ, hNη, _⟩ := grid_parameters_for_accuracy hε hε₁ hbudget
    have hlabels (t : ℕ) (ht : t < T) : run.played t =ᵐ[P] fun ω =>
        pricingGridPolicy η μ (0 : Fin N) t (fun u => J u ω)
          (fun u => run.I u ω) (fun u => run.obs u ω) := by
      filter_upwards [hpolicy t ht] with ω hω
      exact hω.trans (pricingGridPolicy_relabel η μ (0 : Fin N) price hprice (fun u => J u ω)
        (fun u => run.I u ω) (fun u => run.obs u ω) t)
    obtain ⟨hsr, hre⟩ := pricingGrid_expected_regret hη hμ₀ hμ hNη (0 : Fin N) P run J hJ hlabels
  · have hs (ω : Ω) : gridBenchmark T cost (demand ω) (fun t => run.I t ω) (posted ω) n =
        swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) := by
      unfold gridBenchmark swapRegret
      congr 1
      funext f
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [hy t (Finset.mem_range.mp ht), posted]
    exact (integral_congr_ae (ae_of_all P hs)).le.trans hsr
  · have hrs (ω : Ω) : gridBenchmark T cost (demand ω) (fun t => J t ω) (posted ω) n =
        @recommendationMax N ι _ _ ⟨fun _ => (0 : Fin N)⟩ T
          (fun t => J t ω) (fun t => run.I t ω) (fun t => run.y t ω) := by
      unfold gridBenchmark recommendationMax
      congr 1
      funext f
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [hy t (Finset.mem_range.mp ht), posted]
    exact ((integral_congr_ae (ae_of_all P hrs)).le.trans hre).trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))

end CalibeatBandit.Pricing

end

section

set_option autoImplicit false

open MeasureTheory Set

namespace CalibeatBandit.Supplement

open Pricing

noncomputable section

/-- Decode a posted price using the finite grid. Histories outside the support
of the policy can be decoded arbitrarily. -/
private def gridIndex (cost : Price) (n : ℕ) (p : ℝ) : Fin (n + 1) := by
  classical
  exact if h : ∃ i : Fin (n + 1), (gridPrice cost i : ℝ) = p then h.choose else 0

private theorem gridIndex_gridPrice (cost : Price) {n : ℕ}
    (hinj : Function.Injective (@gridPrice cost n)) (i : Fin (n + 1)) :
    gridIndex cost n (gridPrice cost i : ℝ) = i := by
  classical
  unfold gridIndex
  split
  · rename_i h
    apply hinj
    exact Subtype.ext h.choose_spec
  · rename_i h
    exact (h ⟨i, rfl⟩).elim

private theorem measurable_gridIndex (cost : Price) (n : ℕ) :
    Measurable (gridIndex cost n) := by
  classical
  apply measurable_to_countable'
  intro i
  let R := Set.range (fun j : Fin (n + 1) => (gridPrice cost j : ℝ))
  have hR : R.Finite := Set.finite_range _
  have he : (gridIndex cost n) ⁻¹' {i} =
      (R ∩ (gridIndex cost n) ⁻¹' {i}) ∪ (if i = 0 then Rᶜ else ∅) := by
    ext p
    by_cases hp : p ∈ R
    · by_cases hi : i = 0 <;> simp [hp, hi]
    · have hp' : ¬ ∃ j : Fin (n + 1), (gridPrice cost j : ℝ) = p := hp
      by_cases hi : i = 0 <;> simp [gridIndex, hp', hp, hi, Ne.symm]
  rw [he]
  exact ((hR.inter_of_left _).measurableSet).union
    (by split <;> [exact hR.measurableSet.compl; exact MeasurableSet.empty])

private def extendHistory {α : Type*} (fallback : α) {n : ℕ} (x : Fin n → α) (s : ℕ) : α :=
  if h : s < n then x ⟨s, h⟩ else fallback

private theorem measurable_extendHistory {α : Type*} [MeasurableSpace α] (fallback : α)
    {n : ℕ} (s : ℕ) : Measurable (fun x : Fin n → α => extendHistory fallback x s) := by
  unfold extendHistory
  split
  · exact measurable_pi_apply _
  · exact measurable_const

private def gridPlay (cost : Price) (n : ℕ) (η μ : ℝ) (t : ℕ) (h : PriceHistory t) :
    Fin (n + 1) → ℝ :=
  pricingGridPolicy η μ 0 t (extendHistory 0 h.2.1)
    (fun s => gridIndex cost n (extendHistory 0 h.2.2.1 s))
    (extendHistory 0 h.2.2.2)

private def gridSeller (cost : Price) (n : ℕ) (η μ : ℝ) : PricingPolicy :=
  fun t h => recMeasure (fun i : Fin (n + 1) => (gridPrice cost i : ℝ)) (gridPlay cost n η μ t h)

private theorem recMeasure_apply {N : ℕ} (S : Fin N → ℝ) (q : Fin N → ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    recMeasure S q B = ∑ i : Fin N, B.indicator (fun _ => ENNReal.ofReal (q i)) (S i) := by
  classical
  simp only [recMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hB]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : S i ∈ B <;> simp [hi, smul_eq_mul]

private theorem gridSeller_isPricingPolicy (cost : Price) (n : ℕ) (η : ℝ)
    {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1) : IsPricingPolicy (gridSeller cost n η μ) := by
  classical
  intro t
  have hm : Measurable (gridPlay cost n η μ t) := by
    let J (s : ℕ) (h : PriceHistory t) := extendHistory 0 h.2.1 s
    let I (s : ℕ) (h : PriceHistory t) := gridIndex cost n (extendHistory 0 h.2.2.1 s)
    let r (s : ℕ) (h : PriceHistory t) := extendHistory 0 h.2.2.2 s
    have hJ (s : ℕ) : Measurable (J s) :=
      (measurable_extendHistory 0 s).comp measurable_snd.fst
    have hI (s : ℕ) : Measurable (I s) := (measurable_gridIndex cost n).comp
      ((measurable_extendHistory 0 s).comp measurable_snd.snd.fst)
    have hr (s : ℕ) : Measurable (r s) :=
      (measurable_extendHistory 0 s).comp measurable_snd.snd.snd
    have hx := measurable_pricingX η μ (0 : Fin (n + 1)) J I r t
      (fun s _ => hJ s) (fun s _ => hI s) (fun s _ => hr s)
    exact measurable_pi_iff.mpr fun i =>
      (((measurable_pi_apply i).comp hx).const_mul (1 - μ)).add measurable_const
  refine ⟨Measure.measurable_of_measurable_coe _ fun B hB => ?_, fun h => ?_⟩
  · simp only [gridSeller, recMeasure_apply _ _ hB]
    exact Finset.measurable_sum _ fun i _ => by
      by_cases hi : (gridPrice cost i : ℝ) ∈ B
      · simp only [Set.indicator_of_mem hi]
        exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).comp hm)
      · simp only [Set.indicator_of_notMem hi]
        exact measurable_const
  · have hp := pricingGridPolicy_prob η hμ (0 : Fin (n + 1)) t
        (extendHistory 0 h.2.1)
        (fun s => gridIndex cost n (extendHistory 0 h.2.2.1 s))
        (extendHistory 0 h.2.2.2)
    change IsProbVec (gridPlay cost n η μ t h) at hp
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [gridSeller, recMeasure_apply _ _ MeasurableSet.univ, Set.indicator_of_mem (Set.mem_univ _)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2, ENNReal.ofReal_one]
    · simp only [gridSeller, recMeasure_apply _ _ measurableSet_Icc.compl]
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (by simp [(gridPrice cost i).property]) _

private abbrev preDraw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K T : ℕ} {c : ℝ} {S : Fin K → ℝ} {seller : PricingPolicy}
    (run : PricingRun K T c S P seller) (t : ℕ) : MeasurableSpace Ω :=
  run.info t ⊔ MeasurableSpace.comap (run.J t) inferInstance

private theorem preDraw_le_succ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K T : ℕ} {c : ℝ} {S : Fin K → ℝ} {seller : PricingPolicy}
    (run : PricingRun K T c S P seller) {t : ℕ} (ht : t < T) :
    preDraw run t ≤ run.info (t + 1) :=
  sup_le (run.info_mono t ht) (run.J_measurable t ht).comap_le

private def runHistory {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K T : ℕ} {c : ℝ} {S : Fin K → ℝ} {seller : PricingPolicy}
    (run : PricingRun K T c S P seller) (t : ℕ) (ω : Ω) : PriceHistory t :=
  (fun s => recMeasure S (run.q s ω), fun s => S (run.J s ω), fun s => run.price s ω,
    fun s => revenue c (run.D s ω) (run.price s ω))

private theorem runPrice_mem_grid {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {K T n : ℕ} {cost : Price}
    {η μ : ℝ} {S : Fin K → ℝ}
    (run : PricingRun K T cost S P (gridSeller cost n η μ)) {t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂P, run.price t ω ∈ Set.range (fun i : Fin (n + 1) => (gridPrice cost i : ℝ)) := by
  let G := Set.range (fun i : Fin (n + 1) => (gridPrice cost i : ℝ))
  have hG : MeasurableSet G := (Set.finite_range _).measurableSet
  have hP : Measurable (run.price t) :=
    (run.price_measurable t ht).mono (run.info_le _ (by omega)) le_rfl
  have hzero (h : PriceHistory t) : gridSeller cost n η μ t h Gᶜ = 0 := by
    simp only [gridSeller, recMeasure_apply _ _ hG.compl]
    apply Finset.sum_eq_zero
    intro i _
    exact Set.indicator_of_notMem (by simp [G]) _
  have he := run.price_law t ht Gᶜ hG.compl
  change condExp (preDraw run t) P ((run.price t ⁻¹' Gᶜ).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
    fun ω => (gridSeller cost n η μ t (runHistory run t ω) Gᶜ).toReal at he
  have hint := integral_congr_ae he
  rw [integral_condExp ((preDraw_le_succ run ht).trans (run.info_le _ (by omega))),
    integral_indicator_const 1 (hP hG.compl)] at hint
  simp only [hzero, ENNReal.toReal_zero, integral_zero, smul_eq_mul, mul_one] at hint
  rw [ae_iff]
  exact (measureReal_eq_zero_iff).mp hint

private def runDemand {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K T : ℕ} {cost : Price} {S : Fin K → ℝ} {seller : PricingPolicy}
    (run : PricingRun K T cost S P seller) (ω : Ω) (t : ℕ) : Demand :=
  if ht : t < T then
    ⟨fun p => ⟨run.D t ω p, run.D_mem t ht ω p p.property⟩,
      fun a b hab => run.D_antitone t ht ω a.property b.property hab⟩
  else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

private theorem measurable_runRevenue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K T : ℕ} {cost : Price} {S : Fin K → ℝ} {seller : PricingPolicy}
    (run : PricingRun K T cost S P seller) {t : ℕ} (ht : t < T) (p : Price) :
    Measurable[run.info t] (fun ω => Pricing.revenue cost (runDemand run ω t) p) := by
  have hpair : @Measurable Ω (Ω × ℝ) (run.info t)
      (MeasurableSpace.prod (run.info t) (borel ℝ)) (fun ω => (ω, (p : ℝ))) :=
    (@measurable_id Ω (run.info t)).prodMk (@measurable_const ℝ Ω (borel ℝ) (run.info t) _)
  have hD : Measurable[run.info t] (fun ω => run.D t ω p) :=
    (run.D_measurable t ht).comp hpair
  have he : (fun ω => Pricing.revenue cost (runDemand run ω t) p) =
      (fun ω => ((p : ℝ) - cost) * run.D t ω p) := by
    funext ω
    unfold Pricing.revenue runDemand
    rw [dif_pos ht]
  rw [he]
  exact hD.const_mul _

private def gridDrawRun {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {K T n : ℕ} {cost : Price}
    {η μ : ℝ} {S : Fin K → ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (hinj : Function.Injective (@gridPrice cost n))
    (run : PricingRun K T cost S P (gridSeller cost n η μ)) : DrawRun (n + 1) T P where
  info := run.info
  preDraw := preDraw run
  y t ω i := Pricing.revenue cost (runDemand run ω t) (gridPrice cost i)
  I t ω := gridIndex cost n (run.price t ω)
  played t ω := gridPlay cost n η μ t (runHistory run t ω)
  info_le := run.info_le
  info_le_preDraw := fun _ _ => le_sup_left
  preDraw_le_succ := fun _ ht => preDraw_le_succ run ht
  y_measurable := by
    intro t ht
    refine (@measurable_pi_iff Ω (Fin (n + 1)) (fun _ => ℝ) (preDraw run t) _ _).mpr fun i => ?_
    exact (measurable_runRevenue run ht (gridPrice cost i)).mono le_sup_left le_rfl
  I_measurable := fun t ht => (measurable_gridIndex cost n).comp (run.price_measurable t ht)
  y_mem := by
    intro t ht ω i
    have h := abs_revenue_le_one cost (runDemand run ω t) (gridPrice cost i)
    exact ⟨mul_nonneg (sub_nonneg.mpr (gridPrice_ge_cost cost i))
      ((runDemand run ω t) (gridPrice cost i)).property.1, (abs_le.mp h).2⟩
  I_law := by
    classical
    intro t ht i
    have hInd : ((fun ω => gridIndex cost n (run.price t ω)) ⁻¹' {i}).indicator (fun _ => (1 : ℝ))
        =ᵐ[P] (run.price t ⁻¹' {(gridPrice cost i : ℝ)}).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [runPrice_mem_grid run ht] with ω hω
      obtain ⟨j, hj⟩ := hω
      rw [Set.indicator_apply, Set.indicator_apply]
      simp [← hj, gridIndex_gridPrice cost hinj, Subtype.coe_inj, hinj.eq_iff]
    refine (condExp_congr_ae hInd).trans ((run.price_law t ht _ (measurableSet_singleton _)).trans ?_)
    apply ae_of_all
    intro ω
    change (recMeasure (fun j : Fin (n + 1) => (gridPrice cost j : ℝ))
      (gridPlay cost n η μ t (runHistory run t ω)) {(gridPrice cost i : ℝ)}).toReal = _
    rw [recMeasure_apply _ _ (measurableSet_singleton _)]
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (Set.mem_singleton _), ENNReal.toReal_ofReal]
      exact (pricingGridPolicy_prob η hμ (0 : Fin (n + 1)) _ _ _ _).1 i
    · intro j _ hj
      apply Set.indicator_of_notMem
      simpa only [Set.mem_singleton_iff, Subtype.coe_inj, hinj.eq_iff] using hj
    · simp

private theorem gridDrawRun_price_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {K T n : ℕ} {cost : Price}
    {η μ : ℝ} {S : Fin K → ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (hinj : Function.Injective (@gridPrice cost n))
    (run : PricingRun K T cost S P (gridSeller cost n η μ)) :
    ∀ᵐ ω ∂P, ∀ t < T,
      (gridPrice cost ((gridDrawRun hμ hinj run).I t ω) : ℝ) = run.price t ω := by
  rw [ae_all_iff]
  intro t
  by_cases ht : t < T
  · filter_upwards [runPrice_mem_grid run ht] with ω hω _
    obtain ⟨j, hj⟩ := hω
    change (gridPrice cost (gridIndex cost n (run.price t ω)) : ℝ) = run.price t ω
    rw [← hj, gridIndex_gridPrice cost hinj]
  · simp [ht]

private theorem gridDrawRun_plays_policy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {K T n : ℕ} {cost : Price}
    {η μ : ℝ} {S : Fin K → ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (hinj : Function.Injective (@gridPrice cost n))
    (run : PricingRun K T cost S P (gridSeller cost n η μ)) {t : ℕ} (ht : t < T) :
    let draw := gridDrawRun hμ hinj run
    draw.played t =ᵐ[P] fun ω => pricingGridPolicy η μ 0 t
      (fun s => S (run.J s ω)) (fun s => draw.I s ω) (fun s => draw.obs s ω) := by
  intro draw
  filter_upwards [gridDrawRun_price_ae hμ hinj run] with ω hω
  change gridPlay cost n η μ t (runHistory run t ω) = _
  unfold gridPlay
  apply pricingGridPolicy_eq_of_history
  · intro s hs
    simp [extendHistory, runHistory, Nat.lt_succ_of_le hs]
  · intro s hs
    simp [extendHistory, runHistory, hs, draw, gridDrawRun]
  · intro s hs
    have hsT := hs.trans ht
    simp only [extendHistory, dif_pos hs, runHistory]
    change revenue cost (run.D s ω) (run.price s ω) =
      Pricing.revenue cost (runDemand run ω s) (gridPrice cost (draw.I s ω))
    rw [← hω s hsT]
    unfold Pricing.revenue revenue runDemand
    rw [dif_pos hsT]

private theorem pricingRec_le_benchmark {T : ℕ} {cost : Price} (D : ℕ → ℝ → ℝ)
    (demand : ℕ → Demand) (ref posted : ℕ → Price) (r p : ℕ → ℝ)
    (hd : ∀ t < T, ∀ q : Price, (demand t q : ℝ) = D t q)
    (hr : ∀ t < T, (ref t : ℝ) = r t) (hp : ∀ t < T, (posted t : ℝ) = p t) :
    pricingRec T cost D r p ≤ benchmark T cost demand ref posted := by
  unfold pricingRec
  apply csSup_le
  · exact ⟨_, fun _ => 0, measurable_const, fun _ => by simp, rfl⟩
  · rintro z ⟨f, hfm, hfrange, rfl⟩
    let q : Price → Price := fun x => ⟨f x, hfrange x⟩
    have hq : Measurable q := (hfm.comp measurable_subtype_coe).subtype_mk
    have hb := comparison_le_benchmark (T := T) (cost := cost) (demand := demand)
      (reference := ref) (posted := posted) hq
    refine le_trans (le_of_eq ?_) hb
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    simp only [Pricing.revenue, revenue, hd t ht', hp t ht', q, hr t ht']

/-- The grid seller satisfies the mission's outer-expectation bounds. Repeated
entries in the recommendation list represent the same recommendation price. -/
theorem exists_pricingPolicy_accuracy.{u} {K T : ℕ} (hK : 0 < K) {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hbudget : ε < 1 → 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T)
    (cost : Price) :
    ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
      PricingRegretBound.{u} K T cost (ε * T) (ε * T) seller := by
  classical
  let n := ⌈2 / ε⌉₊
  let η := ε / (64 * (n + 1 : ℕ))
  let μ := ε / 16
  have hμ : μ ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [μ]; positivity, by dsimp [μ]; linarith⟩
  refine ⟨gridSeller cost n η μ, gridSeller_isPricingPolicy cost n η hμ, ?_⟩
  intro S hS Ω mΩ P hP run
  let _ : IsProbabilityMeasure P := hP
  let demand := runDemand run
  have hD (ω : Ω) (t : ℕ) (ht : t < T) (q : Price) : (demand ω t q : ℝ) = run.D t ω q := by
    unfold demand runDemand
    rw [dif_pos ht]
  let recommendation (ω : Ω) (t : ℕ) : Price := ⟨S (run.J t ω), hS _⟩
  rcases lt_or_eq_of_le cost.property.2 with hcost | hcost
  swap
  · have hprice : ∀ᵐ ω ∂P, ∀ t < T, (cost : ℝ) = run.price t ω := by
      rw [ae_all_iff]
      intro t
      by_cases ht : t < T
      · filter_upwards [runPrice_mem_grid run ht] with ω hω _
        obtain ⟨i, hi⟩ := hω
        change (gridPrice cost i : ℝ) = run.price t ω at hi
        rwa [gridPrice_eq_cost_of_unit_cost cost hcost] at hi
      · simp [ht]
    have hb (r : ℕ → Ω → ℝ) (ref : Ω → ℕ → Price)
        (hRef : ∀ᵐ ω ∂P, ∀ t < T, (ref ω t : ℝ) = r t ω) :
        OuterExpLE P (fun ω => pricingRec T cost (fun t => run.D t ω)
          (fun t => r t ω) (fun t => run.price t ω)) (ε * T) := by
      refine ⟨fun _ => 0, integrable_zero _ _ _, ?_, by simp; positivity⟩
      filter_upwards [hprice, hRef] with ω hp hr
      have hi := pricingRec_le_benchmark (cost := cost) (fun t => run.D t ω)
        (demand ω) (ref ω) (fun _ => cost) (fun t => r t ω) (fun t => run.price t ω)
        (hD ω) hr hp
      rwa [benchmark_eq_zero_at_unit_cost cost hcost] at hi
    exact ⟨hb run.price (fun _ _ => cost) hprice,
      hb (fun t ω => S (run.J t ω)) recommendation (ae_of_all P (fun _ _ _ => rfl))⟩
  have hn : 0 < n := by
    have h := (div_pos (show (0 : ℝ) < 2 by norm_num) hε).trans_le (Nat.le_ceil (2 / ε))
    exact_mod_cast h
  have hinj := gridPrice_injective cost hcost hn
  let draw := gridDrawRun hμ hinj run
  let price (ω : Ω) (t : ℕ) := gridPrice cost (draw.I t ω)
  let labels := Set.range S
  have : Finite labels := (Set.finite_range S).to_subtype
  let : Fintype labels := Fintype.ofFinite _
  let label (i : Fin K) : labels := ⟨S i, Set.mem_range_self i⟩
  let : Nonempty labels := ⟨label ⟨0, hK⟩⟩
  have hlabel : Function.Surjective label := by
    intro x
    obtain ⟨i, hi⟩ := x.property
    exact ⟨i, Subtype.ext hi⟩
  have hcard : Fintype.card labels ≤ K := by simpa using Fintype.card_le_of_surjective label hlabel
  let recPrice (i : labels) : Price := ⟨i, by obtain ⟨j, hj⟩ := i.property; rw [← hj]; exact hS j⟩
  have hrecPrice : Function.Injective recPrice := fun _ _ h => Subtype.ext (congrArg (fun p : Price => (p : ℝ)) h)
  let J (t : ℕ) (ω : Ω) := label (run.J t ω)
  have hJ (t : ℕ) (_ht : t < T) : Measurable[draw.preDraw t] (J t) :=
    (measurable_of_countable label).comp (Measurable.of_comap_le le_sup_right)
  have hrev (t : ℕ) (ht : t < T) (p : Price) :
      Measurable (fun ω => Pricing.revenue cost (demand ω t) p) :=
    (measurable_runRevenue run ht p).mono (run.info_le _ ht.le) le_rfl
  have hbound (hlt : ε < 1) :
      2 ^ 17 * (ε⁻¹ ^ 4 + (Fintype.card labels : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T := by
    have hc : (Fintype.card labels : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcard
    have hlog : 0 ≤ Real.log (4 / ε) :=
      Real.log_nonneg ((le_div_iff₀ hε).2 (by linarith))
    refine le_trans ?_ (hbudget hlt)
    have hpow : 0 ≤ ε⁻¹ ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hpow)) (by positivity)) hlog
  have hpolicy (t : ℕ) (ht : t < T) : draw.played t =ᵐ[P] fun ω =>
      pricingGridPolicy η μ (0 : Fin (n + 1)) t (fun u => recPrice (J u ω))
        (fun u => draw.I u ω) (fun u => draw.obs u ω) := by
    filter_upwards [gridDrawRun_plays_policy hμ hinj run ht] with ω hω
    exact hω.trans (pricingGridPolicy_relabel η μ (0 : Fin (n + 1))
      (Subtype.val : Price → ℝ) Subtype.val_injective (fun u => recPrice (J u ω))
      (fun u => draw.I u ω) (fun u => draw.obs u ω) t)
  obtain ⟨hs, hr⟩ := theorem_5_1_accuracy P hε hε₁ hbound cost demand recPrice hrecPrice hrev
    draw J hJ (fun _ _ _ _ => rfl) hpolicy
  have hI (t : ℕ) (ht : t < T) : Measurable (draw.I t) :=
    (draw.I_measurable t ht).mono (draw.info_le _ (by omega)) le_rfl
  have hJ' (t : ℕ) (ht : t < T) : Measurable (J t) :=
    (hJ t ht).mono (draw.preDraw_le_ambient ht) le_rfl
  have hInt {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
      [MeasurableSingletonClass ι] (rep : ι → Price) (hrep : Function.Injective rep)
      (ref : ℕ → Ω → ι) (href : ∀ t < T, Measurable (ref t)) :
      Integrable (fun ω => benchmark T cost (demand ω) (fun t => rep (ref t ω)) (price ω)) P := by
    apply integrable_benchmark_of_grids P T cost demand (fun ω t => ref t ω) rep hrep price
    intro m t ht g
    exact (measurable_select (href t ht) fun i => hrev t ht (gridPrice cost (g i))).sub
      (measurable_select (hI t ht) fun i => hrev t ht (gridPrice cost i))
  have hprice := gridDrawRun_price_ae hμ hinj run
  refine ⟨⟨_, hInt (gridPrice cost) hinj draw.I hI, ?_, hs⟩,
    ⟨_, hInt recPrice hrecPrice J hJ', ?_, hr⟩⟩
  · filter_upwards [hprice] with ω hp
    exact pricingRec_le_benchmark (cost := cost) (fun t => run.D t ω) (demand ω)
      (price ω) (price ω) (fun t => run.price t ω) (fun t => run.price t ω) (hD ω) hp hp
  · filter_upwards [hprice] with ω hp
    exact pricingRec_le_benchmark (cost := cost) (fun t => run.D t ω) (demand ω)
      (fun t => recPrice (J t ω)) (price ω) (fun t => S (run.J t ω))
      (fun t => run.price t ω) (hD ω) (fun _ _ => rfl) hp

end

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Pricing

universe u

private theorem pricingRegretBound_mono {K T : ℕ} {c a b : ℝ} {seller : PricingPolicy}
    (h : PricingRegretBound.{u} K T c a a seller) (hab : a ≤ b) :
    PricingRegretBound.{u} K T c b b seller := by
  intro S hS Ω mΩ P hP run
  obtain ⟨⟨g, hg, hdom, hInt⟩, ⟨f, hf, hfdom, hfInt⟩⟩ := h S hS P run
  exact ⟨⟨g, hg, hdom, hInt.trans hab⟩, ⟨f, hf, hfdom, hfInt.trans hab⟩⟩

private theorem log_four_le_two : Real.log 4 ≤ 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

/-- Theorem 5.1 in the mission's pricing protocol, including the regret rate
and its inversion into a round bound for accuracy. -/
theorem theorem_5_1 :
    (∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (K T : ℕ) (c : ℝ), 1 ≤ K → 1 ≤ T → c ∈ Set.Icc (0 : ℝ) 1 →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          seller) ∧
    (∃ C' : ℝ, 0 < C' ∧ ∃ k' : ℕ, ∀ (K T : ℕ) (c ε : ℝ), 1 ≤ K → c ∈ Set.Icc (0 : ℝ) 1 → 0 < ε →
      C' * (ε⁻¹ ^ 4 + K * ε⁻¹ ^ 3) * (1 + Real.log K + |Real.log ε|) ^ k' ≤ T →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c (ε * T) (ε * T) seller) := by
  refine ⟨⟨128, by norm_num, 1, ?_⟩, ⟨2 ^ 18, by positivity, 1, ?_⟩⟩
  · intro K T c hK hT hc
    let cost : Price := ⟨c, hc⟩
    let rate := (T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)
    let L := 1 + Real.log ((K : ℝ) * T)
    have hLlog : 0 ≤ Real.log ((K : ℝ) * T) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hK) (by exact_mod_cast hT))
    have hL : 1 ≤ L := by dsimp [L]; linarith
    have hrate : 0 ≤ rate := by dsimp [rate]; positivity
    have hK' : 0 < K := Nat.zero_lt_of_lt hK
    by_cases h : 2 ≤ T
    · let e := 64 * Real.log (4 * T) * ((T : ℝ) ^ (-(1 / 4) : ℝ) +
          ((K : ℝ) / T) ^ (1 / 3 : ℝ))
      let ε := min e 1
      obtain ⟨he, hb⟩ := pricing_accuracy_budget K T h
      have hε : 0 < ε := lt_min he zero_lt_one
      have hB (hlt : ε < 1) : 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) * Real.log (4 / ε) ≤ T := by
        have he1 : e < 1 := by by_contra! hn; simp [ε, min_eq_right hn] at hlt
        simpa only [ε, min_eq_left he1.le] using hb he1.le
      obtain ⟨seller, hs, hbnd⟩ :=
        exists_pricingPolicy_accuracy.{u} hK' hε (min_le_right _ _) hB cost
      refine ⟨seller, hs, pricingRegretBound_mono hbnd ?_⟩
      have hTpos : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
      have he_rate : e * T = 64 * Real.log (4 * T) * rate := by
        have hx : (T : ℝ) ^ (-(1 / 4) : ℝ) * T = (T : ℝ) ^ (3 / 4 : ℝ) := by
          calc
            _ = (T : ℝ) ^ (-(1 / 4) : ℝ) * (T : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hTpos]; norm_num
        have hy : ((K : ℝ) / T) ^ (1 / 3 : ℝ) * T =
            (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ) := by
          rw [Real.div_rpow (Nat.cast_nonneg K) hTpos.le]
          calc
            _ = (K : ℝ) ^ (1 / 3 : ℝ) * ((T : ℝ) ^ (1 : ℝ) / (T : ℝ) ^ (1 / 3 : ℝ)) := by
              rw [Real.rpow_one]
              ring
            _ = _ := by rw [← Real.rpow_sub hTpos]; norm_num
        dsimp [e, rate]
        rw [mul_assoc, add_mul, hx, hy]
      have hlogT : Real.log (T : ℝ) ≤ Real.log ((K : ℝ) * T) :=
        Real.log_le_log hTpos (le_mul_of_one_le_left hTpos.le (by exact_mod_cast hK))
      have hlog : Real.log (4 * T) ≤ 2 * L := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne']
        dsimp [L]
        linarith [log_four_le_two]
      change ε * T ≤ 128 * rate * L ^ (1 : ℕ)
      calc
        ε * T ≤ e * T := mul_le_mul_of_nonneg_right (min_le_left _ _) hTpos.le
        _ = 64 * Real.log (4 * T) * rate := he_rate
        _ ≤ (64 * (2 * L)) * rate := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by norm_num)) hrate
        _ = 128 * rate * L ^ (1 : ℕ) := by ring
    · have ht1 : T = 1 := by omega
      have hB (hlt : (1 : ℝ) < 1) :
          2 ^ 17 * ((1 : ℝ)⁻¹ ^ 4 + (K : ℝ) * (1 : ℝ)⁻¹ ^ 3) * Real.log (4 / 1) ≤ T :=
        (lt_irrefl _ hlt).elim
      obtain ⟨seller, hs, hbnd⟩ :=
        exists_pricingPolicy_accuracy.{u} hK' (by norm_num : (0 : ℝ) < 1) le_rfl hB cost
      refine ⟨seller, hs, pricingRegretBound_mono hbnd ?_⟩
      have hr : 1 ≤ rate := by
        dsimp [rate]
        rw [ht1]
        simp only [Nat.cast_one, Real.one_rpow]
        have hn : 0 ≤ (K : ℝ) ^ (1 / 3 : ℝ) := by positivity
        linarith
      change (1 : ℝ) * T ≤ 128 * rate * L ^ (1 : ℕ)
      rw [ht1, Nat.cast_one, mul_one, pow_one]
      exact (show (1 : ℝ) ≤ 128 * rate by linarith).trans
        (le_mul_of_one_le_right (by positivity) hL)
  · intro K T c ε hK hc hε hT
    let cost : Price := ⟨c, hc⟩
    let e := min ε 1
    have hK' : 0 < K := Nat.zero_lt_of_lt hK
    have hB (hlt : e < 1) : 2 ^ 17 * (e⁻¹ ^ 4 + (K : ℝ) * e⁻¹ ^ 3) * Real.log (4 / e) ≤ T := by
      have hε₁ : ε < 1 := by by_contra! hn; simp [e, min_eq_right hn] at hlt
      rw [show e = ε from min_eq_left hε₁.le]
      have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
      have hlog : Real.log (4 / ε) ≤ 2 * (1 + Real.log (K : ℝ) + |Real.log ε|) := by
        rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hε.ne']
        linarith [log_four_le_two, neg_le_abs (Real.log ε), abs_nonneg (Real.log ε)]
      refine le_trans ?_ hT
      rw [pow_one]
      have hh : 0 ≤ ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3 := by positivity
      calc
        _ ≤ 2 ^ 17 * (ε⁻¹ ^ 4 + (K : ℝ) * ε⁻¹ ^ 3) *
              (2 * (1 + Real.log (K : ℝ) + |Real.log ε|)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by ring
    obtain ⟨seller, hs, hbnd⟩ :=
      exists_pricingPolicy_accuracy.{u} hK' (lt_min hε zero_lt_one) (min_le_right _ _) hB cost
    exact ⟨seller, hs, pricingRegretBound_mono hbnd
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg T))⟩

end CalibeatBandit.Supplement

end

section

universe u

open CalibeatBandit.Supplement

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (K T : ℕ) (c : ℝ), 1 ≤ K → 1 ≤ T → c ∈ Set.Icc (0 : ℝ) 1 →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          seller) ∧
    (∃ C' : ℝ, 0 < C' ∧ ∃ k' : ℕ, ∀ (K T : ℕ) (c ε : ℝ), 1 ≤ K → c ∈ Set.Icc (0 : ℝ) 1 → 0 < ε →
      C' * (ε⁻¹ ^ 4 + K * ε⁻¹ ^ 3) * (1 + Real.log K + |Real.log ε|) ^ k' ≤ T →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c (ε * T) (ε * T) seller) := CalibeatBandit.Supplement.theorem_5_1

end
