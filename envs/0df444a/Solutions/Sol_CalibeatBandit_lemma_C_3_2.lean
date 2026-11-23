-- Prove2me | solution 2 for CalibeatBandit.lemma_C_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:32:24.218914+00:00
-- url     : https://prove2.me/submissions/b7392e5b-ea53-4fea-b6eb-8b52b75ffb6a

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Theorems.Thm_CalibeatBandit_eq_C_1
import Theorems.Thm_CalibeatBandit_eq_C_3
import Theorems.Thm_CalibeatBandit_eq_C_5
import Theorems.Thm_CalibeatBandit_eq_C_6

section

set_option autoImplicit false

open Matrix
open scoped BigOperators Nat

namespace CalibeatBandit


end CalibeatBandit

end

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

@[fun_prop] private theorem measurable_hedge {g : Ω → Fin K → ℝ} (hg : Measurable g)
    (η : ℝ) (j : Fin K) : Measurable fun ω => FewExperts.hedgeWeights η (g ω) j := by
  unfold FewExperts.hedgeWeights
  exact (Real.continuous_exp.measurable.comp ((measurable_pi_iff.mp hg j).const_mul η)).div
    (Finset.measurable_sum _ fun i _ =>
      Real.continuous_exp.measurable.comp ((measurable_pi_iff.mp hg i).const_mul η))

private theorem measurable_fixedPointSol {lam : Ω → ℝ}
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

private theorem measurable_alg_history (η μ : ℝ) (J I : ℕ → Ω → Fin K) (r : ℕ → Ω → ℝ)
    (t : ℕ) (hJ : ∀ s < t, Measurable (J s)) (hI : ∀ s < t, Measurable (I s))
    (hr : ∀ s < t, Measurable (r s)) :
    let S := fun ω => algState η μ (fun s => J s ω) (fun s => I s ω) (fun s => r s ω) t
    (∀ i j, Measurable fun ω => (S ω).cumSR i j) ∧
    (∀ i j, Measurable fun ω => (S ω).cumRec i j) ∧
    (Measurable fun ω => (S ω).cumHSR) ∧ (Measurable fun ω => (S ω).cumHRec) := by
  induction t with
  | zero =>
    exact ⟨fun _ _ => measurable_const, fun _ _ => measurable_const,
      measurable_const, measurable_const⟩
  | succ t ih =>
    let S := fun ω => algState η μ (fun s => J s ω) (fun s => I s ω) (fun s => r s ω) t
    obtain ⟨hsr, hrec, hHSR, hHRec⟩ := ih (fun s hs => hJ s (by omega))
      (fun s hs => hI s (by omega)) (fun s hs => hr s (by omega))
    have hmSR : Measurable fun ω => (S ω).matSR η := measurable_pi_iff.mpr fun j =>
      measurable_pi_iff.mpr fun i => measurable_hedge (measurable_pi_iff.mpr (hsr i)) η j
    have hmRec : Measurable fun ω => (S ω).matRec η := measurable_pi_iff.mpr fun j =>
      measurable_pi_iff.mpr fun i => measurable_hedge (measurable_pi_iff.mpr (hrec i)) η j
    have hmix : Measurable fun ω => (S ω).lam η :=
      measurable_hedge (measurable_pi_iff.mpr (Fin.forall_fin_two.mpr ⟨hHSR, hHRec⟩)) η 0
    have hj := hJ t (Nat.lt_succ_self _)
    have hi := hI t (Nat.lt_succ_self _)
    have ht := hr t (Nat.lt_succ_self _)
    let x := fun ω => (S ω).roundX η (J t ω)
    have hx := measurable_pi_iff.mp (measurable_fixedPointSol hmix hmSR hmRec hj)
    have hp (j : Fin K) : Measurable fun ω => explore μ (x ω) j :=
      ((hx j).const_mul (1 - μ)).add measurable_const
    let v := fun ω => estimate η (explore μ (x ω)) (I t ω) (r t ω)
    have hv (j : Fin K) : Measurable fun ω => v ω j :=
      (Measurable.ite (hi (measurableSet_singleton j)) (ht.div (hp j)) measurable_const).add
        (measurable_const.div (hp j))
    have hzSR (i : Fin K) : Measurable fun ω =>
        Real.log (∑ j, (S ω).matSR η j i * Real.exp (η * x ω i * v ω j)) :=
      Real.measurable_log.comp (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_iff.mp (measurable_pi_iff.mp hmSR j) i).mul
          (Real.continuous_exp.measurable.comp (((hx i).const_mul η).mul (hv j))))
    have hzRec (i : Fin K) : Measurable fun ω =>
        Real.log (∑ j, (S ω).matRec η j i * Real.exp (η * v ω j)) :=
      Real.measurable_log.comp (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_iff.mp (measurable_pi_iff.mp hmRec j) i).mul
          (Real.continuous_exp.measurable.comp ((hv j).const_mul η)))
    exact ⟨fun i j => (hsr i j).add ((hx i).mul (hv j)),
      fun i j => (hrec i j).add (Measurable.ite (hj (measurableSet_singleton i)) (hv j) measurable_const),
      hHSR.add ((Finset.measurable_sum _ fun i _ => hzSR i).const_mul _),
      hHRec.add ((measurable_select hj hzRec).const_mul _)⟩

private theorem measurable_algX_history (η μ : ℝ) (J I : ℕ → Ω → Fin K) (r : ℕ → Ω → ℝ)
    (t : ℕ) (hJ : ∀ s < t, Measurable (J s)) (hI : ∀ s < t, Measurable (I s))
    (hr : ∀ s < t, Measurable (r s)) (hcur : Measurable (J t)) :
    Measurable fun ω => algX η μ (fun s => J s ω) (fun s => I s ω) (fun s => r s ω) t := by
  let S := fun ω => algState η μ (fun s => J s ω) (fun s => I s ω) (fun s => r s ω) t
  obtain ⟨hsr, hrec, hHSR, hHRec⟩ := measurable_alg_history η μ J I r t hJ hI hr
  have hSR : Measurable (fun ω => (S ω).matSR η) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
      measurable_hedge (measurable_pi_iff.mpr (hsr i)) η j
  have hRec : Measurable (fun ω => (S ω).matRec η) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
      measurable_hedge (measurable_pi_iff.mpr (hrec i)) η j
  have hmix : Measurable (fun ω => (S ω).lam η) :=
    measurable_hedge (measurable_pi_iff.mpr (Fin.forall_fin_two.mpr ⟨hHSR, hHRec⟩)) η 0
  exact measurable_fixedPointSol hmix hSR hRec hcur

end Measurability

namespace ProtocolRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {policy : Policy K}

theorem info_le_info (run : ProtocolRun K T P policy) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    run.info a ≤ run.info b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => exact (ih (by omega)).trans (run.info_mono _ (by omega))

theorem preDraw_le_succ (run : ProtocolRun K T P policy) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ run.info (t + 1) :=
  sup_le (run.info_mono t ht) (run.J_measurable t ht).comap_le

theorem preDraw_le_ambient (run : ProtocolRun K T P policy) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ mΩ :=
  (run.preDraw_le_succ ht).trans (run.info_le _ (Nat.succ_le_of_lt ht))

theorem algX_prob (run : ProtocolRun K T P policy) (η μ : ℝ) (t : ℕ) (ω : Ω) :
    IsProbVec (run.algX η μ t ω) :=
  ((CalibeatBandit.algState η μ (fun s => run.J s ω) (fun s => run.I s ω)
    (fun s => run.obs s ω) t).roundX_spec η (run.J t ω)).1

theorem algV_scaled_mem (run : ProtocolRun K T P policy) {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ) {t : ℕ} (ht : t < T)
    (ω : Ω) (j : Fin K) :
    0 ≤ η * run.algV η μ t ω j ∧ η * run.algV η μ t ω j ≤ 1 := by
  let x := run.algX η μ t ω j
  let p := run.algP η μ t ω j
  let d := (Real.exp 1 - 2) * η
  have hx : 0 ≤ x := (run.algX_prob η μ t ω).1 j
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₈ : η ≤ 1 / 8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hp : 4 * η ≤ p := by
    change 4 * η ≤ (1 - μ) * x + μ / K
    have hle := (le_div_iff₀ hk).mpr (show 4 * η * K ≤ μ by linarith only [hKη])
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by linarith) hx))
  have hp₀ : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hd₀ : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hd₁ : d ≤ η := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three]) hη.le]
  let r := if run.I t ω = j then run.obs t ω else 0
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [r]
    split
    · exact run.y_mem t ht ω (run.I t ω)
    · exact ⟨le_rfl, zero_le_one⟩
  have hv : run.algV η μ t ω j = (r + d) / p := by
    change (if run.I t ω = j then run.obs t ω / p else 0) + d / p = _
    dsimp [r]
    split <;> simp [add_div]
  rw [hv]
  refine ⟨mul_nonneg hη.le (div_nonneg (add_nonneg hr.1 hd₀) hp₀.le), ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hp₀).mpr
  nlinarith [mul_nonneg hη.le (show 0 ≤ 4 - (r + d) by linarith [hr.2])]

theorem algX_measurable (run : ProtocolRun K T P policy) (η μ : ℝ) {t : ℕ} (ht : t < T) :
    Measurable[run.preDraw t] (run.algX η μ t) := by
  have hle (s : ℕ) (hs : s < t) : run.info (s + 1) ≤ run.preDraw t :=
    (run.info_le_info (show s + 1 ≤ t by omega) ht.le).trans le_sup_left
  have hJ (s : ℕ) (hs : s < t) : Measurable[run.preDraw t] (run.J s) :=
    (run.J_measurable s (by omega)).mono (hle s hs) le_rfl
  have hI (s : ℕ) (hs : s < t) : Measurable[run.preDraw t] (run.I s) :=
    (run.I_measurable s (by omega)).mono (hle s hs) le_rfl
  have hr (s : ℕ) (hs : s < t) : Measurable[run.preDraw t] (run.obs s) := by
    unfold ProtocolRun.obs
    refine @measurable_select Ω (run.preDraw t) (Fin K) _ _ _ _ (hI s hs) (fun j ω => run.y s ω j) ?_
    intro j
    exact (measurable_pi_apply j).comp ((run.y_measurable s (by omega)).mono
      ((run.info_mono s (by omega)).trans (hle s hs)) le_rfl)
  exact @measurable_algX_history Ω (run.preDraw t) K η μ run.J run.I run.obs t hJ hI hr
    (measurable_iff_comap_le.mpr le_sup_right)

theorem algV_measurable (run : ProtocolRun K T P policy) (η μ : ℝ) {t : ℕ}
    (ht : t < T) (j : Fin K) :
    Measurable[run.info (t + 1)] (fun ω => run.algV η μ t ω j) := by
  have hx := (measurable_pi_apply j).comp
    ((run.algX_measurable η μ ht).mono (run.preDraw_le_succ ht) le_rfl)
  have hp : Measurable[run.info (t + 1)] (fun ω => run.algP η μ t ω j) :=
    (hx.const_mul (1 - μ)).add measurable_const
  have hi := run.I_measurable t ht
  have hr : Measurable[run.info (t + 1)] (run.obs t) := by
    unfold ProtocolRun.obs
    refine @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ hi
      (fun j ω => run.y t ω j) fun k => ?_
    exact (measurable_pi_apply k).comp ((run.y_measurable t ht).mono (run.info_mono t ht) le_rfl)
  exact (Measurable.ite (hi (measurableSet_singleton j)) (hr.div hp) measurable_const).add
    (measurable_const.div hp)

end ProtocolRun

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit


/-- The unconditional bound on the second moment used in Lemma C.3. -/
theorem integral_secondMoment_le {K T : ℕ} {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P (calibeatPolicy K η μ)) {t : ℕ} (ht : t < T) :
    ∫ ω, (∑ j, run.algX η μ t ω j * run.algV η μ t ω j ^ 2) ∂P ≤ 2 * K / (1 - μ) := by
  obtain ⟨heq, hbound, hsum⟩ := eq_C_6 hK hη hμ₀ hμ hKη P run t ht
  rw [← integral_condExp (m := run.preDraw t) (run.preDraw_le_ambient ht)]
  calc
    _ ≤ ∫ _ : Ω, (2 * (K : ℝ) / (1 - μ)) ∂P := by
      refine integral_mono_ae integrable_condExp (integrable_const _) ?_
      filter_upwards [heq] with ω hω
      rw [hω]
      exact (hbound ω).trans (hsum ω)
    _ = _ := by simp

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

/-- Both groups of internal learners compete with every fixed post-processing rule. -/
theorem internal_potential_bound {K : ℕ} (η μ : ℝ) (hη : 0 < η)
    (J I : ℕ → Fin K) (r : ℕ → ℝ) (T : ℕ) (f : Fin K → Fin K) :
    (∑ t ∈ Finset.range T, ∑ i, algX η μ J I r t i * algV η μ J I r t (f i)) ≤
      K * Real.log K / η + ∑ t ∈ Finset.range T, algHSR η μ J I r t ∧
    (∑ t ∈ Finset.range T, algV η μ J I r t (f (J t))) ≤
      K * Real.log K / η + ∑ t ∈ Finset.range T, algHRec η μ J I r t := by
  let x := algX η μ J I r
  let v := algV η μ J I r
  have bound (g : ℕ → Fin K → Fin K → ℝ) :
      (∑ t ∈ Finset.range T, ∑ i, g t i (f i)) ≤
        K * Real.log K / η +
          1 / η * ∑ i, logPartition η (fun j => ∑ t ∈ Finset.range T, g t i j) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i, (logPartition η (fun j => ∑ t ∈ Finset.range T, g t i j) + Real.log K) / η :=
        Finset.sum_le_sum fun i _ => gain_le_logPartition (f i) hη _
      _ = _ := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  obtain ⟨hSR, hRec⟩ := eq_C_1 η μ hη J I r T
  constructor
  · rw [hSR]
    exact bound fun t i j => x t i * v t j
  · rw [hRec]
    have h := bound (fun t i j => if J t = i then v t j else 0)
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true, v, logPartition] using h

/-- The master learner incurs at most \(\log(2)/\eta\) regret relative to either
feedback stream when its gain is measured by the log of the weighted exponential sum. -/
theorem mixing_potential_bound {K : ℕ} (η μ : ℝ) (hη : 0 < η)
    (J I : ℕ → Fin K) (r : ℕ → ℝ) (T : ℕ) :
    let S := algState η μ J I r
    let H := fun t => ![algHSR η μ J I r t, algHRec η μ J I r t]
    ∀ i : Fin 2, (∑ t ∈ Finset.range T, H t i) ≤ Real.log 2 / η +
      ∑ t ∈ Finset.range T, (1 / η) * Real.log
        ((S t).lam η * Real.exp (η * H t 0) + (1 - (S t).lam η) * Real.exp (η * H t 1)) := by
  intro S H i
  let G (t : ℕ) : Fin 2 → ℝ := ![(S t).cumHSR, (S t).cumHRec]
  have hzero : G 0 = 0 := by ext k; fin_cases k <;> rfl
  have hsucc (t : ℕ) : G (t + 1) = G t + H t := by
    ext k
    fin_cases k <;> rfl
  have hG (t : ℕ) : G t i = ∑ s ∈ Finset.range t, H s i := by
    induction t with
    | zero => simp [hzero]
    | succ t ih => simp [Finset.sum_range_succ, hsucc, ih]
  have hweights (t : ℕ) : FewExperts.hedgeWeights η (G t) 1 = 1 - (S t).lam η := by
    have hpos : 0 < Real.exp (η * G t 0) + Real.exp (η * G t 1) := by positivity
    change FewExperts.hedgeWeights η (G t) 1 = 1 - FewExperts.hedgeWeights η (G t) 0
    simp only [FewExperts.hedgeWeights, Fin.sum_univ_two]
    field_simp [hpos.ne']
    ring
  let L (t : ℕ) := Real.log ((S t).lam η * Real.exp (η * H t 0) +
    (1 - (S t).lam η) * Real.exp (η * H t 1))
  have hstep (t : ℕ) : L t = logPartition η (G (t + 1)) - logPartition η (G t) := by
    have h := logPartition_step (0 : Fin 2) η (G t) (H t)
    rw [hsucc t]
    change L t = logPartition η (fun j => G t j + H t j) - _
    simpa only [L, Fin.sum_univ_two, hweights, show ∀ t, FewExperts.hedgeWeights η (G t) 0 =
      (S t).lam η from fun _ => rfl] using h
  have htel (t : ℕ) : ∑ s ∈ Finset.range t, L s = logPartition η (G t) := by
    induction t with
    | zero => simp [logPartition, hzero]
    | succ t ih => rw [Finset.sum_range_succ, ih, hstep]; ring
  rw [← hG, ← Finset.mul_sum, htel]
  have hbound := gain_le_logPartition i hη (G T)
  linarith only [hbound, show (logPartition η (G T) + Real.log 2) / η =
      Real.log 2 / η + 1 / η * logPartition η (G T) by ring]

end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- The corrected-reward comparison along a fixed history, before averaging
the round-by-round second moments. -/
theorem corrected_regret_pathwise {K T : ℕ} (η μ : ℝ) (hη : 0 < η)
    (J I : ℕ → Fin K) (r : ℕ → ℝ) (f : Fin K → Fin K)
    (hrange : ∀ t < T, ∀ j, 0 ≤ η * algV η μ J I r t j ∧ η * algV η μ J I r t j ≤ 1) :
    let x := algX η μ J I r
    let v := algV η μ J I r
    let B := (K * Real.log K + Real.log 2) / η +
      (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t j * v t j ^ 2
    (∑ t ∈ Finset.range T, ((∑ j, x t j * v t (f j)) - x t ⬝ᵥ v t)) ≤ B ∧
    (∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t)) ≤ B := by
  intro x v B
  let S := algState η μ J I r
  let H := fun t => ![algHSR η μ J I r t, algHRec η μ J I r t]
  let L (t : ℕ) := (1 / η) * Real.log ((S t).lam η * Real.exp (η * H t 0) +
    (1 - (S t).lam η) * Real.exp (η * H t 1))
  have hmix (t : ℕ) (ht : t < T) :
      L t - x t ⬝ᵥ v t ≤ (Real.exp 1 - 2) * η * ∑ j, x t j * v t j ^ 2 := by
    have hx := (S t).roundX_spec η (J t)
    have hlam := (S t).lam_mem η
    have hh := eq_C_3 η ((S t).lam η) hη hlam.1.le hlam.2.le ((S t).matSR η)
      ((S t).matRec η) ((S t).matSR_stochastic η (J t)) ((S t).matRec_stochastic η (J t))
      (J t) (x t) (v t) hx.1 hx.2
    have hle := hh.1.trans_eq hh.2
    have hp : 0 < (S t).lam η * Real.exp (η * H t 0) +
        (1 - (S t).lam η) * Real.exp (η * H t 1) :=
      add_pos (mul_pos hlam.1 (Real.exp_pos _))
        (mul_pos (sub_pos.mpr hlam.2) (Real.exp_pos _))
    have hlog := Real.log_le_log hp hle
    have hfirst := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 / η by positivity)
    have htail := eq_C_5 η hη (x t) (v t) hx.1 (hrange t ht)
    exact (sub_le_sub_right hfirst _).trans (htail.1.trans htail.2)
  have hsum : ∑ t ∈ Finset.range T, (L t - x t ⬝ᵥ v t) ≤
      (Real.exp 1 - 2) * η * ∑ t ∈ Finset.range T, ∑ j, x t j * v t j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hmix t (Finset.mem_range.mp ht)
  have hmaster (i : Fin 2) : (∑ t ∈ Finset.range T, H t i) ≤ Real.log 2 / η +
      ∑ t ∈ Finset.range T, L t :=
    mixing_potential_bound η μ hη J I r T i
  obtain ⟨hsr, hrec⟩ := internal_potential_bound η μ hη J I r T f
  rw [Finset.sum_sub_distrib] at hsum
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := hmaster 0
    change (∑ t ∈ Finset.range T, algHSR η μ J I r t) ≤ _ at h
    dsimp [B]
    rw [add_div]
    linarith only [hsr, h, hsum]
  · rw [Finset.sum_sub_distrib]
    have h := hmaster 1
    change (∑ t ∈ Finset.range T, algHRec η μ J I r t) ≤ _ at h
    dsimp [B]
    rw [add_div]
    linarith only [hrec, h, hsum]

/-- Lemma C.3 in the submitted paper, for the swap and recommendation benchmarks. -/
theorem lemma_C_3 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η)
    (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (∑ i, run.algX η μ t ω i * run.algV η μ t ω (f i) -
          run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.algV η μ t ω (f (run.J t ω)) -
          run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) := by
  let Q (t : ℕ) (ω : Ω) := ∑ j, run.algX η μ t ω j * run.algV η μ t ω j ^ 2
  let C := (K * Real.log K + Real.log 2) / η
  let d := (Real.exp 1 - 2) * η
  let U : ℝ := 2 * K / (1 - μ)
  let B (ω : Ω) := C + d * ∑ t ∈ Finset.range T, Q t ω
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hQint (t : ℕ) (ht : t < T) : Integrable (Q t) P := by
    have hm := run.info_le _ (Nat.succ_le_of_lt ht)
    apply integrable_finsetSum
    intro j _
    have hx := ((measurable_pi_apply j).comp (run.algX_measurable η μ ht)).mono
      (run.preDraw_le_ambient ht) le_rfl
    have hv := (run.algV_measurable η μ ht j).mono hm le_rfl
    refine (integrable_const ((1 / η) ^ 2 : ℝ)).mono'
      (hx.mul (hv.pow_const 2)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have hx₀ := (run.algX_prob η μ t ω).1 j
    have hx₁ := (Finset.single_le_sum (fun k _ => (run.algX_prob η μ t ω).1 k)
      (Finset.mem_univ j)).trans_eq (run.algX_prob η μ t ω).2
    obtain ⟨hv₀, hv₁⟩ := run.algV_scaled_mem hK hη hμ hKη ht ω j
    have hv₀' : 0 ≤ run.algV η μ t ω j := nonneg_of_mul_nonneg_right hv₀ hη
    have hv₁' : run.algV η μ t ω j ≤ 1 / η := (le_div_iff₀ hη).mpr (by linarith only [hv₁])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx₀ (sq_nonneg _))]
    exact (mul_le_of_le_one_left (sq_nonneg _) hx₁).trans (pow_le_pow_left₀ hv₀' hv₁' 2)
  have hBint : Integrable B P :=
    (integrable_const C).add ((integrable_finsetSum _ fun t ht =>
      hQint t (Finset.mem_range.mp ht)).const_mul d)
  have hB : ∫ ω, B ω ∂P ≤ C + d * U * T := by
    unfold B
    rw [integral_add (integrable_const C) ((integrable_finsetSum _ fun t ht =>
      hQint t (Finset.mem_range.mp ht)).const_mul d), integral_const_mul, integral_finsetSum _
      (fun t ht => hQint t (Finset.mem_range.mp ht))]
    rw [show (∫ _ : Ω, C ∂P) = C by simp]
    have hs : ∑ t ∈ Finset.range T, ∫ ω, Q t ω ∂P ≤ (T : ℝ) * U := by
      calc
        _ ≤ ∑ _ ∈ Finset.range T, U := Finset.sum_le_sum fun t ht =>
          integral_secondMoment_le hK hη hμ₀ hμ hKη P run (Finset.mem_range.mp ht)
        _ = _ := by simp
    nlinarith only [mul_le_mul_of_nonneg_left hs hd]
  have integrate (F : Ω → ℝ) (hi : Integrable F P) (hF : ∀ ω, F ω ≤ B ω) :
      ∫ ω, F ω ∂P ≤ C + d * U * T := by
    exact (integral_mono hi hBint hF).trans hB
  let x (t : ℕ) (j : Fin K) (ω : Ω) := run.algX η μ t ω j
  let v (t : ℕ) (j : Fin K) (ω : Ω) := run.algV η μ t ω j
  have hx (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (x t j) :=
    ((measurable_pi_apply j).comp (run.algX_measurable η μ ht)).mono (run.preDraw_le_ambient ht) le_rfl
  have hv (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (v t j) :=
    (run.algV_measurable η μ ht j).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
  have hvb (t : ℕ) (ht : t < T) (j : Fin K) (ω : Ω) : v t j ω ∈ Set.Icc (0 : ℝ) (1 / η) := by
    obtain ⟨h₀, h₁⟩ := run.algV_scaled_mem hK hη hμ hKη ht ω j
    exact ⟨nonneg_of_mul_nonneg_right h₀ hη, (le_div_iff₀ hη).mpr (by linarith only [h₁])⟩
  have weighted (t : ℕ) (ht : t < T) (ω : Ω) (f : Fin K → Fin K) :
      (∑ j, x t j ω * v t (f j) ω) ∈ Set.Icc (0 : ℝ) (1 / η) := by
    have hp := run.algX_prob η μ t ω
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hp.1 j) (hvb t ht (f j) ω).1, ?_⟩
    calc
      _ ≤ ∑ j, x t j ω * (1 / η) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hvb t ht (f j) ω).2 (hp.1 j)
      _ = _ := by rw [← Finset.sum_mul, show (∑ j, x t j ω) = 1 from hp.2, one_mul]
  have integrable_max (g : ℕ → (Fin K → Fin K) → Ω → ℝ)
      (hm : ∀ t < T, ∀ f, Measurable (g t f))
      (hb : ∀ t < T, ∀ f ω, g t f ω ∈ Set.Icc (0 : ℝ) (1 / η)) :
      Integrable (fun ω => Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
        (fun f : Fin K → Fin K => ∑ t ∈ Finset.range T,
          (g t f ω - run.algX η μ t ω ⬝ᵥ run.algV η μ t ω))) P := by
    let F (f : Fin K → Fin K) (ω : Ω) :=
      ∑ t ∈ Finset.range T, (g t f ω - ∑ j, x t j ω * v t j ω)
    have hF (f : Fin K → Fin K) : Measurable (F f) := Finset.measurable_sum _ fun t ht =>
      (hm t (Finset.mem_range.mp ht) f).sub (Finset.measurable_sum _ fun j _ =>
        (hx t (Finset.mem_range.mp ht) j).mul (hv t (Finset.mem_range.mp ht) j))
    have hbF (f : Fin K → Fin K) (ω : Ω) : |F f ω| ≤ T * (1 / η) := by
      calc
        _ ≤ ∑ t ∈ Finset.range T, |g t f ω - ∑ j, x t j ω * v t j ω| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, 1 / η := Finset.sum_le_sum fun t ht => by
          have h₁ := hb t (Finset.mem_range.mp ht) f ω
          have h₂ := weighted t (Finset.mem_range.mp ht) ω id
          apply abs_le.mpr
          change (∑ j, x t j ω * v t j ω) ∈ Set.Icc (0 : ℝ) (1 / η) at h₂
          exact ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩
        _ = _ := by simp
    let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
    have hmax : Measurable (fun ω => Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => F f ω)) := by
      simp_rw [Finset.sup'_univ_eq_ciSup]
      exact Measurable.iSup hF
    refine (integrable_const ((T : ℝ) * (1 / η))).mono' hmax.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    change ‖Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => F f ω)‖ ≤ _
    obtain ⟨f, _, heq⟩ := Finset.exists_mem_eq_sup' ⟨id, Finset.mem_univ _⟩ (fun f => F f ω)
    rw [Real.norm_eq_abs, heq]
    exact hbF f ω
  have path (ω : Ω) (f : Fin K → Fin K) :=
    corrected_regret_pathwise η μ hη (fun t => run.J t ω) (fun t => run.I t ω)
      (fun t => run.obs t ω) f (fun t ht j => run.algV_scaled_mem hK hη hμ hKη ht ω j)
  have hfinal : C + d * U * T =
      (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) := by
    dsimp [C, d, U]
    ring
  rw [← hfinal]
  constructor
  · refine integrate _ (integrable_max (fun t f ω => ∑ j, x t j ω * v t (f j) ω) ?_ ?_) ?_
    · intro t ht f
      exact Finset.measurable_sum _ fun j _ => (hx t ht j).mul (hv t ht (f j))
    · intro t ht f ω
      exact weighted t ht ω f
    · intro ω
      exact Finset.sup'_le _ _ fun f _ => (path ω f).1
  · refine integrate _ (integrable_max (fun t f ω => v t (f (run.J t ω)) ω) ?_ ?_) ?_
    · intro t ht f
      exact measurable_select ((run.J_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl)
        (fun j => hv t ht (f j))
    · intro t ht f ω
      exact hvb t ht (f (run.J t ω)) ω
    · intro ω
      exact Finset.sup'_le _ _ fun f _ => (path ω f).2

end CalibeatBandit

end

open CalibeatBandit MeasureTheory Matrix

set_option autoImplicit false

theorem solution {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (∑ i, run.algX η μ t ω i * run.algV η μ t ω (f i) - run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.algV η μ t ω (f (run.J t ω)) - run.algX η μ t ω ⬝ᵥ run.algV η μ t ω)) ∂P
      ≤ (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ) := CalibeatBandit.lemma_C_3 hK hη hμ0 hμ hKη P run
