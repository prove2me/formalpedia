-- Prove2me | solution 1 for CalibeatBandit.Supplement.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-23T00:36:47.912403+00:00
-- url     : https://prove2.me/submissions/715a51c7-951f-49b5-87b7-fe1403b2ad86

import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_Supplement_robustPolicy
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Definitions.Def_CalibeatBandit_etaStar
import Definitions.Def_CalibeatBandit_rT
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_CalibeatBandit_IsCalibeating
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_CalibeatBandit_Supplement_IsRobust

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

/-- Equation (3.1) has a solution throughout the closed range of mixing weights.
At weight one, take a limit of solutions with weights strictly below one. -/
theorem eq_3_1_solvable {K : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) :
    ∃ p : Fin K → ℝ, IsProbVec p ∧
      (1 - lam • MSR) *ᵥ p = (1 - lam) • (MRec *ᵥ Pi.single J 1) := by
  rcases lt_or_eq_of_le hlam1 with hlt | rfl
  · exact ⟨_, fixedPointSol_spec lam hlam0 hlt MSR MRec hSR hRec J⟩
  let a (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)
  let p (n : ℕ) := fixedPointSol (a n) MSR MRec J
  have ha₀ (n : ℕ) : 0 ≤ a n := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have ha₁ (n : ℕ) : a n < 1 := sub_lt_self _ (by positivity)
  have ha : Tendsto a atTop (𝓝 1) := by
    simpa only [sub_zero, a] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hp (n : ℕ) := fixedPointSol_spec (a n) (ha₀ n) (ha₁ n) MSR MRec hSR hRec J
  obtain ⟨q, hq, φ, hφ, hlim⟩ := (isCompact_stdSimplex ℝ (Fin K)).tendsto_subseq
    (x := p) (fun n => (hp n).1)
  refine ⟨q, hq, ?_⟩
  ext i
  have hq_i := tendsto_pi_nhds.mp hlim i
  have hM_i : Tendsto (fun n => (MSR *ᵥ p (φ n)) i) atTop (𝓝 ((MSR *ᵥ q) i)) := by
    apply (Continuous.tendsto _ q).comp hlim
    change Continuous (fun v : Fin K → ℝ => ∑ j, MSR i j * v j)
    fun_prop
  have hleft := hq_i.sub ((ha.comp hφ.tendsto_atTop).mul hM_i)
  have hright := ((tendsto_const_nhds (x := (1 : ℝ))).sub (ha.comp hφ.tendsto_atTop)).mul
    (tendsto_const_nhds (x := (MRec *ᵥ Pi.single J (1 : ℝ)) i))
  have hstep (n : ℕ) : p (φ n) i - a (φ n) * (MSR *ᵥ p (φ n)) i =
      (1 - a (φ n)) * (MRec *ᵥ Pi.single J (1 : ℝ)) i := by
    have h := congrFun (hp (φ n)).2 i
    simpa only [sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hfinal := tendsto_nhds_unique hleft (hright.congr (fun n => (hstep n).symm))
  simpa only [sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hfinal

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
    0 ≤ η * run.algV η μ t ω j ∧ η * run.algV η μ t ω j ≤ 1 :=
  estimate_scaled_mem hK hη hμ hKη (run.algX η μ t ω) (run.algX_prob η μ t ω)
    (run.I t ω) j (run.obs t ω) (run.y_mem t ht ω (run.I t ω))

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

namespace CalibeatBandit

open MeasureTheory

/-- The part of a bandit interaction needed to analyze a single draw per round.
The recommendation may have any label type and is included in the pre-draw
information. -/
structure DrawRun (K T : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  info : ℕ → MeasurableSpace Ω
  preDraw : ℕ → MeasurableSpace Ω
  y : ℕ → Ω → Fin K → ℝ
  I : ℕ → Ω → Fin K
  played : ℕ → Ω → Fin K → ℝ
  info_le : ∀ t ≤ T, info t ≤ mΩ
  info_le_preDraw : ∀ t < T, info t ≤ preDraw t
  preDraw_le_succ : ∀ t < T, preDraw t ≤ info (t + 1)
  y_measurable : ∀ t < T, Measurable[preDraw t] (y t)
  I_measurable : ∀ t < T, Measurable[info (t + 1)] (I t)
  y_mem : ∀ t < T, ∀ ω i, y t ω i ∈ Set.Icc (0 : ℝ) 1
  I_law : ∀ t < T, ∀ i : Fin K,
    condExp (preDraw t) P ((I t ⁻¹' {i}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      fun ω => played t ω i

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def obs (run : DrawRun K T P) (t : ℕ) (ω : Ω) : ℝ :=
  run.y t ω (run.I t ω)

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

def ProtocolRun.toDrawRun {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : Policy K} (run : ProtocolRun K T P policy) : DrawRun K T P where
  info := run.info
  preDraw := run.preDraw
  y := run.y
  I := run.I
  played := run.played
  info_le := run.info_le
  info_le_preDraw := fun _ _ => le_sup_left
  preDraw_le_succ := fun _ ht => run.preDraw_le_succ ht
  y_measurable := fun t ht => (run.y_measurable t ht).mono le_sup_left le_rfl
  I_measurable := run.I_measurable
  y_mem := run.y_mem
  I_law := run.I_law

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory

/-- The recommendation is already available when the learner draws its action. -/
abbrev QProtocolRun.preDraw {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (t : ℕ) : MeasurableSpace Ω :=
  run.info t ⊔ MeasurableSpace.comap (run.J t) inferInstance

/-- Use the learner draw in the protocol with explicitly observed mixed recommendations. -/
def QProtocolRun.toDrawRun {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy) :
    DrawRun K T P where
  info := run.info
  preDraw := run.preDraw
  y := run.y
  I := run.I
  played t ω := policy t (fun s => run.q s ω) (fun s => run.J s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω))
  info_le := run.info_le
  info_le_preDraw := fun _ _ => le_sup_left
  preDraw_le_succ := fun t ht => sup_le (run.info_mono t ht) (run.J_measurable t ht).comap_le
  y_measurable := fun t ht => (run.y_measurable t ht).mono le_sup_left le_rfl
  I_measurable := run.I_measurable
  y_mem := run.y_mem
  I_law := run.I_law

theorem robustHhat_congr_prefix {K T s : ℕ} {ζ : ℝ}
    {q q' : ℕ → Fin K → ℝ} {I I' : ℕ → Fin K} {r r' : ℕ → ℝ}
    (hq : ∀ v < s, q v = q' v) (hI : ∀ v < s, I v = I' v)
    (hr : ∀ v < s, r v = r' v) :
    robustHhat T ζ q I r s = robustHhat T ζ q' I' r' s := by
  unfold robustHhat
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  unfold robustGhat
  apply Finset.sum_congr rfl
  intro v hv
  have hv' := Finset.mem_range.mp hv
  rw [hq v hv', hI v hv', hr v hv']

private theorem robustCrossed_extend_iff {K T t s : ℕ} {ζ : ℝ} (hs : s ≤ t)
    (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K) (r : ℕ → ℝ) (d : Fin K) :
    robustCrossed T ζ (extendFin 0 (fun v : Fin (t + 1) => q v))
      (extendFin d (fun v : Fin t => I v)) (extendFin 0 (fun v : Fin t => r v)) s
      ↔ robustCrossed T ζ q I r s := by
  unfold robustCrossed
  rw [robustHhat_congr_prefix (q' := q) (I' := I) (r' := r)
    (fun v hv => by simp [extendFin, show v < t + 1 by omega])
    (fun v hv => by simp [extendFin, hv.trans_le hs])
    (fun v hv => by simp [extendFin, hv.trans_le hs])]

/-- Until the first crossing, the learner follows the current recommendation with
probability one minus the exploration rate and otherwise samples uniformly. -/
theorem robustPolicy_eq_follow {K T : ℕ} (ζ : ℝ) (t : ℕ)
    (q : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ)
    (h : ∀ u < t, ¬ robustCrossed T ζ q I r (u + 1)) :
    robustPolicy K T ζ t (fun v => q v) (fun v => J v) (fun v => I v) (fun v => r v) =
      fun i => (1 - robustEps T ζ) * (if J t = i then 1 else 0) + robustEps T ζ / K := by
  classical
  unfold robustPolicy
  dsimp only
  rw [dif_neg]
  · rfl
  · rintro ⟨u, hu, hcross⟩
    exact h u hu ((robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mp hcross)

private theorem calibeatPolicy_congr_prefix {K t : ℕ} (η μ : ℝ)
    {J J' I I' : ℕ → Fin K} {r r' : ℕ → ℝ}
    (hJ : ∀ v ≤ t, J v = J' v) (hI : ∀ v < t, I v = I' v)
    (hr : ∀ v < t, r v = r' v) :
    calibeatPolicy K η μ t J I r = calibeatPolicy K η μ t J' I' r' := by
  have hs (v : ℕ) (hv : v ≤ t) : algState η μ J I r v = algState η μ J' I' r' v := by
    induction v with
    | zero => rfl
    | succ v ih =>
      have hlt := Nat.lt_of_succ_le hv
      simp only [algState, ih hlt.le, hJ v hlt.le, hI v hlt, hr v hlt]
  simp only [calibeatPolicy, algP, algX, hs t le_rfl, hJ t le_rfl]

/-- Once a test has crossed the threshold, the policy uses a fresh copy of
calibeating on the history after the crossing round. -/
theorem robustPolicy_eq_restart {K T : ℕ} (ζ : ℝ) {t u : ℕ}
    (q : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (hu : u < t)
    (hc : robustCrossed T ζ q I r (u + 1))
    (hfirst : ∀ v < u, ¬ robustCrossed T ζ q I r (v + 1)) :
    robustPolicy K T ζ t (fun v => q v) (fun v => J v) (fun v => I v) (fun v => r v) =
      calibeatPolicy K (etaStar K T) (muStar K T) (t - (u + 1))
        (fun v => J (u + 1 + v)) (fun v => I (u + 1 + v)) (fun v => r (u + 1 + v)) := by
  classical
  let Q := extendFin 0 (fun v : Fin (t + 1) => q v)
  let A := extendFin (J 0) (fun v : Fin t => I v)
  let R := extendFin 0 (fun v : Fin t => r v)
  have he : ∃ v, v < t ∧ robustCrossed T ζ Q A R (v + 1) :=
    ⟨u, hu, (robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mpr hc⟩
  have hfind : Nat.find he = u := by
    apply le_antisymm (Nat.find_min' he ⟨hu,
      (robustCrossed_extend_iff (Nat.succ_le_of_lt hu) q I r (J 0)).mpr hc⟩)
    apply le_of_not_gt
    intro hlt
    have hf := Nat.find_spec he
    exact hfirst _ hlt ((robustCrossed_extend_iff (Nat.succ_le_of_lt hf.1) q I r (J 0)).mp hf.2)
  dsimp only [Q, A, R] at he hfind
  unfold robustPolicy
  dsimp only
  split
  · rename_i hyes
    have hfind' : Nat.find hyes = u := hfind
    rw [hfind']
    apply calibeatPolicy_congr_prefix
    · intro v hv
      simp [extendFin, show u + 1 + v < t + 1 by omega]
    · intro v hv
      simp [extendFin, show u + 1 + v < t by omega]
    · intro v hv
      simp [extendFin, show u + 1 + v < t by omega]
  · rename_i hno
    exact (hno he).elim

/-- During the follow phase, each disagreement with the recommendation
can cost at most two units of swap regret and one unit of reward loss. -/
theorem regret_le_of_disagreements {K T : ℕ} (y : ℕ → Fin K → ℝ)
    (I J : ℕ → Fin K) (hy : ∀ t < T, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1) :
    let D : ℝ := ∑ t ∈ Finset.range T, if I t = J t then 0 else 1
    swapRegret T y I ≤ swapRegret T y J + 2 * D ∧
      rewardLoss T y J I ≤ swapRegret T y J + D := by
  classical
  intro D
  have hbase (f : Fin K → Fin K) :
      ∑ t ∈ Finset.range T, (y t (f (J t)) - y t (J t)) ≤ swapRegret T y J := by
    unfold swapRegret
    exact Finset.le_sup' (fun σ : Fin K → Fin K =>
      ∑ t ∈ Finset.range T, (y t (σ (J t)) - y t (J t))) (Finset.mem_univ f)
  constructor
  · unfold swapRegret
    apply Finset.sup'_le
    intro f _
    have h := Finset.sum_le_sum (s := Finset.range T) (fun t ht => show
        y t (f (I t)) - y t (I t) ≤ y t (f (J t)) - y t (J t) +
          2 * (if I t = J t then 0 else 1) by
      by_cases he : I t = J t
      · simp [he]
      · have ht' := Finset.mem_range.mp ht
        simp only [he, if_false, mul_one]
        linarith [(hy t ht' (f (I t))).2, (hy t ht' (I t)).1,
          (hy t ht' (f (J t))).1, (hy t ht' (J t)).2])
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    exact h.trans (add_le_add (hbase f) le_rfl)
  · unfold rewardLoss
    apply Finset.sup'_le
    intro f _
    have h := Finset.sum_le_sum (s := Finset.range T) (fun t ht => show
        y t (f (J t)) - y t (I t) ≤ y t (f (J t)) - y t (J t) +
          (if I t = J t then 0 else 1) by
      by_cases he : I t = J t
      · simp [he]
      · have ht' := Finset.mem_range.mp ht
        simp only [he, if_false]
        linarith [(hy t ht' (I t)).1, (hy t ht' (J t)).2])
    rw [Finset.sum_add_distrib] at h
    exact h.trans (add_le_add (hbase f) le_rfl)

/-- On the event where the recommendation and the two estimation errors
satisfy their prefix bounds, the switching test never fires. -/
theorem robust_never_crosses {K T : ℕ} (ζ : ℝ)
    (q y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ)
    (hRec : ∀ s, 1 ≤ s → s ≤ T → swapRegret s y J ≤ s * robustC K T ζ s)
    (hRealized : ∀ s, 1 ≤ s → s ≤ T →
      pseudoSwapRegret s q y ≤ swapRegret s y J + s * robustC K T ζ s)
    (hEstimate : ∀ u < T, (∀ v < u, ¬ robustCrossed T ζ q I r (v + 1)) →
      robustHhat T ζ q I r (u + 1) ≤
        pseudoSwapRegret (u + 1) q y + (u + 1 : ℕ) * robustC K T ζ (u + 1)) :
    ∀ u < T, ¬ robustCrossed T ζ q I r (u + 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hc
    have hfirst : ∀ v < u, ¬ robustCrossed T ζ q I r (v + 1) :=
      fun v hv => ih v hv (hv.trans hu)
    have h₁ := hEstimate u hu hfirst
    have h₂ := hRealized (u + 1) (by omega) (by omega)
    have h₃ := hRec (u + 1) (by omega) (by omega)
    unfold robustCrossed at hc
    push_cast at h₁ h₂ h₃ hc
    linarith

end CalibeatBandit.Supplement

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

/-- The realized and pseudo recommendation losses have the same expectation. -/
theorem rec_identity_C_1 {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (policy : Policy K) (run : ProtocolRun K T P policy) :
    ∫ ω, pseudoRewardLoss T (fun t => run.played t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P
      = ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        - ∑ t ∈ Finset.range T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P ∧
    ∀ t < T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P = 0 := by
  classical
  let D (t : ℕ) (ω : Ω) := run.played t ω ⬝ᵥ run.y t ω - run.obs t ω
  have hd (t : ℕ) (ht : t < T) : Integrable (D t) P ∧ ∫ ω, D t ω ∂P = 0 := by
    obtain ⟨hi, heq⟩ := run.toDrawRun.condExp_obs P ht
    change Integrable (run.obs t) P at hi
    change condExp (run.preDraw t) P (run.obs t) =ᵐ[P]
      (fun ω => run.played t ω ⬝ᵥ run.y t ω) at heq
    have hp : Integrable (fun ω => run.played t ω ⬝ᵥ run.y t ω) P := integrable_condExp.congr heq
    refine ⟨hp.sub hi, ?_⟩
    unfold D
    rw [integral_sub hp hi, ← integral_congr_ae heq, integral_condExp (run.preDraw_le_ambient ht), sub_self]
  let M (ω : Ω) := rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)
  have heq (ω : Ω) :
      pseudoRewardLoss T (fun t => run.played t ω) (fun t => run.y t ω) (fun t => run.J t ω) =
        M ω - ∑ t ∈ Finset.range T, D t ω := by
    let fval (f : Fin K → Fin K) := ∑ t ∈ Finset.range T,
      (run.y t ω (f (run.J t ω)) - run.obs t ω)
    have hterm (f : Fin K → Fin K) :
        ∑ t ∈ Finset.range T, (run.y t ω (f (run.J t ω)) - run.played t ω ⬝ᵥ run.y t ω) =
          fval f - ∑ t ∈ Finset.range T, D t ω := by
      simp only [fval, D, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    unfold pseudoRewardLoss
    change Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ _ =
      Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ fval - _
    apply le_antisymm
    · apply Finset.sup'_le
      intro f hf
      rw [hterm]
      exact sub_le_sub_right (Finset.le_sup' fval hf) _
    · obtain ⟨f, hf, hfval⟩ := Finset.exists_mem_eq_sup' ⟨id, Finset.mem_univ _⟩ fval
      rw [hfval, ← hterm]
      exact Finset.le_sup' (fun f : Fin K → Fin K => ∑ t ∈ Finset.range T,
        (run.y t ω (f (run.J t ω)) - run.played t ω ⬝ᵥ run.y t ω)) hf
  have hterm_meas (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      Measurable (fun ω => run.y t ω (f (run.J t ω))) := by
    have hm := run.info_le _ (Nat.succ_le_of_lt ht)
    exact measurable_select ((run.J_measurable t ht).mono hm le_rfl) fun j =>
      (measurable_pi_apply (f j)).comp
        ((run.y_measurable t ht).mono ((run.info_mono t ht).trans hm) le_rfl)
  let g (f : Fin K → Fin K) (ω : Ω) := ∑ t ∈ Finset.range T,
    (run.y t ω (f (run.J t ω)) - run.obs t ω)
  have gm (f : Fin K → Fin K) : Measurable (g f) := by
    apply Finset.measurable_sum
    intro t ht
    have h := Finset.mem_range.mp ht
    have hm := run.info_le _ (Nat.succ_le_of_lt h)
    have obs : Measurable (run.obs t) := by
      exact measurable_select ((run.I_measurable t h).mono hm le_rfl) fun j =>
        (measurable_pi_apply j).comp
          ((run.y_measurable t h).mono ((run.info_mono t h).trans hm) le_rfl)
    exact (hterm_meas t h f).sub obs
  have hM : Integrable M P := by
    let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
    have hmeas : Measurable M := by
      change Measurable (fun ω => Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => g f ω))
      simp_rw [Finset.sup'_univ_eq_ciSup]
      exact Measurable.iSup gm
    refine (integrable_const (T : ℝ)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    change ‖Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => g f ω)‖ ≤ _
    obtain ⟨f, _, he⟩ := Finset.exists_mem_eq_sup' ⟨id, Finset.mem_univ _⟩ (fun f => g f ω)
    rw [Real.norm_eq_abs, he]
    calc
      _ ≤ ∑ t ∈ Finset.range T, |run.y t ω (f (run.J t ω)) - run.obs t ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have h₁ := run.y_mem t (Finset.mem_range.mp ht) ω (f (run.J t ω))
        have h₂ : run.obs t ω ∈ Set.Icc (0 : ℝ) 1 :=
          run.y_mem t (Finset.mem_range.mp ht) ω (run.I t ω)
        exact abs_le.mpr ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩
      _ = _ := by simp
  refine ⟨?_, fun t ht => (hd t ht).2⟩
  rw [show (fun ω => pseudoRewardLoss T (fun t => run.played t ω) (fun t => run.y t ω) (fun t => run.J t ω)) =
    (fun ω => M ω - ∑ t ∈ Finset.range T, D t ω) from funext heq]
  rw [integral_sub hM (integrable_finsetSum _ fun t ht => (hd t (Finset.mem_range.mp ht)).1),
    integral_finsetSum _ fun t ht => (hd t (Finset.mem_range.mp ht)).1]
  rfl

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Filter

namespace CalibeatBandit.Supplement.QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- The rounds strictly before `t` have all passed the switching test. -/
def robustFollowing (t : ℕ) : Set Ω :=
  {ω | ∀ u < t, ¬ robustCrossed T ζ (fun s => run.q s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1)}

theorem measurable_robustHhat {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    Measurable[run.info t] (fun ω => robustHhat T ζ (fun u => run.q u ω)
      (fun u => run.I u ω) (fun u => run.y u ω (run.I u ω)) s) := by
  let q := run.q
  let I := run.I
  let r := run.toDrawRun.obs
  have past {u : ℕ} (hu : u < s) : run.info (u + 1) ≤ run.info t :=
    run.toDrawRun.info_le_info ((Nat.succ_le_of_lt hu).trans hst) ht
  have mq (u : ℕ) (hu : u < s) : Measurable[run.info t] (q u) :=
    (run.q_measurable u (hu.trans_le (hst.trans ht))).mono
      ((run.info_mono u (hu.trans_le (hst.trans ht))).trans (past hu)) le_rfl
  have mI (u : ℕ) (hu : u < s) : Measurable[run.info t] (I u) :=
    (run.I_measurable u (hu.trans_le (hst.trans ht))).mono (past hu) le_rfl
  have mr (u : ℕ) (hu : u < s) : Measurable[run.info t] (r u) :=
    (run.toDrawRun.obs_measurable (hu.trans_le (hst.trans ht))).mono (past hu) le_rfl
  change Measurable[run.info t] (fun ω => robustHhat T ζ (fun u => q u ω)
      (fun u => I u ω) (fun u => r u ω) s)
  classical
  let : MeasurableSpace Ω := run.info t
  unfold robustHhat robustGhat
  refine Finset.measurable_sum _ (fun i _ => Measurable.iSup fun j => ?_)
  refine Finset.measurable_sum _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  have hq (k : Fin K) : Measurable (fun ω => q u ω k) := (measurable_pi_apply k).comp (mq u hu')
  have hy (k : Fin K) :
      Measurable (fun ω => robustYhat (followMix (robustEps T ζ) (q u ω)) (I u ω) (r u ω) k) := by
    unfold robustYhat followMix
    exact Measurable.ite ((mI u hu') (measurableSet_singleton k))
      ((mr u hu').div (((hq k).const_mul _).add measurable_const)) measurable_const
  exact (hq i).mul ((hy j).sub (hy i))

theorem measurableSet_robustFollowing {t : ℕ} (ht : t ≤ T) :
    MeasurableSet[run.info t] (run.robustFollowing t) := by
  change MeasurableSet[run.info t]
    {ω | ∀ u < t, ¬ robustCrossed T ζ (fun s => run.q s ω)
      (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1)}
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  unfold robustCrossed
  exact (measurableSet_lt measurable_const (run.measurable_robustHhat (Nat.succ_le_of_lt hu) ht)).compl

variable [IsProbabilityMeasure P]

theorem condExp_robustFollowing_action {t : ℕ} (ht : t < T) (j : Fin K) :
    condExp (run.info t) P ((run.robustFollowing t ∩ (run.I t ⁻¹' {j})).indicator
      (fun _ => (1 : ℝ))) =ᵐ[P]
      (run.robustFollowing t).indicator (fun ω => followMix (robustEps T ζ) (run.q t ω) j) := by
  classical
  let F := run.robustFollowing t
  let yI : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  let yJ : Ω → ℝ := (run.J t ⁻¹' {j}).indicator (fun _ => 1)
  let a : ℝ := 1 - robustEps T ζ
  let b : ℝ := robustEps T ζ / K
  let g : Ω → ℝ := F.indicator (a • yJ + fun _ => b)
  have hF := run.measurableSet_robustFollowing ht.le
  have hFpre : MeasurableSet[run.preDraw t] F := (show run.info t ≤ run.preDraw t from le_sup_left) F hF
  have hIint : Integrable yI P := (integrable_const _).indicator
    ((run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have hJint : Integrable yJ P := (integrable_const _).indicator
    ((run.J_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have hm : run.preDraw t ≤ mΩ := run.toDrawRun.preDraw_le_ambient ht
  let : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  have hg : condExp (run.preDraw t) P (F.indicator yI) =ᵐ[P] g := by
    refine (condExp_indicator hIint hFpre).trans ?_
    filter_upwards [run.I_law t ht j] with ω hw
    by_cases hω : ω ∈ F
    · have h := congrFun (robustPolicy_eq_follow ζ t (fun s => run.q s ω)
        (fun s => run.J s ω) (fun s => run.I s ω)
        (fun s => run.y s ω (run.I s ω)) hω) j
      simp only [g, Set.indicator_of_mem hω, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]
      change condExp (run.preDraw t) P yI ω = _
      rw [hw, h]
      simp [yJ, Set.indicator_apply]
    · simp [g, Set.indicator_of_notMem hω]
  rw [← Set.indicator_indicator]
  refine (condExp_condExp_of_le (μ := P) (f := F.indicator yI) le_sup_left hm).symm.trans
    ((condExp_congr_ae (m := run.info t) hg).trans ?_)
  refine (condExp_indicator ((hJint.smul a).add (integrable_const b)) hF).trans ?_
  filter_upwards [condExp_add (hJint.smul a) (integrable_const b) (run.info t),
    condExp_smul (μ := P) a yJ (run.info t), run.J_law t ht j] with ω hsum hmul hJ
  by_cases hω : ω ∈ run.robustFollowing t
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    simp only [Pi.add_apply] at hsum
    rw [hsum, hmul, condExp_const (run.info_le _ ht.le), Pi.smul_apply, smul_eq_mul, hJ] <;> rfl
  · simp only [Set.indicator_of_notMem hω]

end CalibeatBandit.Supplement.QProtocolRun

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

open MeasureTheory Filter Set
open scoped ENNReal

namespace CalibeatBandit.Supplement

theorem robustEps_pos_of_pos {T : ℕ} (hT : 0 < T) (ζ : ℝ) :
    0 < robustEps T ζ :=
  Real.rpow_pos_of_pos (by exact_mod_cast hT) _

theorem robustEps_le_one_of_nonneg {T : ℕ} (hT : 0 < T) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    robustEps T ζ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (neg_nonpos.mpr hζ)

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- Count disagreements on rounds played in follow mode. -/
noncomputable def followDisagreements (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, (run.robustFollowing t).indicator
    (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω

omit [IsProbabilityMeasure P] in
theorem followDisagreements_nonneg (ω : Ω) : 0 ≤ run.followDisagreements ω := by
  unfold followDisagreements
  exact Finset.sum_nonneg fun t _ => Set.indicator_nonneg (fun _ _ => by split <;> norm_num) _

set_option maxHeartbeats 1000000 in
theorem integrable_followDisagreements_and_le (hK : 0 < K) (hT : 0 < T) (_hζ : 0 ≤ ζ) :
    Integrable run.followDisagreements P ∧
      ∫ ω, run.followDisagreements ω ∂P ≤ robustEps T ζ * T := by
  classical
  let ε := robustEps T ζ
  have hε := robustEps_pos_of_pos hT ζ
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  let F (t : ℕ) := run.robustFollowing t
  let D (t : ℕ) (ω : Ω) := (F t).indicator
    (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω
  have hdt (t : ℕ) (ht : t < T) : Integrable (D t) P ∧
      ∫ ω, D t ω ∂P ≤ ε := by
    let g (j : Fin K) : Ω → ℝ := (F t).indicator (fun ω => if j = run.J t ω then 0 else 1)
    have gmeas (j : Fin K) : Measurable[run.toDrawRun.preDraw t] (g j) := by
      have hJ : Measurable[run.preDraw t] (run.J t) :=
        Measurable.of_comap_le le_sup_right
      have hj := (hJ (measurableSet_singleton j))
      have hset : MeasurableSet[run.preDraw t] {ω | j = run.J t ω} := by
        simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hj
      have hF : MeasurableSet[run.preDraw t] (F t) :=
        (show run.info t ≤ run.preDraw t from le_sup_left) _ (run.measurableSet_robustFollowing ht.le)
      exact (Measurable.ite hset measurable_const measurable_const).indicator hF
    have gb (j : Fin K) (ω : Ω) : |g j ω| ≤ 1 := by
      by_cases hf : ω ∈ F t
      · simp only [g, Set.indicator_of_mem hf]; split <;> norm_num
      · simp [g, Set.indicator_of_notMem hf]
    have hc := run.toDrawRun.condExp_select_played P ht g gmeas 1 gb
    change Integrable (D t) P ∧ _ at hc
    refine ⟨hc.1, ?_⟩
    have he : ∫ ω, D t ω ∂P = ∫ ω, ∑ j, run.toDrawRun.played t ω j * g j ω ∂P := by
      rw [← integral_congr_ae hc.2, integral_condExp (run.toDrawRun.preDraw_le_ambient ht)]
      rfl
    rw [he]
    have hs : Integrable (fun ω => ∑ j, run.toDrawRun.played t ω j * g j ω) P :=
      integrable_condExp.congr hc.2
    calc
      _ ≤ ∫ _ : Ω, ε ∂P := integral_mono hs (integrable_const _) fun ω => by
        by_cases hf : ω ∈ F t
        · have h := robustPolicy_eq_follow ζ t (fun s => run.q s ω) (fun s => run.J s ω)
            (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) hf
          have hj (j : Fin K) : run.toDrawRun.played t ω j * g j ω ≤ ε / K := by
            have hval : run.toDrawRun.played t ω j =
                (1 - ε) * (if run.J t ω = j then 1 else 0) + ε / K := congrFun h j
            rw [hval]
            simp only [g, Set.indicator_of_mem hf]
            by_cases hEq : j = run.J t ω
            · simp only [hEq, if_true, mul_zero]
              exact div_nonneg hε.le hK'.le
            · simp only [hEq, Ne.symm hEq, if_false, mul_zero, zero_add, mul_one, le_refl]
          calc
            _ ≤ ∑ _j : Fin K, ε / K := Finset.sum_le_sum fun j _ => hj j
            _ = ε := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp [hK'.ne']
        · simp only [g, Set.indicator_of_notMem hf, mul_zero, Finset.sum_const_zero]
          exact hε.le
      _ = _ := by simp
  have hd : run.followDisagreements = ∑ t ∈ Finset.range T, D t := by
    ext ω
    simp [followDisagreements, D, F]
  rw [hd]
  refine ⟨integrable_finsetSum' _ fun t ht => (hdt t (Finset.mem_range.mp ht)).1, ?_⟩
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ fun t ht => (hdt t (Finset.mem_range.mp ht)).1]
  calc
    _ ≤ ∑ _t ∈ Finset.range T, ε := Finset.sum_le_sum fun t ht => (hdt t (Finset.mem_range.mp ht)).2
    _ = _ := by simp [ε, mul_comm]

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

namespace CalibeatBandit.Supplement

theorem rewardLoss_le_rounds {K s : ℕ} (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K)
    (hy : ∀ t < s, ∀ i, y t i ∈ Icc (0 : ℝ) 1) :
    rewardLoss s y J I ≤ (s : ℝ) := by
  unfold rewardLoss
  apply Finset.sup'_le
  intro f _
  calc
    _ ≤ ∑ _t ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
      sub_le_iff_le_add.mpr (((hy t (Finset.mem_range.mp ht) (f (J t))).2).trans
        (le_add_of_nonneg_right ((hy t (Finset.mem_range.mp ht) (I t))).1))
    _ = _ := by simp

theorem rewardLoss_abs_le_rounds {K s : ℕ} (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K)
    (hy : ∀ t < s, ∀ i, y t i ∈ Icc (0 : ℝ) 1) :
    |rewardLoss s y J I| ≤ (s : ℝ) := by
  apply abs_le.mpr
  refine ⟨?_, rewardLoss_le_rounds y J I hy⟩
  unfold rewardLoss
  calc
    _ = ∑ _t ∈ Finset.range s, (-1 : ℝ) := by simp
    _ ≤ ∑ t ∈ Finset.range s, (y t (J t) - y t (I t)) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      linarith [(hy t ht' (J t)).1, (hy t ht' (I t)).2]
    _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range s, (y t (f (J t)) - y t (I t))) (Finset.mem_univ id)

theorem swapRegret_nonneg_of_id {K s : ℕ} (y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    0 ≤ swapRegret s y I := by
  unfold swapRegret
  simpa using (Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range s, (y t (f (I t)) - y t (I t))) (Finset.mem_univ id))

private theorem measurable_rewardLoss_prefix {K s : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ → Ω → Fin K → ℝ) (J I : ℕ → Ω → Fin K)
    (hy : ∀ t < s, Measurable (y t)) (hJ : ∀ t < s, Measurable (J t))
    (hI : ∀ t < s, Measurable (I t)) :
    Measurable (fun ω => rewardLoss s (fun t => y t ω) (fun t => J t ω) (fun t => I t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  change Measurable (fun ω => Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun f : Fin K → Fin K => ∑ t ∈ Finset.range s, (y t ω (f (J t ω)) - y t ω (I t ω))))
  simp_rw [Finset.sup'_univ_eq_ciSup]
  refine Measurable.iSup fun f => Finset.measurable_sum _ fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  exact (measurable_select (hJ t ht') (fun i => (measurable_pi_apply (f i)).comp (hy t ht'))).sub
    (measurable_select (hI t ht') (fun i => (measurable_pi_apply i).comp (hy t ht')))

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

theorem measurable_qRunRewardLoss {s : ℕ} (hs : s ≤ T) (bJ bI : Bool) :
    Measurable (fun ω => rewardLoss s (fun t => run.y t ω)
      (fun t => if bJ then run.J t ω else run.I t ω)
      (fun t => if bI then run.J t ω else run.I t ω)) := by
  apply measurable_rewardLoss_prefix
  · intro t ht
    have ht' := ht.trans_le hs
    exact (run.y_measurable t ht').mono (run.info_le t ht'.le) le_rfl
  all_goals
    intro t ht
    have ht' := ht.trans_le hs
    have jm := (run.J_measurable t ht').mono (run.info_le _ (Nat.succ_le_of_lt ht')) le_rfl
    have im := (run.I_measurable t ht').mono (run.info_le _ (Nat.succ_le_of_lt ht')) le_rfl
    split <;> assumption

def recommendationCapEvent : Set Ω :=
  {ω | ∀ s : ℕ, 1 ≤ s → s ≤ T →
    swapRegret s (fun t => run.y t ω) (fun t => run.J t ω) ≤ s * robustC K T ζ s}

theorem measurableSet_recommendationCapEvent :
    MeasurableSet run.recommendationCapEvent := by
  unfold recommendationCapEvent
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun hs => ?_
  exact measurableSet_le (run.measurable_qRunRewardLoss hs true true) measurable_const

set_option maxHeartbeats 1200000 in
/-- The consistency argument only needs a measurable event with the probability
from the prefix concentration bounds and on which the learner keeps following. -/
theorem robust_consistency_of_event (hK : 0 < K) (hT : 0 < T) (hζ : 0 ≤ ζ)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hbad : P Eᶜ ≤ ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)))
    (hfollow : E ∩ run.recommendationCapEvent ⊆ run.robustFollowing T)
    (hcap : ENNReal.ofReal (1 - ρ) ≤ P run.recommendationCapEvent) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P +
          (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P +
          (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T := by
  classical
  let F := run.recommendationCapEvent
  let B := (E ∩ F)ᶜ
  let Y (ω : Ω) := swapRegret T (fun t => run.y t ω) (fun t => run.J t ω)
  let D := run.followDisagreements
  let H (ω : Ω) : ℝ := B.indicator (fun _ => (T : ℝ)) ω
  have hF := run.measurableSet_recommendationCapEvent
  have hB : MeasurableSet B := (hE.inter hF).compl
  have hρ : P Fᶜ ≤ ENNReal.ofReal ρ := by
    rw [prob_compl_eq_one_sub₀ hF.nullMeasurableSet]
    refine (tsub_le_tsub_left hcap (1 : ℝ≥0∞)).trans_eq ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) (sub_nonneg.mpr hρ₁)]
    congr 1
    ring
  have hpos : 0 ≤ (T : ℝ) ^ (-2 : ℝ) := by positivity
  have hBM : P B ≤ ENNReal.ofReal (ρ + (T : ℝ) ^ (-2 : ℝ)) := by
    unfold B
    rw [compl_inter, ENNReal.ofReal_add hρ₀ hpos, add_comm]
    exact (measure_union_le _ _).trans (add_le_add hbad hρ)
  have hdε := run.integrable_followDisagreements_and_le hK hT hζ
  have hd : Integrable D P := hdε.1
  have heD : ∫ ω, D ω ∂P ≤ robustEps T ζ * T := hdε.2
  have hH : Integrable H P := (integrable_const _).indicator hB
  have hEH : ∫ ω, H ω ∂P ≤ (ρ + (T : ℝ) ^ (-2 : ℝ)) * T := by
    change ∫ ω, B.indicator (fun _ => (T : ℝ)) ω ∂P ≤ _
    rw [integral_indicator_const _ hB, smul_eq_mul]
    apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg T)
    change (P B).toReal ≤ _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBM).trans_eq
      (ENNReal.toReal_ofReal (add_nonneg hρ₀ hpos))
  have hYm : Measurable Y := run.measurable_qRunRewardLoss le_rfl true true
  have hYi : Integrable Y P := integrable_of_abs_bound hYm (fun ω =>
    rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
  have hYnonneg (ω : Ω) : 0 ≤ Y ω := swapRegret_nonneg_of_id _ _
  have hAt (ω : Ω) (hω : ω ∈ E ∩ F) :
      swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ≤ Y ω + 2 * D ω ∧
      rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)
        ≤ Y ω + D ω := by
    have hw (t : ℕ) (ht : t < T) : ω ∈ run.robustFollowing t :=
      fun u hu => hfollow hω u (hu.trans ht)
    have hD : D ω = ∑ t ∈ Finset.range T, if run.I t ω = run.J t ω then (0 : ℝ) else 1 := by
      unfold D followDisagreements
      exact Finset.sum_congr rfl fun t ht => Set.indicator_of_mem (hw t (Finset.mem_range.mp ht)) _
    rw [hD]
    exact regret_le_of_disagreements _ _ _ (fun t ht i => run.y_mem t ht ω i)
  have estimate (X : Ω → ℝ) (hX : Integrable X P) (hb : ∀ ω, X ω ≤ (T : ℝ))
      (hgood : ∀ ω ∈ E ∩ F, X ω ≤ Y ω + 2 * D ω) :
      ∫ ω, X ω ∂P ≤ ∫ ω, Y ω ∂P +
        (ρ + (2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ))) * T := by
    have hD2 : Integrable (fun ω => 2 * D ω) P := hd.const_mul (2 : ℝ)
    have hsum : Integrable (fun ω => Y ω + 2 * D ω) P := hYi.add hD2
    have h : (∫ ω, X ω ∂P) ≤ ∫ ω, (Y ω + 2 * D ω) + H ω ∂P :=
      integral_mono hX (hsum.add hH) (fun ω => by
        by_cases hω : ω ∈ E ∩ F
        · have hz : H ω = 0 := Set.indicator_of_notMem (not_not_intro hω) _
          change X ω ≤ Y ω + 2 * D ω + H ω
          rw [hz, add_zero]
          exact hgood ω hω
        · have ht : H ω = (T : ℝ) := Set.indicator_of_mem hω _
          change X ω ≤ Y ω + 2 * D ω + H ω
          rw [ht]
          linarith [hb ω, hYnonneg ω, run.followDisagreements_nonneg ω])
    rw [integral_add hsum hH, integral_add hYi hD2, integral_const_mul] at h
    refine h.trans ?_
    nlinarith only [heD, hEH]
  constructor
  · refine estimate _ ?_ (fun ω => rewardLoss_le_rounds _ _ _
      (fun t ht i => run.y_mem t ht ω i)) (fun ω hω => (hAt ω hω).1)
    exact integrable_of_abs_bound (run.measurable_qRunRewardLoss le_rfl false false)
      (fun ω => rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
  · refine estimate _ ?_ (fun ω => rewardLoss_le_rounds _ _ _
      (fun t ht i => run.y_mem t ht ω i)) ?_
    · exact integrable_of_abs_bound (run.measurable_qRunRewardLoss le_rfl true false)
        (fun ω => rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    · intro ω hω
      linarith [(hAt ω hω).2, run.followDisagreements_nonneg ω]

set_option maxHeartbeats 1200000 in
/-- If the allowed excess regret is at least one per round, the consistency
guarantee holds directly from the reward range. -/
theorem robust_consistency_of_gamma_ge_one (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 1 ≤ γ) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T := by
  have hbase : 0 ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P :=
    integral_nonneg (fun ω => swapRegret_nonneg_of_id _ _)
  have hgap : (T : ℝ) ≤ (ρ + γ) * T :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
  have req (b : Bool) :
      ∫ ω, rewardLoss T (fun t => run.y t ω)
          (fun t => if b then run.J t ω else run.I t ω) (fun t => run.I t ω) ∂P ≤ (T : ℝ) := by
    have hm := run.measurable_qRunRewardLoss le_rfl b false
    have hi := integrable_of_abs_bound (P := P) hm (B := (T : ℝ)) (fun ω =>
      rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    have h := integral_mono hi (integrable_const (T : ℝ)) (fun ω =>
      rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
    simpa using h
  exact ⟨(req false).trans (by linarith), (req true).trans (by linarith)⟩

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit

/-- At the stated horizon the tuned parameters are admissible and the explicit
swap-regret bound is at most \(\varepsilon T\). -/
theorem etaStar_spec {K T : ℕ} {ε : ℝ} (hK : 2 ≤ K) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : 1024 * (K : ℝ) ^ 2 * Real.log K / ε ^ 2 ≤ T) :
    0 < etaStar K T ∧ 0 < muStar K T ∧ muStar K T ≤ 1 / 2 ∧
    rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K) ≤ ε * T := by
  let k : ℝ := K
  let t : ℝ := T
  let d : ℝ := k * Real.log k
  let b : ℝ := 2 * d + Real.log 2
  let a := Real.sqrt (b / (14 * k * t))
  let q := k * a
  have hk : 2 ≤ k := by dsimp [k]; exact_mod_cast hK
  have hk₀ : 0 < k := by linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk
  have hd : 0 < d := mul_pos hk₀ (hlog₂.trans_le hlog)
  have hb : 0 < b := by dsimp [b]; linarith
  have hb_le : b ≤ 3 * d := by
    have h := mul_nonneg (show 0 ≤ k - 1 by linarith) (hlog₂.trans_le hlog).le
    dsimp [b, d]
    linarith
  have hlog_pos : 0 < Real.log k := hlog₂.trans_le hlog
  have ht : 0 < t := lt_of_lt_of_le (by change 0 < 1024 * k ^ 2 * Real.log k / ε ^ 2; positivity) hT
  have htd : 1024 * k * d ≤ t * ε ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hT
    dsimp [d, k, t]
    nlinarith only [h]
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have haq : a ^ 2 * (14 * k * t) = b := by
    have h : a ^ 2 = b / (14 * k * t) := Real.sq_sqrt (by positivity)
    exact (eq_div_iff (by positivity)).mp h
  have hq : 0 < q := mul_pos hk₀ ha
  have hqt : 14 * q ^ 2 * t = k * b := by
    dsimp [q]
    linear_combination k * haq
  have hq_le : q ≤ ε / 32 := by
    have h₁ := mul_le_mul_of_nonneg_left hb_le hk₀.le
    have h₂ : 1024 * q ^ 2 * t ≤ ε ^ 2 * t := by
      nlinarith only [hqt, h₁, htd, mul_nonneg hk₀.le hd.le]
    have h₃ := le_of_mul_le_mul_right (show (32 * q) ^ 2 * t ≤ ε ^ 2 * t by
      nlinarith only [h₂]) ht
    by_contra! h
    have hprod := mul_pos (sub_pos.mpr (show ε < 32 * q by linarith))
      (show 0 < 32 * q + ε by positivity)
    nlinarith only [hprod, h₃]
  have hη : etaStar K T = a := by
    unfold etaStar
    have hsqrt : Real.sqrt ((2 * (K : ℝ) * Real.log K + Real.log 2) / (14 * K * T)) = a := by
      dsimp [a, b, d, k, t]
      congr 2
      ring
    rw [hsqrt]
    apply min_eq_right
    apply (le_div_iff₀ (by positivity)).mpr
    change a * (8 * k) ≤ 1
    dsimp [q] at hq_le
    nlinarith only [hq_le, hε₁]
  have hμ : muStar K T = 4 * q := by unfold muStar; rw [hη]; dsimp [q, k]; ring
  have hμ_le : 4 * q ≤ 1 / 2 := by linarith
  have hrec : rT K T (etaStar K T) (muStar K T) ≤ 28 * q * t := by
    rw [hη, hμ]
    have hba : b / a = 14 * q * t := by
      apply (div_eq_iff ha.ne').mpr
      dsimp [q]
      nlinarith only [haq]
    have hden : 0 < 1 - 4 * q := by linarith
    have hterm : 5 * q * t / (1 - 4 * q) ≤ 10 * q * t := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [mul_nonneg (show 0 ≤ q * t by positivity)
        (show 0 ≤ 1 / 2 - 4 * q by linarith)]
    unfold rT
    have hcoeff : 2 * (K : ℝ) * Real.log K + Real.log 2 = b := by dsimp [b, d, k]; ring
    rw [hcoeff]
    change 4 * q * t + b / a + (5 * a * k * t) / (1 - 4 * q) ≤ _
    rw [hba, show 5 * a * k * t = 5 * q * t by dsimp [q]; ring]
    linarith
  have hs : Real.sqrt (2 * t * k * Real.log k) ≤ ε * t / 8 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h₁ : 128 * d ≤ t * ε ^ 2 := by
      have h₂ := mul_nonneg (show 0 ≤ 1024 * k - 128 by linarith) hd.le
      nlinarith only [h₂, htd]
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht.le
    dsimp [d] at h₂
    nlinarith only [h₂]
  refine ⟨hη ▸ ha, hμ ▸ mul_pos (by norm_num) hq, hμ ▸ hμ_le, ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hq_le ht.le
  change _ + Real.sqrt (2 * t * k * Real.log k) ≤ ε * t
  nlinarith only [hrec, hs, h₁]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

/-- The cumulative form of the worst-case regret rate, including one log factor. -/
noncomputable def robustRate (K T : ℕ) (ζ : ℝ) : ℝ :=
  (K : ℝ) * (T : ℝ) ^ ((1 + ζ) / 2) * (1 + Real.log ((K : ℝ) * T))

theorem robustRate_normalize {K T : ℕ} (hT : 0 < T) (ζ C : ℝ) :
    C * robustRate K T ζ =
      (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log ((K : ℝ) * T)) ^ (1 : ℕ)) * T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  unfold robustRate
  rw [pow_one, show (1 + ζ) / 2 = -(1 - ζ) / 2 + 1 by ring,
    Real.rpow_add hT', Real.rpow_one]
  ring

theorem robustRate_ge_one {K T : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) : 1 ≤ robustRate K T ζ := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hm := one_le_mul_of_one_le_of_one_le hK' hT'
  unfold robustRate
  refine one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK' (Real.one_le_rpow hT' (by positivity))) ?_
  linarith [Real.log_nonneg hm]

theorem robustL_nonneg {K T s : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) :
    0 ≤ robustL K T s := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hall : 1 ≤ 4 * (s : ℝ) * (s + 1) * (T : ℝ) ^ 2 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hs') (by linarith))
      (one_le_pow₀ hT')
  unfold robustL
  exact add_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hK')) (Real.log_nonneg hall)

private theorem robustPrefixThreshold_eq {K T s : ℕ}
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) (ζ : ℝ) :
    (s : ℝ) * robustC K T ζ s =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) +
        (K * (T : ℝ) ^ ζ + 1) * robustL K T s / 3 := by
  let x : ℝ := 2 * (K * (T : ℝ) ^ ζ + 2) * robustL K T s
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hx : 0 ≤ x := by
    have hL := robustL_nonneg hK hT hs
    dsimp [x]
    positivity
  have heq : (s : ℝ) * Real.sqrt (x / s) = Real.sqrt (s * x) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    have hsq := Real.sq_sqrt (show 0 ≤ x / (s : ℝ) by positivity)
    rw [mul_pow, hsq]
    field_simp
  unfold robustC
  change (s : ℝ) * (Real.sqrt (x / s) +
      (K * (T : ℝ) ^ ζ + 1) * robustL K T s / (3 * s)) = _
  rw [mul_add, heq]
  have hx' : (s : ℝ) * x = 2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s := by
    dsimp [x]
    ring
  rw [hx']
  congr 1
  field_simp

theorem robustPrefixThreshold_mono {K T s : ℕ}
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hs : 1 ≤ s) (hst : s ≤ T) (ζ : ℝ) :
    (s : ℝ) * robustC K T ζ s ≤ T * robustC K T ζ T := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ T := by exact_mod_cast hst
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : robustL K T s ≤ robustL K T T := by
    unfold robustL
    apply add_le_add_right
    apply Real.log_le_log (by positivity)
    gcongr
  have hLs := robustL_nonneg hK hT hs
  have hLt := robustL_nonneg hK hT hT
  rw [robustPrefixThreshold_eq hK hT hs, robustPrefixThreshold_eq hK hT hT]
  gcongr

theorem robustThreshold_le_rate {K T : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hsmall : robustRate K T ζ ≤ T) :
    (T : ℝ) * robustC K T ζ T ≤ 20 * robustRate K T ζ := by
  let k : ℝ := K
  let t : ℝ := T
  let L := 1 + Real.log (k * t)
  let a := (1 + ζ) / 2
  have hk : 1 ≤ k := by
    change (1 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hK
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (T : ℝ)
    exact_mod_cast hT
  have hk₀ : 0 < k := by linarith
  have ht₀ : 0 < t := by linarith
  have hkt : 1 ≤ k * t := one_le_mul_of_one_le_of_one_le hk ht
  have hloga : Real.log k ≤ Real.log (k * t) :=
    Real.log_le_log hk₀ (le_mul_of_one_le_right hk₀.le ht)
  have hlogb : Real.log t ≤ Real.log (k * t) :=
    Real.log_le_log ht₀ (le_mul_of_one_le_left ht₀.le hk)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hkt]
  have hlogprod : Real.log (4 * t * (t + 1) * t ^ 2) ≤ 7 + 4 * Real.log t := by
    have harg : 4 * t * (t + 1) * t ^ 2 ≤ 8 * t ^ 4 := by
      have hle : t + 1 ≤ 2 * t := by linarith
      calc
        _ ≤ 4 * t * (2 * t) * t ^ 2 := by gcongr
        _ = _ := by ring
    refine (Real.log_le_log (by positivity) harg).trans ?_
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero _ ht₀.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (x := 8) (by norm_num)]
  have hLbound : robustL K T T ≤ 12 * k * L := by
    unfold robustL
    change k * Real.log k + Real.log (4 * t * (t + 1) * t ^ 2) ≤ _
    have h1 := mul_le_mul_of_nonneg_left hloga hk₀.le
    have h2 : L ≤ k * L := le_mul_of_one_le_left (by linarith) hk
    have h3 : k * Real.log (k * t) ≤ k * L := by
      gcongr
      dsimp [L]
      linarith
    linarith only [h1, h2, h3, hlogprod, hlogb, hL, show Real.log (k * t) = L - 1 by dsimp [L]; ring]
  have hL₀ := robustL_nonneg hK hT hT
  have hz : 1 ≤ t ^ ζ := Real.one_le_rpow ht hζ
  have ha : 1 ≤ t ^ a := Real.one_le_rpow ht (by dsimp [a]; linarith)
  have hkz : 1 ≤ k * t ^ ζ := one_le_mul_of_one_le_of_one_le hk hz
  have hsq : (t ^ a) ^ 2 = t * t ^ ζ := by
    rw [pow_two, ← Real.rpow_add ht₀,
      show a + a = 1 + ζ by dsimp [a]; ring,
      Real.rpow_add ht₀, Real.rpow_one]
  have hr : robustRate K T ζ = k * (t ^ a) * L := rfl
  have hroot : Real.sqrt (2 * t * (k * t ^ ζ + 2) * robustL K T T) ≤
      9 * (k * (t ^ a) * L) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hA : k * t ^ ζ + 2 ≤ 3 * (k * t ^ ζ) := by linarith
    calc
      _ ≤ 2 * t * (3 * (k * t ^ ζ)) * (12 * k * L) := by gcongr
      _ = 72 * k ^ 2 * (t ^ a) ^ 2 * L := by rw [hsq]; ring
      _ ≤ (9 * (k * t ^ a * L)) ^ 2 := by
        have hLsq : L ≤ L ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hL)]
        have hh := mul_le_mul_of_nonneg_left hLsq (show 0 ≤ 72 * k ^ 2 * (t ^ a) ^ 2 by positivity)
        have hnon := mul_nonneg (show (0 : ℝ) ≤ 9 by norm_num) (show 0 ≤ k ^ 2 * (t ^ a) ^ 2 * L ^ 2 by positivity)
        nlinarith only [hh, hnon]
  have hterm : (k * t ^ ζ + 1) * robustL K T T / 3 ≤
      8 * (k * t ^ a * L) := by
    have hA : k * t ^ ζ + 1 ≤ 2 * (k * t ^ ζ) := by linarith
    have hsmall' : (k * L) * t ^ a ≤ t := by
      rw [hr] at hsmall
      nlinarith only [hsmall]
    have hs := mul_le_mul_of_nonneg_right hsmall' (show 0 ≤ k * t ^ a by positivity)
    have hrewrite : (k * L * t ^ a) * (k * t ^ a) = (k ^ 2 * t ^ ζ * L) * t := by
      calc
        _ = k ^ 2 * (t ^ a) ^ 2 * L := by ring
        _ = _ := by rw [hsq]; ring
    rw [hrewrite, show t * (k * t ^ a) = (k * t ^ a) * t by ring] at hs
    have hB := le_of_mul_le_mul_right hs ht₀
    calc
      _ ≤ (2 * (k * t ^ ζ)) * (12 * k * L) / 3 := by gcongr
      _ = 8 * (k ^ 2 * t ^ ζ * L) := by ring
      _ ≤ 8 * (k * t ^ a * L) := by
        exact mul_le_mul_of_nonneg_left (hB.trans (le_mul_of_one_le_right (by positivity) hL)) (by norm_num)
  rw [robustPrefixThreshold_eq hK hT hT, hr]
  change Real.sqrt (2 * t * (k * t ^ ζ + 2) * robustL K T T) +
      (k * t ^ ζ + 1) * robustL K T T / 3 ≤ 20 * (k * t ^ a * L)
  linarith only [hroot, hterm, show 0 ≤ k * t ^ a * L by positivity]

theorem robustRate_restart_parameters {K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hsmall : 32 * robustRate K T ζ ≤ T) :
    0 < etaStar K T ∧ 0 < muStar K T ∧ muStar K T ≤ 1 / 2 ∧
    rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K) ≤
      32 * robustRate K T ζ := by
  let k : ℝ := K
  let t : ℝ := T
  let a := (1 + ζ) / 2
  let L := 1 + Real.log (k * t)
  let B := 32 * robustRate K T ζ
  let e := B / t
  have hk : 1 ≤ k := by
    have hk' : 1 ≤ K := by omega
    change (1 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hk'
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (T : ℝ)
    exact_mod_cast hT
  have ht₀ : 0 < t := by linarith
  have hk₀ : 0 < k := by linarith
  have hkt : 1 ≤ k * t := one_le_mul_of_one_le_of_one_le hk ht
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hkt]
  have hlog : Real.log k ≤ L ^ 2 := by
    have hlog' := Real.log_le_log hk₀ (le_mul_of_one_le_right hk₀.le ht)
    have hL' : L ≤ L ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hL)]
    dsimp [L] at hL'
    dsimp [L]
    linarith
  have hB : B = 32 * k * (t ^ a) * L := by dsimp [B, robustRate, k, t, a, L]; ring
  have he : 0 < e := by
    dsimp [e]
    rw [hB]
    positivity
  have he₁ : e ≤ 1 := by
    exact (div_le_one ht₀).2 hsmall
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg _
  have htsq : t ≤ (t ^ a) ^ 2 := by
    rw [pow_two, ← Real.rpow_add ht₀]
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le ht
      (show 1 ≤ a + a by dsimp [a]; linarith) : t ^ (1 : ℝ) ≤ _)
  have htarget : 1024 * k ^ 2 * Real.log k / e ^ 2 ≤ t := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).2
    have he' : e ^ 2 * t ^ 2 = B ^ 2 := by dsimp [e]; rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ht₀.ne')]
    have hb' : 1024 * k ^ 2 * Real.log k * t ≤ B ^ 2 := by
      rw [hB]
      calc
        _ ≤ 1024 * k ^ 2 * L ^ 2 * (t ^ a) ^ 2 := by gcongr
        _ = _ := by ring
    apply le_of_mul_le_mul_right _ ht₀
    nlinarith only [hb', he']
  obtain ⟨h1,h2,h3,h4⟩ := etaStar_spec (K := K) (T := T) hK he he₁ htarget
  refine ⟨h1,h2,h3,h4.trans_eq ?_⟩
  change B / t * t = B
  exact div_mul_cancel₀ _ ht₀.ne'

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace CalibeatBandit.Supplement

private theorem swapRegret_succ_le {K s : ℕ} (y : ℕ → Fin K → ℝ) (J : ℕ → Fin K)
    (hy : ∀ i, y s i ∈ Icc (0 : ℝ) 1) :
    swapRegret (s + 1) y J ≤ swapRegret s y J + 1 := by
  unfold swapRegret
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_succ]
  refine add_le_add (Finset.le_sup' (fun σ : Fin K → Fin K =>
    ∑ t ∈ Finset.range s, (y t (σ (J t)) - y t (J t))) (Finset.mem_univ f)) ?_
  linarith [(hy (f (J s))).2, (hy (J s)).1]

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (run : QProtocolRun K T P (robustPolicy K T ζ))

private theorem measurable_qRunRewardLoss_stopped (n : Ω → ℕ)
    (hn : Measurable n) (hnT : ∀ ω, n ω ≤ T) (bJ bI : Bool) :
    Measurable (fun ω => rewardLoss (n ω) (fun t => run.y t ω)
      (fun t => if bJ then run.J t ω else run.I t ω)
      (fun t => if bI then run.J t ω else run.I t ω)) := by
  let a (ω : Ω) : Fin (T + 1) := ⟨n ω, Nat.lt_succ_of_le (hnT ω)⟩
  have ha : Measurable a := measurable_to_countable' fun i => by
    have h : a ⁻¹' {i} = n ⁻¹' {(i : ℕ)} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, ← Fin.val_eq_val, a]
    rw [h]
    exact hn (measurableSet_singleton _)
  exact measurable_select ha
    (fun i => run.measurable_qRunRewardLoss (Nat.le_of_lt_succ i.isLt) bJ bI)

set_option maxHeartbeats 1200000 in
/-- The expected regret accrued before the restart is controlled by the
switching threshold, the exploration count, and the concentration failure
probability. The stopping length may include the crossing round. -/
theorem robust_prefix_expected (hK : 1 ≤ K) (hT : 1 ≤ T) (hζ : 0 ≤ ζ)
    (hC : 0 ≤ robustC K T ζ T)
    (n : Ω → ℕ) (hn : Measurable n) (hnT : ∀ ω, n ω ≤ T)
    (hfollowing : ∀ ω t, t < n ω → ω ∈ run.robustFollowing t)
    (E : Set Ω) (hE : MeasurableSet E) (hbad : P Eᶜ ≤ ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)))
    (hest : ∀ ω ∈ E, ∀ t < T, ω ∈ run.robustFollowing t →
      |robustHhat T ζ (fun v => run.q v ω) (fun v => run.I v ω)
        (fun v => run.y v ω (run.I v ω)) (t + 1) -
        pseudoSwapRegret (t + 1) (fun v => run.q v ω) (fun v => run.y v ω)|
        ≤ (↑(t + 1) : ℝ) * robustC K T ζ (t + 1))
    (hrec : ∀ ω ∈ E, ∀ t < T,
      |swapRegret (t + 1) (fun v => run.y v ω) (fun v => run.J v ω) -
        pseudoSwapRegret (t + 1) (fun v => run.q v ω) (fun v => run.y v ω)|
        ≤ (↑(t + 1) : ℝ) * robustC K T ζ (t + 1)) :
    let B : ℝ := 5 * T * robustC K T ζ T + 1 + 2 * robustEps T ζ * T + T * (T : ℝ) ^ (-2 : ℝ)
    (∫ ω, swapRegret (n ω) (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤ B ∧
    (∫ ω, rewardLoss (n ω) (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ B := by
  classical
  intro B
  let C : ℝ := 5 * T * robustC K T ζ T + 1
  let D := run.followDisagreements
  let H (ω : Ω) : ℝ := Eᶜ.indicator (fun _ => (T : ℝ)) ω
  have hC₀ : 0 ≤ 5 * (T : ℝ) * robustC K T ζ T := by positivity
  have hC₁ : 0 ≤ C := by dsimp [C]; positivity
  have hJ (ω : Ω) (hω : ω ∈ E) :
      swapRegret (n ω) (fun t => run.y t ω) (fun t => run.J t ω) ≤ C := by
    by_cases hsmall : n ω ≤ 1
    · have h := rewardLoss_le_rounds (s := n ω) (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.J t ω) (fun t ht i =>
          run.y_mem t (ht.trans_le (hnT ω)) ω i)
      exact h.trans (show (n ω : ℝ) ≤ C by
        have hm : (n ω : ℝ) ≤ 1 := by exact_mod_cast hsmall
        dsimp [C]
        linarith)
    · obtain ⟨s, hs⟩ : ∃ s : ℕ, n ω = s + 2 := ⟨n ω - 2, by omega⟩
      have hprev : s + 1 < n ω := by omega
      have ht : s < T := lt_of_lt_of_le (show s < n ω by omega) (hnT ω)
      have hfp := hfollowing ω (s + 1) hprev
      have hf := hfollowing ω s (by omega)
      have hno := hfp s (Nat.lt_succ_self s)
      unfold robustCrossed at hno
      have hcap := le_of_not_gt hno
      have he := (abs_le.mp (hest ω hω s ht hf)).1
      have hr := (abs_le.mp (hrec ω hω s ht)).2
      have hmono := robustPrefixThreshold_mono hK hT (by omega : 1 ≤ s + 1)
        (by omega : s + 1 ≤ T) ζ
      have hprevR : swapRegret (s + 1) (fun t => run.y t ω) (fun t => run.J t ω)
          ≤ 5 * (T : ℝ) * robustC K T ζ T := by
        push_cast at hcap he hr hmono
        linarith
      have hstep := swapRegret_succ_le (s := s + 1) (fun t => run.y t ω)
        (fun t => run.J t ω) (run.y_mem _ (hprev.trans_le (hnT ω)) ω)
      rw [hs]
      exact hstep.trans (add_le_add hprevR le_rfl)
  have hD (ω : Ω) :
      (∑ t ∈ Finset.range (n ω), if run.I t ω = run.J t ω then (0 : ℝ) else 1) ≤ D ω := by
    unfold D followDisagreements
    calc
      _ = ∑ t ∈ Finset.range (n ω), (run.robustFollowing t).indicator
          (fun ω => if run.I t ω = run.J t ω then (0 : ℝ) else 1) ω := by
        exact Finset.sum_congr rfl fun t ht =>
          (Set.indicator_of_mem (hfollowing ω t (Finset.mem_range.mp ht))
            (fun v => if run.I t v = run.J t v then (0 : ℝ) else 1)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (hnT ω)) fun t _ _ =>
          Set.indicator_nonneg (fun _ _ => by split <;> norm_num) _
  have hf (ω : Ω) (hω : ω ∈ E) :
      swapRegret (n ω) (fun t => run.y t ω) (fun t => run.I t ω) ≤ C + 2 * D ω ∧
      rewardLoss (n ω) (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ≤
        C + 2 * D ω := by
    obtain ⟨hs, hr⟩ := regret_le_of_disagreements (T := n ω)
      (fun t => run.y t ω) (fun t => run.I t ω) (fun t => run.J t ω)
      (fun t ht i => run.y_mem t (ht.trans_le (hnT ω)) ω i)
    exact ⟨hs.trans (by linarith [hJ ω hω, hD ω]),
      hr.trans (by linarith [hJ ω hω, hD ω, run.followDisagreements_nonneg ω])⟩
  have hDX := run.integrable_followDisagreements_and_le (by omega) (by omega) hζ
  have hdi : Integrable D P := hDX.1
  have hhi : Integrable H P := (integrable_const _).indicator hE.compl
  have hEH : ∫ ω, H ω ∂P ≤ (T : ℝ) * (T : ℝ) ^ (-2 : ℝ) := by
    change ∫ ω, Eᶜ.indicator (fun _ => (T : ℝ)) ω ∂P ≤ _
    rw [integral_indicator_const _ hE.compl, smul_eq_mul, mul_comm (T : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    change (P Eᶜ).toReal ≤ _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have bound (X : Ω → ℝ) (hXm : Measurable X) (hX : ∀ ω, |X ω| ≤ (T : ℝ))
      (hgood : ∀ ω ∈ E, X ω ≤ C + 2 * D ω) :
      ∫ ω, X ω ∂P ≤ B := by
    have hXi := integrable_of_abs_bound (P := P) hXm hX
    have hD2 : Integrable (fun ω => 2 * D ω) P := hdi.const_mul 2
    have hC2D : Integrable (fun ω => C + 2 * D ω) P :=
      (integrable_const C).add hD2
    have hx : (∫ ω, X ω ∂P) ≤ ∫ ω, (C + 2 * D ω) + H ω ∂P :=
      integral_mono hXi (hC2D.add hhi) (fun ω => by
        change X ω ≤ C + 2 * D ω + H ω
        by_cases hω : ω ∈ E
        · have hz : H ω = 0 := Set.indicator_of_notMem (not_not_intro hω) _
          rw [hz, add_zero]
          exact hgood ω hω
        · have ht : H ω = (T : ℝ) := Set.indicator_of_mem hω _
          rw [ht]
          linarith [(abs_le.mp (hX ω)).2, run.followDisagreements_nonneg ω])
    rw [integral_add hC2D hhi, integral_add (integrable_const C) hD2, integral_const_mul] at hx
    simp only [integral_const, probReal_univ, one_smul] at hx
    have hdle : ∫ ω, D ω ∂P ≤ robustEps T ζ * T := hDX.2
    dsimp [B, C]
    dsimp [C] at hx
    linarith only [hx, hdle, hEH]
  constructor
  · refine bound _ (run.measurable_qRunRewardLoss_stopped n hn hnT false false) ?_
      (fun ω hω => (hf ω hω).1)
    intro ω
    exact (rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t
      (ht.trans_le (hnT ω)) ω i)).trans (by exact_mod_cast hnT ω)
  · refine bound _ (run.measurable_qRunRewardLoss_stopped n hn hnT true false) ?_
      (fun ω hω => (hf ω hω).2)
    intro ω
    exact (rewardLoss_abs_le_rounds _ _ _ (fun t ht i => run.y_mem t
      (ht.trans_le (hnT ω)) ω i)).trans (by exact_mod_cast hnT ω)

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators Nat

namespace CalibeatBandit

theorem exp_le_quadratic {z : ℝ} (hz₁ : z ≤ 1) :
    Real.exp z ≤ 1 + z + (Real.exp 1 - 2) * z ^ 2 := by
  by_cases hz : 0 ≤ z
  swap
  · have hz₀ : z ≤ 0 := le_of_not_ge hz
    have h : Real.exp z ≤ 1 + z + z ^ 2 / 2 := by
      let f (w : ℝ) := 1 + w + w ^ 2 / 2 - Real.exp w
      have hf' (w : ℝ) : HasDerivAt f (1 + w - Real.exp w) w := by
        have hd := (((hasDerivAt_id w).const_add 1).add ((hasDerivAt_pow 2 w).div_const 2)).sub
          (Real.hasDerivAt_exp w)
        convert hd using 1 <;> first | rfl | norm_num
      have hd : Differentiable ℝ f := fun w => (hf' w).differentiableAt
      have ha : AntitoneOn f (Set.Iic 0) :=
        antitoneOn_of_deriv_nonpos (convex_Iic _) hd.continuous.continuousOn hd.differentiableOn
          (fun w _ => by rw [(hf' w).deriv]; linarith [Real.add_one_le_exp w])
      have hcompare := ha (show z ∈ Set.Iic 0 from hz₀) (show 0 ∈ Set.Iic (0 : ℝ) by simp) hz₀
      have hzero : f 0 = 0 := by norm_num [f]
      rw [hzero] at hcompare
      exact sub_nonneg.mp hcompare
    have he : (1 / 2 : ℝ) ≤ Real.exp 1 - 2 := by
      linarith [Real.quadratic_le_exp_of_nonneg (x := 1) zero_le_one]
    nlinarith only [h, mul_nonneg (sub_nonneg.mpr he) (sq_nonneg z)]
  have series (a : ℝ) : HasSum (fun n : ℕ => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp a
  have tail (a : ℝ) : (∑' n : ℕ, a ^ (n + 2) / ((n + 2)! : ℝ)) = Real.exp a - (1 + a) := by
    have h := (series a).summable.sum_add_tsum_nat_add 2
    rw [(series a).tsum_eq] at h
    norm_num [Finset.sum_range_succ] at h
    linarith
  have htail :
      (∑' n : ℕ, z ^ (n + 2) / ((n + 2)! : ℝ)) ≤
        ∑' n : ℕ, z ^ 2 * (1 ^ (n + 2) / ((n + 2)! : ℝ)) := by
    apply Summable.tsum_le_tsum
    · intro n
      simp only [one_pow, mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [pow_add, mul_comm (z ^ n)]
      exact mul_le_of_le_one_right (sq_nonneg z) (pow_le_one₀ hz hz₁)
    · exact (summable_nat_add_iff 2).2 (series z).summable
    · exact ((summable_nat_add_iff 2).2 (series 1).summable).mul_left _
  rw [tsum_mul_left, tail z, tail 1] at htail
  nlinarith only [htail]

/-- Equation (C.5) in *Calibeating Bandit Advice*. The two inequalities bound
the log-moment by a quadratic in the reward estimates. -/
theorem eq_C_5 {K : ℕ} (η : ℝ) (hη : 0 < η) (x v : Fin K → ℝ) (hx : IsProbVec x)
    (hv : ∀ j, 0 ≤ η * v j ∧ η * v j ≤ 1) :
    1 / η * Real.log (∑ j, x j * Real.exp (η * v j)) - x ⬝ᵥ v
        ≤ 1 / η * Real.log (1 + η * (x ⬝ᵥ v) + (Real.exp 1 - 2) * η ^ 2 * ∑ j, x j * v j ^ 2)
          - x ⬝ᵥ v ∧
    1 / η * Real.log (1 + η * (x ⬝ᵥ v) + (Real.exp 1 - 2) * η ^ 2 * ∑ j, x j * v j ^ 2)
          - x ⬝ᵥ v
        ≤ (Real.exp 1 - 2) * η * ∑ j, x j * v j ^ 2 := by
  obtain ⟨hx₀, hx₁⟩ := hx
  have hsome : ∃ j, 0 < x j := by
    by_contra! h
    have hsum : ∑ j, x j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hx₀ j)
    linarith
  obtain ⟨j, hj⟩ := hsome
  have hmoment : 0 < ∑ j, x j * Real.exp (η * v j) := by
    exact (mul_pos hj (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun j _ => mul_nonneg (hx₀ j) (Real.exp_nonneg _)) (Finset.mem_univ j))
  have hbound : (∑ j, x j * Real.exp (η * v j)) ≤
      1 + η * (x ⬝ᵥ v) + (Real.exp 1 - 2) * η ^ 2 * ∑ j, x j * v j ^ 2 := by
    calc
      _ ≤ ∑ j, x j * (1 + η * v j + (Real.exp 1 - 2) * (η * v j) ^ 2) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (exp_le_quadratic (hv j).2) (hx₀ j)
      _ = ∑ j, (x j + η * (x j * v j) +
          ((Real.exp 1 - 2) * η ^ 2) * (x j * v j ^ 2)) := by
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx₁, dotProduct]
  have hlog := Real.log_le_log hmoment hbound
  have hquad := Real.log_le_sub_one_of_pos (hmoment.trans_le hbound)
  constructor
  · exact sub_le_sub_right (mul_le_mul_of_nonneg_left hlog (by positivity)) _
  · rw [one_div, ← div_eq_inv_mul, sub_le_iff_le_add, div_le_iff₀ hη]
    nlinarith only [hquad]

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit

theorem secondMoment_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : DrawRun K T P) (t : ℕ) (ht : t < T)
    (x : Ω → Fin K → ℝ) (hx : ∀ ω, IsProbVec (x ω)) (hxm : Measurable[run.preDraw t] x)
    (hplay : run.played t =ᵐ[P] fun ω => explore μ (x ω)) :
    let v := fun ω => estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω)
    let p := fun ω => explore μ (x ω)
    condExp (run.preDraw t) P (fun ω => ∑ j, x ω j * v ω j ^ 2)
      =ᵐ[P] (fun ω => ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j)) ∧
    (∀ ω, ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j) ≤ 2 * ∑ j, x ω j / p ω j) ∧
    (∀ ω, 2 * ∑ j, x ω j / p ω j ≤ 2 * K / (1 - μ)) := by
  intro v' p'
  classical
  let x' := x
  let x (j : Fin K) (ω : Ω) := x' ω j
  let p (j : Fin K) (ω : Ω) := p' ω j
  let y (j : Fin K) (ω : Ω) := run.y t ω j
  let v (j : Fin K) (ω : Ω) := v' ω j
  let d := (Real.exp 1 - 2) * η
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hm := run.preDraw_le_ambient ht
  have hx₀ (j : Fin K) (ω : Ω) : 0 ≤ x j ω := (hx ω).1 j
  have hx₁ (j : Fin K) (ω : Ω) : x j ω ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hx₀ k ω) (Finset.mem_univ j)).trans_eq (hx ω).2
  have hμ₁ : μ ≤ 1 := by linarith
  have hp_eq (j : Fin K) (ω : Ω) : p j ω = (1 - μ) * x j ω + μ / K := rfl
  have hp₀ (j : Fin K) (ω : Ω) : μ / (K : ℝ) ≤ p j ω := by
    rw [hp_eq]
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hμ₁) (hx₀ j ω))
  have hp_pos (j : Fin K) (ω : Ω) : 0 < p j ω := (div_pos hμ0 hk).trans_le (hp₀ j ω)
  have hp_eta (j : Fin K) (ω : Ω) : 4 * η ≤ p j ω :=
    ((le_div_iff₀ hk).mpr (by nlinarith only [hKη])).trans (hp₀ j ω)
  have hη₈ : η ≤ 1 / 8 := by
    have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hd₀ : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hd₁ : d ≤ η := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three]) hη.le]
  let indicator (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  let a (j : Fin K) (ω : Ω) := x j ω * (y j ω ^ 2 + 2 * d * y j ω) / p j ω ^ 2
  let b (j : Fin K) (ω : Ω) := x j ω * d ^ 2 / p j ω ^ 2
  have hxm (j : Fin K) : Measurable[run.preDraw t] (x j) :=
    (measurable_pi_apply j).comp hxm
  have hym (j : Fin K) : Measurable[run.preDraw t] (y j) :=
    (measurable_pi_apply j).comp (run.y_measurable t ht)
  have hpm (j : Fin K) : Measurable[run.preDraw t] (p j) := by
    simp only [show p j = (fun ω => (1 - μ) * x j ω + μ / K) from funext (hp_eq j)]
    exact ((hxm j).const_mul _).add measurable_const
  have ham (j : Fin K) : Measurable[run.preDraw t] (a j) :=
    ((hxm j).mul (((hym j).pow_const 2).add ((hym j).const_mul _))).div ((hpm j).pow_const 2)
  have hbm (j : Fin K) : Measurable[run.preDraw t] (b j) :=
    ((hxm j).mul_const _).div ((hpm j).pow_const 2)
  have him (j : Fin K) : Measurable (indicator j) :=
    measurable_const.indicator ((run.I_measurable t ht).mono
      (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  let B : ℝ := (1 + 2 * d + d ^ 2) / (μ / K) ^ 2
  have hbnd (j : Fin K) (ω : Ω) : 0 ≤ a j ω ∧ 0 ≤ b j ω ∧ a j ω + b j ω ≤ B := by
    have hy := run.y_mem t ht ω j
    have hy₀ : 0 ≤ y j ω := hy.1
    have hy₁ : y j ω ≤ 1 := hy.2
    have hN : y j ω ^ 2 + 2 * d * y j ω + d ^ 2 ≤ 1 + 2 * d + d ^ 2 := by
      nlinarith [mul_nonneg hy₀ (sub_nonneg.mpr hy₁), mul_nonneg hd₀ (sub_nonneg.mpr hy₁)]
    have hx : 0 ≤ x j ω := hx₀ j ω
    refine ⟨by dsimp [a]; positivity, by dsimp [b]; positivity, ?_⟩
    dsimp [a, b, B]
    rw [← add_div, ← mul_add]
    apply div_le_div₀ (by positivity) _ (sq_pos_of_pos (div_pos hμ0 hk))
    · exact pow_le_pow_left₀ (div_nonneg hμ0.le hk.le) (hp₀ j ω) 2
    · exact (mul_le_of_le_one_left (by positivity) (hx₁ j ω)).trans hN
  have hi01 (j : Fin K) (ω : Ω) : 0 ≤ indicator j ω ∧ indicator j ω ≤ 1 := by
    by_cases h : run.I t ω = j <;> simp [indicator, h]
  have hpart (j : Fin K) : Integrable (a j * indicator j) P := by
    apply (integrable_const B).mono' (((ham j).mono hm le_rfl).mul (him j)).aestronglyMeasurable
    filter_upwards with ω
    obtain ⟨ha, hb, hab⟩ := hbnd j ω
    change ‖a j ω * indicator j ω‖ ≤ B
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha (hi01 j ω).1)]
    exact (mul_le_of_le_one_right ha (hi01 j ω).2).trans (by linarith)
  have hbint (j : Fin K) : Integrable (b j) P := by
    apply (integrable_const B).mono' ((hbm j).mono hm le_rfl).aestronglyMeasurable
    filter_upwards with ω
    obtain ⟨ha, hb, hab⟩ := hbnd j ω
    rw [Real.norm_eq_abs, abs_of_nonneg hb]
    linarith
  have hiint (j : Fin K) : Integrable (indicator j) P := by
    apply (integrable_const (1 : ℝ)).mono' (him j).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hi01 j ω).1] using (hi01 j ω).2
  have hexpand (j : Fin K) (ω : Ω) :
      x j ω * v j ω ^ 2 = a j ω * indicator j ω + b j ω := by
    have hv : v j ω = (if run.I t ω = j then run.obs t ω / p j ω else 0) + d / p j ω := rfl
    rw [hv]
    by_cases h : run.I t ω = j
    · have hind : indicator j ω = 1 := by simp [indicator, h]
      have hobs : run.obs t ω = y j ω := by simp [DrawRun.obs, y, h]
      rw [if_pos h, hind, hobs, mul_one]
      dsimp [a, b]
      field_simp [(hp_pos j ω).ne']
      ring
    · have hind : indicator j ω = 0 := by simp [indicator, h]
      rw [if_neg h, hind, zero_add, mul_zero, zero_add]
      dsimp [b]
      rw [div_pow, mul_div_assoc]
  have hcond (j : Fin K) :
      condExp (run.preDraw t) P (fun ω => x j ω * v j ω ^ 2) =ᵐ[P] fun ω =>
        x j ω / p j ω * (y j ω ^ 2 + 2 * (Real.exp 1 - 2) * η * y j ω +
          (Real.exp 1 - 2) ^ 2 * η ^ 2 / p j ω) := by
    rw [show (fun ω => x j ω * v j ω ^ 2) = a j * indicator j + b j from funext (hexpand j)]
    refine (condExp_add (hpart j) (hbint j) (run.preDraw t)).trans ?_
    rw [condExp_of_stronglyMeasurable hm (hbm j).stronglyMeasurable (hbint j)]
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (ham j).stronglyMeasurable (hpart j) (hiint j),
      run.I_law t ht j, hplay] with ω hmul hlaw hpω
    change condExp (run.preDraw t) P (a j * indicator j) ω + b j ω = _
    change condExp (run.preDraw t) P (indicator j) ω = run.played t ω j at hlaw
    rw [hpω] at hlaw
    change condExp (run.preDraw t) P (indicator j) ω = p j ω at hlaw
    rw [hmul]
    change a j ω * condExp (run.preDraw t) P (indicator j) ω + b j ω = _
    rw [hlaw]
    dsimp [a, b, d]
    field_simp [(hp_pos j ω).ne']
  constructor
  · have hi (j : Fin K) : Integrable (fun ω => x j ω * v j ω ^ 2) P := by
      rw [show (fun ω => x j ω * v j ω ^ 2) = a j * indicator j + b j from funext (hexpand j)]
      exact (hpart j).add (hbint j)
    rw [show (fun ω => ∑ j, x j ω * v j ω ^ 2) = ∑ j, (fun ω => x j ω * v j ω ^ 2) by
      ext ω; simp [Finset.sum_apply]]
    refine (condExp_finsetSum (fun j _ => hi j) (run.preDraw t)).trans ?_
    have hall := ae_all_iff.mpr hcond
    filter_upwards [hall] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hω j
  constructor
  · intro ω
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hy := run.y_mem t ht ω j
    have hy₀ : 0 ≤ y j ω := hy.1
    have hy₁ : y j ω ≤ 1 := hy.2
    have hdiv : d ^ 2 / p j ω ≤ η / 4 := by
      apply (div_le_iff₀ (hp_pos j ω)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hd₁) (show 0 ≤ η + d by positivity),
        mul_nonneg hη.le (sub_nonneg.mpr (hp_eta j ω))]
    have hterm : y j ω ^ 2 + 2 * d * y j ω + d ^ 2 / p j ω ≤ 2 := by
      nlinarith [mul_nonneg hy₀ (sub_nonneg.mpr hy₁), mul_nonneg hd₀ (sub_nonneg.mpr hy₁)]
    change x j ω / p j ω * (y j ω ^ 2 + 2 * (Real.exp 1 - 2) * η * y j ω +
      (Real.exp 1 - 2) ^ 2 * η ^ 2 / p j ω) ≤ 2 * (x j ω / p j ω)
    simpa only [d, mul_pow, mul_assoc, mul_comm (2 : ℝ) (x j ω / p j ω)] using
      (mul_le_mul_of_nonneg_left hterm (div_nonneg (hx₀ j ω) (hp_pos j ω).le))
  · intro ω
    have hden : 0 < 1 - μ := by linarith
    have hratio (j : Fin K) : x j ω / p j ω ≤ 1 / (1 - μ) := by
      apply (div_le_div_iff₀ (hp_pos j ω) hden).mpr
      rw [hp_eq]
      nlinarith [div_nonneg hμ0.le hk.le]
    have hsum : ∑ j, x j ω / p j ω ≤ (K : ℝ) / (1 - μ) := by
      calc
        _ ≤ ∑ _ : Fin K, (1 / (1 - μ)) := Finset.sum_le_sum fun j _ => hratio j
        _ = _ := by simp [div_eq_mul_inv]
    change 2 * (∑ j, x j ω / p j ω) ≤ 2 * (K : ℝ) / (1 - μ)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- **(C.6): the conditional second moment of the corrected estimates** (§C.2, proof of
Lemma C.3, p.34). In every run of the bandit calibeating algorithm under the hypotheses of
Theorem 3.2, for every round `t`, with `𝒪_{t−1}` the information immediately before `I_t` is sampled,
`E[∑_j x_t(j) v_t(j)² | 𝒪_{t−1}] = ∑_j (x_t(j)/p_t(j)) (y_t(j)² + 2(e − 2)ηy_t(j) + (e − 2)²η²/p_t(j))
  ≤ 2 ∑_j x_t(j)/p_t(j) ≤ 2K/(1 − μ)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.6), p.34.

**Formalization Note.** The hypotheses are those of Theorem 3.2: `K ≥ 1`, learning rate `η > 0`, `0 < μ ≤ 1/2`,
`μ ≥ 4Kη`; `run` is any run of the §2.1 protocol driven by the bandit calibeating algorithm.
`x_t`, `p_t`, `v_t` are `run.algX`, `run.algP`, `run.algV` (the algorithm's quantities along the
realized history); `E` is the Bochner integral against `P`. Rounds are `0, …, T − 1`; `log` is
`Real.log`, `e` is `Real.exp 1`; the maximum over all `f : Fin K → Fin K` is `Finset.sup'`. `𝒪_{t−1}` is `run.preDraw t = info t ⊔ σ(J_t)` (p.31: "all
information immediately before sampling I_t"); the equality holds `P`-almost surely, the two
inequalities for every outcome. -/
theorem eq_C_6 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) (t : ℕ) (ht : t < T) :
    condExp (run.preDraw t) P (fun ω => ∑ j, run.algX η μ t ω j * run.algV η μ t ω j ^ 2)
      =ᵐ[P] (fun ω => ∑ j, run.algX η μ t ω j / run.algP η μ t ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / run.algP η μ t ω j)) ∧
    (∀ ω, ∑ j, run.algX η μ t ω j / run.algP η μ t ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / run.algP η μ t ω j) ≤ 2 * ∑ j, run.algX η μ t ω j / run.algP η μ t ω j) ∧
    (∀ ω, 2 * ∑ j, run.algX η μ t ω j / run.algP η μ t ω j ≤ 2 * K / (1 - μ)) :=
  secondMoment_of_played_eq hK hη hμ0 hμ hKη P run.toDrawRun t ht (run.algX η μ t)
    (run.algX_prob η μ t) (run.algX_measurable η μ ht) (ae_of_all _ fun _ => rfl)

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

/-- **(C.1): the mixing learner's `SR` feedback telescopes** (§C.2, proof of Lemma C.3,
p.32). For the bandit calibeating algorithm with learning rate `η > 0` and every history,
`∑_{t=1}^T H^SR_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T x_t(i) v_t(j)))`,
and likewise
`∑_{t=1}^T H^Rec_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T 1{J_t = i} v_t(j)))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.1), p.32; the `Rec` identity is the "similar" analysis of the
second term of Lemma C.3 (p.32).

**Formalization Note.** `algHSR`, `algHRec`, `algX`, `algV` are the algorithm's `H^SR_t`,
`H^Rec_t`, `x_t`, `v_t` computed from the learner's observations `J`, `I` and observed rewards
`r` (any sequences); rounds are `0, …, T − 1`; `log` is `Real.log`. The identity is exact for every
history and every exploration parameter `μ`. The second conjunct is the `Rec` analogue that the
paper uses without displaying it. -/
theorem eq_C_1 {K : ℕ} (η μ : ℝ) (_hη : 0 < η) (J I : ℕ → Fin K) (r : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, algHSR η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, algX η μ J I r t i * algV η μ J I r t j)) ∧
    ∑ t ∈ Finset.range T, algHRec η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, (if J t = i then algV η μ J I r t j else 0))) := by
  let S := algState η μ J I r
  let x := algX η μ J I r
  let v := algV η μ J I r
  have stateSR (t : ℕ) (i j : Fin K) :
      (S t).cumSR i j = ∑ u ∈ Finset.range t, x u i * v u j := by
    induction t with
    | zero => simp [S, algState, LearnerState.init]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  have stateRec (t : ℕ) (i j : Fin K) :
      (S t).cumRec i j = ∑ u ∈ Finset.range t, (if J u = i then v u j else 0) := by
    induction t with
    | zero => simp [S, algState, LearnerState.init]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  have telescopes (g : ℕ → Fin K → ℝ) (t : ℕ) :
      ∑ u ∈ Finset.range t, (logPartition η (g (u + 1)) - logPartition η (g u)) =
        logPartition η (g t) - logPartition η (g 0) := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, ih]; ring
  have initial (i : Fin K) : logPartition η (fun _ : Fin K => 0) = 0 := by
    have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
    simp [logPartition, hK]
  have hSR (t : ℕ) :
      algHSR η μ J I r t = 1 / η * ∑ i,
        (logPartition η ((S (t + 1)).cumSR i) - logPartition η ((S t).cumSR i)) := by
    unfold algHSR HSRof
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change Real.log (∑ j, FewExperts.hedgeWeights η ((S t).cumSR i) j *
        Real.exp (η * x t i * v t j)) =
      logPartition η (fun j => (S t).cumSR i j + x t i * v t j) -
        logPartition η ((S t).cumSR i)
    simpa only [mul_assoc] using logPartition_step i η ((S t).cumSR i) (fun j => x t i * v t j)
  have hRec (t : ℕ) :
      algHRec η μ J I r t = 1 / η * ∑ i,
        (logPartition η ((S (t + 1)).cumRec i) - logPartition η ((S t).cumRec i)) := by
    unfold algHRec HRecOf
    congr 1
    symm
    rw [Finset.sum_eq_single (s := Finset.univ)
      (f := fun i => logPartition η ((S (t + 1)).cumRec i) - logPartition η ((S t).cumRec i)) (J t)]
    · change logPartition η (fun j => (S t).cumRec (J t) j + if J t = J t then v t j else 0) -
        logPartition η ((S t).cumRec (J t)) = Real.log
          (∑ j, FewExperts.hedgeWeights η ((S t).cumRec (J t)) j * Real.exp (η * v t j))
      simpa only [if_true] using (logPartition_step (J t) η ((S t).cumRec (J t)) (v t)).symm
    · intro i _ hi
      change logPartition η (fun j => (S t).cumRec i j + if J t = i then v t j else 0) -
        logPartition η ((S t).cumRec i) = 0
      simp [Ne.symm hi]
    · simp
  constructor
  · simp_rw [hSR, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [telescopes (fun t => (S t).cumSR i) T, show (S 0).cumSR i = (fun _ => 0) from rfl,
        initial i, sub_zero]
      simp only [logPartition, stateSR, x, v]
  · simp_rw [hRec, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [telescopes (fun t => (S t).cumRec i) T, show (S 0).cumRec i = (fun _ => 0) from rfl,
        initial i, sub_zero]
      simp only [logPartition, stateRec, v]

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

/-- **(C.3): the mixing step** (§C.2, proof of Lemma C.3, pp.33–34). Let `M^SR`, `M^Rec` be
column-stochastic, `λ ∈ [0, 1]`, `x ∈ Δ(𝒜)` a solution of (3.1)
`(I − λM^SR) x = (1 − λ) M^Rec e_J`, `η > 0` and `v` any real vector, and let
`H^SR = (1/η) ∑_i log(∑_j m^SR_i(j) exp(η x(i) v(j)))`, `H^Rec = (1/η) log(∑_j m^Rec_J(j) exp(η v(j)))`.
Then
`λ exp(ηH^SR) + (1 − λ) exp(ηH^Rec) ≤ ∑_j (λ(M^SR x)(j) + (1 − λ)(M^Rec e_J)(j)) exp(ηv(j))
  = ∑_j x(j) exp(ηv(j))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.3), p.34 (the claim stated on p.33).

**Formalization Note.** The printed middle term has `(M^Rec_t)(j)`; the line above it on p.34
derives the bound with `(M^Rec_t e_{J_t})(j)`, which is what is stated. The paper states the
claim for the algorithm's round-`t` quantities; it is stated here for all inputs satisfying the
hypotheses its proof uses. `m^a_i(j)` is the matrix entry `M j i`. -/
theorem eq_C_3 {K : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam0 : 0 ≤ lam) (_hlam1 : lam ≤ 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) (x v : Fin K → ℝ) (hx : IsProbVec x)
    (hfix : (1 - lam • MSR) *ᵥ x = (1 - lam) • (MRec *ᵥ Pi.single J 1)) :
    lam * Real.exp (η * HSRof η MSR x v) + (1 - lam) * Real.exp (η * HRecOf η MRec J v)
        ≤ ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j)
            * Real.exp (η * v j) ∧
    ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j) * Real.exp (η * v j)
        = ∑ j, x j * Real.exp (η * v j) := by
  have logArg_pos (p : Fin K → ℝ) (hp : IsProbVec p) (a : ℝ) :
      0 < ∑ j, p j * Real.exp (a * v j) := by
    have hsome : ∃ j, 0 < p j := by
      by_contra! h
      have hsum : ∑ j, p j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hp.1 j)
      linarith [hp.2]
    obtain ⟨j, hj⟩ := hsome
    exact (mul_pos hj (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun k _ => mul_nonneg (hp.1 k) (Real.exp_nonneg _)) (Finset.mem_univ j))
  let z : Fin K → ℝ := fun i => ∑ j, MSR j i * Real.exp (η * v j)
  have hz (i : Fin K) : 0 < z i := logArg_pos _ (hSR i) η
  have hxone (i : Fin K) : x i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans_eq hx.2
  have hpow (i : Fin K) :
      (∑ j, MSR j i * Real.exp (η * x i * v j)) ≤ z i ^ x i := by
    have h := (Real.concaveOn_rpow (hx.1 i) (hxone i)).le_map_sum
      (t := Finset.univ) (w := fun j => MSR j i) (p := fun j => Real.exp (η * v j))
      (fun j _ => (hSR i).1 j) (hSR i).2
      (fun j _ => show Real.exp (η * v j) ∈ Set.Ici 0 from Real.exp_nonneg _)
    simpa only [smul_eq_mul, ← Real.exp_mul, show ∀ j, η * v j * x i = η * x i * v j by
      intro j; ring, z] using h
  have hSR_exp : Real.exp (η * HSRof η MSR x v) ≤
      ∑ j, (MSR *ᵥ x) j * Real.exp (η * v j) := by
    unfold HSRof
    rw [show η * (1 / η * ∑ i, Real.log (∑ j, MSR j i * Real.exp (η * x i * v j))) =
        ∑ i, Real.log (∑ j, MSR j i * Real.exp (η * x i * v j)) by field_simp]
    rw [Real.exp_sum]
    simp_rw [Real.exp_log (logArg_pos _ (hSR _) _)]
    calc
      _ ≤ ∏ i, z i ^ x i :=
        Finset.prod_le_prod (fun i _ => (logArg_pos _ (hSR i) _).le) (fun i _ => hpow i)
      _ ≤ ∑ i, x i * z i :=
        Real.geom_mean_le_arith_mean_weighted Finset.univ x z (fun i _ => hx.1 i) hx.2
          (fun i _ => (hz i).le)
      _ = _ := by
        simp only [z, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hRec_exp : Real.exp (η * HRecOf η MRec J v) =
      ∑ j, (MRec *ᵥ Pi.single J 1) j * Real.exp (η * v j) := by
    unfold HRecOf
    rw [show η * (1 / η * Real.log (∑ j, MRec j J * Real.exp (η * v j))) =
        Real.log (∑ j, MRec j J * Real.exp (η * v j)) by field_simp]
    rw [Real.exp_log (logArg_pos _ (hRec J) η), mulVec_single_one]
    rfl
  constructor
  · rw [hRec_exp]
    refine (add_le_add_left (mul_le_mul_of_nonneg_left hSR_exp hlam0) _).trans_eq ?_
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [sub_mulVec, one_mulVec, smul_mulVec] at hfix
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrFun hfix j
    change x j - lam * (MSR *ᵥ x) j = (1 - lam) * (MRec *ᵥ Pi.single J 1) j at h
    rw [show lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j = x j by linarith]

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

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit

private theorem integrable_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) (B : ℝ)
    (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using h ω)

theorem correction_loss_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (_hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, ∑ t ∈ Finset.range T, x t ω ⬝ᵥ (v t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) := by
  intro v
  classical
  let d := (Real.exp 1 - 2) * η
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hμ₁ : 0 < 1 - μ := by linarith
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hmin : 0 < μ / (K : ℝ) := div_pos hμ₀ hk
  let loss (t : ℕ) (j : Fin K) (ω : Ω) :=
    x t ω j * (v t ω j - run.y t ω j)
  have coordinate (t : ℕ) (ht : t < T) (j : Fin K) :
      Integrable (loss t j) P ∧ ∫ ω, loss t j ω ∂P ≤ d / (1 - μ) := by
    let x' := x
    let x : Ω → ℝ := fun ω => x' t ω j
    let p : Ω → ℝ := fun ω => explore μ (x' t ω) j
    let y : Ω → ℝ := fun ω => run.y t ω j
    let ind : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
    let a : Ω → ℝ := fun ω => x ω * y ω / p ω
    let b : Ω → ℝ := fun ω => x ω * (d / p ω - y ω)
    have hm := run.preDraw_le_ambient ht
    have hx₀ (ω : Ω) : 0 ≤ x ω := (hx t ht ω).1 j
    have hx₁ (ω : Ω) : x ω ≤ 1 :=
      (Finset.single_le_sum (fun i _ => (hx t ht ω).1 i)
        (Finset.mem_univ j)).trans_eq (hx t ht ω).2
    have hy₀ (ω : Ω) : 0 ≤ y ω := (run.y_mem t ht ω j).1
    have hy₁ (ω : Ω) : y ω ≤ 1 := (run.y_mem t ht ω j).2
    have hp_eq (ω : Ω) : p ω = (1 - μ) * x ω + μ / K := rfl
    have hp₀ (ω : Ω) : μ / (K : ℝ) ≤ p ω := by
      rw [hp_eq]
      exact le_add_of_nonneg_left (mul_nonneg hμ₁.le (hx₀ ω))
    have hp (ω : Ω) : 0 < p ω := hmin.trans_le (hp₀ ω)
    have hxm : Measurable[run.preDraw t] x :=
      (measurable_pi_apply j).comp (hxm t ht)
    have hym : Measurable[run.preDraw t] y :=
      (measurable_pi_apply j).comp (run.y_measurable t ht)
    have hpm : Measurable[run.preDraw t] p := by
      rw [funext hp_eq]
      exact (hxm.const_mul _).add measurable_const
    have ham : Measurable[run.preDraw t] a := (hxm.mul hym).div hpm
    have hbm : Measurable[run.preDraw t] b := hxm.mul ((measurable_const.div hpm).sub hym)
    have him : Measurable ind := measurable_const.indicator
      ((run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
        (measurableSet_singleton j))
    have hind (ω : Ω) : 0 ≤ ind ω ∧ ind ω ≤ 1 := by
      by_cases h : run.I t ω = j <;> simp [ind, h]
    have hii := integrable_bounded (P := P) him 1 fun ω => by
      simpa only [abs_of_nonneg (hind ω).1] using (hind ω).2
    have hai : Integrable (a * ind) P := by
      refine integrable_bounded ((ham.mono hm le_rfl).mul him) (1 / (μ / K)) fun ω => ?_
      change |a ω * ind ω| ≤ _
      have ha₀ : 0 ≤ a ω := div_nonneg (mul_nonneg (hx₀ ω) (hy₀ ω)) (hp ω).le
      rw [abs_of_nonneg (mul_nonneg ha₀ (hind ω).1)]
      refine (mul_le_of_le_one_right ha₀ (hind ω).2).trans ?_
      exact div_le_div₀ zero_le_one
        ((mul_le_of_le_one_left (hy₀ ω) (hx₁ ω)).trans (hy₁ ω)) hmin (hp₀ ω)
    have hbi : Integrable b P := by
      refine integrable_bounded (hbm.mono hm le_rfl) (d / (μ / K) + 1) fun ω => ?_
      have hdp : 0 ≤ d / p ω := div_nonneg hd (hp ω).le
      dsimp [b]
      rw [abs_mul, abs_of_nonneg (hx₀ ω)]
      refine (mul_le_of_le_one_left (abs_nonneg _) (hx₁ ω)).trans ?_
      exact (abs_sub _ _).trans (add_le_add
        (by rw [abs_of_nonneg hdp]; exact div_le_div₀ hd le_rfl hmin (hp₀ ω))
        (by rw [abs_of_nonneg (hy₀ ω)]; exact hy₁ ω))
    have heq : loss t j = a * ind + b := by
      funext ω
      have hv : v t ω j =
          (if run.I t ω = j then run.obs t ω / p ω else 0) + d / p ω := rfl
      change x ω * (v t ω j - y ω) = a ω * ind ω + b ω
      rw [hv]
      by_cases h : run.I t ω = j
      · have hind₁ : ind ω = 1 := by simp [ind, h]
        have hobs : run.obs t ω = y ω := by simp [DrawRun.obs, y, h]
        rw [if_pos h, hind₁, hobs]
        dsimp [a, b]
        ring
      · have hind₀ : ind ω = 0 := by simp [ind, h]
        rw [if_neg h, hind₀]
        simp [b]
    refine ⟨heq ▸ hai.add hbi, ?_⟩
    have hcond : condExp (run.preDraw t) P (loss t j) =ᵐ[P] fun ω => d * (x ω / p ω) := by
      rw [heq]
      refine (condExp_add hai hbi (run.preDraw t)).trans ?_
      rw [condExp_of_stronglyMeasurable hm hbm.stronglyMeasurable hbi]
      filter_upwards [condExp_mul_of_stronglyMeasurable_left ham.stronglyMeasurable hai hii,
        run.I_law t ht j, hplay t ht] with ω hmul hlaw hpω
      change condExp (run.preDraw t) P ind ω = run.played t ω j at hlaw
      rw [hpω] at hlaw
      change condExp (run.preDraw t) P ind ω = p ω at hlaw
      change condExp (run.preDraw t) P (a * ind) ω + b ω = _
      rw [hmul]
      change a ω * condExp (run.preDraw t) P ind ω + b ω = _
      rw [hlaw]
      dsimp [a, b]
      field_simp [(hp ω).ne']
      ring
    rw [← integral_condExp (m := run.preDraw t) hm]
    calc
      _ ≤ ∫ _ : Ω, d / (1 - μ) ∂P := by
        refine integral_mono_ae integrable_condExp (integrable_const _) ?_
        filter_upwards [hcond] with ω hω
        rw [hω, ← mul_one_div d]
        apply mul_le_mul_of_nonneg_left _ hd
        apply (div_le_div_iff₀ (hp ω) hμ₁).mpr
        rw [hp_eq, one_mul]
        linarith
      _ = _ := by simp
  have hfunction : (fun ω => ∑ t ∈ Finset.range T,
      x t ω ⬝ᵥ (v t ω - run.y t ω)) =
      fun ω => ∑ t ∈ Finset.range T, ∑ j, loss t j ω := by
    funext ω
    simp only [dotProduct, Pi.sub_apply, loss]
  rw [hfunction]
  rw [integral_finsetSum (Finset.range T)
    (f := fun t ω => ∑ j, loss t j ω) (fun t ht => integrable_finsetSum _ fun j _ =>
      (coordinate t (Finset.mem_range.mp ht) j).1)]
  calc
    _ ≤ ∑ _ ∈ Finset.range T, ∑ _ : Fin K, d / (1 - μ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [integral_finsetSum _ fun j _ => (coordinate t (Finset.mem_range.mp ht) j).1]
      exact Finset.sum_le_sum fun j _ => (coordinate t (Finset.mem_range.mp ht) j).2
    _ = _ := by simp [d, div_eq_mul_inv]; ring

/-- Lemma C.5. The importance-weighted estimate has conditional mean equal to
the reward, leaving only the explicit correction in expectation. -/
theorem lemma_C_5 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (_hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, ∑ t ∈ Finset.range T, run.algX η μ t ω ⬝ᵥ (run.algV η μ t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) :=
  correction_loss_of_played_eq hK hη hμ₀ hμ _hKη P run.toDrawRun (run.algX η μ)
    (fun t _ => run.algX_prob η μ t) (fun _ ht => run.algX_measurable η μ ht)
    (fun _ _ => ae_of_all _ fun _ => rfl)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

/-- A one-round exponential bound for the corrected estimate of a fixed action.
The two terms are the events that the learner plays or does not play that action. -/
theorem corrected_estimate_exp_le_one {η p y : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hp : 0 < p) (hp₁ : p ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    let d := (Real.exp 1 - 2) * η
    p * Real.exp (η * (y - (y + d) / p)) +
      (1 - p) * Real.exp (η * (y - d / p)) ≤ 1 := by
  intro d
  let c := Real.exp 1 - 2
  let a := η * (y - y / p)
  let b := η * y
  let k := c * η ^ 2 / p
  have hc : 0 ≤ c := sub_nonneg.mpr Real.exp_one_gt_two.le
  have hb : b ≤ 1 := (mul_le_of_le_one_right hη hy₁).trans hη₁
  have ha : a ≤ 1 := (mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg hy hp.le)) hη).trans hb
  have hmean : p * a + (1 - p) * b = 0 := by
    dsimp [a, b]
    field_simp [hp.ne']
    ring
  have hsq : p * a ^ 2 + (1 - p) * b ^ 2 ≤ η ^ 2 / p := by
    have heq : p * a ^ 2 + (1 - p) * b ^ 2 = η ^ 2 * y ^ 2 * (1 - p) / p := by
      dsimp [a, b]
      field_simp [hp.ne']
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ hp.le
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hy₁)]
    have ht : y ^ 2 * (1 - p) ≤ 1 :=
      (mul_le_of_le_one_right (sq_nonneg y) (by linarith)).trans hy2
    simpa only [mul_assoc] using mul_le_of_le_one_right (sq_nonneg η) ht
  have htwo : p * Real.exp a + (1 - p) * Real.exp b ≤ 1 + k := by
    have hca := mul_le_mul_of_nonneg_left (exp_le_quadratic ha) hp.le
    have hcb := mul_le_mul_of_nonneg_left (exp_le_quadratic hb) (sub_nonneg.mpr hp₁)
    have hcs := mul_le_mul_of_nonneg_left hsq hc
    dsimp [k]
    rw [← mul_div_assoc] at hcs
    nlinarith only [hca, hcb, hmean, hcs]
  have ha_eq : η * (y - (y + d) / p) = -k + a := by
    dsimp [d, k, c, a]
    ring
  have hb_eq : η * (y - d / p) = -k + b := by
    dsimp [d, k, c, b]
    ring
  rw [ha_eq, hb_eq, Real.exp_add, Real.exp_add]
  calc
    _ = Real.exp (-k) * (p * Real.exp a + (1 - p) * Real.exp b) := by ring
    _ ≤ Real.exp (-k) * (1 + k) := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ ≤ Real.exp (-k) * Real.exp k := by
      exact mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp k)
        (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

set_option maxHeartbeats 650000 in
/-- The per-round conditional exponential bound for a weighted post-processing
rule. The weights may be selected using the information available before the draw. -/
theorem condExp_estimation_step_of_played_eq {K T : ℕ} {ι : Type*} [Fintype ι] {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) {t : ℕ} (ht : t < T)
    (x : Ω → Fin K → ℝ) (hx : ∀ ω, IsProbVec (x ω))
    (hxm : Measurable[run.preDraw t] x)
    (hplay : run.played t =ᵐ[P] fun ω => explore μ (x ω))
    (f : ι → Fin K) (w : Ω → ι → ℝ) (hw₀ : ∀ ω i, 0 ≤ w ω i)
    (hw : ∀ ω, ∑ i, w ω i = 1)
    (hwm : Measurable[run.preDraw t] w) :
    condExp (run.preDraw t) P (fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω) (f i)))) ≤ᵐ[P] fun _ => 1 := by
  classical
  let p (ω : Ω) := explore μ (x ω)
  let y (ω : Ω) := run.y t ω
  let d := (Real.exp 1 - 2) * η
  let g (j : Fin K) (ω : Ω) := Real.exp (η * ∑ i, w ω i *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i))))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₁ : η ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hμ₁ : μ ≤ 1 := by linarith
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hp (ω : Ω) : IsProbVec (p ω) := explore_prob hK hμ₀.le hμ₁ (hx ω)
  have hp₀ (ω : Ω) (j : Fin K) : 0 < p ω j :=
    (div_pos hμ₀ hk).trans_le
      (le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hμ₁) ((hx ω).1 j)))
  have hp₁ (ω : Ω) (j : Fin K) : p ω j ≤ 1 :=
    (Finset.single_le_sum (fun i _ => (hp ω).1 i) (Finset.mem_univ j)).trans_eq (hp ω).2
  have hy (ω : Ω) (j : Fin K) : y ω j ∈ Set.Icc (0 : ℝ) 1 := run.y_mem t ht ω j
  have hmY (j : Fin K) : Measurable[run.preDraw t] (fun ω => y ω j) :=
    (measurable_pi_apply j).comp (run.y_measurable t ht)
  have hmP (j : Fin K) : Measurable[run.preDraw t] (fun ω => p ω j) :=
    (((measurable_pi_apply j).comp hxm).const_mul _).add measurable_const
  have hg (j : Fin K) : Measurable[run.preDraw t] (g j) := by
    apply Real.continuous_exp.measurable.comp
    apply Measurable.const_mul
    refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hwm).mul ?_
    by_cases e : j = f i
    · simp only [e, if_true]
      exact (hmY (f i)).sub (((hmY (f i)).add measurable_const).div (hmP (f i)))
    · simp only [if_neg e]
      exact (hmY (f i)).sub (measurable_const.div (hmP (f i)))
  have hgb (j : Fin K) (ω : Ω) : |g j ω| ≤ Real.exp η := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    refine mul_le_of_le_one_right hη.le ?_
    calc
      _ ≤ ∑ i, w ω i * 1 := Finset.sum_le_sum fun i _ => by
        apply mul_le_mul_of_nonneg_left _ (hw₀ ω i)
        refine (sub_le_self _ ?_).trans (hy ω (f i)).2
        split
        · exact div_nonneg (add_nonneg (hy ω (f i)).1 hd) (hp₀ ω (f i)).le
        · exact div_nonneg hd (hp₀ ω (f i)).le
      _ = _ := by simp only [mul_one, hw ω]
  obtain ⟨_, hce⟩ := run.condExp_select_played P ht g hg _ hgb
  have hselected : (fun ω => g (run.I t ω) ω) = fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω) (f i))) := by
    funext ω
    apply congrArg Real.exp
    refine congrArg (η * ·) (Finset.sum_congr rfl fun i _ => ?_)
    dsimp [y, p]
    change w ω i * (run.y t ω (f i) - _) = w ω i * (run.y t ω (f i) -
      ((if run.I t ω = f i then run.obs t ω / p ω (f i) else 0) +
        d / p ω (f i)))
    by_cases e : run.I t ω = f i
    · simp [e, p, DrawRun.obs, add_div]
    · simp [e, p]
  rw [← hselected]
  filter_upwards [hce, hplay] with ω he hpω
  rw [he, hpω]
  change ∑ j, p ω j * g j ω ≤ 1
  let a (j : Fin K) (i : ι) := η *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i)))
  have hjensen (j : Fin K) : g j ω ≤ ∑ i, w ω i * Real.exp (a j i) := by
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := w ω) (p := a j)
      (fun i _ => hw₀ ω i) (hw ω) (fun i _ => Set.mem_univ (a j i))
    have heq : g j ω = Real.exp (∑ i, w ω i * a j i) := by
      unfold g a
      simp only [Finset.mul_sum]
      apply congrArg Real.exp
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    simpa only [smul_eq_mul] using h
  calc
    _ ≤ ∑ j, p ω j * ∑ i, w ω i * Real.exp (a j i) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hjensen j) ((hp ω).1 j)
    _ = ∑ i, w ω i * ∑ j, p ω j * Real.exp (a j i) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ i, w ω i * 1 := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw₀ ω i)
      let j := f i
      have hs : (∑ k ∈ Finset.univ.erase j, p ω k) = 1 - p ω j := by
        have h := Finset.sum_erase_add _ (fun k => p ω k) (Finset.mem_univ j)
        rw [(hp ω).2] at h
        linarith
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have hdiff : (∑ k ∈ Finset.univ.erase j, p ω k * Real.exp (a k i)) =
          (1 - p ω j) * Real.exp (η * (y ω j - d / p ω j)) := by
        rw [← hs, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hn := (Finset.mem_erase.mp hk).1
        simp [a, j, hn]
      rw [hdiff]
      have hsame : a j i = η * (y ω j - (y ω j + d) / p ω j) := by simp [a, j]
      rw [hsame, add_comm]
      exact corrected_estimate_exp_le_one hη.le hη₁ (hp₀ ω j) (hp₁ ω j) (hy ω j).1 (hy ω j).2
    _ = 1 := by simp only [mul_one, hw ω]


set_option maxHeartbeats 500000 in
/-- The estimation bound for an arbitrary finite reference set. -/
theorem estimation_loss_of_played_eq {K T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hne : (Finset.univ : Finset (ι → Fin K)).Nonempty)
    {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω))
    (w : ℕ → Ω → ι → ℝ) (hw₀ : ∀ t < T, ∀ ω i, 0 ≤ w t ω i)
    (hw : ∀ t < T, ∀ ω, ∑ i, w t ω i = 1)
    (hwm : ∀ t < T, Measurable[run.preDraw t] (w t)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, Finset.univ.sup' hne (fun f : ι → Fin K =>
      ∑ t ∈ Finset.range T, ∑ i, w t ω i * (run.y t ω (f i) - v t ω (f i))) ∂P
      ≤ Fintype.card ι * Real.log K / η := by
  intro v
  classical
  have hvb (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin K) :
      0 ≤ η * v t ω j ∧ η * v t ω j ≤ 1 :=
    estimate_scaled_mem hK hη hμ hKη (x t ω) (hx t ht ω) (run.I t ω) j
      (run.obs t ω) (run.y_mem t ht ω (run.I t ω))
  have hvm (t : ℕ) (ht : t < T) (j : Fin K) :
      Measurable[run.info (t + 1)] (fun ω => v t ω j) := by
    have hxm' := ((measurable_pi_apply j).comp (hxm t ht)).mono (run.preDraw_le_succ t ht) le_rfl
    have hp : Measurable[run.info (t + 1)] (fun ω => explore μ (x t ω) j) :=
      (hxm'.const_mul (1 - μ)).add measurable_const
    have hy : Measurable[run.info (t + 1)] (run.obs t) := by
      unfold DrawRun.obs
      exact @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ (run.I_measurable t ht)
        (fun j ω => run.y t ω j) (fun j => (measurable_pi_apply j).comp
          ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl))
    exact (Measurable.ite (run.I_measurable t ht (measurableSet_singleton j))
      (hy.div hp) measurable_const).add (measurable_const.div hp)
  let D (t : ℕ) (f : ι → Fin K) (ω : Ω) :=
    ∑ i, w t ω i * (run.y t ω (f i) - v t ω (f i))
  have hm (t : ℕ) (ht : t < T) (f : ι → Fin K) :
      Measurable[run.info (t + 1)] (D t f) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hwi := (measurable_pi_apply i).comp
      ((hwm t ht).mono (run.preDraw_le_succ t ht) le_rfl)
    have hyi := (measurable_pi_apply (f i)).comp
      ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl)
    exact hwi.mul (hyi.sub (hvm t ht (f i)))
  have hb (t : ℕ) (ht : t < T) (f : ι → Fin K) (ω : Ω) :
      |D t f ω| ≤ 1 + 1 / η := by
    calc
      _ ≤ ∑ i, |w t ω i * (run.y t ω (f i) - v t ω (f i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w t ω i * (1 + 1 / η) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw₀ := hw₀ t ht ω i
        rw [abs_mul, abs_of_nonneg hw₀]
        apply mul_le_mul_of_nonneg_left _ hw₀
        have hy := run.y_mem t ht ω (f i)
        have hv := hvb t ht ω (f i)
        have hv₀ := nonneg_of_mul_nonneg_right hv.1 hη
        have hv₁ := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hv.2)
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, div_nonneg zero_le_one hη.le]⟩
      _ = _ := by rw [← Finset.sum_mul, hw t ht ω, one_mul]
  let F (f : ι → Fin K) (ω : Ω) := ∑ t ∈ Finset.range T, D t f ω
  have hmF (f : ι → Fin K) : Measurable (F f) :=
    Finset.measurable_sum _ fun t ht =>
      (hm t (Finset.mem_range.mp ht) f).mono (run.info_le _ (Finset.mem_range.mp ht)) le_rfl
  have hbF (f : ι → Fin K) (ω : Ω) : |F f ω| ≤ T * (1 + 1 / η) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |D t f ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 + 1 / η) := Finset.sum_le_sum fun t ht =>
        hb t (Finset.mem_range.mp ht) f ω
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hE (f : ι → Fin K) : (∫ ω, Real.exp (η * F f ω) ∂P) ≤ 1 := by
    have h := run.integral_exp_sum_le_one P (fun t ω => η * D t f ω)
      (fun t ht => (hm t ht f).const_mul η)
      (fun t ht ω => show |η * D t f ω| ≤ η * (1 + 1 / η) by
        rw [abs_mul, abs_of_pos hη]
        exact mul_le_mul_of_nonneg_left (hb t ht f ω) hη.le)
      (fun t ht => condExp_estimation_step_of_played_eq hK hη hμ₀ hμ hKη P run ht
        (x t) (hx t ht) (hxm t ht) (hplay t ht) f (w t) (hw₀ t ht) (hw t ht) (hwm t ht))
    simpa only [F, Finset.mul_sum] using h
  have h := integral_max_le_log_card P hne F hη hmF hbF hE
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

theorem condExp_estimation_step {K T : ℕ} {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P (calibeatPolicy K η μ)) {t : ℕ} (ht : t < T)
    (f : Fin K → Fin K) (w : Ω → Fin K → ℝ) (hw : ∀ ω, IsProbVec (w ω))
    (hwm : Measurable[run.preDraw t] w) :
    condExp (run.preDraw t) P (fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - run.algV η μ t ω (f i)))) ≤ᵐ[P] fun _ => 1 :=
  condExp_estimation_step_of_played_eq hK hη hμ₀ hμ hKη P run.toDrawRun ht
    (run.algX η μ t) (run.algX_prob η μ t) (run.algX_measurable η μ ht)
    (ae_of_all _ fun _ => rfl) f w (fun ω => (hw ω).1) (fun ω => (hw ω).2) hwm


set_option maxHeartbeats 500000 in
/-- Lemma C.4. The expected worst estimation loss is bounded by the logarithm
of the number of post-processing rules, divided by the learning rate. -/
theorem lemma_C_4 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, ∑ i, run.algX η μ t ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))) ∂P
      ≤ K * Real.log K / η ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.y t ω (f (run.J t ω)) - run.algV η μ t ω (f (run.J t ω)))) ∂P
      ≤ K * Real.log K / η := by
  classical
  have bound (w : ℕ → Ω → Fin K → ℝ) (hw : ∀ t < T, ∀ ω, IsProbVec (w t ω))
      (hwm : ∀ t < T, Measurable[run.preDraw t] (w t)) :
      ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, ∑ i, w t ω i *
          (run.y t ω (f i) - run.algV η μ t ω (f i))) ∂P ≤ K * Real.log K / η := by
    simpa only [Fintype.card_fin, ProtocolRun.algV, CalibeatBandit.algV,
      CalibeatBandit.algP, ProtocolRun.algX, ProtocolRun.toDrawRun, DrawRun.obs,
      ProtocolRun.obs] using estimation_loss_of_played_eq
      ⟨id, Finset.mem_univ _⟩ hK hη hμ₀ hμ hKη P run.toDrawRun (run.algX η μ)
      (fun t _ => run.algX_prob η μ t) (fun _ ht => run.algX_measurable η μ ht)
      (fun _ _ => ae_of_all _ fun _ => rfl) w
      (fun t ht ω => (hw t ht ω).1) (fun t ht ω => (hw t ht ω).2) hwm
  refine ⟨bound (run.algX η μ) (fun t _ => run.algX_prob η μ t)
    (fun _ ht => run.algX_measurable η μ ht), ?_⟩
  let w (t : ℕ) (ω : Ω) : Fin K → ℝ := Pi.single (run.J t ω) 1
  have hw (t : ℕ) (ω : Ω) : IsProbVec (w t ω) := by
    constructor
    · intro i
      by_cases h : run.J t ω = i <;> simp [w, Pi.single_apply, h]
    · simp [w, Pi.single_apply]
  have hm (t : ℕ) : Measurable[run.preDraw t] (w t) := by
    have hJ : Measurable[run.preDraw t] (run.J t) := measurable_iff_comap_le.mpr le_sup_right
    have hset (i : Fin K) : MeasurableSet[run.preDraw t] {ω | i = run.J t ω} := by
      simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hJ (measurableSet_singleton i)
    let : MeasurableSpace Ω := run.preDraw t
    refine measurable_pi_iff.mpr fun i => ?_
    simpa only [w, Pi.single_apply] using
      (Measurable.ite (hset i) (measurable_const (a := (1 : ℝ))) (measurable_const (a := (0 : ℝ))))
  have h := bound w (fun t _ => hw t) (fun t _ => hm t)
  simpa [w, Pi.single_apply, Finset.sum_ite_eq', eq_comm] using h

end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix CalibeatBandit
open scoped BigOperators

/-- **The three-part decomposition of the pseudo regrets** (§C.2, p.32). Let
`p_t = (1 − μ) x_t + μ u` with `x_t ∈ Δ(𝒜)`, `u = (1/K)·𝟏`, `0 ≤ μ ≤ 1`, rewards
`y_t ∈ [0,1]^K`, arbitrary vectors `v_t` and actions `J_t`. Then
`R^{SR,p}_T ≤ μT + max_f ∑_t (∑_i x_t(i) v_t(f(i)) − ⟨x_t, v_t⟩)
  + max_f ∑_t ∑_i x_t(i)(y_t(f(i)) − v_t(f(i))) + ∑_t ⟨x_t, v_t − y_t⟩`
and
`R^{Rec,p}_T ≤ μT + max_f ∑_t (v_t(f(J_t)) − ⟨x_t, v_t⟩) + max_f ∑_t (y_t(f(J_t)) − v_t(f(J_t)))
  + ∑_t ⟨x_t, v_t − y_t⟩`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, p.32 (the two displays before Lemma C.3).

**Formalization Note.** Deterministic: the inequalities hold for every realization. The paper
states them for the algorithm's `x_t`, `v_t` with `0 < μ ≤ 1/2`; here `x`, `v`, `J` are arbitrary
(with `x_t ∈ Δ(𝒜)`) and `0 ≤ μ ≤ 1`. Rounds are `0, …, T − 1`; `p` is only constrained on
those rounds. -/
theorem decomposition_C_2_for_robust {K T : ℕ} (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (x v y p : ℕ → Fin K → ℝ) (J : ℕ → Fin K) (hx : ∀ t < T, IsProbVec (x t))
    (hy : ∀ t < T, ∀ j, y t j ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ t < T, ∀ j, p t j = (1 - μ) * x t j + μ / K) :
    pseudoSwapRegret T p y ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (∑ i, x t i * v t (f i) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, ∑ i, x t i * (y t (f i) - v t (f i)))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) ∧
    pseudoRewardLoss T p y J ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (y t (f (J t)) - v t (f (J t))))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) := by
  have p_eq (t : ℕ) (ht : t < T) :
      p t = (1 - μ) • x t + (fun _ => μ / K) := by
    ext j
    exact hp t ht j
  have uniform_le (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      ∑ i, μ / K * (y t (f i) - y t i) ≤ μ := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) fun i _ =>
      mul_le_of_le_one_right (show 0 ≤ μ / (K : ℝ) by positivity)
        (show y t (f i) - y t i ≤ 1 by linarith [(hy t ht (f i)).2, (hy t ht i).1])
    by_cases hK : K = 0
    · subst K
      simpa using hμ0
    · refine h.trans_eq ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
      field_simp
  have exploration (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      (∑ i, p t i * y t (f i)) - p t ⬝ᵥ y t ≤
        (1 - μ) * ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t) + μ := by
    have expand : (∑ i, p t i * y t (f i)) - p t ⬝ᵥ y t =
        (1 - μ) * ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t) +
          ∑ i, μ / K * (y t (f i) - y t i) := by
      simp only [p_eq t ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, add_mul,
        Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      ring_nf
    rw [expand]
    exact add_le_add_right (uniform_le t ht f) _
  have recExplore (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      y t (f (J t)) - p t ⬝ᵥ y t ≤ y t (f (J t)) - x t ⬝ᵥ y t + μ := by
    have hupper : x t ⬝ᵥ y t ≤ 1 := by
      unfold dotProduct
      refine (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ((hx t ht).1 i) (hy t ht i).2).trans_eq
        (hx t ht).2
    have hnonneg : 0 ≤ ∑ i, μ / K * y t i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hy t ht i).1
    have hexpand : p t ⬝ᵥ y t =
        (1 - μ) * (x t ⬝ᵥ y t) + ∑ i, μ / K * y t i := by
      simp only [p_eq t ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand]
    nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr hupper)]
  have sup_decompose (A B C : (Fin K → Fin K) → ℝ) (D : ℝ)
      (h : ∀ f, A f = B f + C f + D) :
      (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ A) ≤
        (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ B) +
        (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ C) + D := by
    apply Finset.sup'_le
    intro f hf
    rw [h f]
    gcongr <;> exact Finset.le_sup' _ hf
  let sr : (Fin K → Fin K) → ℝ :=
    fun f => ∑ t ∈ Finset.range T, ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t)
  let recPayoff : (Fin K → Fin K) → ℝ :=
    fun f => ∑ t ∈ Finset.range T, (y t (f (J t)) - x t ⬝ᵥ y t)
  have sr0 : 0 ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := by
    have h := Finset.le_sup' sr (Finset.mem_univ (id : Fin K → Fin K))
    simpa [sr, dotProduct] using h
  have srExplore : pseudoSwapRegret T p y ≤ μ * T + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := by
    unfold pseudoSwapRegret
    apply Finset.sup'_le
    intro f hf
    have h := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
      exploration t (Finset.mem_range.mp ht) f
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hle : sr f ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := Finset.le_sup' sr hf
    have hmul := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hμ1)
    change _ ≤ (1 - μ) * sr f + (T : ℝ) * μ at h
    nlinarith [mul_nonneg hμ0 sr0]
  have recExploreSum : pseudoRewardLoss T p y J ≤ μ * T + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ recPayoff := by
    unfold pseudoRewardLoss
    apply Finset.sup'_le
    intro f hf
    have h := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
      recExplore t (Finset.mem_range.mp ht) f
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hle : recPayoff f ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ recPayoff :=
      Finset.le_sup' recPayoff hf
    change _ ≤ recPayoff f + (T : ℝ) * μ at h
    linarith
  constructor
  · refine srExplore.trans ?_
    have h := sup_decompose sr
      (fun f => ∑ t ∈ Finset.range T, ((∑ i, x t i * v t (f i)) - x t ⬝ᵥ v t))
      (fun f => ∑ t ∈ Finset.range T, ∑ i, x t i * (y t (f i) - v t (f i)))
      (∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t)) ?_
    · linarith
    · intro f
      simp only [sr, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
  · refine recExploreSum.trans ?_
    have h := sup_decompose recPayoff
      (fun f => ∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t))
      (fun f => ∑ t ∈ Finset.range T, (y t (f (J t)) - v t (f (J t))))
      (∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t)) ?_
    · linarith
    · intro f
      simp only [recPayoff, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

private theorem abs_weighted_sum_le {K : ℕ} {p a : Fin K → ℝ}
    (hp : IsProbVec p) {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    |∑ i, p i * a i| ≤ B := by
  calc
    _ ≤ ∑ i, |p i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * B := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_nonneg (hp.1 i)]
      exact mul_le_mul_of_nonneg_left (ha i) (hp.1 i)
    _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

set_option maxHeartbeats 850000 in
/-- The two expected pseudo regrets, obtained by combining Lemmas C.3, C.4 and C.5. -/
theorem pseudo_regret_bound {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, pseudoSwapRegret T (fun t => run.algP η μ t ω) (fun t => run.y t ω) ∂P ≤ rT K T η μ ∧
    ∫ ω, pseudoRewardLoss T (fun t => run.algP η μ t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P
      ≤ rT K T η μ := by
  let x (t : ℕ) (ω : Ω) := run.algX η μ t ω
  let p (t : ℕ) (ω : Ω) := run.algP η μ t ω
  let v (t : ℕ) (ω : Ω) := run.algV η μ t ω
  let y (t : ℕ) (ω : Ω) := run.y t ω
  let B := 1 + 1 / η
  have hx (t : ℕ) (ω : Ω) : IsProbVec (x t ω) := run.algX_prob η μ t ω
  have hp (t : ℕ) (ω : Ω) : IsProbVec (p t ω) :=
    explore_prob hK hμ₀.le (by linarith) (hx t ω)
  have hxM (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (fun ω => x t ω j) :=
    (measurable_pi_apply j).comp ((run.algX_measurable η μ ht).mono (run.preDraw_le_ambient ht) le_rfl)
  have hpM (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (fun ω => p t ω j) :=
    ((hxM t ht j).const_mul _).add measurable_const
  have hvM (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (fun ω => v t ω j) :=
    (run.algV_measurable η μ ht j).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
  have hyM (t : ℕ) (ht : t < T) (j : Fin K) : Measurable (fun ω => y t ω j) :=
    (measurable_pi_apply j).comp ((run.y_measurable t ht).mono (run.info_le _ ht.le) le_rfl)
  have hJ (t : ℕ) (ht : t < T) : Measurable (run.J t) :=
    (run.J_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
  have hbV (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin K) : |v t ω j| ≤ B := by
    obtain ⟨h₀, h₁⟩ := run.algV_scaled_mem hK hη hμ hKη ht ω j
    rw [abs_of_nonneg (nonneg_of_mul_nonneg_right h₀ hη)]
    have h := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using h₁)
    dsimp [B]
    linarith
  have hbY (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin K) : |y t ω j| ≤ B := by
    obtain ⟨h₀, h₁⟩ := run.y_mem t ht ω j
    rw [abs_of_nonneg h₀]
    exact h₁.trans (le_add_of_nonneg_right (by positivity))
  have hdot (a b : Ω → Fin K → ℝ) (ha : ∀ j, Measurable (fun ω => a ω j))
      (hb : ∀ j, Measurable (fun ω => b ω j)) :
      Measurable (fun ω => a ω ⬝ᵥ b ω) :=
    Finset.measurable_sum _ fun i _ => (ha i).mul (hb i)
  have hsum (D : ℕ → Ω → ℝ) (hm : ∀ t < T, Measurable (D t))
      (hb : ∀ t < T, ∀ ω, |D t ω| ≤ B + B) :
      Measurable (fun ω => ∑ t ∈ Finset.range T, D t ω) ∧
        ∀ ω, |∑ t ∈ Finset.range T, D t ω| ≤ T * (B + B) := by
    refine ⟨Finset.measurable_sum _ fun t ht => hm t (Finset.mem_range.mp ht), fun ω => ?_⟩
    calc
      _ ≤ ∑ t ∈ Finset.range T, |D t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (B + B) := Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) ω
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  let M (D : ℕ → (Fin K → Fin K) → Ω → ℝ) (ω : Ω) :=
    Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f => ∑ t ∈ Finset.range T, D t f ω)
  have hmax (D : ℕ → (Fin K → Fin K) → Ω → ℝ)
      (hm : ∀ t < T, ∀ f, Measurable (D t f)) (hb : ∀ t < T, ∀ f ω, |D t f ω| ≤ B + B) :
      Integrable (M D) P :=
    integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T * (B + B))
      (fun f => (hsum (fun t => D t f) (fun t ht => hm t ht f) (fun t ht => hb t ht f)).1)
      (fun f => (hsum (fun t => D t f) (fun t ht => hm t ht f) (fun t ht => hb t ht f)).2)
  have hsub {a b : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B) : |a - b| ≤ B + B :=
    (abs_sub _ _).trans (add_le_add ha hb)
  have hweighted (a b : ℕ → Ω → Fin K → ℝ) (ha : ∀ t ω, IsProbVec (a t ω))
      (haM : ∀ t < T, ∀ j, Measurable (fun ω => a t ω j))
      (hbM : ∀ t < T, ∀ j, Measurable (fun ω => b t ω j))
      (hbB : ∀ t < T, ∀ ω j, |b t ω j| ≤ B) :
      Integrable (M (fun t f ω => (∑ i, a t ω i * b t ω (f i)) - a t ω ⬝ᵥ b t ω)) P := by
    apply hmax
    · intro t ht f
      exact (hdot (a t) (fun ω i => b t ω (f i)) (haM t ht) (fun i => hbM t ht (f i))).sub
        (hdot (a t) (b t) (haM t ht) (hbM t ht))
    · intro t ht f ω
      exact hsub (abs_weighted_sum_le (ha t ω) fun i => hbB t ht ω (f i))
        (abs_weighted_sum_le (ha t ω) (hbB t ht ω))
  have hrec (a b : ℕ → Ω → Fin K → ℝ) (ha : ∀ t ω, IsProbVec (a t ω))
      (haM : ∀ t < T, ∀ j, Measurable (fun ω => a t ω j))
      (hbM : ∀ t < T, ∀ j, Measurable (fun ω => b t ω j))
      (hbB : ∀ t < T, ∀ ω j, |b t ω j| ≤ B) :
      Integrable (M (fun t f ω => b t ω (f (run.J t ω)) - a t ω ⬝ᵥ b t ω)) P := by
    apply hmax
    · intro t ht f
      exact (measurable_select (hJ t ht) (fun j => hbM t ht (f j))).sub
        (hdot (a t) (b t) (haM t ht) (hbM t ht))
    · intro t ht f ω
      exact hsub (hbB t ht ω (f (run.J t ω))) (abs_weighted_sum_le (ha t ω) (hbB t ht ω))
  let L (ω : Ω) := ∑ t ∈ Finset.range T, x t ω ⬝ᵥ (v t ω - y t ω)
  have hiL : Integrable L P := by
    have h := hsum (fun t ω => x t ω ⬝ᵥ (v t ω - y t ω))
      (fun t ht => hdot (x t) (fun ω i => v t ω i - y t ω i) (hxM t ht)
        (fun i => (hvM t ht i).sub (hyM t ht i)))
      (fun t ht ω => abs_weighted_sum_le (hx t ω) (fun i => hsub (hbV t ht ω i) (hbY t ht ω i)))
    exact integrable_of_abs_bound h.1 h.2
  let S := M (fun t f ω => ∑ i, x t ω i * (y t ω (f i) - v t ω (f i)))
  have hiS : Integrable S P := by
    apply hmax
    · intro t ht f
      exact hdot (x t) (fun ω i => y t ω (f i) - v t ω (f i)) (hxM t ht)
        (fun i => (hyM t ht (f i)).sub (hvM t ht (f i)))
    · intro t ht f ω
      exact abs_weighted_sum_le (hx t ω) fun i => hsub (hbY t ht ω (f i)) (hbV t ht ω (f i))
  let R := M (fun t f ω => y t ω (f (run.J t ω)) - v t ω (f (run.J t ω)))
  have hiR : Integrable R P := by
    apply hmax
    · intro t ht f
      exact measurable_select (hJ t ht) fun j => (hyM t ht (f j)).sub (hvM t ht (f j))
    · intro t ht f ω
      exact hsub (hbY t ht ω _) (hbV t ht ω _)
  have decompose (ω : Ω) := _root_.decomposition_C_2_for_robust μ hμ₀.le (by linarith)
    (fun t => x t ω) (fun t => v t ω) (fun t => y t ω) (fun t => p t ω)
    (fun t => run.J t ω) (fun t _ => hx t ω) (fun t ht => run.y_mem t ht ω)
    (T := T) (fun _ _ _ => rfl)
  obtain ⟨hsr, hrc⟩ := lemma_C_3 hK hη hμ₀ hμ hKη P run
  obtain ⟨hes, her⟩ := lemma_C_4 hK hη hμ₀ hμ hKη P run
  have hel := lemma_C_5 hK hη hμ₀ hμ hKη P run
  let c := (Real.exp 1 - 2) * η * K * T / (1 - μ)
  let a := (K * Real.log K + Real.log 2) / η + 2 * (Real.exp 1 - 2) * η * K * T / (1 - μ)
  have hfinal : μ * T + a + K * Real.log K / η + c ≤ rT K T η μ := by
    have hm : 0 ≤ η * K * T / (1 - μ) := div_nonneg (by positivity) (by linarith)
    have he : 3 * (Real.exp 1 - 2) ≤ 5 := by linarith [Real.exp_one_lt_three]
    have h := mul_le_mul_of_nonneg_right he hm
    unfold rT
    dsimp [a, c]
    rw [add_div]
    linear_combination h
  have combine (F G H : Ω → ℝ) (hiF : Integrable F P)
      (hiG : Integrable G P) (hiH : Integrable H P)
      (hbG : (∫ ω, G ω ∂P) ≤ a) (hbH : (∫ ω, H ω ∂P) ≤ K * Real.log K / η)
      (hpoint : ∀ ω, F ω ≤ μ * T + G ω + H ω + L ω) :
      (∫ ω, F ω ∂P) ≤ rT K T η μ := by
    let C : Ω → ℝ := fun _ => μ * T
    have hiConst : Integrable C P := integrable_const _
    have hiCG : Integrable (fun ω => C ω + G ω) P := hiConst.add hiG
    have hiCGH : Integrable (fun ω => C ω + G ω + H ω) P := hiCG.add hiH
    have hiRhs : Integrable (fun ω => C ω + G ω + H ω + L ω) P := hiCGH.add hiL
    have h := integral_mono hiF hiRhs hpoint
    have hrhs : (∫ ω, C ω + G ω + H ω + L ω ∂P) =
        μ * T + (∫ ω, G ω ∂P) + (∫ ω, H ω ∂P) + ∫ ω, L ω ∂P := by
      rw [integral_add hiCGH hiL, integral_add hiCG hiH, integral_add hiConst hiG]
      simp [C]
    rw [hrhs] at h
    exact h.trans (hfinal.trans' (by linarith only [hbG, hbH, hel]))
  refine ⟨combine _ _ S (hweighted p y hp hpM hyM hbY) (hweighted x v hx hxM hvM hbV)
      hiS hsr hes (fun ω => (decompose ω).1),
    combine _ _ R (hrec p y hp hpM hyM hbY) (hrec x v hx hxM hvM hbV)
      hiR hrc her (fun ω => (decompose ω).2)⟩

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

/-- Sampling conversion for the discrete interaction protocol. -/
theorem sampling_conversion_C_1 {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (policy : Policy K)
    (run : ProtocolRun K T P policy) (hK : 0 < K) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
      ≤ ∫ ω, pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) ∂P
        + Real.sqrt (2 * T * K * Real.log K) :=
  run.toDrawRun.sampling_conversion P hK

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

universe u

/-- The finite-horizon inequalities in the first conjunct of Theorem 3.2. -/
def HasFiniteHorizonBounds : Prop :=
  ∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : ProtocolRun K T P (calibeatPolicy K η μ)),
      ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
      ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ

private theorem benchmark_le_horizon {K T : ℕ} (y : ℕ → Fin K → ℝ) (I J : ℕ → Fin K)
    (hy : ∀ t < T, ∀ j, y t j ∈ Set.Icc (0 : ℝ) 1) :
    swapRegret T y I ≤ T ∧ rewardLoss T y J I ≤ T := by
  have h (a b : ℕ → Fin K) :
      ∑ t ∈ Finset.range T, (y t (a t) - y t (b t)) ≤ (T : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have ha := hy t (Finset.mem_range.mp ht) (a t)
        have hb := hy t (Finset.mem_range.mp ht) (b t)
        exact sub_le_self _ hb.1 |>.trans ha.2
      _ = _ := by simp
  constructor
  · unfold swapRegret
    exact Finset.sup'_le _ _ fun f _ => h (fun t => f (I t)) I
  · unfold rewardLoss
    exact Finset.sup'_le _ _ fun f _ => h (fun t => f (J t)) I

private theorem integral_le_const {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ ω, f ω ≤ C) : ∫ ω, f ω ∂P ≤ C := by
  by_cases hi : Integrable f P
  · calc
      _ ≤ ∫ _ : Ω, C ∂P := integral_mono hi (integrable_const C) hf
      _ = C := by simp
  · rwa [integral_undef hi]

private theorem one_action_calibeating (T : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (policy : Policy 1) : IsCalibeating.{u} 1 T ε ε policy := by
  intro Ω m P pP run
  have h {a b : ℕ → Fin 1} (ω : Ω) (f : Fin 1 → Fin 1) :
      ∑ t ∈ Finset.range T, (run.y t ω (f (a t)) - run.y t ω (b t)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Subsingleton.elim (f (a t)) (b t), sub_self]
  have hSR (ω : Ω) : swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) = 0 := by
    unfold swapRegret
    simp_rw [h]
    exact Finset.sup'_const _ _
  have hRec (ω : Ω) : rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) = 0 := by
    unfold rewardLoss
    simp_rw [h]
    exact Finset.sup'_const _ _
  simp only [hSR, hRec, integral_zero, and_self]
  positivity

/-- The normalized and sample-complexity conclusions of Theorem 3.2 follow
from the finite-horizon bounds. -/
theorem normalized_and_tuned (h : HasFiniteHorizonBounds.{u}) :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) := by
  constructor
  · intro K T η μ hK hη hμ₀ hμ₁ hKη Ω m P pP run
    by_cases hT : T = 0
    · subst T
      simp [swapRegret, rewardLoss]
      exact Finset.sup'_le _ _ fun _ _ => le_rfl
    have ht : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hT
    have hn : 0 ≤ 2 * (K : ℝ) * Real.log K := by
      have hk : 1 ≤ (K : ℝ) := by exact_mod_cast hK
      exact mul_nonneg (by positivity) (Real.log_nonneg hk)
    have hsqrt : Real.sqrt (2 * K * Real.log K / T) * T =
        Real.sqrt (2 * T * K * Real.log K) := by
      rw [Real.sqrt_div hn]
      have hsq := Real.sq_sqrt ht.le
      have hpos := Real.sqrt_pos.mpr ht
      have ht' : (T : ℝ) = Real.sqrt T * Real.sqrt T := by nlinarith only [hsq]
      calc
        Real.sqrt (2 * K * Real.log K) / Real.sqrt T * T =
            Real.sqrt (2 * K * Real.log K) * Real.sqrt T := by
          apply (div_mul_eq_mul_div _ _ _).trans
          apply (div_eq_iff hpos.ne').mpr
          linear_combination Real.sqrt (2 * K * Real.log K) * ht'
        _ = _ := by rw [← Real.sqrt_mul hn]; congr 1; ring
    simpa only [add_mul, div_mul_cancel₀ _ ht.ne', hsqrt] using h K T η μ hK hη hμ₀ hμ₁ hKη P run
  · refine ⟨1024, by norm_num, ?_⟩
    intro K T ε hK hε hT
    by_cases hk : K = 1
    · subst K
      exact one_action_calibeating T hε.le _
    by_cases hε₁ : ε ≤ 1
    · have hp := etaStar_spec (K := K) (T := T) (ε := ε) (by omega) hε hε₁ hT
      intro P pP run
      have hb := h K T (etaStar K T) (muStar K T) hK hp.1 hp.2.1 hp.2.2.1
        (le_refl _) P run
      have hs : 0 ≤ Real.sqrt (2 * T * K * Real.log K) := Real.sqrt_nonneg _
      exact ⟨hb.1.trans hp.2.2.2, hb.2.trans (by linarith [hp.2.2.2])⟩
    · intro P pP run
      have hTε : (T : ℝ) ≤ ε * T := le_mul_of_one_le_left (by positivity) (le_of_not_ge hε₁)
      exact ⟨(integral_le_const P _ T (by positivity) fun ω =>
          (benchmark_le_horizon _ _ (fun t => run.J t ω) fun t ht j => run.y_mem t ht ω j).1).trans hTε,
        (integral_le_const P _ T (by positivity) fun ω =>
          (benchmark_le_horizon _ _ _ fun t ht j => run.y_mem t ht ω j).2).trans hTε⟩
theorem finite_horizon_bounds : HasFiniteHorizonBounds.{u} := by
  intro K T η μ hK hη hμ₀ hμ hKη Ω m P pP run
  obtain ⟨hs, hr⟩ := pseudo_regret_bound hK hη hμ₀ hμ hKη P run
  have hs' := sampling_conversion_C_1 P _ run hK
  obtain ⟨hr', hzero⟩ := rec_identity_C_1 P _ run
  have hsum : (∑ t ∈ Finset.range T, ∫ ω,
      (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P) = 0 :=
    Finset.sum_eq_zero fun t ht => hzero t (Finset.mem_range.mp ht)
  rw [hsum, sub_zero] at hr'
  exact ⟨hs'.trans (add_le_add_left hs _), hr'.symm.le.trans hr⟩

/-- Theorem 3.2. The finite-horizon regret bounds, their normalized
calibeating guarantee, and the round complexity with the tuned parameters. -/
theorem theorem_3_2 :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (run : ProtocolRun K T P (calibeatPolicy K η μ)),
        ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
        ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ) ∧
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) :=
  ⟨finite_horizon_bounds, normalized_and_tuned finite_horizon_bounds⟩

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Set Filter MeasureTheory
open scoped ENNReal

section Segment

variable {K n m : ℕ}

/-- The best swap over a concatenated history cannot improve on the sum of
the best swaps on the two parts of the history. -/
theorem swapRegret_split_le (y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    swapRegret (n + m) y I ≤ swapRegret n y I +
      swapRegret m (fun t => y (n + t)) (fun t => I (n + t)) := by
  classical
  unfold swapRegret
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_add]
  apply add_le_add
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range n, (y t (f (I t)) - y t (I t))) (Finset.mem_univ f)
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range m, (y (n + t) (f (I (n + t))) - y (n + t) (I (n + t))))
      (Finset.mem_univ f)

/-- The analogous splitting bound for reward loss against a recommendation. -/
theorem rewardLoss_split_le (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) :
    rewardLoss (n + m) y J I ≤ rewardLoss n y J I +
      rewardLoss m (fun t => y (n + t)) (fun t => J (n + t)) (fun t => I (n + t)) := by
  classical
  unfold rewardLoss
  apply Finset.sup'_le
  intro f _
  rw [Finset.sum_range_add]
  apply add_le_add
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range n, (y t (f (J t)) - y t (I t))) (Finset.mem_univ f)
  · exact Finset.le_sup' (fun f : Fin K → Fin K =>
      ∑ t ∈ Finset.range m, (y (n + t) (f (J (n + t))) - y (n + t) (I (n + t))))
      (Finset.mem_univ f)

theorem QProtocolRun.info_le_info {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {policy : QPolicy K} (run : QProtocolRun K T P policy)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) : run.info a ≤ run.info b :=
  run.toDrawRun.info_le_info hab hb

theorem QProtocolRun.integrable_rewardLoss_segment {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (n m : ℕ) (hnm : n + m ≤ T) :
    Integrable (fun ω => rewardLoss m (fun t => run.y (n + t) ω)
      (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)) P := by
  classical
  unfold rewardLoss
  apply integrable_finset_max (B := (m : ℝ))
  · intro f
    refine Finset.measurable_sum _ fun t ht => ?_
    have hlt : n + t < T := by
      have := Finset.mem_range.mp ht
      omega
    have hy := (run.y_measurable (n + t) hlt).mono (run.info_le _ hlt.le) le_rfl
    have hj := (run.J_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    have hi := (run.I_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    exact (measurable_select hj (fun i => (measurable_pi_apply (f i)).comp hy)).sub
      (measurable_select hi (fun i => (measurable_pi_apply i).comp hy))
  · intro f ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _t ∈ Finset.range m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have hlt : n + t < T := by
          have := Finset.mem_range.mp ht
          omega
        have hy₁ := run.y_mem _ hlt ω (f (run.J (n + t) ω))
        have hy₂ := run.y_mem _ hlt ω (run.I (n + t) ω)
        exact abs_le.mpr ⟨by linarith [hy₁.1, hy₂.2], by linarith [hy₁.2, hy₂.1]⟩
      _ = _ := by simp

theorem QProtocolRun.integrable_swapRegret_segment {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {policy : QPolicy K} (run : QProtocolRun K T P policy)
    (n m : ℕ) (hnm : n + m ≤ T) :
    Integrable (fun ω => swapRegret m (fun t => run.y (n + t) ω)
      (fun t => run.I (n + t) ω)) P := by
  classical
  unfold swapRegret
  apply integrable_finset_max (B := (m : ℝ))
  · intro f
    refine Finset.measurable_sum _ fun t ht => ?_
    have hlt : n + t < T := by
      have := Finset.mem_range.mp ht
      omega
    have hy := (run.y_measurable (n + t) hlt).mono (run.info_le _ hlt.le) le_rfl
    have hi := (run.I_measurable (n + t) hlt).mono (run.info_le _ (by omega)) le_rfl
    exact (measurable_select hi (fun i => (measurable_pi_apply (f i)).comp hy)).sub
      (measurable_select hi (fun i => (measurable_pi_apply i).comp hy))
  · intro f ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _t ∈ Finset.range m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have hlt : n + t < T := by
          have := Finset.mem_range.mp ht
          omega
        have hy₁ := run.y_mem _ hlt ω (f (run.I (n + t) ω))
        have hy₂ := run.y_mem _ hlt ω (run.I (n + t) ω)
        exact abs_le.mpr ⟨by linarith [hy₁.1, hy₂.2], by linarith [hy₁.2, hy₂.1]⟩
      _ = _ := by simp

end Segment

section Condition

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem condExp_smul_measure_ae [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    condExp m (c • P) f =ᵐ[c • P] condExp m P f := by
  let : IsFiniteMeasure (c • P) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top P _)⟩
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (hf.smul_measure hc)
  · intro s _ _
    exact (integrable_condExp.smul_measure hc).integrableOn
  · intro s hs _
    simp only [Measure.restrict_smul, integral_smul_measure]
    rw [setIntegral_condExp hm hf hs]
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- Conditional probability on a measurable event of positive mass. -/
noncomputable def eventProbability (P : Measure Ω) (s : Set Ω) : Measure Ω :=
  (P s)⁻¹ • P.restrict s

theorem eventProbability_isProbabilityMeasure [IsFiniteMeasure P] {s : Set Ω}
    (hs₀ : P s ≠ 0) : IsProbabilityMeasure (eventProbability P s) := by
  constructor
  simp [eventProbability, ENNReal.inv_mul_cancel hs₀ (measure_ne_top P s)]

theorem ae_eventProbability_mem [IsFiniteMeasure P] {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂eventProbability P s, ω ∈ s :=
  Measure.ae_smul_measure (ae_restrict_mem hs) _

theorem ae_eventProbability_of_ae {s : Set Ω} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂eventProbability P s, p ω :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

theorem condExp_eventProbability_ae [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[m] s) (hs₀ : P s ≠ 0)
    {f : Ω → ℝ} (hf : Integrable f P) :
    Filter.EventuallyEq (ae (@eventProbability Ω mΩ P s))
      (condExp m (@eventProbability Ω mΩ P s) f) (condExp m P f) := by
  unfold eventProbability
  have h₁ := @condExp_smul_measure_ae Ω mΩ (P.restrict s) _ m hm f
    hf.integrableOn (P s)⁻¹ (ENNReal.inv_ne_top.mpr hs₀)
  have h₂ := condExp_restrict_ae_eq_restrict (μ := P) hm hs hf
  exact h₁.trans (Measure.ae_smul_measure h₂ _)

end Condition

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory Filter Set
open scoped ENNReal

/-- A shifted run on the event that the learner has switched at time `n`.
The event is known at time `n`, so conditioning on it leaves the later
conditional action and recommendation laws unchanged. -/
noncomputable def QProtocolRun.restartOn {K T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {qpolicy : QPolicy K} (run : QProtocolRun K T P qpolicy)
    (n : ℕ) (hn : n ≤ T) (s : Set Ω) (hs : MeasurableSet[run.info n] s)
    (hs₀ : P s ≠ 0) (policy : Policy K)
    (hpolicy : ∀ t < T - n, ∀ ω ∈ s,
      run.toDrawRun.played (n + t) ω =
        policy t (fun i => run.J (n + i) ω) (fun i => run.I (n + i) ω)
          (fun i => run.y (n + i) ω (run.I (n + i) ω))) :
    ProtocolRun K (T - n) (eventProbability P s) policy where
  info t := run.info (n + t)
  q t := run.q (n + t)
  y t := run.y (n + t)
  J t := run.J (n + t)
  I t := run.I (n + t)
  info_le t ht := run.info_le _ (by omega)
  info_mono t ht := run.info_mono _ (by omega)
  q_measurable t ht := run.q_measurable _ (by omega)
  y_measurable t ht := run.y_measurable _ (by omega)
  J_measurable t ht := run.J_measurable _ (by omega)
  I_measurable t ht := run.I_measurable _ (by omega)
  q_nonneg t ht := run.q_nonneg _ (by omega)
  q_sum t ht := run.q_sum _ (by omega)
  y_mem t ht := run.y_mem _ (by omega)
  J_law t ht j := by
    have ht' : n + t < T := by omega
    have hs' : MeasurableSet[run.info (n + t)] s :=
      run.info_le_info (by omega) ht'.le _ hs
    have hj := (run.J_measurable _ ht').mono (run.info_le _ (by omega)) le_rfl
    exact (condExp_eventProbability_ae (run.info_le _ ht'.le) hs' hs₀
      ((integrable_const (1 : ℝ)).indicator (hj (measurableSet_singleton j)))).trans
        (ae_eventProbability_of_ae (run.J_law _ ht' j))
  I_law t ht i := by
    have ht' : n + t < T := by omega
    have hsambient : MeasurableSet s := run.info_le _ hn _ hs
    have hs' : MeasurableSet[run.preDraw (n + t)] s :=
      (run.info_le_info (by omega) ht'.le).trans le_sup_left _ hs
    have hi := (run.I_measurable _ ht').mono (run.info_le _ (by omega)) le_rfl
    refine (condExp_eventProbability_ae (run.toDrawRun.preDraw_le_ambient ht')
      hs' hs₀ ((integrable_const (1 : ℝ)).indicator (hi (measurableSet_singleton i)))).trans ?_
    filter_upwards [ae_eventProbability_of_ae (run.I_law _ ht' i),
      ae_eventProbability_mem (P := P) hsambient] with ω hl hω
    exact hl.trans (congrFun (hpolicy t ht ω hω) i)

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement.QProtocolRun

open MeasureTheory Set

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- The crossing round belongs to the follow phase, so the restart begins
one round after the first crossing. If there is no crossing, all rounds follow. -/
noncomputable def robustFollowLength (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ u < T, robustCrossed T ζ (fun s => run.q s ω)
    (fun s => run.I s ω) (fun s => run.y s ω (run.I s ω)) (u + 1) then Nat.find h + 1 else T

theorem robustFollowLength_le (ω : Ω) : run.robustFollowLength ω ≤ T := by
  classical
  unfold robustFollowLength
  split
  · rename_i h
    exact Nat.succ_le_of_lt (Nat.find_spec h).1
  · rfl

theorem lt_robustFollowLength_iff (ω : Ω) (t : ℕ) :
    t < run.robustFollowLength ω ↔ t < T ∧ ω ∈ run.robustFollowing t := by
  classical
  change _ ↔ t < T ∧ ∀ s < t, ¬ robustCrossed T ζ (fun v => run.q v ω)
    (fun v => run.I v ω) (fun v => run.y v ω (run.I v ω)) (s + 1)
  unfold robustFollowLength
  split
  · rename_i h
    have hs := Nat.find_spec h
    constructor
    · intro ht
      refine ⟨by omega, fun s hst hc => ?_⟩
      exact (Nat.find_min h (show s < Nat.find h by omega)) ⟨by omega, hc⟩
    · rintro ⟨_, hnever⟩
      by_contra! hn
      exact hnever _ (by omega) hs.2
  · rename_i h
    exact ⟨fun ht => ⟨ht, fun s hst hc => h ⟨s, hst.trans ht, hc⟩⟩, And.left⟩

theorem robustFollowLength_pos (hT : 0 < T) (ω : Ω) :
    0 < run.robustFollowLength ω :=
  (run.lt_robustFollowLength_iff ω 0).2 ⟨hT, by simp [robustFollowing]⟩

theorem follows_before_length {ω : Ω} {t : ℕ} (ht : t < run.robustFollowLength ω) :
    ω ∈ run.robustFollowing t :=
  ((run.lt_robustFollowLength_iff ω t).1 ht).2

theorem measurableSet_robustFollowLength_eq {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[run.info n] {ω | run.robustFollowLength ω = n} := by
  rcases n with _ | n
  · rcases eq_zero_or_pos T with hT | hT
    · have he : {ω | run.robustFollowLength ω = 0} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        have := run.robustFollowLength_le ω
        omega
      rw [he]
      exact .univ
    · have he : {ω | run.robustFollowLength ω = 0} = ∅ := by
        ext ω
        exact ⟨fun h => False.elim (Nat.ne_of_gt (run.robustFollowLength_pos hT ω) h),
          fun h => False.elim h⟩
      rw [he]
      exact @MeasurableSet.empty Ω (run.info 0)
  · have he : {ω | run.robustFollowLength ω = n + 1} =
        run.robustFollowing n ∩ {ω | ¬ (n + 1 < T ∧ ω ∈ run.robustFollowing (n + 1))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      rw [← (run.lt_robustFollowLength_iff ω (n + 1))]
      have h := run.lt_robustFollowLength_iff ω n
      have hn' : n < T := by omega
      constructor
      · intro hlen
        exact ⟨(h.mp (by omega)).2, by omega⟩
      · rintro ⟨hF, hnF⟩
        have hlen := h.mpr ⟨hn', hF⟩
        omega
    rw [he]
    have hF := run.measurableSet_robustFollowing (show n ≤ T by omega)
    refine (run.info_mono n (by omega) _ hF).inter ?_
    by_cases h : n + 1 < T
    · have he : {ω | ¬ (n + 1 < T ∧ ω ∈ run.robustFollowing (n + 1))} =
          (run.robustFollowing (n + 1))ᶜ := by ext ω; simp [h]
      rw [he]
      exact (run.measurableSet_robustFollowing hn).compl
    · simp [h]

theorem measurable_robustFollowLength : Measurable run.robustFollowLength := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n ≤ T
  · exact run.info_le n hn _ (run.measurableSet_robustFollowLength_eq hn)
  · have he : run.robustFollowLength ⁻¹' {n} = ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      have := run.robustFollowLength_le ω
      omega
    rw [he]
    exact .empty

theorem played_eq_restart_of_length {n t : ℕ} {ω : Ω} (ht : t < T - n)
    (hω : run.robustFollowLength ω = n) :
    run.toDrawRun.played (n + t) ω =
      calibeatPolicy K (etaStar K T) (muStar K T) t
        (fun i => run.J (n + i) ω) (fun i => run.I (n + i) ω)
        (fun i => run.y (n + i) ω (run.I (n + i) ω)) := by
  classical
  have hn : n < T := by omega
  unfold robustFollowLength at hω
  split at hω
  · rename_i h
    let u := Nat.find h
    have hc := Nat.find_spec h
    have hfst (v : ℕ) (hv : v < u) :
        ¬ robustCrossed T ζ (fun s => run.q s ω) (fun s => run.I s ω)
          (fun s => run.y s ω (run.I s ω)) (v + 1) := by
      intro hv'
      exact Nat.find_min h hv ⟨hv.trans hc.1, hv'⟩
    have hnu : u + 1 = n := hω
    have hut : u < n + t := by omega
    have he := robustPolicy_eq_restart (T := T) ζ (fun v => run.q v ω)
      (fun v => run.J v ω) (fun v => run.I v ω) (fun v => run.y v ω (run.I v ω))
      hut hc.2 hfst
    rw [hnu, Nat.add_sub_cancel_left] at he
    exact he
  · omega

end CalibeatBandit.Supplement.QProtocolRun

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement.QProtocolRun

open MeasureTheory Set
open scoped ENNReal

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} (run : QProtocolRun K T P (robustPolicy K T ζ))

private theorem followLength_pick (f : ℕ → Ω → ℝ) :
    (fun ω => f (run.robustFollowLength ω) ω) =
      (fun ω => ∑ n ∈ Finset.range (T + 1),
        ({v | run.robustFollowLength v = n} : Set Ω).indicator (f n) ω) := by
  classical
  funext ω
  rw [Finset.sum_eq_single (run.robustFollowLength ω)]
  · simp
  · intro n _ hn
    simp [Ne.symm hn]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le (run.robustFollowLength_le ω)))).elim

theorem integrable_robustFollowLength_apply (f : ℕ → Ω → ℝ)
    (hf : ∀ n ≤ T, Integrable (f n) P) :
    Integrable (fun ω => f (run.robustFollowLength ω) ω) P := by
  classical
  rw [run.followLength_pick f]
  apply integrable_finsetSum
  intro n hn
  have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  exact (hf n hn').indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))

theorem integral_robustFollowLength_apply (f : ℕ → Ω → ℝ)
    (hf : ∀ n ≤ T, Integrable (f n) P) :
    (∫ ω, f (run.robustFollowLength ω) ω ∂P) =
      ∑ n ∈ Finset.range (T + 1), ∫ ω in {v | run.robustFollowLength v = n}, f n ω ∂P := by
  classical
  rw [run.followLength_pick f, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact integral_indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))
  · intro n hn
    have hn' : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact (hf n hn').indicator (run.info_le n hn' _ (run.measurableSet_robustFollowLength_eq hn'))

noncomputable def robustPrefixSwapRegret (ω : Ω) : ℝ :=
  swapRegret (run.robustFollowLength ω) (fun t => run.y t ω) (fun t => run.I t ω)

noncomputable def robustPrefixRewardLoss (ω : Ω) : ℝ :=
  rewardLoss (run.robustFollowLength ω) (fun t => run.y t ω)
    (fun t => run.J t ω) (fun t => run.I t ω)

noncomputable def robustSuffixSwapRegret (ω : Ω) : ℝ :=
  let n := run.robustFollowLength ω
  swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω)

noncomputable def robustSuffixRewardLoss (ω : Ω) : ℝ :=
  let n := run.robustFollowLength ω
  rewardLoss (T - n) (fun t => run.y (n + t) ω)
    (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)

variable [IsProbabilityMeasure P]

theorem integrable_robustPrefixSwapRegret : Integrable run.robustPrefixSwapRegret P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => swapRegret n (fun t => run.y t ω) (fun t => run.I t ω)) fun n hn =>
    by simpa only [zero_add] using run.integrable_swapRegret_segment 0 n (by simpa using hn)

theorem integrable_robustPrefixRewardLoss : Integrable run.robustPrefixRewardLoss P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => rewardLoss n (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)) fun n hn =>
    by simpa only [zero_add] using run.integrable_rewardLoss_segment 0 n (by simpa using hn)

theorem integrable_robustSuffixSwapRegret : Integrable run.robustSuffixSwapRegret P :=
  run.integrable_robustFollowLength_apply
    (fun n ω => swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω)) fun n hn =>
    run.integrable_swapRegret_segment n (T - n) (by omega)

theorem integrable_robustSuffixRewardLoss : Integrable run.robustSuffixRewardLoss P :=
  run.integrable_robustFollowLength_apply (fun n ω => rewardLoss (T - n)
    (fun t => run.y (n + t) ω) (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω)) fun n hn =>
    run.integrable_rewardLoss_segment n (T - n) (by omega)

theorem robustRegret_split :
    ((∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
      (∫ ω, run.robustPrefixSwapRegret ω ∂P) + (∫ ω, run.robustSuffixSwapRegret ω ∂P)) ∧
    ((∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤
      (∫ ω, run.robustPrefixRewardLoss ω ∂P) + (∫ ω, run.robustSuffixRewardLoss ω ∂P)) := by
  constructor
  · rw [← integral_add run.integrable_robustPrefixSwapRegret run.integrable_robustSuffixSwapRegret]
    apply integral_mono
    · simpa only [zero_add] using run.integrable_swapRegret_segment 0 T (by simp)
    · exact run.integrable_robustPrefixSwapRegret.add run.integrable_robustSuffixSwapRegret
    · intro ω
      let n := run.robustFollowLength ω
      have hn : n ≤ T := run.robustFollowLength_le ω
      have h := swapRegret_split_le (n := n) (m := T - n)
        (fun t => run.y t ω) (fun t => run.I t ω)
      rwa [show n + (T - n) = T by omega] at h
  · rw [← integral_add run.integrable_robustPrefixRewardLoss run.integrable_robustSuffixRewardLoss]
    apply integral_mono
    · simpa only [zero_add] using run.integrable_rewardLoss_segment 0 T (by simp)
    · exact run.integrable_robustPrefixRewardLoss.add run.integrable_robustSuffixRewardLoss
    · intro ω
      let n := run.robustFollowLength ω
      have hn : n ≤ T := run.robustFollowLength_le ω
      have h := rewardLoss_split_le (n := n) (m := T - n)
        (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω)
      rwa [show n + (T - n) = T by omega] at h

private theorem restart_setIntegral_le {s : Set Ω} (hs : P s ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (h : (∫ ω, f ω ∂eventProbability P s) ≤ B) :
    (∫ ω in s, f ω ∂P) ≤ B * P.real s := by
  have heq : P s • eventProbability P s = P.restrict s := by
    rw [eventProbability, smul_smul, ENNReal.mul_inv_cancel hs (measure_ne_top P s), one_smul]
  rw [← heq, integral_smul_measure, smul_eq_mul, measureReal_def, mul_comm B]
  exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg

private theorem robustSuffix_integrals_on_length_le (hK : 0 < K)
    (hη : 0 < etaStar K T) (hμ : 0 < muStar K T) (hμ' : muStar K T ≤ 1 / 2)
    {n : ℕ} (hn : n ≤ T) :
    let s := {ω | run.robustFollowLength ω = n}
    let B := rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K)
    ((∫ ω in s, swapRegret (T - n) (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω) ∂P) ≤
      B * P.real s) ∧
    ((∫ ω in s, rewardLoss (T - n) (fun t => run.y (n + t) ω)
      (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω) ∂P) ≤ B * P.real s) := by
  intro s B
  by_cases hs₀ : P s = 0
  · simp [Measure.restrict_eq_zero.mpr hs₀, measureReal_def, hs₀]
  have hs : MeasurableSet[run.info n] s := run.measurableSet_robustFollowLength_eq hn
  let : IsProbabilityMeasure (eventProbability P s) := eventProbability_isProbabilityMeasure hs₀
  let restart := run.restartOn n hn s hs hs₀ (calibeatPolicy K (etaStar K T) (muStar K T))
    (fun t ht _ hω => run.played_eq_restart_of_length ht hω)
  have hb := finite_horizon_bounds K (T - n) (etaStar K T) (muStar K T) hK hη hμ hμ'
    (by unfold muStar; rfl) (eventProbability P s) restart
  have hsuf : (T - n : ℕ) ≤ T := Nat.sub_le ..
  have hrt : rT K (T - n) (etaStar K T) (muStar K T) ≤ rT K T (etaStar K T) (muStar K T) := by
    have hden : 0 ≤ 1 - muStar K T := by linarith
    unfold rT
    gcongr
  have hlog : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hsqrt : Real.sqrt (2 * ↑(T - n) * K * Real.log K) ≤ Real.sqrt (2 * T * K * Real.log K) := by
    apply Real.sqrt_le_sqrt
    gcongr
  exact ⟨restart_setIntegral_le hs₀ (hb.1.trans (add_le_add hrt hsqrt)),
    restart_setIntegral_le hs₀ (hb.2.trans (hrt.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))))⟩

/-- The expected regret after restarting is bounded by the full-horizon
calibeating bound. Each first-crossing event gets its own conditional run. -/
theorem robust_restart_regret (hK : 0 < K)
    (hη : 0 < etaStar K T) (hμ : 0 < muStar K T) (hμ' : muStar K T ≤ 1 / 2) :
    let B := rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K)
    ((∫ ω, run.robustSuffixSwapRegret ω ∂P) ≤ B) ∧
      ((∫ ω, run.robustSuffixRewardLoss ω ∂P) ≤ B) := by
  intro B
  let E (n : ℕ) : Set Ω := {ω | run.robustFollowLength ω = n}
  have hmass : (∑ n ∈ Finset.range (T + 1), P.real (E n)) = 1 := by
    have h := (run.integral_robustFollowLength_apply (fun _ _ => (1 : ℝ))
      (fun _ _ => integrable_const _)).symm
    simpa only [E, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      probReal_univ] using h
  have hsum : (∑ n ∈ Finset.range (T + 1), B * P.real (E n)) = B := by
    rw [← Finset.mul_sum, hmass, mul_one]
  constructor
  · unfold robustSuffixSwapRegret
    rw [run.integral_robustFollowLength_apply (fun n ω => swapRegret (T - n)
      (fun t => run.y (n + t) ω) (fun t => run.I (n + t) ω))
      (fun n hn => run.integrable_swapRegret_segment n (T - n) (by omega)), ← hsum]
    exact Finset.sum_le_sum fun n hn => (run.robustSuffix_integrals_on_length_le hK hη hμ hμ'
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).1
  · unfold robustSuffixRewardLoss
    rw [run.integral_robustFollowLength_apply (fun n ω => rewardLoss (T - n)
      (fun t => run.y (n + t) ω) (fun t => run.J (n + t) ω) (fun t => run.I (n + t) ω))
      (fun n hn => run.integrable_rewardLoss_segment n (T - n) (by omega)), ← hsum]
    exact Finset.sum_le_sum fun n hn => (run.robustSuffix_integrals_on_length_le hK hη hμ hμ'
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).2

end CalibeatBandit.Supplement.QProtocolRun

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem factorial_ge_geometric (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * 3 ^ (n + 1) ≤ (n + 2 + 1).factorial
    rw [pow_succ, Nat.factorial_succ, ← mul_assoc]
    calc
      2 * 3 ^ n * 3 ≤ (n + 2).factorial * 3 := Nat.mul_le_mul_right _ ih
      _ ≤ (n + 2 + 1) * (n + 2).factorial := by
        rw [mul_comm ((n + 2).factorial)]
        exact Nat.mul_le_mul_right _ (by omega)

private theorem exp_le_bernstein {x a : ℝ} (hx : |x| ≤ a) (ha : a < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - a / 3)) := by
  let f (n : ℕ) := x ^ n / (n.factorial : ℝ)
  have ha₀ : 0 ≤ a := (abs_nonneg x).trans hx
  have h₁ : HasSum f (Real.exp x) := by
    simpa [f, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have h₂ := hasSum_geometric_of_lt_one (show 0 ≤ a / 3 by positivity) (show a / 3 < 1 by linarith)
  have hsplit : Real.exp x = 1 + x + ∑' n, f (n + 2) := by
    rw [← h₁.tsum_eq, ← h₁.summable.sum_add_tsum_nat_add 2]
    simp [f, Finset.sum_range_succ]
  rw [hsplit]
  apply add_le_add_right
  have htail := (summable_nat_add_iff 2).2 h₁.summable
  calc
    (∑' n, f (n + 2)) ≤ ∑' n, (x ^ 2 / 2) * (a / 3) ^ n := by
      apply htail.tsum_le_tsum _ (h₂.mul_left (x ^ 2 / 2)).summable
      intro n
      have hf := (show (2 : ℝ) * (3 : ℝ) ^ n ≤ ((n + 2).factorial : ℝ) by
        exact_mod_cast factorial_ge_geometric n)
      have h0 : (0 : ℝ) < ((n + 2).factorial : ℝ) := by positivity
      have heq : (x ^ 2 / 2) * (a / 3) ^ n = (x ^ 2 * a ^ n) / (2 * 3 ^ n) := by
        rw [div_pow, div_mul_div_comm]
      rw [heq]
      exact (div_le_div_of_nonneg_right (show x ^ (n + 2) ≤ x ^ 2 * a ^ n by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hx _)) (sq_nonneg x)) h0.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hf)
    _ = x ^ 2 / (2 * (1 - a / 3)) := by
      rw [(h₂.mul_left (x ^ 2 / 2)).tsum_eq]
      have hn : 1 - a / 3 ≠ 0 := by linarith
      field_simp

private theorem condExp_bernstein_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ _ X) {b v η : ℝ}
    (hb : ∀ ω, |X ω| ≤ b) (hv : 0 ≤ v)
    (hη : 0 ≤ η) (hηb : η * b < 3)
    (hc : condExp m P X =ᵐ[P] 0)
    (hvX : condExp m P (fun ω => X ω ^ 2) ≤ᵐ[P] fun _ => v) :
    let α := η ^ 2 / (2 * (1 - η * b / 3))
    condExp m P (fun ω => Real.exp (η * X ω - α * v)) ≤ᵐ[P] fun _ => 1 := by
  intro α
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (sq_nonneg _) (by linarith)
  let k := Real.exp (-(α * v))
  let F : Ω → ℝ := fun ω => k * (1 + η * X ω + α * X ω ^ 2)
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX b hb
  have hi2 : Integrable (fun ω => X ω ^ 2) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ (fun ω => X ω ^ 2) (hX.pow_const (2 : ℕ)) (b ^ 2) ?_
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) _
  have hA : Integrable (fun ω => 1 + η * X ω) P :=
    (integrable_const _).add (hi.const_mul η)
  have hB : Integrable (fun ω => α * X ω ^ 2) P := hi2.const_mul α
  have hF : Integrable F P := (hA.add hB).const_mul k
  have hE : Integrable (fun ω => Real.exp (η * X ω - α * v)) P := by
    have hf : @Measurable Ω ℝ mΩ _ (fun ω => Real.exp (η * X ω - α * v)) :=
      Real.continuous_exp.measurable.comp ((hX.const_mul η).sub measurable_const)
    refine @integrable_of_abs_bound Ω mΩ P _ _ hf (Real.exp (η * b)) fun ω => ?_
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    exact (sub_le_self _ (mul_nonneg hα hv)).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb ω)) hη)
  have he (ω : Ω) : Real.exp (η * X ω - α * v) ≤ F ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
    have h := exp_le_bernstein (x := η * X ω) (a := η * b)
      (by rw [abs_mul, abs_of_nonneg hη]; exact mul_le_mul_of_nonneg_left (hb ω) hη) hηb
    have heq : (η * X ω) ^ 2 / (2 * (1 - η * b / 3)) = α * X ω ^ 2 := by
      dsimp [α]
      ring
    rw [heq] at h
    exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  have hF' :
      condExp m P F =ᵐ[P] fun ω =>
        k * (1 + η * condExp m P X ω + α * condExp m P (fun ω => X ω ^ 2) ω) := by
    let U : Ω → ℝ := fun _ => 1
    let Y : Ω → ℝ := η • X
    let Z : Ω → ℝ := α • (fun ω => X ω ^ 2)
    have hiU : Integrable U P := integrable_const _
    have hiY : Integrable Y P := hi.smul η
    have hiZ : Integrable Z P := hi2.smul α
    have hU : condExp m P U = U := condExp_const hm (1 : ℝ)
    have hY : condExp m P Y =ᵐ[P] η • condExp m P X := condExp_smul ..
    have hZ : condExp m P Z =ᵐ[P] α • condExp m P (fun ω => X ω ^ 2) := condExp_smul ..
    have heq : F = k • (U + Y + Z) := rfl
    rw [heq]
    filter_upwards [condExp_smul (μ := P) k (U + Y + Z) m, condExp_add (hiU.add hiY) hiZ m,
      condExp_add hiU hiY m, hY, hZ] with ω h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.smul_apply, h₂, Pi.add_apply, h₃, Pi.add_apply, hU, h₄, h₅]
    rfl
  filter_upwards [condExp_mono (m := m) hE hF (ae_of_all _ he), hF', hc, hvX] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂, h₃]
  change k * (1 + η * 0 + α * condExp m P (fun ω => X ω ^ 2) ω) ≤ 1
  calc
    _ ≤ k * (1 + α * v) := by
      rw [mul_zero, add_zero]
      gcongr
    _ ≤ k * Real.exp (α * v) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _ |>.trans_eq' (add_comm _ _))
        (Real.exp_nonneg _)
    _ = 1 := by dsimp [k]; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- Bernstein's upper tail for martingale differences with a uniform bound on
their absolute size and on their conditional second moments. -/
theorem bernstein_upper_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < ∑ t ∈ Finset.range s, d t ω}
      ≤ ENNReal.ofReal (Real.exp (-L)) := by
  let V : ℝ := s * v
  let R : ℝ := Real.sqrt (2 * V * L)
  let c := b / 3
  let D := V + c * R
  let η := R / D
  let α := η ^ 2 / (2 * (1 - η * b / 3))
  let A := R + c * L
  have hV : 0 < V := by exact mul_pos (by exact_mod_cast hs) hv
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hc₀ : 0 ≤ c := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hη : 0 ≤ η := by positivity
  have hnorm : 1 - η * b / 3 = V / D := by
    dsimp [η]
    field_simp
    dsimp [D, c]
    ring
  have hηb : η * b < 3 := by nlinarith only [hnorm, (div_pos hV hD)]
  have hR2 : R ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  have hα : α = R ^ 2 / (2 * D * V) := by
    dsimp only [α]
    rw [hnorm]
    dsimp only [η]
    field_simp [ne_of_gt hD, ne_of_gt hV]
  have hexp : -η * A + s * (α * v) = -L := by
    rw [show (s : ℝ) * (α * v) = α * V by dsimp [V]; ring]
    calc
      _ = (-(R * A) + R ^ 2 / 2) / D := by
        rw [hα]
        dsimp only [η]
        field_simp [ne_of_gt hD, ne_of_gt hV]
      _ = -(L * D) / D := by
        congr 1
        dsimp only [A, D]
        rw [mul_add, ← pow_two, hR2]
        ring
      _ = -L := by rw [neg_div, mul_div_cancel_right₀ _ hD.ne']
  let S (ω : Ω) : ℝ := ∑ t ∈ Finset.range s, d t ω
  have hmS : Measurable S := by
    apply Finset.measurable_sum
    intro t ht'
    have ht : t < s := Finset.mem_range.mp ht'
    exact (hm t ht).mono (hinfo_le (t + 1) (by omega)) le_rfl
  have hS (ω : Ω) : |S ω| ≤ s * b := by
    calc
      _ ≤ ∑ t ∈ Finset.range s, |d t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range s, b := Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have hi : Integrable (fun ω => Real.exp (η * S ω)) P := by
    apply integrable_of_abs_bound (B := Real.exp (η * (s * b)))
      (Real.continuous_exp.measurable.comp (hmS.const_mul _))
    intro ω
    change |Real.exp (η * S ω)| ≤ _
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hS ω)) hη)
  have hg (t : ℕ) (ht : t < s) : condExp (info t) P
      (fun ω => Real.exp (η * d t ω - α * v)) ≤ᵐ[P] fun _ => 1 :=
    @condExp_bernstein_le_one Ω mΩ P _ (info t) (hinfo_le t ht.le) _ ((hm t ht).mono (hinfo_le (t+1) (by omega)) le_rfl) b v η
      (hb t ht) hv.le hη hηb (hc t ht) (hvX t ht)
  have hbound := integral_exp_sum_le_one P info info hinfo hinfo_le
    (fun n hn => hinfo_le n hn.le) (fun _ _ => le_rfl)
    (fun t ω => η * d t ω - α * v) (B := η * b + |α * v|)
    (fun t ht => ((hm t ht).const_mul η).sub measurable_const)
    (fun t ht ω => (abs_sub _ _).trans (by
      rw [abs_mul, abs_of_nonneg hη]
      gcongr
      exact hb t ht ω)) hg
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Real.exp_sub] at hbound
  rw [integral_div] at hbound
  have hmgf : mgf S P η ≤ Real.exp (s * (α * v)) := by
    unfold mgf
    rw [show (s : ℝ) * (α * v) = α * (s * v) by ring]
    simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos _)).mp hbound
  have hre : P.real {ω | A < S ω} ≤ Real.exp (-L) := by
    calc
      _ ≤ P.real {ω | A ≤ S ω} :=
        measureReal_mono (μ := P) (s₁ := {ω | A < S ω}) (s₂ := {ω | A ≤ S ω}) (fun ω h => (show A < S ω from h).le) (measure_ne_top _ _)
      _ ≤ Real.exp (-η * A) * mgf S P η :=
        measure_ge_le_exp_mul_mgf A hη hi
      _ ≤ Real.exp (-η * A) * Real.exp (s * (α * v)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, hexp]
  have hR' : R = Real.sqrt (2 * s * v * L) := by
    dsimp [R, V]
    congr 1
    ring
  have hA : A = Real.sqrt (2 * s * v * L) + b * L / 3 := by
    change R + c * L = _
    rw [hR']
    dsimp [c]
    ring
  rw [← hA, ← ENNReal.ofReal_toReal (measure_ne_top P {ω | A < S ω})]
  exact ENNReal.ofReal_le_ofReal hre

/-- The two-sided form of the same concentration bound. -/
theorem bernstein_abs_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < |∑ t ∈ Finset.range s, d t ω|}
      ≤ 2 * ENNReal.ofReal (Real.exp (-L)) := by
  let A := Real.sqrt (2 * s * v * L) + b * L / 3
  let high : Set Ω := {ω | A < ∑ t ∈ Finset.range s, d t ω}
  let low : Set Ω := {ω | A < ∑ t ∈ Finset.range s, -d t ω}
  have hhi : P high ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le d hb₀ hv hL hm hb hc hvX
  have hlo : P low ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le (fun t ω => -d t ω) hb₀ hv hL
      (fun t ht => (hm t ht).neg) (fun t ht ω => by simpa using hb t ht ω)
      (fun t ht => (condExp_neg ..).trans (by simpa using (hc t ht).neg))
      (fun t ht => by simpa only [neg_sq] using hvX t ht)
  calc
    _ ≤ P (high ∪ low) := by
      apply measure_mono
      intro ω hω
      change A < |∑ t ∈ Finset.range s, d t ω| at hω
      rw [abs_eq_max_neg, lt_max_iff] at hω
      simpa [high, low, Finset.sum_neg_distrib] using hω
    _ ≤ P high + P low := measure_union_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add hhi hlo

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal

private theorem condExp_select_on {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : Set Ω} (hF : @MeasurableSet Ω mΩ F) {I : Ω → ι} (hI : @Measurable Ω ι mΩ _ I)
    {p : Ω → ι → ℝ}
    (hlaw : ∀ j, condExp m P ((F ∩ I ⁻¹' {j}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      F.indicator (fun ω => p ω j))
    (g : ι → Ω → ℝ) (hg : ∀ j, Measurable[m] (g j))
    (B : ℝ) (hb : ∀ j ω, |g j ω| ≤ B) :
    condExp m P (F.indicator (fun ω => g (I ω) ω)) =ᵐ[P]
      F.indicator (fun ω => ∑ j, p ω j * g j ω) := by
  classical
  let ind (j : ι) : Ω → ℝ := (F ∩ I ⁻¹' {j}).indicator (fun _ => 1)
  have hindMeas (j : ι) : @Measurable Ω ℝ mΩ _ (ind j) :=
    measurable_const.indicator (hF.inter (hI (measurableSet_singleton _)))
  have hindBound (j : ι) (ω : Ω) : |ind j ω| ≤ 1 := by
    by_cases h : ω ∈ F ∩ I ⁻¹' {j} <;> simp [ind, h]
  have hintegrable (j : ι) : Integrable (ind j) P :=
    @integrable_of_abs_bound Ω mΩ P _ (ind j) (hindMeas j) 1 (hindBound j)
  have hprod (j : ι) : Integrable (g j * ind j) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ (g j * ind j)
      (((hg j).mono hm le_rfl).mul (hindMeas j)) B fun ω => ?_
    rw [Pi.mul_apply, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hindBound j ω)).trans (hb j ω)
  have heq : F.indicator (fun ω => g (I ω) ω) = ∑ j, g j * ind j := by
    funext ω
    by_cases h : ω ∈ F <;>
      simp [Finset.sum_apply, ind, Set.indicator_apply, h, mul_ite]
  rw [heq]
  refine (condExp_finsetSum (fun j _ => hprod j) m).trans ?_
  have ha (j : ι) : condExp m P (g j * ind j) =ᵐ[P]
      fun ω => g j ω * F.indicator (fun ξ => p ξ j) ω := by
    refine (condExp_mul_of_stronglyMeasurable_left (hg j).stronglyMeasurable
      (hprod j) (hintegrable j)).trans ?_
    filter_upwards [hlaw j] with ω h
    change g j ω * condExp m P (ind j) ω = _
    rw [h]
  filter_upwards [ae_all_iff.mpr ha] with ω h
  rw [Finset.sum_apply]
  by_cases hω : ω ∈ F
  · rw [Set.indicator_of_mem hω]
    exact Finset.sum_congr rfl fun j _ => by rw [h j, Set.indicator_of_mem hω, mul_comm]
  · rw [Set.indicator_of_notMem hω]
    exact Finset.sum_eq_zero fun j _ => by rw [h j, Set.indicator_of_notMem hω, mul_zero]

private theorem sum_centered_square_le {ι : Type*} [Fintype ι] (p f : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    let c := ∑ i, p i * f i
    ∑ i, p i * (f i - c) ^ 2 ≤ ∑ i, p i * f i ^ 2 := by
  intro c
  have heq (i : ι) : p i * (f i - c) ^ 2 =
      p i * f i ^ 2 - 2 * c * (p i * f i) + p i * c ^ 2 := by ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp]
  change (∑ i, p i * f i ^ 2) - 2 * c * c + 1 * c ^ 2 ≤ _
  nlinarith only [sq_nonneg c]

private theorem condExp_centered_selected_on {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : Set Ω} (hF : @MeasurableSet Ω mΩ F) {I : Ω → ι} (hI : @Measurable Ω ι mΩ _ I)
    {p : Ω → ι → ℝ}
    (hlaw : ∀ j, condExp m P ((F ∩ I ⁻¹' {j}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      F.indicator (fun ω => p ω j))
    (g : ι → Ω → ℝ) {c : Ω → ℝ} (hg : ∀ j, Measurable[m] (g j))
    (hc : Measurable[m] c)
    (B v : ℝ) (hb : ∀ j ω, |g j ω - c ω| ≤ B)
    (hpsum : ∀ ω, ∑ j, p ω j = 1)
    (hmean : ∀ ω, ∑ j, p ω j * g j ω = c ω)
    (hsecond : ∀ ω, ∑ j, p ω j * g j ω ^ 2 ≤ v) (hv : 0 ≤ v) :
    let d := F.indicator (fun ω => g (I ω) ω - c ω)
    (condExp m P d =ᵐ[P] 0) ∧
      (condExp m P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => v) := by
  intro d
  have h₁ := @condExp_select_on Ω ι mΩ _ _ _ P _ m hm F hF I hI p hlaw (fun j ω => g j ω - c ω)
    (fun j => (hg j).sub hc) B hb
  have h₂ := @condExp_select_on Ω ι mΩ _ _ _ P _ m hm F hF I hI p hlaw (fun j ω => (g j ω - c ω) ^ 2)
    (fun j => ((hg j).sub hc).pow_const _) (B ^ 2) (fun j ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb j ω) _)
  constructor
  · filter_upwards [h₁] with ω he
    rw [he]
    change F.indicator _ ω = 0
    by_cases hω : ω ∈ F
    · rw [Set.indicator_of_mem hω]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, hmean, one_mul, sub_self]
    · exact Set.indicator_of_notMem hω _
  · have heq : (fun ω => d ω ^ 2) = F.indicator (fun ω => (g (I ω) ω - c ω) ^ 2) := by
      funext ω
      by_cases hω : ω ∈ F <;> simp [d, hω]
    rw [heq]
    filter_upwards [h₂] with ω he
    rw [he]
    by_cases hω : ω ∈ F
    · rw [Set.indicator_of_mem hω]
      exact (by simpa only [hmean] using sum_centered_square_le (p ω) (fun j => g j ω) (hpsum ω)
        : (∑ j, p ω j * (g j ω - c ω) ^ 2) ≤ ∑ j, p ω j * g j ω ^ 2).trans (hsecond ω)
    · rwa [Set.indicator_of_notMem hω]
 
private def pushMass {K : ℕ} (σ : Fin K → Fin K) (q : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if σ i = j then q i else 0

private theorem sum_pushMass_mul {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) :
    ∑ j, pushMass σ q j * y j = ∑ i, q i * y (σ i) := by
  classical
  unfold pushMass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem pushMass_prob {K : ℕ} (σ : Fin K → Fin K) {q : Fin K → ℝ}
    (hq : IsProbVec q) : IsProbVec (pushMass σ q) := by
  refine ⟨fun j => Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · split
    · exact hq.1 _
    · exact le_rfl
  · simpa only [mul_one] using (sum_pushMass_mul σ q (fun _ => 1)).trans (by simpa using hq.2)

private theorem prob_le_one {K : ℕ} {q : Fin K → ℝ} (hq : IsProbVec q) (j : Fin K) :
    q j ≤ 1 :=
  (Finset.single_le_sum (fun i _ => hq.1 i) (Finset.mem_univ j)).trans_eq hq.2

private theorem followMix_prob {K : ℕ} (hK : 0 < K) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {q : Fin K → ℝ} (hq : IsProbVec q) :
    IsProbVec (followMix ε q) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  refine ⟨fun j => add_nonneg (mul_nonneg (sub_nonneg.mpr hε₁) (hq.1 j))
    (div_nonneg hε₀ (by positivity)), ?_⟩
  unfold followMix
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq.2, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

def robustSwapStep {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) : ℝ :=
  ∑ i, q i * (y (σ i) - y i)

private theorem robustSwapStep_eq {K : ℕ} (σ : Fin K → Fin K) (q y : Fin K → ℝ) :
    robustSwapStep σ q y = ∑ j, (pushMass σ q j - q j) * y j := by
  unfold robustSwapStep
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, sum_pushMass_mul]

private theorem robustSwapStep_abs_le {K : ℕ} (σ : Fin K → Fin K) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    |robustSwapStep σ q y| ≤ 1 := by
  calc
    _ ≤ ∑ j, |q j * (y (σ j) - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, q j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hq.1 j)]
      have hp := hy (σ j)
      have hq' := hy j
      exact mul_le_of_le_one_right (hq.1 j) (abs_le.mpr ⟨by linarith [hp.1, hq'.2],
        by linarith [hp.2, hq'.1]⟩)
    _ = 1 := hq.2

private def followedSwapScore {K : ℕ} (σ : Fin K → Fin K) (ε : ℝ) (q y : Fin K → ℝ)
    (j : Fin K) : ℝ :=
  (pushMass σ q j - q j) * y j / followMix ε q j

private theorem followMix_ge_uniform {K : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    {q : Fin K → ℝ} (hq : IsProbVec q) (j : Fin K) :
    ε / K ≤ followMix ε q j := by
  unfold followMix
  linarith only [mul_nonneg (sub_nonneg.mpr hε) (hq.1 j)]

private theorem followedSwapScore_abs_le {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) (j : Fin K) :
    |followedSwapScore σ ε q y j| ≤ K / ε := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp := followMix_ge_uniform hε₁ hq j
  have hpos := (div_pos hε₀ hk).trans_le hp
  have hQ := pushMass_prob σ hq
  have hd : |pushMass σ q j - q j| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hQ.1 j, prob_le_one hq j],
      by linarith [prob_le_one hQ j, hq.1 j]⟩
  unfold followedSwapScore
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg (hy j).1]
  calc
    _ ≤ 1 / followMix ε q j := by gcongr; exact (mul_le_of_le_one_right (abs_nonneg _) (hy j).2).trans hd
    _ ≤ 1 / (ε / K) := one_div_le_one_div_of_le (div_pos hε₀ hk) hp
    _ = _ := one_div_div _ _

private theorem followedSwapScore_mean {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {q y : Fin K → ℝ}
    (hq : IsProbVec q) :
    ∑ j, followMix ε q j * followedSwapScore σ ε q y j = robustSwapStep σ q y := by
  rw [robustSwapStep_eq]
  apply Finset.sum_congr rfl
  intro j _
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp := (div_pos hε₀ hk).trans_le (followMix_ge_uniform hε₁ hq j)
  unfold followedSwapScore
  field_simp

private theorem followedSwapScore_second {K : ℕ} (hK : 0 < K)
    (σ : Fin K → Fin K) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) {q y : Fin K → ℝ}
    (hq : IsProbVec q) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ j, followMix ε q j * followedSwapScore σ ε q y j ^ 2 ≤ K / ε + 2 := by
  let Q := pushMass σ q
  let p := followMix ε q
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hQ := pushMass_prob σ hq
  have hε₂ : ε ≤ 1 := by linarith
  have hp (j : Fin K) := followMix_ge_uniform hε₂ hq j
  have hp_pos (j : Fin K) := (div_pos hε₀ hk).trans_le (hp j)
  have hQpart (j : Fin K) : Q j ^ 2 / p j ≤ (K / ε) * Q j := by
    calc
      _ ≤ Q j ^ 2 / (ε / K) := div_le_div_of_nonneg_left (sq_nonneg _) (div_pos hε₀ hk) (hp j)
      _ = K / ε * Q j ^ 2 := by simp only [div_div_eq_mul_div]; ring
      _ ≤ _ := by
        gcongr
        exact pow_le_of_le_one (hQ.1 j) (prob_le_one hQ j) (by norm_num)
  have hqpart (j : Fin K) : q j ^ 2 / p j ≤ 2 * q j := by
    apply (div_le_iff₀ (hp_pos j)).2
    have hp' : (1 - ε) * q j ≤ p j := le_add_of_nonneg_right (div_nonneg hε₀.le hk.le)
    have hh : q j ≤ (2 * (1 - ε)) * q j :=
      le_mul_of_one_le_left (hq.1 j) (by linarith)
    have hh' : q j ≤ 2 * p j := hh.trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp' (by norm_num))
    calc
      q j ^ 2 = q j * q j := pow_two _
      _ ≤ q j * (2 * p j) := mul_le_mul_of_nonneg_left hh' (hq.1 j)
      _ = _ := by ring
  calc
    _ = ∑ j, ((Q j - q j) * y j) ^ 2 / p j := by
      apply Finset.sum_congr rfl
      intro j _
      unfold followedSwapScore
      change p j * ((Q j - q j) * y j / p j) ^ 2 = _
      field_simp
    _ ≤ ∑ j, ((K / ε) * Q j + 2 * q j) := by
      apply Finset.sum_le_sum
      intro j _
      refine (show ((Q j - q j) * y j) ^ 2 / p j ≤ Q j ^ 2 / p j + q j ^ 2 / p j from ?_).trans
        (add_le_add (hQpart j) (hqpart j))
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (hp_pos j).le
      rw [mul_pow]
      have hyy : y j ^ 2 ≤ 1 := by
        exact pow_le_one₀ (hy j).1 (hy j).2
      calc
        _ ≤ (Q j - q j) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hyy
        _ ≤ _ := by nlinarith only [mul_nonneg (hQ.1 j) (hq.1 j)]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hQ.2, hq.2, mul_one, mul_one]

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : QProtocolRun K T P (robustPolicy K T ζ))

def robustEstimatorDifference (σ : Fin K → Fin K) (t : ℕ) : Ω → ℝ :=
  (run.robustFollowing t).indicator (fun ω =>
    followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) (run.I t ω) -
      robustSwapStep σ (run.q t ω) (run.y t ω))

def robustRecommendationDifference (σ : Fin K → Fin K) (t : ℕ) : Ω → ℝ :=
  fun ω => run.y t ω (σ (run.J t ω)) - run.y t ω (run.J t ω) -
    robustSwapStep σ (run.q t ω) (run.y t ω)

private theorem robustSwapStep_measurable (σ : Fin K → Fin K) {t : ℕ} (ht : t < T) :
    Measurable[run.info t] (fun ω => robustSwapStep σ (run.q t ω) (run.y t ω)) := by
  have hQm := run.q_measurable t ht
  have hYm := run.y_measurable t ht
  let _ : MeasurableSpace Ω := run.info t
  unfold robustSwapStep
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp hQm).mul
    (((measurable_pi_apply (σ j)).comp hYm).sub
      ((measurable_pi_apply j).comp hYm))

private theorem followedSwapScore_measurable (σ : Fin K → Fin K) {t : ℕ}
    (ht : t < T) (j : Fin K) :
    Measurable[run.info t] (fun ω =>
      followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) j) := by
  let q := run.q t
  let y := run.y t
  have hQm : Measurable[run.info t] q := run.q_measurable t ht
  have hYm : Measurable[run.info t] y := run.y_measurable t ht
  let _ : MeasurableSpace Ω := run.info t
  have mq (i : Fin K) : Measurable (fun ω => q ω i) :=
    (measurable_pi_apply i).comp hQm
  have mp : Measurable (fun ω => pushMass σ (q ω) j) := by
    unfold pushMass
    apply Finset.measurable_sum
    intro i _
    by_cases h : σ i = j <;> simp only [h, if_true, if_false]
    · exact mq i
    · exact measurable_const
  have my : Measurable (fun ω => y ω j) :=
    (measurable_pi_apply j).comp hYm
  unfold followedSwapScore followMix
  exact ((mp.sub (mq j)).mul my).div (((mq j).const_mul _).add measurable_const)

private theorem robustEps_pos_eq {T : ℕ} (hT : 0 < T) (ζ : ℝ) :
    0 < robustEps T ζ ∧ (robustEps T ζ)⁻¹ = (T : ℝ) ^ ζ := by
  rw [robustEps, Real.rpow_neg (by positivity), inv_inv]
  exact ⟨by positivity, rfl⟩

theorem robustEstimatorDifference_bounds (hK : 0 < K) {t : ℕ}
    (ht : t < T) (hε : robustEps T ζ ≤ 1 / 2) (σ : Fin K → Fin K) :
    let d := run.robustEstimatorDifference σ t
    Measurable[run.info (t + 1)] d ∧
      (∀ ω, |d ω| ≤ K * (T : ℝ) ^ ζ + 1) ∧
      (condExp (run.info t) P d =ᵐ[P] 0) ∧
      (condExp (run.info t) P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => K * (T : ℝ) ^ ζ + 2) := by
  intro d
  let ε := robustEps T ζ
  let g (j : Fin K) (ω : Ω) := followedSwapScore σ ε (run.q t ω) (run.y t ω) j
  let c (ω : Ω) := robustSwapStep σ (run.q t ω) (run.y t ω)
  have hε₀ : 0 < ε := (robustEps_pos_eq (by omega) ζ).1
  have hε₁ : ε ≤ 1 := by dsimp [ε]; linarith
  have hcast : (K : ℝ) / ε = K * (T : ℝ) ^ ζ := by
    rw [div_eq_mul_inv, (robustEps_pos_eq (by omega) ζ).2]
  have hg : ∀ j, Measurable[run.info t] (g j) := run.followedSwapScore_measurable σ ht
  have hc : Measurable[run.info t] c := run.robustSwapStep_measurable σ ht
  have hq (ω : Ω) : IsProbVec (run.q t ω) :=
    ⟨run.q_nonneg t ht ω, run.q_sum t ht ω⟩
  have hb (j : Fin K) (ω : Ω) : |g j ω - c ω| ≤ K / ε + 1 :=
    (abs_sub _ _).trans (add_le_add
      (followedSwapScore_abs_le hK σ hε₀ hε₁ (hq ω) (run.y_mem t ht ω) j)
      (robustSwapStep_abs_le σ (hq ω) (run.y_mem t ht ω)))
  have hF := run.measurableSet_robustFollowing ht.le
  have hm₂ := run.info_mono t ht
  have hm₀ := run.info_le (t + 1) (by omega)
  have hmeas : Measurable[run.info (t + 1)] d := by
    change Measurable[run.info (t+1)]
      ((run.robustFollowing t).indicator fun ω => g (run.I t ω) ω - c ω)
    have hIm := run.I_measurable t ht
    have hFm := hm₂ _ hF
    let _ : MeasurableSpace Ω := run.info (t+1)
    exact ((measurable_select hIm
      (fun j => (hg j).mono hm₂ le_rfl)).sub (hc.mono hm₂ le_rfl)).indicator hFm
  have hav := condExp_centered_selected_on (run.info_le t ht.le) (run.info_le t ht.le _ hF)
    ((run.I_measurable t ht).mono hm₀ le_rfl)
    (run.condExp_robustFollowing_action ht) g hg hc (K / ε + 1) (K / ε + 2) hb
    (fun ω => (followMix_prob hK hε₀.le hε₁ (hq ω)).2)
    (fun ω => followedSwapScore_mean hK σ hε₀ hε₁ (hq ω))
    (fun ω => followedSwapScore_second hK σ hε₀ hε (hq ω) (run.y_mem t ht ω)) (by positivity)
  refine ⟨hmeas, fun ω => ?_, hav.1, ?_⟩
  · rw [← hcast]
    change |(run.robustFollowing t).indicator (fun ω => g (run.I t ω) ω - c ω) ω| ≤ _
    by_cases h : ω ∈ run.robustFollowing t
    · rw [Set.indicator_of_mem h]
      exact hb _ _
    · rw [Set.indicator_of_notMem h, abs_zero]
      positivity
  · rw [← hcast]
    exact hav.2

theorem robustRecommendationDifference_bounds {t : ℕ} (ht : t < T) (σ : Fin K → Fin K) :
    let d := run.robustRecommendationDifference σ t
    Measurable[run.info (t + 1)] d ∧
      (∀ ω, |d ω| ≤ 2) ∧
      (condExp (run.info t) P d =ᵐ[P] 0) ∧
      (condExp (run.info t) P (fun ω => d ω ^ 2) ≤ᵐ[P] fun _ => 1) := by
  intro d
  let g (j : Fin K) (ω : Ω) := run.y t ω (σ j) - run.y t ω j
  let c (ω : Ω) := robustSwapStep σ (run.q t ω) (run.y t ω)
  have hg (j : Fin K) : Measurable[run.info t] (g j) :=
    ((measurable_pi_apply (σ j)).comp (run.y_measurable t ht)).sub
      ((measurable_pi_apply j).comp (run.y_measurable t ht))
  have hc : Measurable[run.info t] c := run.robustSwapStep_measurable σ ht
  have hq (ω : Ω) : IsProbVec (run.q t ω) :=
    ⟨run.q_nonneg t ht ω, run.q_sum t ht ω⟩
  have hgb (j : Fin K) (ω : Ω) : |g j ω| ≤ 1 := by
    have hs := run.y_mem t ht ω (σ j)
    have hj := run.y_mem t ht ω j
    dsimp [g]
    exact abs_le.mpr ⟨by linarith [hs.1,hj.2], by linarith [hs.2,hj.1]⟩
  have hb (j : Fin K) (ω : Ω) : |g j ω - c ω| ≤ 2 := by
    calc
      _ ≤ |g j ω| + |c ω| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hgb j ω) (robustSwapStep_abs_le σ (hq ω) (run.y_mem t ht ω))
      _ = 2 := by norm_num
  have hm₂ := run.info_mono t ht
  have hm₀ := run.info_le (t + 1) (by omega)
  have hmeas : Measurable[run.info (t+1)] d := by
    have hJm := run.J_measurable t ht
    let _ : MeasurableSpace Ω := run.info (t+1)
    exact (measurable_select hJm (fun j => (hg j).mono hm₂ le_rfl)).sub
      (hc.mono hm₂ le_rfl)
  have hav := condExp_centered_selected_on (F := Set.univ)
    (run.info_le t ht.le) MeasurableSet.univ ((run.J_measurable t ht).mono hm₀ le_rfl)
    (fun j => by simpa using run.J_law t ht j) g hg hc 2 1 hb
    (fun ω => (hq ω).2) (fun _ => rfl)
    (fun ω => calc
      _ ≤ ∑ j, run.q t ω j * 1 := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hgb j ω)) ((hq ω).1 j)
      _ = 1 := by simpa only [mul_one] using (hq ω).2) (by norm_num)
  refine ⟨hmeas, fun ω => hb _ ω, ?_, ?_⟩
  · change condExp (run.info t) P (fun ω => g (run.J t ω) ω - c ω) =ᵐ[P] 0
    simpa only [Set.indicator_univ] using hav.1
  · change condExp (run.info t) P (fun ω => (g (run.J t ω) ω - c ω) ^ 2) ≤ᵐ[P] fun _ => 1
    simpa only [Set.indicator_univ] using hav.2

omit [IsProbabilityMeasure P] in
theorem followedSwapScore_eq_robustSwapStep (σ : Fin K → Fin K) (t : ℕ) (ω : Ω) :
    followedSwapScore σ (robustEps T ζ) (run.q t ω) (run.y t ω) (run.I t ω) =
      robustSwapStep σ (run.q t ω) (robustYhat
        (followMix (robustEps T ζ) (run.q t ω)) (run.I t ω) (run.y t ω (run.I t ω))) := by
  classical
  rw [robustSwapStep_eq]
  unfold followedSwapScore robustYhat
  simp [mul_ite, Finset.sum_ite_eq, mul_div_assoc]

end QProtocolRun

end

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

private theorem condExp_exp_centered_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (hb : ∀ ω, |X ω| ≤ 1)
    (hc : condExp m P X =ᵐ[P] 0) (s : ℝ) :
    condExp m P (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) ≤ᵐ[P] fun _ => 1 := by
  let k := Real.exp (-(s ^ 2 / 2))
  let A := k * Real.cosh s
  let B := k * Real.sinh s
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX 1 hb
  have he : Integrable (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ _ (Real.continuous_exp.measurable.comp
      ((hX.const_mul s).sub measurable_const)) (Real.exp |s|) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ s * X ω := sub_le_self _ (by positivity)
      _ ≤ |s * X ω| := le_abs_self _
      _ ≤ |s| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb ω)
  have heq (ω : Ω) : Real.exp (s * X ω - s ^ 2 / 2) ≤ A + B * X ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm (Real.exp _)]
    have h := mul_le_mul_of_nonneg_left (Real.exp_mul_le_cosh_add_mul_sinh (hb ω) s)
      (Real.exp_nonneg (-(s ^ 2 / 2)))
    have hleft : Real.exp (-(s ^ 2 / 2)) * Real.exp (s * X ω) =
        Real.exp (-(s ^ 2 / 2)) * Real.exp (X ω * s) := by rw [mul_comm s]
    rw [hleft]
    exact h.trans_eq (by unfold A B k; ring)
  have hA : Integrable (fun _ : Ω => A) P := integrable_const _
  have hB : Integrable (fun ω => B * X ω) P := hi.const_mul B
  have hcond := condExp_mono (m := m) he (hA.add hB) (ae_of_all _ heq)
  have hbPull : condExp m P (fun ω => B * X ω) =ᵐ[P] fun ω => B * condExp m P X ω :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const hB hi
  have hconst : A ≤ 1 := by
    calc
      A ≤ k * Real.exp (s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq s) (Real.exp_nonneg _)
      _ = 1 := by unfold k; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  filter_upwards [hcond, condExp_add hA hB m, hbPull, hc] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂]
  change condExp m P (fun _ : Ω => A) ω + condExp m P (fun ω => B * X ω) ω ≤ 1
  simpa only [condExp_const hm, h₃, h₄, Pi.zero_apply, mul_zero, add_zero] using hconst

/-- Lemma 4.10 for increments bounded by one. The two signs of each
martingale index the competitors in the exponential maximum. -/
theorem martingale_max_abs_le {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} (hT : 0 < T) (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ 1)
    (hc : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  classical
  let L := Real.log (2 * Fintype.card ι)
  have hL : 0 < L := by
    apply Real.log_pos
    have h : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    linarith
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  let R := Real.sqrt (2 * T * L)
  have hrad : 0 < 2 * T * L := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr hrad
  let s := R / T
  have hs : 0 < s := div_pos hR ht
  let X (t : ℕ) (j : ι × Bool) : Ω → ℝ := if j.2 then d t j.1 else -d t j.1
  have hXm (t : ℕ) (ht : t < T) (j : ι × Bool) : Measurable[info (t + 1)] (X t j) := by
    unfold X
    split
    · exact hm t ht j.1
    · exact (hm t ht j.1).neg
  have hXb (t : ℕ) (ht : t < T) (j : ι × Bool) (ω : Ω) : |X t j ω| ≤ 1 := by
    unfold X
    split <;> simpa using hb t ht j.1 ω
  have hXc (t : ℕ) (ht : t < T) (j : ι × Bool) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    unfold X
    split
    · exact hc t ht j.1
    · filter_upwards [condExp_neg (μ := P) (m := info t) (f := d t j.1), hc t ht j.1] with ω h he
      simp [h, he]
  let F (j : ι × Bool) (ω : Ω) := ∑ t ∈ Finset.range T, (X t j ω - s / 2)
  have hfm (j : ι × Bool) : Measurable (F j) :=
    Finset.measurable_sum _ fun t ht =>
      ((hXm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl).sub measurable_const
  have hfb (j : ι × Bool) (ω : Ω) : |F j ω| ≤ T * (1 + |s / 2|) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |X t j ω - s / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 + |s / 2|) := Finset.sum_le_sum fun t ht =>
        (abs_sub _ _).trans (add_le_add_left (hXb t (Finset.mem_range.mp ht) j ω) _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hExp (j : ι × Bool) : (∫ ω, Real.exp (s * F j ω) ∂P) ≤ 1 := by
    have h := integral_exp_sum_le_one P info info
      (fun _ _ h _ => info.mono h) (fun n _ => info.le n) (fun n _ => info.le n) (fun _ _ => le_rfl)
      (fun t ω => s * X t j ω - s ^ 2 / 2)
      (B := |s| + |s ^ 2 / 2|)
      (fun t ht => ((hXm t ht j).const_mul s).sub measurable_const)
      (fun t ht ω => (abs_sub _ _).trans (by
        rw [abs_mul]
        exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (hXb t ht j ω)) _))
      (fun t ht => condExp_exp_centered_le_one (info.le t)
        ((hXm t ht j).mono (info.le _) le_rfl) (hXb t ht j) (hXc t ht j) s)
    have heq (ω : Ω) : s * F j ω =
        ∑ t ∈ Finset.range T, (s * X t j ω - s ^ 2 / 2) := by
      simp only [F, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    simpa only [heq] using h
  have hF := integral_max_le_log_card P Finset.univ_nonempty F hs hfm hfb hExp
  let M (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty
      (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
  have hiM : Integrable M P := by
    apply integrable_finset_max Finset.univ_nonempty (B := T)
    · intro j
      have hmeas : Measurable (fun ω => ∑ t ∈ Finset.range T, d t j ω) :=
        Finset.measurable_sum _ fun t ht => (hm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp hmeas
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) j ω
        _ = _ := by simp
  have hf (ω : Ω) (j : ι) (b : Bool) :
      F (j, b) ω = (if b then ∑ t ∈ Finset.range T, d t j ω
      else -(∑ t ∈ Finset.range T, d t j ω)) - T * (s / 2) := by
    cases b <;> simp [F, X, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hM (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun j => F j ω) = M ω - T * (s / 2) := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun ⟨j, b⟩ _ => ?_
      rw [hf]
      apply sub_le_sub_right
      refine le_trans ?_ (Finset.le_sup' (fun j => |∑ t ∈ Finset.range T, d t j ω|) (Finset.mem_univ j))
      cases b <;> simp [le_abs_self, neg_le_abs]
    · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
      change M ω = _ at hj
      rw [hj]
      let z := ∑ t ∈ Finset.range T, d t j ω
      change |z| - _ ≤ _
      by_cases hz : 0 ≤ z
      · rw [abs_of_nonneg hz, ← show F (j, true) ω = z - T * (s / 2) by simpa only [if_true] using hf ω j true]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, true))
      · rw [abs_of_neg (lt_of_not_ge hz), ← show F (j, false) ω = -z - T * (s / 2) by
            simpa only [Bool.false_eq_true, if_false] using hf ω j false]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, false))
  simp_rw [hM, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ)] at hF
  rw [integral_sub hiM (integrable_const (T * (s / 2)))] at hF
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hF
  change (∫ ω, M ω ∂P) - T * (s / 2) ≤ L / s at hF
  have hRsq : R ^ 2 = 2 * T * L := Real.sq_sqrt hrad.le
  have hhalf : L / s = R / 2 := by
    apply (div_eq_iff hs.ne').mpr
    dsimp [s]
    field_simp [ht.ne']
    nlinarith only [hRsq]
  have hother : (T : ℝ) * (s / 2) = R / 2 := by
    dsimp [s]
    field_simp [ht.ne']
  rw [hhalf, hother] at hF
  change (∫ ω, M ω ∂P) ≤ R
  linarith only [hF]

/-- Lemma 4.10 with an arbitrary positive bound on the increments. -/
theorem lemma_4_10 {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} {c : ℝ} (hc : 0 < c)
    (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ c)
    (hcenter : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      c * Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  by_cases hT : T = 0
  · subst T
    simp
  let X (t : ℕ) (j : ι) (ω : Ω) := d t j ω / c
  have hXm (t : ℕ) (ht : t < T) (j : ι) : Measurable[info (t + 1)] (X t j) :=
    (hm t ht j).div_const c
  have hXb (t : ℕ) (ht : t < T) (j : ι) (ω : Ω) : |X t j ω| ≤ 1 := by
    change |d t j ω / c| ≤ 1
    rw [abs_div, abs_of_pos hc]
    exact (div_le_one hc).mpr (hb t ht j ω)
  have hXc (t : ℕ) (ht : t < T) (j : ι) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    have hi : Integrable (d t j) P :=
      integrable_of_abs_bound ((hm t ht j).mono (info.le _) le_rfl) (hb t ht j)
    have hprod : Integrable ((fun _ : Ω => c⁻¹) * d t j) P := hi.const_mul _
    have heq : X t j = (fun _ : Ω => c⁻¹) * d t j := by
      funext ω
      simp only [X, Pi.mul_apply, div_eq_inv_mul]
    rw [heq]
    have hmconst : StronglyMeasurable[info t] (fun _ : Ω => c⁻¹) := stronglyMeasurable_const
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hmconst hprod hi,
      hcenter t ht j] with ω h₁ h₂
    simp [h₁, h₂]
  have h := martingale_max_abs_le P info (Nat.pos_of_ne_zero hT) X hXm hXb hXc
  have hscale (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d t j ω|) =
        c * Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, X t j ω|) := by
    let F (j : ι) := |∑ t ∈ Finset.range T, X t j ω|
    have hj (j : ι) : |∑ t ∈ Finset.range T, d t j ω| = c * F j := by
      unfold F X
      rw [← Finset.sum_div, abs_div, abs_of_pos hc]
      field_simp
    simp_rw [hj]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j hj => ?_
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' F hj) hc.le
    · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty F
      rw [heq]
      exact Finset.le_sup' (fun j => c * F j) hj
  simp_rw [hscale]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h hc.le

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

def swapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i j : Fin K) : ℝ :=
  ∑ t ∈ Finset.range T, q t i * (u t j - u t i)

def bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i : Fin K) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)

theorem bestSwapGain_nonneg {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i : Fin K) :
    0 ≤ bestSwapGain T q u i := by
  simpa [swapGain] using swapGain_le_best (T := T) q u i i

/-- Lemma 4.3. Each row maximum dominates any individual comparison, any
convex combination of comparisons, and any comparison restricted to an event. -/
theorem lemma_4_3 {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K)
    (w : Fin K → ℝ) (hw : IsProbVec w) (event : Prop) [Decidable event] :
    swapGain T q u i j ≤ bestSwapGain T q u i ∧
    (∑ j, w j * swapGain T q u i j) ≤ bestSwapGain T q u i ∧
    (if event then swapGain T q u i j else 0) ≤ bestSwapGain T q u i := by
  refine ⟨swapGain_le_best q u i j, ?_, ?_⟩
  · calc
      _ ≤ ∑ j, w j * bestSwapGain T q u i :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (swapGain_le_best q u i j) (hw.1 j)
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]
  · split
    · exact swapGain_le_best q u i j
    · exact bestSwapGain_nonneg q u i

/-- The swap map can maximize every row independently. -/
theorem pseudoSwapRegret_eq_sum_bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) :
    pseudoSwapRegret T q u = ∑ i, bestSwapGain T q u i := by
  classical
  have score (f : Fin K → Fin K) :
      (∑ t ∈ Finset.range T, ((∑ i, q t i * u t (f i)) - q t ⬝ᵥ u t)) =
        ∑ i, swapGain T q u i (f i) := by
    unfold swapGain dotProduct
    have h (t : ℕ) : (∑ i, q t i * u t (f i)) - ∑ i, q t i * u t i =
        ∑ i, q t i * (u t (f i) - u t i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [h]
    exact Finset.sum_comm
  unfold pseudoSwapRegret
  simp_rw [score]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => Finset.sum_le_sum fun i _ => swapGain_le_best q u i (f i)
  · have exists_best (i : Fin K) : ∃ j, bestSwapGain T q u i = swapGain T q u i j := by
      obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
      exact ⟨j, h⟩
    choose f hf using exists_best
    calc
      _ = ∑ i, swapGain T q u i (f i) := Finset.sum_congr rfl fun i _ => hf i
      _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K => ∑ i, swapGain T q u i (f i))
        (Finset.mem_univ f)

/-- The deterministic root comparison used in Lemma 4.4. -/
theorem root_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) -
      (∑ t ∈ Finset.range T, q t i * u t i) ≤ bestSwapGain T q u i := by
  have hsum : swapGain T q u i rootA + swapGain T q u i rootB =
      (∑ t ∈ Finset.range T, q t i) * (1 / (2 * H)) -
        2 * (∑ t ∈ Finset.range T, q t i * u t i) := by
    simp only [swapGain, ← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t ht => by
      rw [← hroot t (Finset.mem_range.mp ht)]
      ring
  have half : (∑ t ∈ Finset.range T, q t i) / (4 * H) =
      ((∑ t ∈ Finset.range T, q t i) * (1 / (2 * H))) / 2 := by
    by_cases h : H = 0
    · simp [h]
    · field_simp
      ring
  linarith only [half, hsum, swapGain_le_best (T := T) q u i rootA,
    swapGain_le_best (T := T) q u i rootB]

theorem unnamed_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (i rootA rootB : Fin K) (H : ℝ)
    (hi : ∀ t < T, u t i = 0)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ Finset.range T, q t i) / (4 * H) ≤ bestSwapGain T q u i := by
  have hzero : (∑ t ∈ Finset.range T, q t i * u t i) = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hi t (Finset.mem_range.mp ht), mul_zero]
  simpa only [hzero, sub_zero] using root_bestSwapGain q u i rootA rootB H hroot

/-- The two deterministic comparisons used for a leaf action in Lemma 4.5.
The selected auxiliary action has bonus probability one in the leaf's period. -/
theorem leaf_bestSwapGain {K T : ℕ} (q u : ℕ → Fin K → ℝ)
    (period : Finset ℕ) (hperiod : period ⊆ Finset.range T)
    (i auxiliary rootA rootB : Fin K) (H : ℝ)
    (hq : ∀ t < T, 0 ≤ q t i) (hu : ∀ t < T, 0 ≤ u t auxiliary)
    (hoff : ∀ t < T, t ∉ period → u t i = 0)
    (hon : ∀ t ∈ period, u t auxiliary = 1)
    (hroot : ∀ t < T, u t rootA + u t rootB = 1 / (2 * H)) :
    (∑ t ∈ period, q t i * (1 - u t i)) ≤ bestSwapGain T q u i ∧
      (∑ t ∈ Finset.range T, q t i) / (4 * H) -
        (∑ t ∈ period, q t i * u t i) ≤ bestSwapGain T q u i := by
  classical
  constructor
  · apply le_trans _ (swapGain_le_best (T := T) q u i auxiliary)
    unfold swapGain
    have h := Finset.sum_le_sum_of_subset_of_nonneg hperiod
      (f := fun t => q t i * (u t auxiliary - u t i))
      (fun t ht hout => by
        rw [hoff t (Finset.mem_range.mp ht) hout, sub_zero]
        exact mul_nonneg (hq t (Finset.mem_range.mp ht)) (hu t (Finset.mem_range.mp ht)))
    have he : (∑ t ∈ period, q t i * (1 - u t i)) =
        ∑ t ∈ period, q t i * (u t auxiliary - u t i) :=
      Finset.sum_congr rfl fun t ht => by rw [hon t ht]
    exact he.le.trans h
  · have he : (∑ t ∈ period, q t i * u t i) = ∑ t ∈ Finset.range T, q t i * u t i := by
      apply Finset.sum_subset hperiod
      intro t ht hout
      rw [hoff t (Finset.mem_range.mp ht) hout, mul_zero]
    rw [he]
    exact root_bestSwapGain q u i rootA rootB H hroot

/-- After averaging over the fresh leaf coin, the two leaf comparisons give
the factor 1/(8H) in Lemma 4.5. -/
theorem leaf_expected_gain {H total inside gain : ℝ} (h₁ : inside / 2 ≤ gain)
    (h₂ : total / (4 * H) - inside / 2 ≤ gain) :
    total / (8 * H) ≤ gain := by
  have he : total / (4 * H) = 2 * (total / (8 * H)) := by ring
  linarith only [h₁, h₂, he]

/-- The case split of Lemma 4.9 after taking expectations. The two groups
partition the learner's play mass, and their swap gains are nonnegative. -/
theorem aggregate_swap_gain {T auxMass auxGain otherGain H : ℝ}
    (hT : 0 ≤ T) (hH : 1 ≤ H)
    (haux₀ : 0 ≤ auxGain) (hother₀ : 0 ≤ otherGain)
    (haux : auxMass / (4 * H) - T / (64 * H) ≤ auxGain)
    (hother : (T - auxMass) / (184 * H ^ 5) ≤ otherGain) :
    T / (368 * H ^ 5) ≤ auxGain + otherGain := by
  have hH₀ : 0 < H := by linarith
  have hpos : 0 < 184 * H ^ 5 := by positivity
  by_cases h : auxMass ≤ T / 2
  · calc
      _ = (T / 2) / (184 * H ^ 5) := by ring
      _ ≤ (T - auxMass) / (184 * H ^ 5) :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      _ ≤ otherGain := hother
      _ ≤ _ := le_add_of_nonneg_left haux₀
  · have hh : H ≤ H ^ 5 := by
      calc
        H = H * 1 := (mul_one _).symm
        _ ≤ H * H ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) hH₀.le
        _ = _ := by ring
    have hbig : 64 * H ≤ 368 * H ^ 5 := by linarith
    have hm : T / (368 * H ^ 5) ≤ T / (64 * H) :=
      div_le_div_of_nonneg_left hT (by positivity) hbig
    have haux' : T / (8 * H) ≤ auxMass / (4 * H) := by
      rw [show T / (8 * H) = (T / 2) / (4 * H) by ring]
      exact div_le_div_of_nonneg_right (le_of_not_ge h) (by positivity)
    have heq : T / (8 * H) = 8 * (T / (64 * H)) := by ring
    have hn : 0 ≤ T / (64 * H) := by positivity
    linarith only [hm, haux', heq, hn, haux, hother₀]

/-- Averaging the one-period comparison between the baseline world and the
worlds with a selected auxiliary action. Here `baseline j` is the expected
number of plays of action j under the baseline law. -/
theorem auxiliary_average_le {M : ℕ} (hM : 0 < M) {period η : ℝ}
    (hperiod : 0 ≤ period) (hη : 0 ≤ η)
    (baseline selected : Fin M → ℝ) (hbase : ∀ j, 0 ≤ baseline j)
    (hcounts : (∑ j, baseline j) ≤ period)
    (hcompare : ∀ j, selected j ≤ baseline j + η * period * Real.sqrt (baseline j / 6)) :
    (∑ j, selected j) / M ≤ period / M + η * period * Real.sqrt (period / (6 * M)) := by
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hs : (∑ j, Real.sqrt (baseline j)) ≤ Real.sqrt (M * period) := by
    have h := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin M)))
      (f := baseline) (g := fun _ => 1) hbase (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    calc
      _ ≤ Real.sqrt (∑ j, baseline j) * Real.sqrt M := by simpa only [mul_one] using h
      _ ≤ Real.sqrt period * Real.sqrt M :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcounts) (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_comm, ← Real.sqrt_mul hM'.le]
  have hall := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun j _ => hcompare j
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Real.sqrt_div (hbase _),
    ← Finset.sum_div] at hall
  calc
    _ ≤ (period + η * period * (Real.sqrt (M * period) / Real.sqrt 6)) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      exact hall.trans (add_le_add hcounts (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)) (mul_nonneg hη hperiod)))
    _ = _ := by
      rw [add_div, mul_div_assoc, div_div, Real.sqrt_mul hM'.le,
        Real.sqrt_div hperiod, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      have hsM : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM'.le
      have hpM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM'
      have hp6 : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      rw [← hsM]
      rw [Real.sqrt_sq hpM.le]
      field_simp

/-- The conversion from the proxy swap gain to realized swap regret.
The error for each action is bounded by its largest row deviation. -/
theorem swapRegret_ge_proxy {K T : ℕ} (a : ℝ)
    (q u y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) :
    a * pseudoSwapRegret T q u -
      (∑ i : Fin K, Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I t) 1) y i j - a * swapGain T q u i j|)) ≤
      swapRegret T y I := by
  classical
  let played (t : ℕ) : Fin K → ℝ := Pi.single (I t) 1
  have hplayed : swapRegret T y I = pseudoSwapRegret T played y := by
    unfold swapRegret pseudoSwapRegret
    simp [played, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  rw [hplayed, pseudoSwapRegret_eq_sum_bestSwapGain, pseudoSwapRegret_eq_sum_bestSwapGain,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
  change bestSwapGain T q u i = swapGain T q u i j at heq
  have herr := Finset.le_sup' (fun j => |swapGain T played y i j - a * swapGain T q u i j|) hj
  change a * bestSwapGain T q u i -
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T played y i j - a * swapGain T q u i j|) ≤ bestSwapGain T played y i
  rw [heq]
  have h₁ := neg_le_abs (swapGain T played y i j - a * swapGain T q u i j)
  have h₂ := swapGain_le_best (T := T) played y i j
  linarith only [herr, h₁, h₂]

set_option maxHeartbeats 450000 in
/-- The final martingale comparison for the discrete lower bound. Each
increment is the observed swap gain minus its conditional prediction. -/
theorem expected_swapRegret_ge_proxy {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (info : Filtration ℕ mΩ)
    (anchor : Fin K) (a c : ℝ) (hc : 0 < c)
    (q u y : Ω → ℕ → Fin K → ℝ) (I : Ω → ℕ → Fin K)
    (hy : ∀ t < T, ∀ ω j, y ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hym : ∀ t < T, ∀ j, Measurable (fun ω => y ω t j))
    (hI : ∀ t < T, Measurable (fun ω => I ω t))
    (hq : ∀ t < T, ∀ ω, IsProbVec (q ω t))
    (hu : ∀ t < T, ∀ ω j, u ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hqm : ∀ t < T, ∀ j, Measurable (fun ω => q ω t j))
    (hum : ∀ t < T, ∀ j, Measurable (fun ω => u ω t j)) :
    let d (i : Fin K) (t : ℕ) (j : Fin K) (ω : Ω) :=
      (Pi.single (I ω t) (1 : ℝ) : Fin K → ℝ) i * (y ω t j - y ω t i) -
        a * (q ω t i * (u ω t j - u ω t i))
    (∀ t < T, ∀ i j, Measurable[info (t + 1)] (d i t j)) →
    (∀ t < T, ∀ i j ω, |d i t j ω| ≤ c) →
    (∀ t < T, ∀ i j, condExp (info t) P (d i t j) =ᵐ[P] 0) →
    a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) -
      K * (c * Real.sqrt (2 * T * Real.log (2 * K))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂P := by
  classical
  intro d hdm hdb hdc
  let _ : Nonempty (Fin K) := ⟨anchor⟩
  let D (i : Fin K) (ω : Ω) :=
    Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d i t j ω|)
  have hD (i : Fin K) : Integrable (D i) P := by
    apply integrable_finset_max Finset.univ_nonempty _ (B := (T : ℝ) * c)
    · intro j
      have h : Measurable (fun ω => ∑ t ∈ Finset.range T, d i t j ω) :=
        Finset.measurable_sum _ fun t ht =>
          (hdm t (Finset.mem_range.mp ht) i j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp h
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d i t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, c := Finset.sum_le_sum fun t ht =>
          hdb t (Finset.mem_range.mp ht) i j ω
        _ = _ := by simp
  have d_bound (i : Fin K) : ∫ ω, D i ω ∂P ≤ c * Real.sqrt (2 * T * Real.log (2 * K)) := by
    simpa only [Fintype.card_fin] using lemma_4_10 P info hc (d i)
      (fun t ht j => hdm t ht i j) (fun t ht j => hdb t ht i j) (fun t ht j => hdc t ht i j)
  have sum_bound (F : ℕ → Ω → ℝ) (hF : ∀ t < T, ∀ ω, |F t ω| ≤ 1) (ω : Ω) :
      |∑ t ∈ Finset.range T, F t ω| ≤ (T : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |F t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
        hF t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have diff_bound {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hreal : Integrable (fun ω => swapRegret T (y ω) (I ω)) P := by
    unfold swapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (measurable_select (hI t (Finset.mem_range.mp ht)) (fun j => hym t (Finset.mem_range.mp ht) (f j))).sub
          (measurable_select (hI t (Finset.mem_range.mp ht)) (hym t (Finset.mem_range.mp ht)))
    · intro f ω
      exact sum_bound (fun t ω => y ω t (f (I ω t)) - y ω t (I ω t))
        (fun t ht ω => diff_bound (hy t ht ω _) (hy t ht ω _)) ω
  have hproxy : Integrable (fun ω => pseudoSwapRegret T (q ω) (u ω)) P := by
    unfold pseudoSwapRegret
    apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
    · intro f
      exact Finset.measurable_sum _ fun t ht =>
        (Finset.measurable_sum _ fun i _ => (hqm t (Finset.mem_range.mp ht) i).mul
          (hum t (Finset.mem_range.mp ht) (f i))).sub (Finset.measurable_sum _ fun i _ =>
          (hqm t (Finset.mem_range.mp ht) i).mul (hum t (Finset.mem_range.mp ht) i))
    · intro f ω
      apply sum_bound (fun t ω => (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t) _ ω
      intro t ht ω
      have he : (∑ i, q ω t i * u ω t (f i)) - q ω t ⬝ᵥ u ω t =
          ∑ i, q ω t i * (u ω t (f i) - u ω t i) := by
        simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      rw [he]
      calc
        _ ≤ ∑ i, |q ω t i * (u ω t (f i) - u ω t i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q ω t i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg ((hq t ht ω).1 i)]
          exact mul_le_of_le_one_right ((hq t ht ω).1 i) (diff_bound (hu t ht ω _) (hu t ht ω _))
        _ = 1 := (hq t ht ω).2
  have heq (ω : Ω) (i : Fin K) :
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j =>
        |swapGain T (fun t => Pi.single (I ω t) 1) (y ω) i j -
          a * swapGain T (q ω) (u ω) i j|) = D i ω := by
    unfold D
    congr 1
    funext j
    congr 1
    simp only [d, swapGain, Finset.mul_sum, Finset.sum_sub_distrib]
  have hp (ω : Ω) := swapRegret_ge_proxy (T := T) a (q ω) (u ω) (y ω) (I ω)
  simp_rw [heq] at hp
  have hi : Integrable (fun ω => ∑ i, D i ω) P := integrable_finsetSum _ fun i _ => hD i
  have hi' : Integrable (fun ω => a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω) P :=
    (hproxy.const_mul a).sub hi
  have hle := integral_mono hi' hreal hp
  have h' : (∫ ω, a * pseudoSwapRegret T (q ω) (u ω) - ∑ i, D i ω ∂P) =
      a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) - ∑ i, ∫ ω, D i ω ∂P := by
    rw [integral_sub (hproxy.const_mul a) hi, integral_const_mul, integral_finsetSum _ (fun i _ => hD i)]
  rw [h'] at hle
  have hs : (∑ i, ∫ ω, D i ω ∂P) ≤ K * (c * Real.sqrt (2 * T * Real.log (2 * K))) := by
    calc
      _ ≤ ∑ _ : Fin K, c * Real.sqrt (2 * T * Real.log (2 * K)) :=
        Finset.sum_le_sum fun i _ => d_bound i
      _ = _ := by simp
  linarith only [hs, hle]

/-- The last quantitative step in Theorem 4.1. The summed martingale
deviation is lower order than the proxy gain at horizon K⁴. -/
theorem discrete_lower_bound_rate :
    ∀ᶠ k : ℝ in atTop, ∀ H : ℝ, 1 ≤ H → H ≤ 2 * Real.log k →
      k ^ 3 / (10 ^ 10 * (Real.log k) ^ 6) ≤
        k ^ 3 / (17664000 * H ^ 6) -
          k ^ 2 / (16000 * H) * Real.sqrt (2 * Real.log (2 * k)) := by
  let C : ℝ := 1 / 10000000
  have hlog := (isLittleO_log_rpow_rpow_atTop (s := 1) 7 (by norm_num)).def
    (c := C) (by norm_num [C])
  filter_upwards [hlog, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℝ)] with k hsmall hL hk H hH hH'
  let L := Real.log k
  have hL₀ : 0 < L := by unfold L; linarith
  have hk₀ : 0 < k := by linarith
  have hs : L ^ 7 ≤ C * k := by
    change ‖L ^ (7 : ℝ)‖ ≤ C * ‖k ^ (1 : ℝ)‖ at hsmall
    rw [show L ^ (7 : ℝ) = L ^ (7 : ℕ) by exact Real.rpow_ofNat L 7,
      Real.rpow_one, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg hk₀.le] at hsmall
    exact hsmall
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hk
  have hsqrt : Real.sqrt (2 * Real.log (2 * k)) ≤ 2 * L := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [Real.log_mul (by norm_num) hk₀.ne']
    change 2 * (Real.log 2 + L) ≤ (2 * L) ^ 2
    nlinarith [mul_nonneg hL₀.le (sub_nonneg.mpr hL)]
  have hH₀ : 0 < H := by linarith
  have hmain : k ^ 3 / (1130496000 * L ^ 6) ≤ k ^ 3 / (17664000 * H ^ 6) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hp := pow_le_pow_left₀ hH₀.le hH' 6
    change H ^ 6 ≤ (2 * L) ^ 6 at hp
    nlinarith only [hp]
  have herr : k ^ 2 / (16000 * H) * Real.sqrt (2 * Real.log (2 * k)) ≤
      k ^ 2 * L / 8000 := by
    have hc : k ^ 2 / (16000 * H) ≤ k ^ 2 / 16000 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    calc
      _ ≤ k ^ 2 / (16000 * H) * (2 * L) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ (k ^ 2 / 16000) * (2 * L) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hscaled : k ^ 2 * L / 8000 ≤ k ^ 3 / (80000000000 * L ^ 6) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hs (sq_nonneg k)
    norm_num [C] at h
    nlinarith only [h]
  have hfinal : k ^ 3 / (10 ^ 10 * L ^ 6) + k ^ 3 / (80000000000 * L ^ 6) ≤
      k ^ 3 / (1130496000 * L ^ 6) := by
    have h := div_nonneg (show 0 ≤ k ^ 3 by positivity) (show 0 ≤ L ^ 6 by positivity)
    rw [mul_comm (10 ^ 10 : ℝ), mul_comm (80000000000 : ℝ), mul_comm (1130496000 : ℝ),
      ← div_div, ← div_div, ← div_div]
    norm_num
    linarith
  change k ^ 3 / (10 ^ 10 * L ^ 6) ≤ _
  linarith only [hfinal, hmain, herr, hscaled]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Filter MeasureTheory
open scoped BigOperators ENNReal

private theorem abs_max_sub_max_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (h : ∀ i, |f i - g i| ≤ C) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤ C := by
  classical
  apply abs_le.mpr
  constructor
  · have hle : Finset.univ.sup' Finset.univ_nonempty g
        ≤ Finset.univ.sup' Finset.univ_nonempty f + C := by
      apply Finset.sup'_le
      intro i hi
      linarith only [(abs_le.mp (h i)).1, Finset.le_sup' f hi]
    linarith
  · have hle : Finset.univ.sup' Finset.univ_nonempty f
        ≤ Finset.univ.sup' Finset.univ_nonempty g + C := by
      apply Finset.sup'_le
      intro i hi
      linarith only [(abs_le.mp (h i)).2, Finset.le_sup' g hi]
    linarith

private theorem pseudoSwapRegret_eq_robustSwapStep {K : ℕ} (s : ℕ)
    (q y : ℕ → Fin K → ℝ) :
    pseudoSwapRegret s q y = Finset.univ.sup' ⟨id, Finset.mem_univ id⟩
      (fun σ : Fin K → Fin K => ∑ t ∈ Finset.range s, robustSwapStep σ (q t) (y t)) := by
  unfold pseudoSwapRegret robustSwapStep dotProduct
  simp_rw [mul_sub, Finset.sum_sub_distrib]

private theorem robustHhat_eq_pseudoSwapRegret {K : ℕ} (hK : 0 < K) (T : ℕ) (ζ : ℝ)
    (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K) (r : ℕ → ℝ) (s : ℕ) :
    robustHhat T ζ q I r s = pseudoSwapRegret s q
      (fun t => robustYhat (followMix (robustEps T ζ) (q t)) (I t) (r t)) := by
  classical
  let _ : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  rw [pseudoSwapRegret_eq_sum_bestSwapGain]
  unfold robustHhat bestSwapGain
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sup'_univ_eq_ciSup (α := ℝ) (f := swapGain s q _ i)).symm

private theorem robustL_pos {K T s : ℕ} (hK : 0 < K) (hT : 0 < T) (hs : 0 < s) :
    0 < robustL K T s := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold robustL
  refine add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (Real.log_nonneg hk)) (Real.log_pos ?_)
  have ht₂ : (1 : ℝ) ≤ (T : ℝ) ^ 2 := one_le_pow₀ ht
  calc
    (1 : ℝ) < 4 * 1 * (1 + 1) * 1 := by norm_num
    _ ≤ _ := by gcongr

private theorem robustC_mul {K T s : ℕ} (ζ : ℝ) (hs : 0 < s) :
    (s : ℝ) * robustC K T ζ s =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) +
      (K * (T : ℝ) ^ ζ + 1) * robustL K T s / 3 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let c := 2 * (K * (T : ℝ) ^ ζ + 2) * robustL K T s
  have hfirst : (s : ℝ) * Real.sqrt (c / s) =
      Real.sqrt (2 * s * (K * (T : ℝ) ^ ζ + 2) * robustL K T s) := by
    rw [show (s : ℝ) * Real.sqrt (c / s) = Real.sqrt ((s : ℝ)^2 * (c / s)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs'.le]]
    congr 1
    dsimp [c]
    field_simp
  unfold robustC
  rw [mul_add]
  change _ + _ = _ + _
  rw [hfirst]
  congr 1
  field_simp

private theorem sum_reciprocal_succ_mul_succ (T : ℕ) :
    (∑ u ∈ Finset.range T, 1 / (((u : ℝ) + 1) * ((u : ℝ) + 2))) = 1 - 1 / (T + 1) := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

private theorem robustL_union_factor {K T u : ℕ} (hK : 0 < K) (hT : 0 < T) :
    (Fintype.card (Fin K → Fin K) : ℝ) * (2 * Real.exp (-robustL K T (u + 1))) =
      (1 / (2 * (T : ℝ) ^ 2)) * (1 / (((u : ℝ) + 1) * ((u : ℝ) + 2))) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, robustL, neg_add,
    Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hk]
  rw [Real.exp_log (by positivity)]
  push_cast
  field_simp [ne_of_gt hk]
  ring

private theorem measure_prefix_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {K T : ℕ} (hK : 0 < K) (hT : 0 < T) (bad : ℕ → (Fin K → Fin K) → Set Ω)
    (hbad : ∀ u < T, ∀ σ, P (bad u σ) ≤ 2 * ENNReal.ofReal (Real.exp (-robustL K T (u+1)))) :
    P (⋃ u ∈ Finset.range T, ⋃ σ, bad u σ) ≤
      ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let f (u : ℕ) := (1 / (2 * (T : ℝ) ^ 2)) * (1 / (((u : ℝ) + 1) * ((u : ℝ) + 2)))
  have hB (u : ℕ) (hu : u < T) : P (⋃ σ, bad u σ) ≤ ENNReal.ofReal (f u) := by
    calc
      _ ≤ ∑' σ, P (bad u σ) := measure_iUnion_le _
      _ ≤ ∑ _ : Fin K → Fin K, 2 * ENNReal.ofReal (Real.exp (-robustL K T (u+1))) := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun σ _ => hbad u hu σ
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        unfold f
        rw [← robustL_union_factor hK hT (u := u), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        norm_num
  calc
    _ ≤ ∑ u ∈ Finset.range T, P (⋃ σ, bad u σ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ Finset.range T, ENNReal.ofReal (f u) := Finset.sum_le_sum fun u hu => hB u (Finset.mem_range.mp hu)
    _ = ENNReal.ofReal (∑ u ∈ Finset.range T, f u) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => by unfold f; positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      unfold f
      rw [← Finset.mul_sum, sum_reciprocal_succ_mul_succ]
      exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

namespace QProtocolRun

variable {K T : ℕ} {ζ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : QProtocolRun K T P (robustPolicy K T ζ))

/-- Equation (C.11) for each prefix whose last round is in follow mode. -/
def robustEstimationGood : Set Ω :=
  {ω | ∀ u < T, ω ∈ run.robustFollowing u →
    |robustHhat T ζ (fun t => run.q t ω) (fun t => run.I t ω) (fun t => run.y t ω (run.I t ω)) (u+1)
      - pseudoSwapRegret (u+1) (fun t => run.q t ω) (fun t => run.y t ω)|
        ≤ (u+1 : ℕ) * robustC K T ζ (u+1)}

/-- Equation (C.12) for all recommendation prefixes. -/
def robustRecommendationGood : Set Ω :=
  {ω | ∀ u < T,
    |swapRegret (u+1) (fun t => run.y t ω) (fun t => run.J t ω)
      - pseudoSwapRegret (u+1) (fun t => run.q t ω) (fun t => run.y t ω)|
        ≤ (u+1 : ℕ) * robustC K T ζ (u+1)}

private theorem measurable_pseudoSwapRegret {s : ℕ} (hs : s ≤ T) :
    Measurable (fun ω => pseudoSwapRegret s (fun t => run.q t ω) (fun t => run.y t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  simp only [pseudoSwapRegret_eq_robustSwapStep, Finset.sup'_univ_eq_ciSup]
  apply Measurable.iSup
  intro σ
  apply Finset.measurable_sum
  intro t ht
  have h₁ := (Finset.mem_range.mp ht).trans_le hs
  have h₂ := run.info_le t h₁.le
  unfold robustSwapStep
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp ((run.q_measurable t h₁).mono h₂ le_rfl)).mul
    (((measurable_pi_apply (σ i)).comp ((run.y_measurable t h₁).mono h₂ le_rfl)).sub
      ((measurable_pi_apply i).comp ((run.y_measurable t h₁).mono h₂ le_rfl)))

private theorem measurable_recSwapRegret {s : ℕ} (hs : s ≤ T) :
    Measurable (fun ω => swapRegret s (fun t => run.y t ω) (fun t => run.J t ω)) := by
  classical
  let _ : Nonempty (Fin K → Fin K) := ⟨id⟩
  unfold swapRegret
  simp only [Finset.sup'_univ_eq_ciSup]
  apply Measurable.iSup
  intro σ
  apply Finset.measurable_sum
  intro t ht
  have ht' := (Finset.mem_range.mp ht).trans_le hs
  have h₂ := run.info_le t ht'.le
  have h₃ := run.info_le (t+1) (Nat.succ_le_of_lt ht')
  exact measurable_select ((run.J_measurable t ht').mono h₃ le_rfl) fun j =>
    (((measurable_pi_apply (σ j)).comp ((run.y_measurable t ht').mono h₂ le_rfl)).sub
      ((measurable_pi_apply j).comp ((run.y_measurable t ht').mono h₂ le_rfl)))

theorem measurableSet_robustEstimationGood : MeasurableSet run.robustEstimationGood := by
  unfold robustEstimationGood
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  have hs : u + 1 ≤ T := Nat.succ_le_of_lt hu
  have hM := (run.measurable_robustHhat (s := u+1) (t := u+1) le_rfl hs).mono
    (run.info_le _ hs) le_rfl
  have hA := measurableSet_le ((hM.sub (run.measurable_pseudoSwapRegret hs)).abs)
    (measurable_const (a := ((u+1 : ℕ) : ℝ) * robustC K T ζ (u+1)))
  exact ((run.info_le u hu.le _ (run.measurableSet_robustFollowing hu.le)).compl.union hA).congr
    (by ext ω; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]; tauto)

theorem measurableSet_robustRecommendationGood : MeasurableSet run.robustRecommendationGood := by
  unfold robustRecommendationGood
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
  have hs : u + 1 ≤ T := Nat.succ_le_of_lt hu
  exact measurableSet_le
    (((run.measurable_recSwapRegret hs).sub (run.measurable_pseudoSwapRegret hs)).abs) measurable_const

theorem measure_compl_robustEstimationGood (hK : 0 < K) (hT : 0 < T)
    (hε : robustEps T ζ ≤ 1 / 2) :
    P run.robustEstimationGoodᶜ ≤ ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let bad (u : ℕ) (σ : Fin K → Fin K) : Set Ω :=
    {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
      |∑ t ∈ Finset.range (u+1), run.robustEstimatorDifference σ t ω|}
  refine (measure_mono (show run.robustEstimationGoodᶜ ⊆ ⋃ u ∈ Finset.range T, ⋃ σ, bad u σ from ?_)).trans
    (measure_prefix_union P hK hT bad fun u hu σ => ?_)
  · intro ω hω
    simp only [Set.mem_compl_iff, robustEstimationGood, Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    by_contra! hb
    apply hω
    intro u hu hf
    rw [robustHhat_eq_pseudoSwapRegret hK]
    simp only [pseudoSwapRegret_eq_robustSwapStep]
    letI : Nonempty (Fin K → Fin K) := ⟨id⟩
    apply abs_max_sub_max_le
    intro σ
    rw [← Finset.sum_sub_distrib]
    have heq : ∀ t < u+1, robustSwapStep σ (run.q t ω)
        (robustYhat (followMix (robustEps T ζ) (run.q t ω)) (run.I t ω) (run.y t ω (run.I t ω))) -
        robustSwapStep σ (run.q t ω) (run.y t ω) = run.robustEstimatorDifference σ t ω := by
      intro t ht
      have htFollow : ω ∈ run.robustFollowing t := fun v hv => hf v (by omega)
      unfold robustEstimatorDifference
      rw [Set.indicator_of_mem htFollow, run.followedSwapScore_eq_robustSwapStep]
    rw [Finset.sum_congr rfl fun t ht => heq t (Finset.mem_range.mp ht)]
    exact not_lt.mp (hb u hu σ)
  · have hs : 0 < u+1 := by omega
    have hsT : u+1 ≤ T := by omega
    have hL := robustL_pos hK hT hs
    change P {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
        |∑ t ∈ Finset.range (u+1), run.robustEstimatorDifference σ t ω|} ≤ _
    rw [robustC_mul _ hs]
    refine bernstein_abs_tail P run.info hs (fun a n ha hn => run.toDrawRun.info_le_info ha (hn.trans hsT))
      (fun n hn => run.info_le n (hn.trans hsT)) (run.robustEstimatorDifference σ)
      (by positivity) (by positivity) hL ?_ ?_ ?_ ?_
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.2.1
    · exact fun t ht => (run.robustEstimatorDifference_bounds hK (ht.trans_le hsT) hε σ).2.2.2

theorem measure_compl_robustRecommendationGood (hK : 0 < K) (hT : 0 < T)
    (hε : robustEps T ζ ≤ 1 / 2) :
    P run.robustRecommendationGoodᶜ ≤ ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 2)) := by
  classical
  let bad (u : ℕ) (σ : Fin K → Fin K) : Set Ω :=
    {ω | (u+1 : ℕ) * robustC K T ζ (u+1) <
      |∑ t ∈ Finset.range (u+1), run.robustRecommendationDifference σ t ω|}
  refine (measure_mono (show run.robustRecommendationGoodᶜ ⊆ ⋃ u ∈ Finset.range T, ⋃ σ, bad u σ from ?_)).trans
    (measure_prefix_union P hK hT bad fun u hu σ => ?_)
  · intro ω hω
    simp only [Set.mem_compl_iff, robustRecommendationGood, Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    by_contra! hb
    apply hω
    intro u hu
    rw [pseudoSwapRegret_eq_robustSwapStep]
    unfold swapRegret
    letI : Nonempty (Fin K → Fin K) := ⟨id⟩
    apply abs_max_sub_max_le
    intro σ
    rw [← Finset.sum_sub_distrib]
    exact not_lt.mp (hb u hu σ)
  · have hs : 0 < u+1 := by omega
    have hsT : u+1 ≤ T := by omega
    have hL := robustL_pos hK hT hs
    have hp : (1 : ℝ) ≤ K * (T : ℝ) ^ ζ := by
      have hpos : 0 < (T : ℝ) ^ ζ := by positivity
      have ht1 : (1 : ℝ) ≤ (T : ℝ) ^ ζ := by
        have hT₀ : (0 : ℝ) ≤ T := by positivity
        have hi : ((T : ℝ) ^ ζ)⁻¹ ≤ 1 / 2 := by
          simpa only [robustEps, Real.rpow_neg hT₀] using hε
        linarith only [(inv_le_iff_one_le_mul₀ hpos).mp hi]
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hK) ht1
    have hc : Real.sqrt (2 * (u+1 : ℕ) * 1 * robustL K T (u+1)) +
          2 * robustL K T (u+1) / 3 ≤ (u+1 : ℕ) * robustC K T ζ (u+1) := by
      rw [robustC_mul _ hs]
      apply add_le_add
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hp]) (by positivity)) hL.le)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hp]) hL.le) (by norm_num)
    have hsub : bad u σ ⊆ {ω |
        Real.sqrt (2 * (u+1 : ℕ) * 1 * robustL K T (u+1)) + 2 * robustL K T (u+1) / 3 <
          |∑ t ∈ Finset.range (u+1), run.robustRecommendationDifference σ t ω|} := by
      intro ω hω
      exact hc.trans_lt hω
    refine (measure_mono hsub).trans ?_
    refine bernstein_abs_tail P run.info hs (fun a n ha hn => run.toDrawRun.info_le_info ha (hn.trans hsT))
      (fun n hn => run.info_le n (hn.trans hsT)) (run.robustRecommendationDifference σ)
      (by norm_num) (by norm_num) hL ?_ ?_ ?_ ?_
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.2.1
    · exact fun t ht => (run.robustRecommendationDifference_bounds (ht.trans_le hsT) σ).2.2.2

end QProtocolRun

end CalibeatBandit.Supplement

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open MeasureTheory Set
open scoped ENNReal

private theorem robust_inverse_square (T : ℕ) :
    (T : ℝ) ^ (-2 : ℝ) = ((T : ℝ) ^ (2 : ℕ))⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg (Nat.cast_nonneg T), Real.rpow_ofNat]

private theorem robustEps_le_half_of_four_le {T : ℕ}
    (hT : 4 ≤ T) {ζ : ℝ} (hζ : 1 / 2 ≤ ζ) :
    robustEps T ζ ≤ 1 / 2 := by
  have ht : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have ht1 : 1 ≤ (T : ℝ) := by linarith
  have hs := Real.sqrt_le_sqrt ht
  rw [show Real.sqrt (4 : ℝ) = 2 by norm_num] at hs
  have h := Real.rpow_le_rpow_of_exponent_le ht1 (show -ζ ≤ -(1 / 2) by linarith)
  refine h.trans ?_
  rw [Real.rpow_neg (Nat.cast_nonneg T), ← Real.sqrt_eq_rpow]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs

private theorem robustEps_mul_le_rate {K T : ℕ} {ζ : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hζ : 1 / 2 ≤ ζ) :
    robustEps T ζ * (T : ℝ) ≤ robustRate K T ζ := by
  have ht1 : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have ht₀ : 0 < (T : ℝ) := by linarith
  have hk1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hL := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 ht1)
  calc
    _ = (T : ℝ) ^ (-ζ + 1) := by
      unfold robustEps
      rw [Real.rpow_add ht₀, Real.rpow_one]
    _ ≤ (T : ℝ) ^ ((1 + ζ) / 2) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    _ ≤ _ := by
      unfold robustRate
      have hn : 0 ≤ (T : ℝ) ^ ((1 + ζ) / 2) := by positivity
      calc
        _ ≤ _ * _ := le_mul_of_one_le_left hn hk1
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

private theorem robust_one_action (y : ℕ → Fin 1 → ℝ) (I J : ℕ → Fin 1) (T : ℕ) :
    rewardLoss T y J I = 0 := by
  have h (f : Fin 1 → Fin 1) :
      ∑ t ∈ Finset.range T, (y t (f (J t)) - y t (I t)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Subsingleton.elim (f (J t)) (I t), sub_self]
  unfold rewardLoss
  simp_rw [h]
  exact Finset.sup'_const _ _

universe u

/-- Algorithm 2, with the switching threshold from the paper and the tuned
calibeating policy after the switch, satisfies both clauses of robust calibeating. -/
theorem theorem_3_5 :
    ∀ ζ : ℝ, 1 / 2 < ζ → ζ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ K T : ℕ, 1 ≤ K → 1 ≤ T →
        IsRobust.{u} K T
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (2 * (T : ℝ) ^ (-ζ) + (T : ℝ) ^ (-2 : ℝ))
          (robustC K T ζ) (robustPolicy K T ζ) := by
  intro ζ hζ _
  refine ⟨160, by norm_num, 1, ?_⟩
  intro K T hK hT
  have hpK : 0 < K := by omega
  have hpT : 0 < T := by omega
  have hz : 0 ≤ ζ := by linarith
  let R := robustRate K T ζ
  have hR : 1 ≤ R := robustRate_ge_one hK hT hz
  have threshNonneg : 0 ≤ robustC K T ζ T := by
    have hL := robustL_nonneg hK hT hT
    unfold robustC
    positivity
  have bad {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : QProtocolRun K T P (robustPolicy K T ζ))
      (hε : robustEps T ζ ≤ 1 / 2) :
      P (run.robustEstimationGood ∩ run.robustRecommendationGood)ᶜ ≤
        ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ)) := by
    rw [compl_inter, robust_inverse_square]
    have hE := run.measure_compl_robustEstimationGood hpK hpT hε
    have hJ := run.measure_compl_robustRecommendationGood hpK hpT hε
    refine (measure_union_le _ _).trans ((add_le_add hE hJ).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  constructor
  · intro Ω mΩ P iP run
    rw [← robustRate_normalize hpT ζ (160 : ℝ)]
    change (∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
      160 * R ∧ (∫ ω, rewardLoss T (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ 160 * R
    have trivial (h : (T : ℝ) ≤ 160 * R) :
        (∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P) ≤
          160 * R ∧ (∫ ω, rewardLoss T (fun t => run.y t ω)
            (fun t => run.J t ω) (fun t => run.I t ω) ∂P) ≤ 160 * R := by
      have hS := run.integrable_swapRegret_segment 0 T (by simp)
      have hR := run.integrable_rewardLoss_segment 0 T (by simp)
      simp only [zero_add] at hS hR
      have A := integral_mono hS (integrable_const (T : ℝ)) (fun ω =>
        rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
      have B := integral_mono hR (integrable_const (T : ℝ)) (fun ω =>
        rewardLoss_le_rounds _ _ _ (fun t ht i => run.y_mem t ht ω i))
      simp only [integral_const, probReal_univ, one_smul] at A B
      exact ⟨A.trans h, B.trans h⟩
    by_cases hsmall : 32 * R ≤ (T : ℝ)
    swap
    · exact trivial (by linarith)
    by_cases h1 : K = 1
    · subst K
      have hs (ω : Ω) : swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) = 0 :=
        robust_one_action _ _ _ _
      have hr (ω : Ω) : rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω)
          (fun t => run.I t ω) = 0 := robust_one_action _ _ _ _
      simp only [hs, hr, integral_zero]
      constructor <;> linarith
    have hT4 : 4 ≤ T := by
      have hTr : (4 : ℝ) ≤ T := by linarith
      exact_mod_cast hTr
    have hε := robustEps_le_half_of_four_le hT4 hζ.le
    let E := run.robustEstimationGood ∩ run.robustRecommendationGood
    have hE : MeasurableSet E :=
      run.measurableSet_robustEstimationGood.inter run.measurableSet_robustRecommendationGood
    have hprefix := run.robust_prefix_expected hK hT hz threshNonneg
      run.robustFollowLength run.measurable_robustFollowLength run.robustFollowLength_le
      (fun ω t ht => run.follows_before_length ht) E hE (bad P run hε)
      (fun _ hω => hω.1) (fun _ hω => hω.2)
    obtain ⟨he, hm, hm', hbound⟩ := robustRate_restart_parameters (by omega : 2 ≤ K) hT hz hsmall
    have hsuffix := run.robust_restart_regret hpK he hm hm'
    have hthresh : (T : ℝ) * robustC K T ζ T ≤ 20 * R :=
      robustThreshold_le_rate hK hT hz (by linarith)
    have hεR : robustEps T ζ * T ≤ R := robustEps_mul_le_rate hK hT hζ.le
    have hTinv : (T : ℝ) * (T : ℝ) ^ (-2 : ℝ) ≤ 1 := by
      have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
      have htp : 0 < (T : ℝ) := by linarith
      rw [robust_inverse_square, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).2 (by nlinarith [mul_nonneg htp.le (sub_nonneg.mpr ht)])
    have hpreS : (∫ ω, run.robustPrefixSwapRegret ω ∂P) ≤ 104 * R := by
      have hp := hprefix.1
      change (∫ ω, run.robustPrefixSwapRegret ω ∂P) ≤ _ at hp
      linarith [hp, hεR, hthresh, hTinv]
    have hpreR : (∫ ω, run.robustPrefixRewardLoss ω ∂P) ≤ 104 * R := by
      have hp := hprefix.2
      change (∫ ω, run.robustPrefixRewardLoss ω ∂P) ≤ _ at hp
      linarith [hp, hεR, hthresh, hTinv]
    have hspl := run.robustRegret_split
    exact ⟨hspl.1.trans (by linarith [hpreS, hsuffix.1, hbound]),
      hspl.2.trans (by linarith [hpreR, hsuffix.2, hbound])⟩
  · intro Ω mΩ P iP run ρ hρ₀ hρ₁ hcap
    by_cases hε : robustEps T ζ ≤ 1 / 2
    · let E := run.robustEstimationGood ∩ run.robustRecommendationGood
      have hE : MeasurableSet E :=
        run.measurableSet_robustEstimationGood.inter run.measurableSet_robustRecommendationGood
      apply run.robust_consistency_of_event hpK hpT hz ρ hρ₀ hρ₁ E hE (bad P run hε) _ hcap
      intro ω hω
      refine robust_never_crosses ζ (fun t => run.q t ω) (fun t => run.y t ω)
        (fun t => run.J t ω) (fun t => run.I t ω) (fun t => run.y t ω (run.I t ω))
        hω.2 ?_ ?_
      · intro s hs hst
        have he := hω.1.2 (s - 1) (by omega)
        rw [show s - 1 + 1 = s by omega] at he
        linarith only [(abs_le.mp he).1]
      · intro t ht hf
        linarith only [(abs_le.mp (hω.1.1 t ht hf)).2]
    · have hγ : 1 ≤ 2 * robustEps T ζ + (T : ℝ) ^ (-2 : ℝ) := by
        have h : (1 / 2 : ℝ) < robustEps T ζ := lt_of_not_ge hε
        linarith [Real.rpow_nonneg (Nat.cast_nonneg T) (-2 : ℝ)]
      exact run.robust_consistency_of_gamma_ge_one ρ _ hρ₀ hγ

end CalibeatBandit.Supplement

end

section

universe u

open MeasureTheory Filter Asymptotics CalibeatBandit CalibeatBandit.Supplement

set_option autoImplicit false in
theorem solution :
    ∀ ζ : ℝ, 1 / 2 < ζ → ζ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ K T : ℕ, 1 ≤ K → 1 ≤ T →
        IsRobust.{u} K T
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (2 * (T : ℝ) ^ (-ζ) + (T : ℝ) ^ (-2 : ℝ))
          (robustC K T ζ) (robustPolicy K T ζ) := CalibeatBandit.Supplement.theorem_3_5

end
