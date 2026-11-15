-- Prove2me | solution 1 for CalibeatBandit.pseudo_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T16:35:06.970865+00:00
-- url     : https://prove2.me/submissions/804bf97c-51ae-4ea6-8d92-95cc0507a293

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_rT

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
    (∀ ω, 2 * ∑ j, run.algX η μ t ω j / run.algP η μ t ω j ≤ 2 * K / (1 - μ)) := by
  classical
  let x (j : Fin K) (ω : Ω) := run.algX η μ t ω j
  let p (j : Fin K) (ω : Ω) := run.algP η μ t ω j
  let y (j : Fin K) (ω : Ω) := run.y t ω j
  let v (j : Fin K) (ω : Ω) := run.algV η μ t ω j
  let d := (Real.exp 1 - 2) * η
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hm := run.preDraw_le_ambient ht
  have hx₀ (j : Fin K) (ω : Ω) : 0 ≤ x j ω := (run.algX_prob η μ t ω).1 j
  have hx₁ (j : Fin K) (ω : Ω) : x j ω ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hx₀ k ω) (Finset.mem_univ j)).trans_eq (run.algX_prob η μ t ω).2
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
    (measurable_pi_apply j).comp (run.algX_measurable η μ ht)
  have hym (j : Fin K) : Measurable[run.preDraw t] (y j) :=
    (measurable_pi_apply j).comp ((run.y_measurable t ht).mono le_sup_left le_rfl)
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
      have hobs : run.obs t ω = y j ω := by simp [ProtocolRun.obs, y, h]
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
      run.I_law t ht j] with ω hmul hlaw
    change condExp (run.preDraw t) P (a j * indicator j) ω + b j ω = _
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

/-- Lemma C.5. The importance-weighted estimate has conditional mean equal to
the reward, leaving only the explicit correction in expectation. -/
theorem lemma_C_5 {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (_hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, ∑ t ∈ Finset.range T, run.algX η μ t ω ⬝ᵥ (run.algV η μ t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) := by
  classical
  let d := (Real.exp 1 - 2) * η
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hμ₁ : 0 < 1 - μ := by linarith
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hmin : 0 < μ / (K : ℝ) := div_pos hμ₀ hk
  let loss (t : ℕ) (j : Fin K) (ω : Ω) :=
    run.algX η μ t ω j * (run.algV η μ t ω j - run.y t ω j)
  have coordinate (t : ℕ) (ht : t < T) (j : Fin K) :
      Integrable (loss t j) P ∧ ∫ ω, loss t j ω ∂P ≤ d / (1 - μ) := by
    let x : Ω → ℝ := fun ω => run.algX η μ t ω j
    let p : Ω → ℝ := fun ω => run.algP η μ t ω j
    let y : Ω → ℝ := fun ω => run.y t ω j
    let ind : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
    let a : Ω → ℝ := fun ω => x ω * y ω / p ω
    let b : Ω → ℝ := fun ω => x ω * (d / p ω - y ω)
    have hm := run.preDraw_le_ambient ht
    have hx₀ (ω : Ω) : 0 ≤ x ω := (run.algX_prob η μ t ω).1 j
    have hx₁ (ω : Ω) : x ω ≤ 1 :=
      (Finset.single_le_sum (fun i _ => (run.algX_prob η μ t ω).1 i)
        (Finset.mem_univ j)).trans_eq (run.algX_prob η μ t ω).2
    have hy₀ (ω : Ω) : 0 ≤ y ω := (run.y_mem t ht ω j).1
    have hy₁ (ω : Ω) : y ω ≤ 1 := (run.y_mem t ht ω j).2
    have hp_eq (ω : Ω) : p ω = (1 - μ) * x ω + μ / K := rfl
    have hp₀ (ω : Ω) : μ / (K : ℝ) ≤ p ω := by
      rw [hp_eq]
      exact le_add_of_nonneg_left (mul_nonneg hμ₁.le (hx₀ ω))
    have hp (ω : Ω) : 0 < p ω := hmin.trans_le (hp₀ ω)
    have hxm : Measurable[run.preDraw t] x :=
      (measurable_pi_apply j).comp (run.algX_measurable η μ ht)
    have hym : Measurable[run.preDraw t] y :=
      (measurable_pi_apply j).comp ((run.y_measurable t ht).mono le_sup_left le_rfl)
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
      have hv : run.algV η μ t ω j =
          (if run.I t ω = j then run.obs t ω / p ω else 0) + d / p ω := rfl
      change x ω * (run.algV η μ t ω j - y ω) = a ω * ind ω + b ω
      rw [hv]
      by_cases h : run.I t ω = j
      · have hind₁ : ind ω = 1 := by simp [ind, h]
        have hobs : run.obs t ω = y ω := by simp [ProtocolRun.obs, y, h]
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
        run.I_law t ht j] with ω hmul hlaw
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
      run.algX η μ t ω ⬝ᵥ (run.algV η μ t ω - run.y t ω)) =
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

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- Conditional expectation of a bounded function evaluated at the played action. -/
theorem ProtocolRun.condExp_select_played {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {policy : Policy K}
    (run : ProtocolRun K T P policy) {t : ℕ} (ht : t < T)
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
theorem ProtocolRun.condExp_obs {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {policy : Policy K}
    (run : ProtocolRun K T P policy) {t : ℕ} (ht : t < T) :
    Integrable (run.obs t) P ∧
    condExp (run.preDraw t) P (run.obs t) =ᵐ[P]
      fun ω => run.played t ω ⬝ᵥ run.y t ω := by
  have h := run.condExp_select_played P ht (fun j ω => run.y t ω j)
    (fun j => (measurable_pi_apply j).comp ((run.y_measurable t ht).mono le_sup_left le_rfl)) 1
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
    obtain ⟨hi, heq⟩ := run.condExp_obs P ht
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

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem ProtocolRun.integral_exp_sum_le_one {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {policy : Policy K}
    (run : ProtocolRun K T P policy) (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[run.info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (run.preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[run.info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (run.info_le_info hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (run.info_le n hn) le_rfl)
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
        ((hm n hn).mono (run.info_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (show run.info n ≤ run.preDraw n from le_sup_left) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := run.preDraw n) (run.preDraw_le_ambient hn)]
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
theorem condExp_estimation_step {K T : ℕ} {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P (calibeatPolicy K η μ)) {t : ℕ} (ht : t < T)
    (f : Fin K → Fin K) (w : Ω → Fin K → ℝ) (hw : ∀ ω, IsProbVec (w ω))
    (hwm : Measurable[run.preDraw t] w) :
    condExp (run.preDraw t) P (fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - run.algV η μ t ω (f i)))) ≤ᵐ[P] fun _ => 1 := by
  classical
  let x (ω : Ω) := run.algX η μ t ω
  let p (ω : Ω) := run.algP η μ t ω
  let y (ω : Ω) := run.y t ω
  let d := (Real.exp 1 - 2) * η
  let g (j : Fin K) (ω : Ω) := Real.exp (η * ∑ i, w ω i *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i))))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₁ : η ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hμ₁ : μ ≤ 1 := by linarith
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hx (ω : Ω) : IsProbVec (x ω) := run.algX_prob η μ t ω
  have hp (ω : Ω) : IsProbVec (p ω) := explore_prob hK hμ₀.le hμ₁ (hx ω)
  have hp₀ (ω : Ω) (j : Fin K) : 0 < p ω j :=
    (div_pos hμ₀ hk).trans_le
      (le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hμ₁) ((hx ω).1 j)))
  have hp₁ (ω : Ω) (j : Fin K) : p ω j ≤ 1 :=
    (Finset.single_le_sum (fun i _ => (hp ω).1 i) (Finset.mem_univ j)).trans_eq (hp ω).2
  have hy (ω : Ω) (j : Fin K) : y ω j ∈ Set.Icc (0 : ℝ) 1 := run.y_mem t ht ω j
  have hmY (j : Fin K) : Measurable[run.preDraw t] (fun ω => y ω j) :=
    (measurable_pi_apply j).comp ((run.y_measurable t ht).mono le_sup_left le_rfl)
  have hmP (j : Fin K) : Measurable[run.preDraw t] (fun ω => p ω j) :=
    (((measurable_pi_apply j).comp (run.algX_measurable η μ ht)).const_mul _).add measurable_const
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
        apply mul_le_mul_of_nonneg_left _ ((hw ω).1 i)
        refine (sub_le_self _ ?_).trans (hy ω (f i)).2
        split
        · exact div_nonneg (add_nonneg (hy ω (f i)).1 hd) (hp₀ ω (f i)).le
        · exact div_nonneg hd (hp₀ ω (f i)).le
      _ = _ := by simp only [mul_one, (hw ω).2]
  obtain ⟨_, hce⟩ := run.condExp_select_played P ht g hg _ hgb
  have hselected : (fun ω => g (run.I t ω) ω) = fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))) := by
    funext ω
    apply congrArg Real.exp
    refine congrArg (η * ·) (Finset.sum_congr rfl fun i _ => ?_)
    dsimp [y, p]
    change w ω i * (run.y t ω (f i) - _) = w ω i * (run.y t ω (f i) -
      ((if run.I t ω = f i then run.obs t ω / run.algP η μ t ω (f i) else 0) +
        d / run.algP η μ t ω (f i)))
    by_cases e : run.I t ω = f i
    · simp [e, ProtocolRun.obs, add_div]
    · simp [e]
  rw [← hselected]
  filter_upwards [hce] with ω he
  rw [he]
  change ∑ j, p ω j * g j ω ≤ 1
  let a (j i : Fin K) := η *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i)))
  have hjensen (j : Fin K) : g j ω ≤ ∑ i, w ω i * Real.exp (a j i) := by
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := w ω) (p := a j)
      (fun i _ => (hw ω).1 i) (hw ω).2 (fun i _ => Set.mem_univ (a j i))
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
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ ((hw ω).1 i)
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
    _ = 1 := by simp only [mul_one, (hw ω).2]


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
    let D (t : ℕ) (f : Fin K → Fin K) (ω : Ω) :=
      ∑ i, w t ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))
    have hm (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
        Measurable[run.info (t + 1)] (D t f) := by
      refine Finset.measurable_sum _ fun i _ => ?_
      have hwi := (measurable_pi_apply i).comp
        ((hwm t ht).mono (run.preDraw_le_succ ht) le_rfl)
      have hyi := (measurable_pi_apply (f i)).comp
        ((run.y_measurable t ht).mono (run.info_mono t ht) le_rfl)
      exact hwi.mul (hyi.sub (run.algV_measurable η μ ht (f i)))
    have hb (t : ℕ) (ht : t < T) (f : Fin K → Fin K) (ω : Ω) :
        |D t f ω| ≤ 1 + 1 / η := by
      calc
        _ ≤ ∑ i, |w t ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, w t ω i * (1 + 1 / η) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hw₀ := (hw t ht ω).1 i
          rw [abs_mul, abs_of_nonneg hw₀]
          apply mul_le_mul_of_nonneg_left _ hw₀
          have hy := run.y_mem t ht ω (f i)
          have hv := run.algV_scaled_mem hK hη hμ hKη ht ω (f i)
          have hv₀ := nonneg_of_mul_nonneg_right hv.1 hη
          have hv₁ := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hv.2)
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, div_nonneg zero_le_one hη.le]⟩
        _ = _ := by rw [← Finset.sum_mul, (hw t ht ω).2, one_mul]
    let F (f : Fin K → Fin K) (ω : Ω) := ∑ t ∈ Finset.range T, D t f ω
    have hmF (f : Fin K → Fin K) : Measurable (F f) :=
      Finset.measurable_sum _ fun t ht =>
        (hm t (Finset.mem_range.mp ht) f).mono (run.info_le _ (Finset.mem_range.mp ht)) le_rfl
    have hbF (f : Fin K → Fin K) (ω : Ω) : |F f ω| ≤ T * (1 + 1 / η) := by
      calc
        _ ≤ ∑ t ∈ Finset.range T, |D t f ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (1 + 1 / η) := Finset.sum_le_sum fun t ht =>
          hb t (Finset.mem_range.mp ht) f ω
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hE (f : Fin K → Fin K) : (∫ ω, Real.exp (η * F f ω) ∂P) ≤ 1 := by
      have h := run.integral_exp_sum_le_one P (fun t ω => η * D t f ω)
        (fun t ht => (hm t ht f).const_mul η)
        (fun t ht ω => show |η * D t f ω| ≤ η * (1 + 1 / η) by
          rw [abs_mul, abs_of_pos hη]
          exact mul_le_mul_of_nonneg_left (hb t ht f ω) hη.le)
        (fun t ht => condExp_estimation_step hK hη hμ₀ hμ hKη P run ht f (w t)
          (hw t ht) (hwm t ht))
      simpa only [F, Finset.mul_sum] using h
    have h := integral_max_le_log_card P ⟨id, Finset.mem_univ _⟩ F hη hmF hbF hE
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h
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
theorem calibeatingDecomposition {K T : ℕ} (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
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
  have decompose (ω : Ω) := _root_.calibeatingDecomposition μ hμ₀.le (by linarith)
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

open CalibeatBandit MeasureTheory Matrix

set_option autoImplicit false

theorem solution {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, pseudoSwapRegret T (fun t => run.algP η μ t ω) (fun t => run.y t ω) ∂P ≤ rT K T η μ ∧
    ∫ ω, pseudoRewardLoss T (fun t => run.algP η μ t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P ≤ rT K T η μ := CalibeatBandit.pseudo_regret_bound hK hη hμ0 hμ hKη P run
