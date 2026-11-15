-- Prove2me | solution 1 for CalibeatBandit.lemma_C_4
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T16:35:04.164589+00:00
-- url     : https://prove2.me/submissions/87dbeca5-da7c-4d1b-a648-f878e8c04dd5

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss

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

open CalibeatBandit MeasureTheory Matrix

set_option autoImplicit false

theorem solution {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : ProtocolRun K T P (calibeatPolicy K η μ)) :
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, ∑ i, run.algX η μ t ω i * (run.y t ω (f i) - run.algV η μ t ω (f i))) ∂P
      ≤ K * Real.log K / η ∧
    ∫ ω, Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
        ∑ t ∈ Finset.range T, (run.y t ω (f (run.J t ω)) - run.algV η μ t ω (f (run.J t ω)))) ∂P
      ≤ K * Real.log K / η := CalibeatBandit.lemma_C_4 hK hη hμ0 hμ hKη P run
