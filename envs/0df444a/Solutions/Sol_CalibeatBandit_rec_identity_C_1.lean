-- Prove2me | solution 1 for CalibeatBandit.rec_identity_C_1
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T16:35:07.96116+00:00
-- url     : https://prove2.me/submissions/ae622771-b7df-4e2c-98c6-3c314b71dddd

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss

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

open CalibeatBandit MeasureTheory Matrix

set_option autoImplicit false

theorem solution {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (policy : Policy K) (run : ProtocolRun K T P policy) :
    ∫ ω, pseudoRewardLoss T (fun t => run.played t ω) (fun t => run.y t ω) (fun t => run.J t ω) ∂P
      = ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        - ∑ t ∈ Finset.range T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P ∧
    ∀ t < T, ∫ ω, (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P = 0 := CalibeatBandit.rec_identity_C_1 P policy run
