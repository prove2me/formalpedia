-- Prove2me | solution 1 for AvgRewardPMD.SPMD.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:22:22.26391+00:00
-- url     : https://prove2.me/submissions/34ec9a6b-9298-40dc-957e-fd0d7a908145

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Theorems.Thm_AvgRewardPMD_SPMD_lemma_4
import Theorems.Thm_AvgRewardPMD_SPMD_kl_uniform_le_log

open FoundationsML.ReinforcementLearning MeasureTheory ProbabilityTheory AvgRewardPMD.SPMD Filter

set_option linter.unusedSectionVars false

namespace SPMDThm1Aux

lemma term_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : x - y ≤ x * Real.log (x / y) := by
  rcases hx.eq_or_lt with h0 | hx
  · rw [← h0]; simp; linarith
  · have ht : 0 < x / y := div_pos hx hy
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
    rw [Real.log_inv] at h
    have hy' : y ≠ 0 := hy.ne'
    have hx' : x ≠ 0 := hx.ne'
    calc x - y = x * (1 - (x/y)⁻¹) := by field_simp
      _ ≤ x * Real.log (x / y) := mul_le_mul_of_nonneg_left (by linarith) hx.le

lemma term_gt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    x - y < x * Real.log (x / y) := by
  rcases hx.eq_or_lt with h0 | hx
  · rw [← h0]; simp; linarith
  · have ht : 0 < x / y := div_pos hx hy
    have h1 : (x/y)⁻¹ ≠ 1 := by
      intro h; apply hxy
      rw [inv_eq_one, div_eq_one_iff_eq hy.ne'] at h; exact h
    have h := Real.log_lt_sub_one_of_pos (inv_pos.2 ht) h1
    rw [Real.log_inv] at h
    have hy' : y ≠ 0 := hy.ne'
    have hx' : x ≠ 0 := hx.ne'
    calc x - y = x * (1 - (x/y)⁻¹) := by field_simp
      _ < x * Real.log (x / y) := mul_lt_mul_of_pos_left (by linarith) hx

lemma kl_nonneg' {A : Type*} [Fintype A] (p r : A → ℝ) (hp : p ∈ stdSimplex ℝ A)
    (hr : ∀ a, 0 < r a) (hrs : ∑ a, r a = 1) : 0 ≤ kl p r := by
  unfold kl
  have : ∑ a, (p a - r a) ≤ ∑ a, p a * Real.log (p a / r a) :=
    Finset.sum_le_sum fun a _ => term_ge _ _ (hp.1 a) (hr a)
  rw [Finset.sum_sub_distrib, hp.2, hrs] at this
  linarith

/-- The KL-prox minimizer (with no regularizer) is the Gibbs update. -/
lemma gibbs {A : Type*} [Fintype A] (lam : ℝ) (Q q qp : A → ℝ)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1) (hqp : qp ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * qp a + 0) + kl qp q ≤ lam * (∑ a, Q a * p a + 0) + kl p q) :
    ∀ a, qp a = q a * Real.exp (-(lam * Q a)) / ∑ b, q b * Real.exp (-(lam * Q b)) := by
  set Z := ∑ b, q b * Real.exp (-(lam * Q b)) with hZ
  have hne : (Finset.univ : Finset A).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (s := Finset.univ) (f := q) (by rw [hqs]; norm_num)
  have hZpos : 0 < Z := Finset.sum_pos (fun b _ => mul_pos (hq b) (Real.exp_pos _)) hne
  set ps : A → ℝ := fun a => q a * Real.exp (-(lam * Q a)) / Z with hps
  have hpspos : ∀ a, 0 < ps a := fun a => div_pos (mul_pos (hq a) (Real.exp_pos _)) hZpos
  have hpss : ∑ a, ps a = 1 := by
    simp only [ps]; rw [← Finset.sum_div]; exact div_self hZpos.ne'
  have hpsS : ps ∈ stdSimplex ℝ A := ⟨fun a => (hpspos a).le, hpss⟩
  have ident : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * p a + 0) + kl p q = kl p ps - Real.log Z := by
    intro p hp
    have key : ∀ a, p a * Real.log (p a / ps a)
        = lam * (Q a * p a) + p a * Real.log (p a / q a) + p a * Real.log Z := by
      intro a
      rcases (hp.1 a).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hqa : q a ≠ 0 := (hq a).ne'
        have hZ0 : Z ≠ 0 := hZpos.ne'
        have he : Real.exp (lam * Q a) ≠ 0 := (Real.exp_pos _).ne'
        have : p a / ps a = (p a / q a) * (Z * Real.exp (lam * Q a)) := by
          simp only [ps]; rw [Real.exp_neg]; field_simp
        rw [this, Real.log_mul (div_pos hpos (hq a)).ne' (mul_pos hZpos (Real.exp_pos _)).ne',
          Real.log_mul hZ0 he, Real.log_exp]
        ring
    unfold kl
    simp_rw [key]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp.2]
    ring
  have h1 := hmin ps hpsS
  rw [ident qp hqp, ident ps hpsS] at h1
  have hkl0 : kl ps ps = 0 := by
    unfold kl; apply Finset.sum_eq_zero; intro a _
    rw [div_self (hpspos a).ne', Real.log_one, mul_zero]
  rw [hkl0] at h1
  have hle : kl qp ps ≤ 0 := by linarith
  -- each term equality
  have hterm : ∀ a ∈ (Finset.univ : Finset A),
      0 ≤ qp a * Real.log (qp a / ps a) - (qp a - ps a) := fun a _ => by
    linarith [term_ge (qp a) (ps a) (hqp.1 a) (hpspos a)]
  have hsum : ∑ a, (qp a * Real.log (qp a / ps a) - (qp a - ps a)) = kl qp ps := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hqp.2, hpss]; unfold kl; ring
  have hsum0 : ∑ a, (qp a * Real.log (qp a / ps a) - (qp a - ps a)) = 0 := by
    apply le_antisymm (by linarith) (Finset.sum_nonneg hterm)
  intro a
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum0 a (Finset.mem_univ a)
  by_contra hne'
  have := term_gt (qp a) (ps a) (hqp.1 a) (hpspos a) hne'
  linarith

lemma kl_step {A : Type*} [Fintype A] (lam : ℝ) (hlam : 0 ≤ lam) (Q q ps pstar : A → ℝ)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1) (hpstar : pstar ∈ stdSimplex ℝ A)
    (hps : ∀ a, ps a = q a * Real.exp (-(lam * Q a)) / ∑ b, q b * Real.exp (-(lam * Q b))) :
    kl pstar ps ≤ kl pstar q + 2 * lam * ∑ a, |Q a| := by
  set Z := ∑ b, q b * Real.exp (-(lam * Q b)) with hZ
  have hne : (Finset.univ : Finset A).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (s := Finset.univ) (f := q) (by rw [hqs]; norm_num)
  have hZpos : 0 < Z := Finset.sum_pos (fun b _ => mul_pos (hq b) (Real.exp_pos _)) hne
  set M := ∑ a, |Q a| with hM
  have hQM : ∀ a, |Q a| ≤ M := fun a =>
    Finset.single_le_sum (f := fun b => |Q b|) (fun b _ => abs_nonneg (Q b)) (Finset.mem_univ a)
  have hdiff : kl pstar ps - kl pstar q = Real.log Z + lam * ∑ a, pstar a * Q a := by
    unfold kl
    rw [← Finset.sum_sub_distrib]
    have e : ∀ a, pstar a * Real.log (pstar a / ps a) - pstar a * Real.log (pstar a / q a)
        = pstar a * Real.log Z + lam * (pstar a * Q a) := by
      intro a
      rcases (hpstar.1 a).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · rw [hps a]
        have hqa : q a ≠ 0 := (hq a).ne'
        have hZ0 : Z ≠ 0 := hZpos.ne'
        have he : Real.exp (lam * Q a) ≠ 0 := (Real.exp_pos _).ne'
        have hpa : pstar a ≠ 0 := hpos.ne'
        have : pstar a / (q a * Real.exp (-(lam * Q a)) / Z)
            = (pstar a / q a) * (Z * Real.exp (lam * Q a)) := by
          rw [Real.exp_neg]; field_simp
        rw [this, Real.log_mul (div_pos hpos (hq a)).ne' (mul_pos hZpos (Real.exp_pos _)).ne',
          Real.log_mul hZ0 he, Real.log_exp, Real.log_div hpa hqa]
        ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hpstar.2, ← Finset.mul_sum]; ring
  have hZle : Z ≤ Real.exp (lam * M) := by
    calc Z ≤ ∑ b, q b * Real.exp (lam * M) := by
          apply Finset.sum_le_sum; intro b _
          apply mul_le_mul_of_nonneg_left _ (hq b).le
          apply Real.exp_le_exp.2
          have h1 : 0 ≤ M + Q b := by linarith [neg_abs_le (Q b), hQM b]
          nlinarith [mul_nonneg hlam h1]
      _ = Real.exp (lam * M) := by rw [← Finset.sum_mul, hqs, one_mul]
  have hlogZ : Real.log Z ≤ lam * M := by
    calc Real.log Z ≤ Real.log (Real.exp (lam * M)) := Real.log_le_log hZpos hZle
      _ = lam * M := Real.log_exp _
  have hPQ : ∑ a, pstar a * Q a ≤ M := by
    calc ∑ a, pstar a * Q a ≤ ∑ a, pstar a * M := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hQM a)) (hpstar.1 a)
      _ = M := by rw [← Finset.sum_mul, hpstar.2, one_mul]
  have := mul_le_mul_of_nonneg_left hPQ hlam
  linarith

lemma gibbs_pos {A : Type*} [Fintype A] (lam : ℝ) (Q q : A → ℝ) (hq : ∀ a, 0 < q a)
    (hqs : ∑ a, q a = 1) (a : A) :
    0 < q a * Real.exp (-(lam * Q a)) / ∑ b, q b * Real.exp (-(lam * Q b)) := by
  have hne : (Finset.univ : Finset A).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (s := Finset.univ) (f := q) (by rw [hqs]; norm_num)
  exact div_pos (mul_pos (hq a) (Real.exp_pos _))
    (Finset.sum_pos (fun b _ => mul_pos (hq b) (Real.exp_pos _)) hne)

section avg
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma stoch_pow_bound (M : Matrix S S ℝ) (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1)
    (v : S → ℝ) (B : ℝ) (hv : ∀ s, |v s| ≤ B) : ∀ t s, |((M ^ t).mulVec v) s| ≤ B := by
  intro t
  induction t with
  | zero => intro s; simpa using hv s
  | succ t ih =>
    intro s
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc |(M.mulVec ((M ^ t).mulVec v)) s|
        = |∑ s', M s s' * ((M ^ t).mulVec v) s'| := rfl
      _ ≤ ∑ s', |M s s' * ((M ^ t).mulVec v) s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', M s s' * B := by
          apply Finset.sum_le_sum; intro s' _
          rw [abs_mul, abs_of_nonneg (hM0 s s')]
          exact mul_le_mul_of_nonneg_left (ih s') (hM0 s s')
      _ = B := by rw [← Finset.sum_mul, hM1, one_mul]

lemma stateMatrix_nonneg (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A → ℝ)
    (hπ : IsPolicy π) (s s' : S) : 0 ≤ stateMatrix P π s s' := by
  simp only [stateMatrix, Matrix.of_apply, InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma stateMatrix_row (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A → ℝ)
    (hπ : IsPolicy π) (s : S) : ∑ s', stateMatrix P π s s' = 1 := by
  simp only [stateMatrix, Matrix.of_apply, InducedTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

lemma inducedReward_bound (π : S → A → ℝ) (hπ : IsPolicy π) (c : S → A → ℝ) (s : S) :
    |InducedReward π c s| ≤ ∑ s, ∑ a, |c s a| := by
  have hle1 : ∀ a, π s a ≤ 1 := fun a => by
    have := Finset.single_le_sum (f := π s) (fun b _ => (hπ s).1 b) (Finset.mem_univ a)
    rw [(hπ s).2] at this; exact this
  calc |InducedReward π c s| = |∑ a, π s a * c s a| := rfl
    _ ≤ ∑ a, |π s a * c s a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |c s a| := by
        apply Finset.sum_le_sum; intro a _
        rw [abs_mul, abs_of_nonneg ((hπ s).1 a)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hle1 a)
    _ ≤ ∑ s, ∑ a, |c s a| :=
        Finset.single_le_sum (f := fun s => ∑ a, |c s a|)
          (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ s)

lemma avgCost_bound (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (c : S → A → ℝ) (s₀ : S) :
    ∃ C, ∀ π : S → A → ℝ, IsPolicy π → |avgCost P π c s₀| ≤ C := by
  set B := ∑ s, ∑ a, |c s a|
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  refine ⟨max B |(Classical.choice (⟨0⟩ : Nonempty ℝ) : ℝ)|, fun π hπ => ?_⟩
  set u : ℕ → ℝ := fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s₀ with hu
  have hub : ∀ T, |u T| ≤ B := by
    intro T
    have hx := stoch_pow_bound (stateMatrix P π) (stateMatrix_nonneg P hP π hπ)
      (stateMatrix_row P hP π hπ) (InducedReward π c) B (inducedReward_bound π hπ c)
    rcases Nat.eq_zero_or_pos T with h0 | hT
    · simp [u, h0, hB]
    · simp only [u]
      rw [abs_mul, abs_inv, Nat.abs_cast]
      have hTpos : (0:ℝ) < T := by exact_mod_cast hT
      rw [inv_mul_le_iff₀ hTpos]
      calc |∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s₀|
          ≤ ∑ t ∈ Finset.range T, |(((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s₀| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.range T, B := Finset.sum_le_sum fun t _ => hx t s₀
        _ = T * B := by simp
  show |limUnder Filter.atTop u| ≤ _
  by_cases hc : ∃ x, Filter.Tendsto u Filter.atTop (nhds x)
  · obtain ⟨x, hx⟩ := hc
    rw [hx.limUnder_eq]
    have : |x| ≤ B := le_of_tendsto (hx.abs) (Filter.Eventually.of_forall hub)
    exact this.trans (le_max_left _ _)
  · rw [limUnder_of_not_tendsto hc]
    exact le_max_right _ _

lemma continuous_stateMatrix_pow (P : S → A → S → ℝ) (t : ℕ) :
    Continuous (fun π : S → A → ℝ => (stateMatrix P π) ^ t) := by
  induction t with
  | zero => simp only [pow_zero]; exact continuous_const
  | succ t ih =>
    simp only [pow_succ]
    refine ih.matrix_mul ?_
    refine continuous_pi fun s => continuous_pi fun s' => ?_
    simp only [stateMatrix, Matrix.of_apply, InducedTransition]
    fun_prop

lemma measurable_avgCost (P : S → A → S → ℝ) (c : S → A → ℝ) (s₀ : S) :
    Measurable (fun π : S → A → ℝ => avgCost P π c s₀) := by
  have hf : ∀ T : ℕ, StronglyMeasurable (fun π : S → A → ℝ => (T : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s₀) := by
    intro T
    apply Continuous.stronglyMeasurable
    refine continuous_const.mul (continuous_finsetSum _ fun t _ => ?_)
    have h1 := (continuous_stateMatrix_pow P t).matrix_mulVec
      (show Continuous (fun π : S → A → ℝ => InducedReward π c) by
        refine continuous_pi fun s => ?_
        simp only [InducedReward]; fun_prop)
    exact (continuous_apply s₀).comp h1
  exact (StronglyMeasurable.limUnder hf).measurable

end avg

end SPMDThm1Aux

open SPMDThm1Aux in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P) (c : S → A → ℝ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (bias κ : ℝ) (hκ : 0 < κ) (K : ℕ) (hK : 1 ≤ K) (lam : ℝ)
    (hlam : lam = 2 * Real.sqrt (Real.log (Fintype.card A)) / (κ * Real.sqrt K))
    (hiter : IsSPMDIterates (fun _ _ => 0) (fun _ => lam) Qhat π)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' c) Qhat π bias κ K) (s₀ : S) :
    (∫ ξ, ∑ k ∈ Finset.range K, (avgCost P (π k ξ) c s₀ - avgCost P πstar c s₀) ∂μ
        ≤ κ * Real.sqrt (K * Real.log (Fintype.card A)) + K * bias) ∧
    (∀ r : Ω → ℕ, Measurable r → (∀ i < K, μ {ξ | r ξ = i} = (K : ENNReal)⁻¹) →
      IndepFun r (fun ξ k => π k ξ) μ →
      ∫ ξ, (avgCost P (π (r ξ) ξ) c s₀ - avgCost P πstar c s₀) ∂μ
        ≤ κ * Real.sqrt (Real.log (Fintype.card A)) / Real.sqrt K + bias) := by
  classical
  obtain ⟨νstar, hνstar, -⟩ := (Classical.choose_spec hmix) πstar hπstar
  have hνS : νstar ∈ stdSimplex ℝ S := ⟨hνstar.1.1, hνstar.1.2⟩
  have hAne : (Finset.univ : Finset A).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (s := Finset.univ) (f := πstar s₀)
      (by rw [(hπstar s₀).2]; norm_num)
  obtain ⟨a₀, -⟩ := hAne
  have hcardpos : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨a₀⟩
  set Lg := Real.log (Fintype.card A) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by
    have : 1 ≤ Fintype.card A := Fintype.card_pos_iff.2 ⟨a₀⟩
    exact_mod_cast this)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  -- pathwise structure of the iterates
  have hpol : ∀ k ξ, IsPolicy (π k ξ) ∧ ∀ s a, 0 < π k ξ s a := by
    intro k ξ
    induction k with
    | zero =>
      have h0 := (hiter ξ).1
      refine ⟨fun s => ⟨fun a => by rw [h0]; positivity, ?_⟩, fun s a => by rw [h0]; positivity⟩
      simp_rw [h0]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    | succ k ih =>
      have hk := fun s => (hiter ξ).2 k s
      have hform := fun s => gibbs lam (fun a => Qhat k ξ (s, a)) (π k ξ s) (π (k+1) ξ s)
        (ih.2 s) (ih.1 s).2 (hk s).1 (hk s).2
      refine ⟨fun s => ⟨(hk s).1.1, (hk s).1.2⟩, fun s a => ?_⟩
      rw [hform s a]
      exact gibbs_pos lam (fun a => Qhat k ξ (s, a)) _ (ih.2 s) (ih.1 s).2 a
  set D : ℕ → Ω → ℝ := fun k ξ => stationaryKL νstar (π k ξ) πstar with hD
  have hDnn : ∀ k ξ, 0 ≤ D k ξ := by
    intro k ξ
    simp only [D, stationaryKL]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hνstar.1.1 s)
      (kl_nonneg' _ _ ⟨(hπstar s).1, (hπstar s).2⟩ ((hpol k ξ).2 s) ((hpol k ξ).1 s).2)
  set Mq : ℕ → Ω → ℝ := fun k ξ => ∑ s, νstar s * ∑ a, |Qhat k ξ (s, a)| with hMq
  have hDstep : ∀ k ξ, D (k+1) ξ ≤ D k ξ + 2 * lam * Mq k ξ := by
    intro k ξ
    simp only [D, stationaryKL, Mq]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro s _
    have hk := (hiter ξ).2 k s
    have hform := gibbs lam (fun a => Qhat k ξ (s, a)) (π k ξ s) (π (k+1) ξ s)
        ((hpol k ξ).2 s) ((hpol k ξ).1 s).2 hk.1 hk.2
    have := kl_step lam hlam0 (fun a => Qhat k ξ (s, a)) (π k ξ s) (π (k+1) ξ s) (πstar s)
      ((hpol k ξ).2 s) ((hpol k ξ).1 s).2 ⟨(hπstar s).1, (hπstar s).2⟩ hform
    have := mul_le_mul_of_nonneg_left this (hνstar.1.1 s)
    nlinarith
  have hD0 : ∀ ξ, D 0 ξ ≤ Lg := by
    intro ξ
    have h0 : π 0 ξ = fun _ _ => 1 / (Fintype.card A : ℝ) := by
      funext s a; exact (hiter ξ).1 s a
    simp only [D]; rw [h0]
    exact kl_uniform_le_log νstar hνS πstar hπstar
  have hDbound : ∀ k ξ, D k ξ ≤ Lg + ∑ j ∈ Finset.range k, 2 * lam * Mq j ξ := by
    intro k ξ
    induction k with
    | zero => simpa using hD0 ξ
    | succ k ih => rw [Finset.sum_range_succ]; linarith [hDstep k ξ]
  -- measurability / integrability
  have hmeasπ : ∀ k ≤ K, ∀ s a, Measurable (fun ξ => π k ξ s a) := fun k hk s a =>
    (hcrit.1 k hk s a).mono (ℱ.le k) le_rfl
  have hMqint : ∀ k < K, Integrable (Mq k) μ := by
    intro k hk
    simp only [Mq]
    refine integrable_finsetSum _ fun s _ => ?_
    exact (integrable_finsetSum _ fun a _ => (hcrit.2.1 k hk (s, a)).abs).const_mul _
  have hDmeas : ∀ k ≤ K, Measurable (D k) := by
    intro k hk
    simp only [D, stationaryKL, kl]
    refine Finset.measurable_sum _ fun s _ => ?_
    refine Measurable.const_mul (Finset.measurable_sum _ fun a _ => ?_) _
    exact ((measurable_const.div (hmeasπ k hk s a)).log).const_mul _
  have hDint : ∀ k ≤ K, Integrable (D k) μ := by
    intro k hk
    have hgint : Integrable (fun ξ => Lg + ∑ j ∈ Finset.range k, 2 * lam * Mq j ξ) μ := by
      refine (integrable_const Lg).add (integrable_finsetSum _ fun j hj => ?_)
      have := Finset.mem_range.1 hj
      exact (hMqint j (by omega)).const_mul (2 * lam)
    refine Integrable.mono' hgint
      (hDmeas k hk).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn k ξ)]
    exact hDbound k ξ
  obtain ⟨C, hC⟩ := avgCost_bound P hP c s₀
  set gap : ℕ → Ω → ℝ := fun k ξ => avgCost P (π k ξ) c s₀ - avgCost P πstar c s₀ with hgap
  have hgapmeas : ∀ k ≤ K, Measurable (gap k) := by
    intro k hk
    have : Measurable (fun ξ => π k ξ) :=
      measurable_pi_lambda _ fun s => measurable_pi_lambda _ fun a => hmeasπ k hk s a
    exact ((measurable_avgCost P c s₀).comp this).sub_const _
  have hgapbd : ∀ k ξ, |gap k ξ| ≤ C + C := by
    intro k ξ
    simp only [gap]
    calc |avgCost P (π k ξ) c s₀ - avgCost P πstar c s₀|
        ≤ |avgCost P (π k ξ) c s₀| + |avgCost P πstar c s₀| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC _ (hpol k ξ).1) (hC _ hπstar)
  have hgapint : ∀ k ≤ K, Integrable (gap k) μ := fun k hk =>
    Integrable.of_bound (hgapmeas k hk).aestronglyMeasurable (C + C)
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hgapbd k ξ)
  -- bias is nonnegative
  have hbias : 0 ≤ bias := by
    have h := hcrit.2.2.1 0 (by omega)
    obtain ⟨ξ, hξ⟩ := h.exists
    refine le_trans ?_ hξ
    simp only [span]
    set x := fun x => μ[fun ξ' => Qhat 0 ξ' x | ℱ 0] ξ - diffQ P (π 0 ξ) c x
    have hb := (Set.finite_range x).bddAbove
    have hb' := (Set.finite_range x).bddBelow
    have := (ciInf_le hb' (s₀, a₀)).trans (le_ciSup hb (s₀, a₀))
    linarith
  -- one-step inequality from Lemma 4
  have hQbar : ∀ n ≤ K, CriticAssumption μ ℱ
      (fun π' => diffQ P π' (fun s a => c s a + (fun (_ : S) (_ : A → ℝ) => (0:ℝ)) s (π' s)))
      Qhat π bias κ n := by
    intro n hn
    simp only [add_zero]
    obtain ⟨h1, h2, h3, h4⟩ := hcrit
    exact ⟨fun k hk => h1 k (hk.trans hn), fun k hk => h2 k (hk.trans_le hn),
      fun k hk => h3 k (hk.trans_le hn), fun k hk => h4 k (hk.trans_le hn)⟩
  have hconv : IsKLStrongConvex (fun (_ : S) (_ : A → ℝ) => (0:ℝ)) 0 := by
    intro s
    refine ⟨le_rfl, convexOn_const _ (convex_stdSimplex ℝ A), fun p' _ _ => ⟨0, fun p _ => ?_⟩⟩
    simp
  have hLip : IsL1Lipschitz (fun (_ : S) (_ : A → ℝ) => (0:ℝ)) 0 := by
    intro s p _ p' _; simp
  have step : ∀ k < K, lam * ∫ ξ, gap k ξ ∂μ + ∫ ξ, D (k+1) ξ ∂μ
      ≤ ∫ ξ, D k ξ ∂μ + lam * bias + lam ^ 2 * (κ ^ 2 / 4) := by
    intro k hk
    have L4 := lemma_4 P hP hmix c (fun _ _ => 0) 0 0 hconv hLip πstar hπstar νstar hνstar μ ℱ
      Qhat π (fun _ => lam) k (fun _ _ => hlam0) bias κ hiter (hQbar (k+1) hk) s₀
    simp only [add_zero, mul_zero, one_mul] at L4
    rw [integral_add ((hgapint k hk.le).const_mul lam) (hDint (k+1) hk), integral_const_mul] at L4
    have e : lam ^ 2 * (κ ^ 2 / 4 + (0:ℝ) ^ 2) = lam ^ 2 * (κ ^ 2 / 4) := by ring
    simp only [gap, D]
    linarith
  -- telescoping
  have tele : ∀ n ≤ K, lam * ∑ k ∈ Finset.range n, ∫ ξ, gap k ξ ∂μ + ∫ ξ, D n ξ ∂μ
      ≤ ∫ ξ, D 0 ξ ∂μ + n * (lam * bias + lam ^ 2 * (κ ^ 2 / 4)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := step n (by omega)
      rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith
  have hd0 : ∫ ξ, D 0 ξ ∂μ ≤ Lg := by
    calc ∫ ξ, D 0 ξ ∂μ ≤ ∫ _ξ, Lg ∂μ :=
          integral_mono (hDint 0 (by omega)) (integrable_const _) hD0
      _ = Lg := by simp
  have hdK : 0 ≤ ∫ ξ, D K ξ ∂μ := integral_nonneg (hDnn K)
  have hmain : ∑ k ∈ Finset.range K, ∫ ξ, gap k ξ ∂μ ≤ κ * Real.sqrt (K * Lg) + K * bias := by
    rcases hLg0.eq_or_lt with hL0 | hLpos
    · -- |A| = 1: every policy equals πstar
      have hcard1 : Fintype.card A = 1 := by
        have h := hL0.symm
        rw [hLg, Real.log_eq_zero] at h
        rcases h with h | h | h
        · linarith
        · exact_mod_cast h
        · linarith
      obtain ⟨a1, ha1⟩ := Fintype.card_eq_one_iff.1 hcard1
      have hpe : ∀ p : S → A → ℝ, IsPolicy p → p = πstar := by
        intro p hp
        funext s a
        have e1 := (hp s).2
        have e2 := (hπstar s).2
        rw [Fintype.sum_eq_single a1 (fun b hb => absurd (ha1 b) hb)] at e1 e2
        rw [ha1 a, e1, e2]
      have hz : ∀ k, ∫ ξ, gap k ξ ∂μ = 0 := by
        intro k
        have : gap k = fun _ => 0 := by
          funext ξ; simp only [gap]; rw [hpe _ (hpol k ξ).1]; ring
        rw [this]; simp
      simp only [hz, Finset.sum_const_zero, ← hL0, mul_zero, Real.sqrt_zero, zero_add]
      positivity
    · have hlampos : 0 < lam := by rw [hlam]; positivity
      have hT := tele K le_rfl
      have hsL := Real.sq_sqrt hLg0
      have hsK := Real.sq_sqrt hKpos.le
      have hsLpos : 0 < Real.sqrt Lg := Real.sqrt_pos.2 hLpos
      have hsKpos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
      rw [Real.sqrt_mul hKpos.le]
      set sL := Real.sqrt Lg with hsLdef
      set t := Real.sqrt (K : ℝ) with htdef
      have e1 : (K : ℝ) * (lam ^ 2 * (κ ^ 2 / 4)) = Lg := by
        rw [hlam, ← hsK, ← hsL]
        field_simp
        ring
      have e2 : lam * (κ * (t * sL)) = 2 * Lg := by
        rw [hlam, ← hsL]
        field_simp
      have key : lam * (∑ k ∈ Finset.range K, ∫ ξ, gap k ξ ∂μ)
          ≤ lam * (κ * (Real.sqrt K * Real.sqrt Lg) + K * bias) := by
        rw [mul_add, e2]
        nlinarith
      exact le_of_mul_le_mul_left key hlampos
  refine ⟨?_, ?_⟩
  · rw [integral_finsetSum _ fun k hk => hgapint k (Finset.mem_range.1 hk).le]
    exact hmain
  · intro r hr hunif hind
    -- r < K almost surely
    have hrK : ∀ᵐ ξ ∂μ, r ξ < K := by
      have hU : μ {ξ | r ξ < K} = 1 := by
        have hset : {ξ | r ξ < K} = ⋃ i ∈ Finset.range K, {ξ | r ξ = i} := by
          ext ξ; simp
        rw [hset, measure_biUnion_finset]
        · rw [Finset.sum_congr rfl fun i hi => hunif i (Finset.mem_range.1 hi)]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          exact ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : K ≠ 0)) (by simp)
        · intro i _ j _ hij
          exact Set.disjoint_left.2 fun ξ h1 h2 => hij (h1.symm.trans h2)
        · intro i _; exact hr (measurableSet_singleton i)
      have hms : MeasurableSet {ξ | r ξ < K} := hr measurableSet_Iio
      rw [ae_iff]
      have : {a | ¬ r a < K} = {ξ | r ξ < K}ᶜ := by ext; simp
      rw [this, prob_compl_eq_zero_iff hms]
      exact hU
    set ind : ℕ → Ω → ℝ := fun i ξ => if r ξ = i then 1 else 0 with hind_def
    have hcongr : (fun ξ => avgCost P (π (r ξ) ξ) c s₀ - avgCost P πstar c s₀)
        =ᵐ[μ] fun ξ => ∑ i ∈ Finset.range K, ind i ξ * gap i ξ := by
      filter_upwards [hrK] with ξ hξ
      simp only [ind, gap, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp [hξ]
    have hindmeas : ∀ i, Measurable (ind i) := fun i =>
      (measurable_of_countable (fun n : ℕ => if n = i then (1:ℝ) else 0)).comp hr
    have hterm : ∀ i ∈ Finset.range K, ∫ ξ, ind i ξ * gap i ξ ∂μ = (K : ℝ)⁻¹ * ∫ ξ, gap i ξ ∂μ := by
      intro i hi
      have hiK := Finset.mem_range.1 hi
      have hI : IndepFun (ind i) (gap i) μ := by
        have := hind.comp (measurable_of_countable (fun n : ℕ => if n = i then (1:ℝ) else 0))
          (((measurable_avgCost P c s₀).comp (measurable_pi_apply i)).sub_const
            (avgCost P πstar c s₀))
        exact this
      rw [hI.integral_fun_mul_eq_mul_integral (hindmeas i).aestronglyMeasurable
        (hgapmeas i hiK.le).aestronglyMeasurable]
      congr 1
      have : ind i = Set.indicator {ξ | r ξ = i} 1 := by
        funext ξ; simp only [ind, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
      rw [this, integral_indicator_one (show MeasurableSet {ξ | r ξ = i} from hr (measurableSet_singleton i)), Measure.real,
        hunif i hiK, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [integral_congr_ae hcongr, integral_finsetSum _ fun i hi => ?_]
    · rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKpos.le
      have hsKpos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
      have hm := mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hKpos.le)
      calc (K : ℝ)⁻¹ * ∑ i ∈ Finset.range K, ∫ ξ, gap i ξ ∂μ
          ≤ (K : ℝ)⁻¹ * (κ * Real.sqrt (K * Lg) + K * bias) := hm
        _ = κ * Real.sqrt Lg / Real.sqrt K + bias := by
          rw [Real.sqrt_mul hKpos.le]
          set t := Real.sqrt (K : ℝ) with htdef
          rw [← hsK]
          field_simp
    · have hiK := Finset.mem_range.1 hi
      refine Integrable.of_bound ((hindmeas i).mul (hgapmeas i hiK.le)).aestronglyMeasurable
        (C + C) (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |ind i ξ| ≤ 1 := by simp only [ind]; split_ifs <;> simp
      calc |ind i ξ| * |gap i ξ| ≤ 1 * (C + C) :=
            mul_le_mul h1 (hgapbd i ξ) (abs_nonneg _) zero_le_one
        _ = C + C := one_mul _
