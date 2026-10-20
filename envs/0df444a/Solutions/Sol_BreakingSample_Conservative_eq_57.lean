-- Prove2me | solution 1 for BreakingSample.Conservative.eq_57
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T03:58:52.979904+00:00
-- url     : https://prove2.me/submissions/94df2626-f2d9-40e8-b02d-5cdb0eb51061

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Perturbed_Absorbing
import Definitions.Def_BreakingSample_Conservative_Rule

set_option autoImplicit false

open Matrix

theorem bs1_mp {S : Type} [Fintype S] (M : Matrix S S ℝ) (hM0 : ∀ s s', 0 ≤ M s s')
    (hM1 : ∀ s, ∑ s', M s s' = 1) (γ c : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (y : S → ℝ)
    (h : ∀ s, y s ≤ c + γ * ∑ s', M s s' * y s') : ∀ s, y s ≤ c / (1 - γ) := by
  intro s
  have : Nonempty S := ⟨s⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max y
  have hsum : ∑ s', M s0 s' * y s' ≤ y s0 := by
    calc ∑ s', M s0 s' * y s' ≤ ∑ s', M s0 s' * y s0 :=
          Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hs0 s') (hM0 s0 s'))
      _ = y s0 := by rw [← Finset.sum_mul, hM1, one_mul]
  have h1 := h s0
  have h2 : y s0 * (1 - γ) ≤ c := by nlinarith
  calc y s ≤ y s0 := hs0 s
    _ ≤ c / (1 - γ) := by rw [le_div_iff₀ (by linarith)]; exact h2


open FoundationsML.ReinforcementLearning in
theorem bs1_D_prob {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1) (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · show 0 ≤ (if s = s0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ s, (if s = s0 then (1 : ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · show 0 ≤ ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s'
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (hT0 s s'))
    · show ∑ s', ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hT1, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem bs1_D_front {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    show ∑ s, (if s = s0 then (1 : ℝ) else 0) * InducedTransition π P s u =
      ∑ s', InducedTransition π P s0 s' * (if u = s' then (1 : ℝ) else 0)
    simp
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          show ∑ v, OccupationDist π P s0 (t + 1) v * InducedTransition π P v u = _
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := rfl

open FoundationsML.ReinforcementLearning in
theorem bs1_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := bs1_D_prob π P hT0 hT1 s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning in
theorem bs1_bellman_gen {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => bs1_summable π P hT0 hT1 γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [bs1_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    show γ ^ 0 * ∑ u, (if u = s then (1 : ℝ) else 0) * InducedReward π Er u = _
    simp
  rw [h0]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_it_det {S A : Type} [Fintype A] [DecidableEq A] (π : S → A) (P : S → A → S → ℝ)
    (s s' : S) : InducedTransition (detPolicy π) P s s' = P s (π s) s' := by
  simp [InducedTransition, detPolicy]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_ir_det {S A : Type} [Fintype A] [DecidableEq A] (π : S → A) (r : S → A → ℝ)
    (s : S) : InducedReward (detPolicy π) r s = r s (π s) := by
  simp [InducedReward, detPolicy]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_value_bellman {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) (s : S) :
    value P r γ π s = policyReward r π s
      + γ * ∑ s', policyMatrix P π s s' * value P r γ π s' := by
  unfold value
  rw [bs1_bellman_gen (detPolicy π) P (fun s s' => by rw [bs1_it_det]; exact (hP s (π s)).1 s')
    (fun s => by simp_rw [bs1_it_det]; exact (hP s (π s)).2) r γ hγ0 hγ1 s]
  simp only [bs1_it_det, bs1_ir_det, policyReward, policyMatrix]


-- ===== eq_56: Bellman optimality, verification, reward-Lipschitz, net =====

theorem bs56_sum_le {S : Type} [Fintype S] (m f g : S → ℝ) (hm0 : ∀ y, 0 ≤ m y)
    (hm1 : ∑ y, m y = 1) (c : ℝ) (h : ∀ y, f y ≤ g y + c) :
    ∑ y, m y * f y ≤ ∑ y, m y * g y + c := by
  calc ∑ y, m y * f y ≤ ∑ y, m y * (g y + c) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (hm0 y))
    _ = ∑ y, m y * g y + c := by
        rw [Finset.sum_congr rfl (fun y _ => mul_add (m y) (g y) c), Finset.sum_add_distrib,
          ← Finset.sum_mul, hm1, one_mul]

theorem bs56_sup_le {A : Type} [Fintype A] [Nonempty A] (f g : A → ℝ) (c : ℝ)
    (h : ∀ a, f a ≤ g a + c) :
    Finset.univ.sup' Finset.univ_nonempty f ≤ Finset.univ.sup' Finset.univ_nonempty g + c := by
  apply Finset.sup'_le
  intro a _
  have h1 : g a ≤ Finset.univ.sup' Finset.univ_nonempty g := Finset.le_sup' g (Finset.mem_univ a)
  linarith [h a]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs56_verify {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W : S → ℝ)
    (hW : ∀ x, W x = Finset.univ.sup' Finset.univ_nonempty
        (fun b => r x b + γ * ∑ y, P x b y * W y)) :
    ∀ x, optValue P r γ x = W x := by
  have hup : ∀ π : S → A, ∀ x, value P r γ π x ≤ W x := by
    intro π
    have hmp := bs1_mp (policyMatrix P π) (fun s s' => (hP s (π s)).1 s')
      (fun s => (hP s (π s)).2) γ 0 hγ0 hγ1 (fun x => value P r γ π x - W x) (fun x => by
        show value P r γ π x - W x ≤
          0 + γ * ∑ s', policyMatrix P π x s' * (value P r γ π s' - W s')
        have h1 := bs1_value_bellman P hP r γ hγ0 hγ1 π x
        have h2 : r x (π x) + γ * ∑ y, P x (π x) y * W y ≤ W x :=
          le_of_le_of_eq (Finset.le_sup' (fun b => r x b + γ * ∑ y, P x b y * W y)
            (Finset.mem_univ (π x))) (hW x).symm
        simp only [policyReward, policyMatrix] at h1 ⊢
        simp only [mul_sub, Finset.sum_sub_distrib]
        linarith)
    intro x
    have h3 : value P r γ π x - W x ≤ 0 / (1 - γ) := hmp x
    rw [zero_div] at h3
    linarith
  have hex : ∀ x, ∃ b, W x = r x b + γ * ∑ y, P x b y * W y := by
    intro x
    obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun b => r x b + γ * ∑ y, P x b y * W y)
    exact ⟨b, (hW x).trans hb⟩
  choose πg hπg using hex
  have hlow : ∀ x, W x ≤ value P r γ πg x := by
    have hmp := bs1_mp (policyMatrix P πg) (fun s s' => (hP s (πg s)).1 s')
      (fun s => (hP s (πg s)).2) γ 0 hγ0 hγ1 (fun x => W x - value P r γ πg x) (fun x => by
        show W x - value P r γ πg x ≤
          0 + γ * ∑ s', policyMatrix P πg x s' * (W s' - value P r γ πg s')
        have h1 := bs1_value_bellman P hP r γ hγ0 hγ1 πg x
        simp only [policyReward, policyMatrix] at h1 ⊢
        simp only [mul_sub, Finset.sum_sub_distrib]
        linarith [hπg x])
    intro x
    have h3 : W x - value P r γ πg x ≤ 0 / (1 - γ) := hmp x
    rw [zero_div] at h3
    linarith
  intro x
  unfold optValue
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun π _ => hup π x)
  · exact (hlow x).trans (Finset.le_sup' (fun π : S → A => value P r γ π x) (Finset.mem_univ πg))

theorem bs56_exists_fix {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ W : S → ℝ, ∀ x, W x = Finset.univ.sup' Finset.univ_nonempty
        (fun b => r x b + γ * ∑ y, P x b y * W y) := by
  let T : (S → ℝ) → (S → ℝ) := fun W x => Finset.univ.sup' Finset.univ_nonempty
        (fun b => r x b + γ * ∑ y, P x b y * W y)
  have hstep : ∀ W W' : S → ℝ, ∀ x, T W x ≤ T W' x + γ * dist W W' := by
    intro W W' x
    apply bs56_sup_le
    intro b
    have hs : ∑ y, P x b y * W y ≤ ∑ y, P x b y * W' y + dist W W' := by
      apply bs56_sum_le _ _ _ (hP x b).1 (hP x b).2
      intro y
      have h1 := dist_le_pi_dist W W' y
      rw [Real.dist_eq] at h1
      linarith [le_abs_self (W y - W' y)]
    have e1 := mul_le_mul_of_nonneg_left hs hγ0
    rw [mul_add] at e1
    show r x b + γ * ∑ y, P x b y * W y ≤ r x b + γ * ∑ y, P x b y * W' y + γ * dist W W'
    linarith
  have hK : ContractingWith (⟨γ, hγ0⟩ : NNReal) T := by
    refine ⟨NNReal.coe_lt_coe.mp (by rw [NNReal.coe_one]; exact hγ1), ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro W W'
    refine (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).2 ?_
    intro x
    show dist (T W x) (T W' x) ≤ γ * dist W W'
    rw [Real.dist_eq, abs_sub_le_iff]
    have h1 := hstep W W' x
    have h2 := hstep W' W x
    rw [dist_comm W' W] at h2
    constructor <;> linarith
  refine ⟨ContractingWith.fixedPoint T hK, fun x => ?_⟩
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := T) hK
  exact (congrFun hfix x).symm

open BreakingSample.Perturbed in
theorem bs56_opt_bellman {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ x, optValue P r γ x = Finset.univ.sup' Finset.univ_nonempty (fun b => optQ P r γ x b) := by
  obtain ⟨W, hW⟩ := bs56_exists_fix P hP r γ hγ0 hγ1
  have h := bs56_verify P hP r γ hγ0 hγ1 W hW
  intro x
  rw [h x, hW x]
  exact Finset.sup'_congr _ rfl (fun b _ => by simp only [optQ, h])

open BreakingSample.Perturbed in

open BreakingSample.Perturbed in
theorem bs56_absorb_kernel {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (s : S) (a : A) : FoundationsML.ReinforcementLearning.IsTransitionKernel (absorbKernel P s a) := by
  intro s1 a1
  by_cases h : s1 = s ∧ a1 = a
  · simp only [absorbKernel, if_pos h]
    refine ⟨fun s' => by split_ifs <;> norm_num, by simp⟩
  · simp only [absorbKernel, if_neg h]
    exact hP s1 a1

open BreakingSample.Perturbed in

/-- Conservative policies agree when the threshold avoids every gap by more than `2ω`. -/
theorem bs57_agree {S A : Type} [LinearOrder A] (Q Q' : S → A → ℝ) (V V' : S → ℝ) (ω ς : ℝ)
    (hQ : ∀ s a, |Q' s a - Q s a| ≤ ω) (hV : ∀ s, |V' s - V s| ≤ ω)
    (hς : ∀ s a, ς < V s - Q s a - 2 * ω ∨ V s - Q s a + 2 * ω < ς)
    (π π' : S → A) (h1 : BreakingSample.Conservative.IsConservative Q V ς π)
    (h2 : BreakingSample.Conservative.IsConservative Q' V' ς π') : π = π' := by
  have key : ∀ s a, (V s - ς < Q s a ↔ V' s - ς < Q' s a) := by
    intro s a
    have hq := abs_le.mp (hQ s a)
    have hv := abs_le.mp (hV s)
    rcases hς s a with h | h
    · constructor <;> intro _ <;> linarith
    · constructor <;> intro _ <;> linarith
  funext s
  apply le_antisymm
  · exact (h1 s).2 (π' s) ((key s (π' s)).mpr (h2 s).1)
  · exact (h2 s).2 (π s) ((key s (π s)).mp (h1 s).1)

theorem bs57_sup_abs {A : Type} [Fintype A] [Nonempty A] (f g : A → ℝ) (c : ℝ)
    (h : ∀ a, |f a - g a| ≤ c) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤ c := by
  have h1 := bs56_sup_le f g c (fun a => by linarith [(abs_le.mp (h a)).2])
  have h2 := bs56_sup_le g f c (fun a => by linarith [(abs_le.mp (h a)).1])
  rw [abs_le]; constructor <;> linarith

theorem bs57_unif_Icc (ξ : ℝ) (hξ : 0 < ξ) (a b : ℝ) :
    BreakingSample.Perturbed.unifInterval ξ (Set.Icc a b) ≤ ENNReal.ofReal ((b - a) / ξ) := by
  unfold BreakingSample.Perturbed.unifInterval
  rw [ProbabilityTheory.cond_apply measurableSet_Icc, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_div_of_pos hξ, div_eq_mul_inv, mul_comm]
  gcongr
  calc MeasureTheory.volume (Set.Icc 0 ξ ∩ Set.Icc a b) ≤ MeasureTheory.volume (Set.Icc a b) :=
        MeasureTheory.measure_mono Set.inter_subset_right
    _ = ENNReal.ofReal (b - a) := Real.volume_Icc

open BreakingSample.Perturbed in
theorem bs57_value_close {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsDiscountedMDP P r γ)
    (s : S) (a : A) (u : ℝ) (ω : ℝ)
    (hQ : ∀ s' a', |optQ (absorbKernel P s a) (absorbReward r s a u) γ s' a' - optQ P r γ s' a'| ≤ ω) :
    ∀ x, |optValue (absorbKernel P s a) (absorbReward r s a u) γ x - optValue P r γ x| ≤ ω := by
  obtain ⟨hP, -, hγ0, hγ1, -, -⟩ := hM
  intro x
  rw [bs56_opt_bellman P hP r γ hγ0.le hγ1 x,
    bs56_opt_bellman (absorbKernel P s a) (bs56_absorb_kernel P hP s a) (absorbReward r s a u) γ hγ0.le hγ1 x]
  exact bs57_sup_abs _ _ ω (fun b => hQ x b)

open BreakingSample.Perturbed BreakingSample.Conservative in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [LinearOrder A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ) :
    let ω : ℝ := ξ * δ / (8 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))
    BreakingSample.Perturbed.unifInterval ξ {ς : ℝ | ¬ ∀ (s : S) (a : A) (u₀ : ℝ), u₀ ∈ BreakingSample.Perturbed.epsNet γ ((1 - γ) * ω) →
        (∀ s' a', |BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ s' a' - BreakingSample.Perturbed.optQ P r γ s' a'| ≤ ω) →
        ∀ π π' : S → A, IsConservative (BreakingSample.Perturbed.optQ P r γ) (BreakingSample.Perturbed.optValue P r γ) ς π →
          IsConservative (BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ)
            (BreakingSample.Perturbed.optValue (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ) ς π' → π = π'}
      ≤ ENNReal.ofReal δ := by
  intro ω
  have hS : Nonempty S := hM.2.2.2.2.1
  set g : S × A → ℝ := fun p => optValue P r γ p.1 - optQ P r γ p.1 p.2 with hg
  have hsub : {ς : ℝ | ¬ ∀ (s : S) (a : A) (u₀ : ℝ), u₀ ∈ epsNet γ ((1 - γ) * ω) →
        (∀ s' a', |optQ (absorbKernel P s a) (absorbReward r s a u₀) γ s' a' - optQ P r γ s' a'| ≤ ω) →
        ∀ π π' : S → A, IsConservative (optQ P r γ) (optValue P r γ) ς π →
          IsConservative (optQ (absorbKernel P s a) (absorbReward r s a u₀) γ)
            (optValue (absorbKernel P s a) (absorbReward r s a u₀) γ) ς π' → π = π'}
      ⊆ ⋃ p : S × A, Set.Icc (g p - 2 * ω) (g p + 2 * ω) := by
    intro ς hς
    by_contra hU
    apply hς
    intro s a u₀ _ hQ π π' h1 h2
    refine bs57_agree _ _ _ _ ω ς hQ (bs57_value_close P r γ hM s a u₀ ω hQ) ?_ π π' h1 h2
    intro s' a'
    have hn : ς ∉ Set.Icc (g (s', a') - 2 * ω) (g (s', a') + 2 * ω) :=
      fun h => hU (Set.mem_iUnion.mpr ⟨(s', a'), h⟩)
    simp only [Set.mem_Icc, not_and_or, not_le, hg] at hn
    rcases hn with h | h
    · left; linarith
    · right; linarith
  have hcS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hcA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  calc unifInterval ξ _ ≤ unifInterval ξ (⋃ p : S × A, Set.Icc (g p - 2 * ω) (g p + 2 * ω)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ ∑ p : S × A, unifInterval ξ (Set.Icc (g p - 2 * ω) (g p + 2 * ω)) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : S × A, ENNReal.ofReal (4 * ω / ξ) := by
        apply Finset.sum_le_sum
        intro p _
        have := bs57_unif_Icc ξ hξ (g p - 2 * ω) (g p + 2 * ω)
        have e : g p + 2 * ω - (g p - 2 * ω) = 4 * ω := by ring
        rw [e] at this
        exact this
    _ = ENNReal.ofReal ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (4 * ω / ξ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ← Nat.cast_mul, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have : (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (4 * ω / ξ) = δ / 2 := by
          simp only [ω]
          field_simp
          ring
        rw [this]; linarith
