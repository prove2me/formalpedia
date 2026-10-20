-- Prove2me | solution 1 for BreakingSample.Conservative.eq_56
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T03:51:38.209364+00:00
-- url     : https://prove2.me/submissions/83eb2940-9a1e-4833-ba54-092255c3341f

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

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
theorem bs56_value_lip {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P) (r1 r2 : S → A → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : ∀ x b, r1 x b ≤ r2 x b + δ) :
    ∀ x, optValue P r1 γ x ≤ optValue P r2 γ x + δ / (1 - γ) := by
  intro x
  unfold optValue
  apply Finset.sup'_le
  intro π _
  have hmp := bs1_mp (policyMatrix P π) (fun s s' => (hP s (π s)).1 s')
    (fun s => (hP s (π s)).2) γ δ hγ0 hγ1 (fun x => value P r1 γ π x - value P r2 γ π x)
    (fun x => by
      show value P r1 γ π x - value P r2 γ π x ≤
        δ + γ * ∑ s', policyMatrix P π x s' * (value P r1 γ π s' - value P r2 γ π s')
      have h1 := bs1_value_bellman P hP r1 γ hγ0 hγ1 π x
      have h2 := bs1_value_bellman P hP r2 γ hγ0 hγ1 π x
      simp only [policyReward] at h1 h2
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith [hδ x (π x)])
  have h3 : value P r1 γ π x - value P r2 γ π x ≤ δ / (1 - γ) := hmp x
  have h4 : value P r2 γ π x ≤ Finset.univ.sup' Finset.univ_nonempty (fun π => value P r2 γ π x) :=
    Finset.le_sup' (fun π : S → A => value P r2 γ π x) (Finset.mem_univ π)
  linarith

open BreakingSample.Perturbed in
theorem bs56_optQ_lip {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ)
    (hP : FoundationsML.ReinforcementLearning.IsTransitionKernel P) (r1 r2 : S → A → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : ∀ x b, |r1 x b - r2 x b| ≤ δ) :
    ∀ x b, |optQ P r1 γ x b - optQ P r2 γ x b| ≤ δ / (1 - γ) := by
  have hA := bs56_value_lip P hP r1 r2 γ hγ0 hγ1 δ
    (fun x b => by linarith [(abs_le.mp (hδ x b)).2])
  have hB := bs56_value_lip P hP r2 r1 γ hγ0 hγ1 δ
    (fun x b => by linarith [(abs_le.mp (hδ x b)).1])
  intro x b
  have hs1 := bs56_sum_le (P x b) _ _ (hP x b).1 (hP x b).2 _ hA
  have hs2 := bs56_sum_le (P x b) _ _ (hP x b).1 (hP x b).2 _ hB
  have e1 := mul_le_mul_of_nonneg_left hs1 hγ0
  have e2 := mul_le_mul_of_nonneg_left hs2 hγ0
  rw [mul_add] at e1 e2
  have hd := abs_le.mp (hδ x b)
  have h1g : 0 < 1 - γ := by linarith
  have key : δ + γ * (δ / (1 - γ)) = δ / (1 - γ) := by field_simp; ring
  unfold optQ
  rw [abs_le]
  constructor <;> linarith

theorem bs56_net (ε B x : ℝ) (hε : 0 < ε) (hx : |x| < B) :
    ∃ k : ℤ, |(k : ℝ)| * ε < B ∧ |(k : ℝ) * ε - x| ≤ ε := by
  rcases le_or_gt 0 x with h0 | h0
  · have h1 : ((⌊x / ε⌋ : ℤ) : ℝ) * ε ≤ x := (le_div_iff₀ hε).mp (Int.floor_le _)
    have h2 : x < (((⌊x / ε⌋ : ℤ) : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp (Int.lt_floor_add_one _)
    have h3 : (0 : ℝ) ≤ ((⌊x / ε⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr (div_nonneg h0 hε.le)
    rw [add_mul, one_mul] at h2
    rw [abs_of_nonneg h0] at hx
    refine ⟨⌊x / ε⌋, ?_, ?_⟩
    · rw [abs_of_nonneg h3]; linarith
    · rw [abs_le]; constructor <;> linarith
  · have h1 : ((⌊-x / ε⌋ : ℤ) : ℝ) * ε ≤ -x := (le_div_iff₀ hε).mp (Int.floor_le _)
    have h2 : -x < (((⌊-x / ε⌋ : ℤ) : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp (Int.lt_floor_add_one _)
    have h3 : (0 : ℝ) ≤ ((⌊-x / ε⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr (div_nonneg (by linarith) hε.le)
    rw [add_mul, one_mul] at h2
    rw [abs_of_neg h0] at hx
    refine ⟨-⌊-x / ε⌋, ?_, ?_⟩
    · simp only [Int.cast_neg, abs_neg]; rw [abs_of_nonneg h3]; linarith
    · simp only [Int.cast_neg, neg_mul]; rw [abs_le]; constructor <;> linarith

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
theorem bs56_absorb_id {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) (a : A) (u : ℝ) (W : S → ℝ)
    (x : S) (b : A) :
    absorbReward r s a u x b + γ * ∑ y, absorbKernel P s a x b y * W y =
      if x = s ∧ b = a then u + γ * W s else r x b + γ * ∑ y, P x b y * W y := by
  by_cases h : x = s ∧ b = a
  · simp [absorbReward, absorbKernel, h]
  · simp only [absorbReward, absorbKernel, if_neg h]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs56_opt_bounds {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (hr : ∀ x b, 0 ≤ r x b ∧ r x b ≤ 1) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ x, 0 ≤ optValue P r γ x ∧ optValue P r γ x ≤ 1 / (1 - γ) := by
  have hpol : ∀ π : S → A, ∀ x, 0 ≤ value P r γ π x ∧ value P r γ π x ≤ 1 / (1 - γ) := by
    intro π
    have hU := bs1_mp (policyMatrix P π) (fun s s' => (hP s (π s)).1 s')
      (fun s => (hP s (π s)).2) γ 1 hγ0 hγ1 (fun x => value P r γ π x) (fun x => by
        show value P r γ π x ≤ 1 + γ * ∑ s', policyMatrix P π x s' * value P r γ π s'
        have h1 := bs1_value_bellman P hP r γ hγ0 hγ1 π x
        simp only [policyReward] at h1
        linarith [(hr x (π x)).2])
    have hL := bs1_mp (policyMatrix P π) (fun s s' => (hP s (π s)).1 s')
      (fun s => (hP s (π s)).2) γ 0 hγ0 hγ1 (fun x => -value P r γ π x) (fun x => by
        show -value P r γ π x ≤ 0 + γ * ∑ s', policyMatrix P π x s' * -value P r γ π s'
        have h1 := bs1_value_bellman P hP r γ hγ0 hγ1 π x
        simp only [policyReward] at h1
        simp only [mul_neg, Finset.sum_neg_distrib]
        linarith [(hr x (π x)).1])
    intro x
    have h1 : value P r γ π x ≤ 1 / (1 - γ) := hU x
    have h2 : -value P r γ π x ≤ 0 / (1 - γ) := hL x
    rw [zero_div] at h2
    exact ⟨by linarith, h1⟩
  intro x
  unfold optValue
  constructor
  · exact (hpol (fun _ => Classical.arbitrary A) x).1.trans
      (Finset.le_sup' (fun π : S → A => value P r γ π x) (Finset.mem_univ _))
  · exact Finset.sup'_le _ _ (fun π _ => (hpol π x).2)

open BreakingSample.Perturbed in
theorem bs56_main {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsDiscountedMDP P r γ)
    (ω : ℝ) (hω : 0 < ω) (s : S) (a : A) :
    ∃ u₀ ∈ epsNet γ ((1 - γ) * ω), ∀ s' a',
      |optQ (absorbKernel P s a) (absorbReward r s a u₀) γ s' a' - optQ P r γ s' a'| ≤ ω := by
  obtain ⟨hP, hr, hγ0, hγ1, -, -⟩ := hM
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = optQ P r γ s a - γ * optValue P r γ s := ⟨_, rfl⟩
  have hP' := bs56_absorb_kernel P hP s a
  have hQeq : ∀ x b, absorbReward r s a u x b + γ * ∑ y, absorbKernel P s a x b y *
      optValue P r γ y = optQ P r γ x b := by
    intro x b
    rw [bs56_absorb_id]
    split_ifs with h
    · rw [h.1, h.2, hu]; ring
    · rfl
  have hB := bs56_opt_bellman P hP r γ hγ0.le hγ1
  have hV' : ∀ x, optValue (absorbKernel P s a) (absorbReward r s a u) γ x = optValue P r γ x :=
    bs56_verify _ hP' _ γ hγ0.le hγ1 (optValue P r γ) (fun x => by
      rw [hB x]
      exact Finset.sup'_congr _ rfl (fun b _ => (hQeq x b).symm))
  have hQ' : ∀ x b, optQ (absorbKernel P s a) (absorbReward r s a u) γ x b = optQ P r γ x b := by
    intro x b
    show absorbReward r s a u x b + γ * ∑ y, absorbKernel P s a x b y *
      optValue (absorbKernel P s a) (absorbReward r s a u) γ y = _
    simp_rw [hV']
    exact hQeq x b
  have hbd := bs56_opt_bounds P hP r hr γ hγ0.le hγ1
  have hQV : optQ P r γ s a ≤ optValue P r γ s := by
    rw [hB s]
    exact Finset.le_sup' (fun b => optQ P r γ s b) (Finset.mem_univ a)
  have hQ0 : 0 ≤ optQ P r γ s a := by
    have hs := Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) =>
      mul_nonneg ((hP s a).1 y) (hbd y).1)
    have := mul_nonneg hγ0.le hs
    unfold optQ
    linarith [(hr s a).1]
  have h1g : 0 < 1 - γ := by linarith
  have hc : 1 / (1 - γ) * (1 - γ) = 1 := by field_simp
  have hc0 : 0 < 1 / (1 - γ) := by positivity
  have e1 := mul_le_mul_of_nonneg_left (hbd s).2 h1g.le
  have e2 := mul_le_mul_of_nonneg_left (hbd s).2 hγ0.le
  have e3 := mul_pos hγ0 hc0
  have hus : |u| < 1 / (1 - γ) := by
    rw [abs_lt]
    constructor <;> nlinarith [(hbd s).1]
  have hε : 0 < (1 - γ) * ω := mul_pos h1g hω
  obtain ⟨k, hk1, hk2⟩ := bs56_net ((1 - γ) * ω) (1 / (1 - γ)) u hε hus
  refine ⟨k * ((1 - γ) * ω), by rw [epsNet, Set.mem_ofPred_eq]; exact ⟨k, rfl, hk1⟩, ?_⟩
  intro x b
  have hL := bs56_optQ_lip (absorbKernel P s a) hP' (absorbReward r s a (k * ((1 - γ) * ω)))
    (absorbReward r s a u) γ hγ0.le hγ1 ((1 - γ) * ω) (fun x b => by
      unfold absorbReward
      split_ifs
      · exact hk2
      · simp only [sub_self, abs_zero]; exact hε.le)
  rw [← hQ' x b]
  calc _ ≤ (1 - γ) * ω / (1 - γ) := hL x b
    _ = ω := by field_simp

open BreakingSample.Perturbed in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (ω : ℝ) (hω : 0 < ω) :
    ∀ s a, ∃ u₀ ∈ BreakingSample.Perturbed.epsNet γ ((1 - γ) * ω), ∀ s' a',
      |BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ s' a' - BreakingSample.Perturbed.optQ P r γ s' a'| ≤ ω := by
  intro s a
  exact bs56_main P r γ hM ω hω s a
