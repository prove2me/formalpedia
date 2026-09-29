-- Prove2me | solution 1 for FoundationsML.ReinforcementLearning.bellman_optimality_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T12:24:23.793379+00:00
-- url     : https://prove2.me/submissions/6637a7c8-dc26-4d56-a162-f4ca3831b76f

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem rl_M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

open FoundationsML.ReinforcementLearning in
theorem rl_M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

open FoundationsML.ReinforcementLearning in
theorem rl_D_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 s : S) :
    OccupationDist π P s0 0 s = if s = s0 then 1 else 0 := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_succ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist π P s0 (t + 1) s' =
      ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · rw [rl_D_zero]
      split_ifs <;> norm_num
    · simp [rl_D_zero]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [rl_D_succ]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (rl_M_nonneg π hπ P hP s s'))
    · simp only [rl_D_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, rl_M_sum π hπ P hP, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem rl_D_front {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    simp [rl_D_succ, rl_D_zero]
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          rw [rl_D_succ]
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := by
          simp only [rl_D_succ]

open FoundationsML.ReinforcementLearning in
theorem rl_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s0 t
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
theorem rl_bellman {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => rl_summable π hπ P hP γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [rl_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    simp [rl_D_zero]
  rw [h0]

open FoundationsML.ReinforcementLearning in
theorem rl_expand {S A : Type*} [Fintype S] [Fintype A]
    (σ : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (W : S → ℝ) (u : S) :
    InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u' =
      ∑ c, σ u c * (Er u c + γ * ∑ u', P u c u' * W u') := by
  unfold InducedReward InducedTransition
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning in
theorem rl_VQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (u : S) :
    PolicyValue π P Er γ u = ∑ c, π u c * QFunction π P Er γ u c := by
  rw [rl_bellman π hπ P hP Er γ hγ0 hγ1 u, rl_expand π P Er γ (PolicyValue π P Er γ) u]
  rfl

open FoundationsML.ReinforcementLearning in
theorem rl_compare {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W : S → ℝ) (s0 : S) :
    W s0 - PolicyValue σ P Er γ s0 =
      ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) := by
  have hb := rl_summable σ hσ P hP γ hγ0 hγ1 W s0
  have hc := rl_summable σ hσ P hP γ hγ0 hγ1 (InducedReward σ Er) s0
  have hb1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ u, OccupationDist σ P s0 (t + 1) u * W u) :=
    (summable_nat_add_iff 1).mpr hb
  have h1 : ∀ t : ℕ, ∑ u, OccupationDist σ P s0 (t + 1) u * W u =
      ∑ u, OccupationDist σ P s0 t u * ∑ u', InducedTransition σ P u u' * W u' := by
    intro t
    simp only [rl_D_succ]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hsplit : ∀ t : ℕ, ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) =
      ∑ u, OccupationDist σ P s0 t u * W u - ∑ u, OccupationDist σ P s0 t u * InducedReward σ Er u
        - γ * ∑ u, OccupationDist σ P s0 t u * ∑ u', InducedTransition σ P u u' * W u' := by
    intro t
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hterm : ∀ t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) =
      (γ ^ t * ∑ u, OccupationDist σ P s0 t u * W u
        - γ ^ (t + 1) * ∑ u, OccupationDist σ P s0 (t + 1) u * W u)
        - γ ^ t * ∑ u, OccupationDist σ P s0 t u * InducedReward σ Er u := by
    intro t
    rw [hsplit t, h1 t, pow_succ]
    ring
  rw [tsum_congr hterm, (hb.sub hb1).tsum_sub hc, hb.tsum_sub hb1, hb.tsum_eq_zero_add]
  have h0 : γ ^ 0 * ∑ u, OccupationDist σ P s0 0 u * W u = W s0 := by
    simp [rl_D_zero]
  rw [h0]
  unfold PolicyValue
  ring

open FoundationsML.ReinforcementLearning in
theorem rl_compare_fn {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W δ : S → ℝ)
    (hδ : ∀ u, δ u = W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u'))
    (s0 : S) :
    W s0 - PolicyValue σ P Er γ s0 = ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u * δ u := by
  have h : δ = fun u => W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u') :=
    funext hδ
  subst h
  exact rl_compare σ hσ P hP Er γ hγ0 hγ1 W s0

open FoundationsML.ReinforcementLearning in
theorem rl_improve_le {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W δ : S → ℝ)
    (hδ : ∀ u, δ u = W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u'))
    (hnn : ∀ u, 0 ≤ δ u) (s0 : S) :
    PolicyValue σ P Er γ s0 ≤ W s0 := by
  have h := rl_compare_fn σ hσ P hP Er γ hγ0 hγ1 W δ hδ s0
  have h2 : 0 ≤ ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u * δ u :=
    tsum_nonneg (fun t => mul_nonneg (pow_nonneg hγ0 t)
      (Finset.sum_nonneg (fun u _ => mul_nonneg ((rl_D_prob σ hσ P hP s0 t).1 u) (hnn u))))
  linarith

open FoundationsML.ReinforcementLearning in
theorem rl_improve_lt {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W δ : S → ℝ)
    (hδ : ∀ u, δ u = W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u'))
    (hnp : ∀ u, δ u ≤ 0) (s0 : S) (hs0 : δ s0 < 0) :
    W s0 < PolicyValue σ P Er γ s0 := by
  have h := rl_compare_fn σ hσ P hP Er γ hγ0 hγ1 W δ hδ s0
  have hsumm := rl_summable σ hσ P hP γ hγ0 hγ1 δ s0
  rw [hsumm.tsum_eq_zero_add] at h
  have h0 : γ ^ 0 * ∑ u, OccupationDist σ P s0 0 u * δ u = δ s0 := by
    simp [rl_D_zero]
  have hrest : ∑' t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist σ P s0 (t + 1) u * δ u ≤ 0 :=
    tsum_nonpos (fun t => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ0 _)
      (Finset.sum_nonpos (fun u _ =>
        mul_nonpos_of_nonneg_of_nonpos ((rl_D_prob σ hσ P hP s0 (t + 1)).1 u) (hnp u))))
  linarith

open FoundationsML.ReinforcementLearning in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsOptimalPolicy π P Er γ ↔
      ∀ s : S, ∀ a : A, π s a > 0 →
        ∀ a' : A, QFunction π P Er γ s a' ≤ QFunction π P Er γ s a := by
  classical
  have hδQ : ∀ (σ : S → A → ℝ) (u : S),
      PolicyValue π P Er γ u - (InducedReward σ Er u +
          γ * ∑ u', InducedTransition σ P u u' * PolicyValue π P Er γ u') =
        ∑ c, π u c * QFunction π P Er γ u c - ∑ c, σ u c * QFunction π P Er γ u c := by
    intro σ u
    rw [rl_expand σ P Er γ (PolicyValue π P Er γ) u, rl_VQ π hπ P hP Er γ hγ0 hγ1 u]
    rfl
  unfold IsOptimalPolicy
  constructor
  · intro hopt s a hpos a'
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ
      (fun c => QFunction π P Er γ s c) ⟨a, Finset.mem_univ a⟩
    obtain ⟨σ, hσdef⟩ : ∃ σ : S → A → ℝ,
        σ = fun u c => if u = s then (if c = b then 1 else 0) else π u c := ⟨_, rfl⟩
    have hσ : IsPolicy σ := by
      intro u
      by_cases hu : u = s
      · refine ⟨fun c => ?_, ?_⟩
        · by_cases hc : c = b <;> simp [hσdef, hu, hc]
        · simp [hσdef, hu]
      · have h := hπ u
        simpa [hσdef, hu] using h
    have hVlt : ∑ c, π s c * QFunction π P Er γ s c < QFunction π P Er γ s b := by
      calc ∑ c, π s c * QFunction π P Er γ s c < ∑ c, π s c * QFunction π P Er γ s b := by
            apply Finset.sum_lt_sum
            · intro c _
              exact mul_le_mul_of_nonneg_left (hb c (Finset.mem_univ c)) ((hπ s).1 c)
            · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left
                (lt_of_lt_of_le hlt (hb a' (Finset.mem_univ a'))) hpos⟩
        _ = QFunction π P Er γ s b := by rw [← Finset.sum_mul, (hπ s).2, one_mul]
    have hσs : ∑ c, σ s c * QFunction π P Er γ s c = QFunction π P Er γ s b := by
      simp [hσdef]
    have hσu : ∀ u, u ≠ s →
        ∑ c, σ u c * QFunction π P Er γ u c = ∑ c, π u c * QFunction π P Er γ u c := by
      intro u hu
      simp [hσdef, hu]
    obtain ⟨δ, hδdef⟩ : ∃ δ : S → ℝ, ∀ u, δ u = PolicyValue π P Er γ u - (InducedReward σ Er u +
        γ * ∑ u', InducedTransition σ P u u' * PolicyValue π P Er γ u') := ⟨_, fun u => rfl⟩
    have hδs : δ s < 0 := by
      rw [hδdef s, hδQ σ s, hσs]
      linarith
    have hδle : ∀ u, δ u ≤ 0 := by
      intro u
      by_cases hu : u = s
      · rw [hu]; exact hδs.le
      · rw [hδdef u, hδQ σ u, hσu u hu, sub_self]
    have hlt2 := rl_improve_lt σ hσ P hP Er γ hγ0 hγ1 (PolicyValue π P Er γ) δ hδdef hδle s hδs
    have hle2 := hopt σ hσ s
    linarith
  · intro h σ hσ s
    obtain ⟨δ, hδdef⟩ : ∃ δ : S → ℝ, ∀ u, δ u = PolicyValue π P Er γ u - (InducedReward σ Er u +
        γ * ∑ u', InducedTransition σ P u u' * PolicyValue π P Er γ u') := ⟨_, fun u => rfl⟩
    have hnn : ∀ u, 0 ≤ δ u := by
      intro u
      rw [hδdef u, hδQ σ u, sub_nonneg]
      have hX : ∀ b, π u b * (∑ c, σ u c * QFunction π P Er γ u c) ≤
          π u b * QFunction π P Er γ u b := by
        intro b
        rcases ((hπ u).1 b).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · refine mul_le_mul_of_nonneg_left ?_ hpos.le
          calc ∑ c, σ u c * QFunction π P Er γ u c ≤ ∑ c, σ u c * QFunction π P Er γ u b :=
                Finset.sum_le_sum (fun c _ =>
                  mul_le_mul_of_nonneg_left (h u b hpos c) ((hσ u).1 c))
            _ = QFunction π P Er γ u b := by rw [← Finset.sum_mul, (hσ u).2, one_mul]
      calc ∑ c, σ u c * QFunction π P Er γ u c
          = ∑ b, π u b * (∑ c, σ u c * QFunction π P Er γ u c) := by
            rw [← Finset.sum_mul, (hπ u).2, one_mul]
        _ ≤ ∑ b, π u b * QFunction π P Er γ u b := Finset.sum_le_sum (fun b _ => hX b)
    exact rl_improve_le σ hσ P hP Er γ hγ0 hγ1 (PolicyValue π P Er γ) δ hδdef hnn s
