-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.lemma4_reachability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:25:11.016713+00:00
-- url     : https://prove2.me/submissions/9ef45e14-d076-4ed8-bd57-925bc97c9177

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model



namespace FedergruenZipkin.AvgCost
open scoped ENNReal

def l4Act (M : Model) (U L z : ℤ) : Set ℤ :=
  if z ≤ L then {z + M.b} else Set.Icc z (min (z + M.b) U)

def l4RR (M : Model) (U L x' : ℤ) : ℕ → Set ℤ
  | 0 => {x'}
  | n + 1 => {z | ∃ y ∈ l4Act M U L z, ∃ j : ℕ, 0 < M.p j ∧ y - j ∈ l4RR M U L x' n}

def l4Reach (M : Model) (U L x' z : ℤ) : Prop := ∃ n, z ∈ l4RR M U L x' n

lemma l4_reach_self (M : Model) (U L x' : ℤ) : l4Reach M U L x' x' := ⟨0, rfl⟩

lemma l4_step (M : Model) (U L x' z y : ℤ) (j : ℕ) (hy : y ∈ l4Act M U L z)
    (hj : 0 < M.p j) (h : l4Reach M U L x' (y - j)) : l4Reach M U L x' z := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, y, hy, j, hj, hn⟩

lemma l4_act_hi (M : Model) (U L z y : ℤ) (hz : L < z) (h1 : z ≤ y) (h2 : y ≤ z + M.b)
    (h3 : y ≤ U) : y ∈ l4Act M U L z := by
  unfold l4Act
  rw [if_neg (by omega)]
  exact ⟨h1, le_min h2 h3⟩

lemma l4_act_lo (M : Model) (U L z : ℤ) (hz : z ≤ L) : z + M.b ∈ l4Act M U L z := by
  unfold l4Act
  rw [if_pos hz]
  rfl

lemma l4_Dm_lt_b (M : Model) (Dm : ℕ) (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0) : Dm < M.b := by
  have hs : Summable (fun j : ℕ => (j : ℝ) * M.p j) := by
    by_contra h
    have := M.mean_pos
    rw [tsum_eq_zero_of_not_summable h] at this
    exact lt_irrefl _ this
  have h1 : (Dm : ℝ) = ∑' j : ℕ, (Dm : ℝ) * M.p j := by
    rw [tsum_mul_left, M.p_sum.tsum_eq, mul_one]
  have h2 : ∑' j : ℕ, (Dm : ℝ) * M.p j ≤ ∑' j : ℕ, (j : ℝ) * M.p j := by
    apply Summable.tsum_le_tsum _ (M.p_sum.summable.mul_left _) hs
    intro j
    rcases lt_or_ge j Dm with h | h
    · rw [hDm.2 j h]; simp
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (M.p_nonneg j)
  have := M.mean_lt_b
  have : (Dm : ℝ) < M.b := by linarith
  exact_mod_cast this

/-- the combinatorial core: every state is backward-reachable. -/
lemma l4_reach_all (M : Model) (U L : ℤ) (Dm Dp : ℕ)
    (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0)
    (hDp : Dm < Dp ∧ 0 < M.p Dp ∧ ∀ j, Dm < j → j < Dp → M.p j = 0)
    (hL : L < U - M.b) (hUL : max (M.b : ℤ) ((Dm : ℤ) + Dp) ≤ U - L)
    (x' : ℤ) (hx1 : L ≤ x') (hx2 : x' ≤ U - Dm) :
    ∀ z, z ≤ U → l4Reach M U L x' z := by
  have hb := l4_Dm_lt_b M Dm hDm
  have hmax := le_trans (le_max_right _ _) hUL
  -- claim 2: z ∈ (L, x' + Dm]
  have c2 : ∀ n : ℕ, ∀ z : ℤ, (x' + Dm - z).toNat = n → L < z → z ≤ x' + Dm →
      l4Reach M U L x' z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hn hz1 hz2
      by_cases hc : x' + Dm ≤ z + M.b
      · apply l4_step M U L x' z (x' + Dm) Dm (l4_act_hi M U L z _ hz1 hz2 hc (by omega)) hDm.1
        simpa using l4_reach_self M U L x'
      · apply l4_step M U L x' z (z + M.b) Dm
          (l4_act_hi M U L z _ hz1 (by omega) le_rfl (by omega)) hDm.1
        exact ih _ (by omega) _ rfl (by omega) (by omega)
  -- claim for the upper region
  have cup : ∀ z, L < z → z ≤ U → l4Reach M U L x' z := by
    rcases Nat.eq_zero_or_pos Dm with h0 | hpos
    · -- Dm = 0
      subst h0
      have hp0 := hDm.1
      have up : ∀ n : ℕ, ∀ z y : ℤ, (y - z).toNat = n → L < z → z ≤ y → y ≤ U → ∀ j : ℕ,
          0 < M.p j → l4Reach M U L x' (y - j) → l4Reach M U L x' z := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro z y hn hz hzy hyU j hj hr
          by_cases hc : y ≤ z + M.b
          · exact l4_step M U L x' z y j (l4_act_hi M U L z y hz hzy hc hyU) hj hr
          · apply l4_step M U L x' z (z + M.b) 0
              (l4_act_hi M U L z _ hz (by omega) le_rfl (by omega)) hp0
            simp only [Nat.cast_zero, sub_zero]
            exact ih _ (by omega) (z + M.b) y rfl (by omega) (by omega) hyU j hj hr
      intro z hz1 hz2
      by_cases hzx : z ≤ x'
      · exact c2 _ z rfl hz1 (by simpa using hzx)
      have main : ∀ n : ℕ, ∀ z : ℤ, (z - x').toNat = n → x' < z → z ≤ U →
          l4Reach M U L x' z := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro z hn hz1 hz2
          by_cases hA : x' + Dp ≤ U
          · by_cases hB : z ≤ x' + Dp
            · exact up _ z (x' + Dp) rfl (by omega) hB hA Dp hDp.2.1
                (by simpa using l4_reach_self M U L x')
            · apply l4_step M U L x' z z Dp
                (l4_act_hi M U L z z (by omega) le_rfl (by omega) hz2) hDp.2.1
              exact ih _ (by omega) _ rfl (by omega) (by omega)
          · by_cases hC : L < U - Dp
            · exact up _ z U rfl (by omega) hz2 le_rfl Dp hDp.2.1
                (c2 _ _ rfl (by omega) (by omega))
            · by_cases hD : z - Dp ≤ L - M.b
              · apply up _ z (L - M.b + 1 + Dp) rfl (by omega) (by omega) (by omega) Dp hDp.2.1
                rw [show L - (M.b : ℤ) + 1 + Dp - Dp = L - M.b + 1 by ring]
                apply l4_step M U L x' _ (L - M.b + 1 + M.b) 0 (l4_act_lo M U L _ (by omega)) hp0
                simp only [Nat.cast_zero, sub_zero]
                exact c2 _ _ rfl (by omega) (by omega)
              · apply l4_step M U L x' z z Dp
                  (l4_act_hi M U L z z (by omega) le_rfl (by omega) hz2) hDp.2.1
                apply l4_step M U L x' _ (z - Dp + M.b) 0 (l4_act_lo M U L _ (by omega)) hp0
                simp only [Nat.cast_zero, sub_zero]
                by_cases hE : z - Dp + M.b ≤ x'
                · exact c2 _ _ rfl (by omega) (by omega)
                · exact ih _ (by omega) _ rfl (by omega) (by omega)
      exact main _ z rfl (by omega) hz2
    · -- Dm > 0
      have main : ∀ n : ℕ, ∀ z : ℤ, (z - x').toNat = n → x' < z → z ≤ U →
          l4Reach M U L x' z := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro z hn hz1 hz2
          by_cases hB : z ≤ x' + Dm
          · exact c2 _ z rfl (by omega) hB
          · apply l4_step M U L x' z z Dm
              (l4_act_hi M U L z z (by omega) le_rfl (by omega) hz2) hDm.1
            exact ih _ (by omega) _ rfl (by omega) (by omega)
      intro z hz1 hz2
      by_cases hzx : z ≤ x'
      · exact c2 _ z rfl hz1 (by omega)
      · exact main _ z rfl (by omega) hz2
  -- claim 3: below L
  have clo : ∀ n : ℕ, ∀ z : ℤ, (L + 1 - z).toNat = n → z ≤ U → l4Reach M U L x' z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hn hz
      by_cases hzL : L < z
      · exact cup z hzL hz
      · apply l4_step M U L x' z (z + M.b) Dm (l4_act_lo M U L z (by omega)) hDm.1
        exact ih _ (by omega) _ rfl (by omega)
  intro z hz
  exact clo _ z rfl hz

open Classical in
noncomputable def l4Delta (M : Model) (U L x' z : ℤ) : ℤ :=
  if h : ∃ n, z ∈ l4RR M U L x' (n + 1) then
    Classical.choose (show ∃ y ∈ l4Act M U L z, ∃ j : ℕ, 0 < M.p j ∧
      y - j ∈ l4RR M U L x' (Nat.find h) from Nat.find_spec h)
  else if z ≤ L then z + M.b else z

lemma l4Delta_spec (M : Model) (U L x' z : ℤ) (h : ∃ n, z ∈ l4RR M U L x' (n + 1)) :
    ∃ N, (∀ k, z ∈ l4RR M U L x' (k + 1) → N ≤ k) ∧
      l4Delta M U L x' z ∈ l4Act M U L z ∧ ∃ j : ℕ, 0 < M.p j ∧
        l4Delta M U L x' z - j ∈ l4RR M U L x' N := by
  classical
  refine ⟨Nat.find h, fun k hk => Nat.find_min' h hk, ?_⟩
  have hs := Classical.choose_spec (show ∃ y ∈ l4Act M U L z, ∃ j : ℕ, 0 < M.p j ∧
      y - j ∈ l4RR M U L x' (Nat.find h) from Nat.find_spec h)
  have hd : l4Delta M U L x' z = Classical.choose (show ∃ y ∈ l4Act M U L z, ∃ j : ℕ, 0 < M.p j ∧
      y - j ∈ l4RR M U L x' (Nat.find h) from Nat.find_spec h) := by
    unfold l4Delta
    rw [dif_pos h]
  rw [hd]
  exact hs

lemma l4Delta_feas (M : Model) (U L x' : ℤ) (hL : L < U - M.b) :
    FeasibleL M U L (l4Delta M U L x') := by
  have key : ∀ z, l4Delta M U L x' z ∈ l4Act M U L z ∨
      (¬ z ≤ L ∧ l4Delta M U L x' z = z) := by
    intro z
    by_cases h : ∃ n, z ∈ l4RR M U L x' (n + 1)
    · obtain ⟨N, -, h1, -⟩ := l4Delta_spec M U L x' z h
      exact Or.inl h1
    · by_cases hz : z ≤ L
      · left
        have : l4Delta M U L x' z = z + M.b := by
          unfold l4Delta; rw [dif_neg h, if_pos hz]
        rw [this]; exact l4_act_lo M U L z hz
      · right
        refine ⟨hz, ?_⟩
        unfold l4Delta; rw [dif_neg h, if_neg hz]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases key x with h | ⟨_, h⟩
    · unfold l4Act at h
      split_ifs at h with hxL
      · rw [Set.mem_singleton_iff] at h; rw [h]; omega
      · obtain ⟨h1, h2⟩ := h
        have := min_le_left (x + M.b) U
        have := min_le_right (x + M.b) U
        omega
    · rw [h]; omega
  · rcases key x with h | ⟨h', _⟩
    · unfold l4Act at h
      rw [if_pos hx, Set.mem_singleton_iff] at h
      exact h
    · exact absurd hx h'

lemma l4_pos (M : Model) (U L x' : ℤ) :
    ∀ n z, z ∈ l4RR M U L x' n →
      ∃ m : ℕ, 0 < (P M (l4Delta M U L x'))^[m] (Set.indicator {x'} 1) z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz
    rcases n with _ | k
    · refine ⟨0, ?_⟩
      have : z = x' := hz
      subst this
      simp
    · obtain ⟨N, hN, -, j, hj, hr⟩ := l4Delta_spec M U L x' z ⟨k, hz⟩
      have hNk := hN k hz
      obtain ⟨m, hm⟩ := ih N (by omega) _ hr
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      unfold P
      refine lt_of_lt_of_le ?_ (ENNReal.le_tsum j)
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hj).ne' hm.ne'

theorem lemma4_core (M : Model) (U L : ℤ) (Dm Dp : ℕ)
    (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0)
    (hDp : Dm < Dp ∧ 0 < M.p Dp ∧ ∀ j, Dm < j → j < Dp → M.p j = 0)
    (hL : L < U - M.b) (hUL : max (M.b : ℤ) ((Dm : ℤ) + Dp) ≤ U - L) :
    ∀ x' : ℤ, L ≤ x' → x' ≤ U - Dm → ∃ δ : ℤ → ℤ, FeasibleL M U L δ ∧
      ∀ x₀ : ℤ, L ≤ x₀ → x₀ ≤ U - Dm → ∃ n : ℕ, 0 < (P M δ)^[n] (Set.indicator {x'} 1) x₀ := by
  intro x' hx1 hx2
  refine ⟨l4Delta M U L x', l4Delta_feas M U L x' hL, ?_⟩
  intro x₀ h1 h2
  obtain ⟨n, hn⟩ := l4_reach_all M U L Dm Dp hDm hDp hL hUL x' hx1 hx2 x₀ (by omega)
  exact l4_pos M U L x' n x₀ hn

end FedergruenZipkin.AvgCost

open FedergruenZipkin.AvgCost


theorem solution (M : Model) (U L : ℤ) (Dm Dp : ℕ)
    (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0)
    (hDp : Dm < Dp ∧ 0 < M.p Dp ∧ ∀ j, Dm < j → j < Dp → M.p j = 0)
    (hL : L < U - M.b) (hUL : max (M.b : ℤ) ((Dm : ℤ) + Dp) ≤ U - L) :
    ∀ x' : ℤ, L ≤ x' → x' ≤ U - Dm → ∃ δ : ℤ → ℤ, FeasibleL M U L δ ∧
      ∀ x₀ : ℤ, L ≤ x₀ → x₀ ≤ U - Dm → ∃ n : ℕ, 0 < (P M δ)^[n] (Set.indicator {x'} 1) x₀ := by
  exact lemma4_core M U L Dm Dp hDm hDp hL hUL
