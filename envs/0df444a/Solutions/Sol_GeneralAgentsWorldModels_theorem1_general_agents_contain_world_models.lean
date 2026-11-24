-- Prove2me | solution 1 for GeneralAgentsWorldModels.theorem1_general_agents_contain_world_models
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:13:31.577462+00:00
-- url     : https://prove2.me/submissions/b5178338-4720-411c-b904-9abad8c2d993

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic
import Theorems.Thm_GeneralAgentsWorldModels_theorem1_binomial_quantile_bound
import Theorems.Thm_GeneralAgentsWorldModels_theorem1_agent_choice_inequalities

set_option autoImplicit false

open Finset

universe u v

namespace GeneralAgentsWorldModels

lemma gl_sum_pmf (m : ℕ) (p : ℝ) : ∑ r ∈ range (m + 1), binPmf m p r = 1 := by
  have h := add_pow p (1 - p) m
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  refine sum_congr rfl fun r _ => ?_
  unfold binPmf; ring

lemma gl_binLE_add_binGE (m k : ℕ) (p : ℝ) (hk : k ≤ m) :
    binLE m p k + binGE m p (k + 1) = 1 := by
  unfold binLE binGE
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_range_add_sum_Ico _ (by omega), gl_sum_pmf]

lemma gl_binGE_zero (m : ℕ) (p : ℝ) : binGE m p 0 = 1 := by
  unfold binGE; rw [← Nat.range_succ_eq_Icc_zero, gl_sum_pmf]

lemma gl_binGE_top (m : ℕ) (p : ℝ) : binGE m p (m + 1) = 0 := by
  unfold binGE; rw [Finset.Icc_eq_empty (by omega), sum_empty]

open Classical in
/-- The least threshold `k` at which `π` starts with `a` on `abGoal a b s s' m k` (capped at `m`). -/
noncomputable def gl_kstar {S A : Type*} (m : ℕ) (π : GCPolicy S A) (s : S) (a b : A) (s' : S) :
    ℕ :=
  Nat.find (⟨m, Or.inr le_rfl⟩ : ∃ k, π (abGoal a b s s' m k) [] s = a ∨ m ≤ k)

open Classical in
lemma gl_kstar_le {S A : Type*} (m : ℕ) (π : GCPolicy S A) (s : S) (a b : A) (s' : S) :
    gl_kstar m π s a b s' ≤ m := by
  unfold gl_kstar
  exact Nat.find_min' _ (Or.inr le_rfl)

open Classical in
lemma gl_kstar_spec {S A : Type*} (m : ℕ) (π : GCPolicy S A) (s : S) (a b : A) (s' : S) :
    π (abGoal a b s s' m (gl_kstar m π s a b s')) [] s = a ∨ m ≤ gl_kstar m π s a b s' := by
  unfold gl_kstar
  exact Nat.find_spec (⟨m, Or.inr le_rfl⟩ : ∃ k, π (abGoal a b s s' m k) [] s = a ∨ m ≤ k)

open Classical in
lemma gl_kstar_min {S A : Type*} (m : ℕ) (π : GCPolicy S A) (s : S) (a b : A) (s' : S)
    (j : ℕ) (hj : j < gl_kstar m π s a b s') : π (abGoal a b s s' m j) [] s ≠ a := by
  unfold gl_kstar at hj
  have h' := Nat.find_min (⟨m, Or.inr le_rfl⟩ : ∃ k, π (abGoal a b s s' m k) [] s = a ∨ m ≤ k) hj
  exact fun h => h' (Or.inl h)

lemma gl_ratio_le (x y δ : ℝ) (hδ : δ < 1) (hxy : x + y = 1) (h : y * (1 - δ) ≤ x) :
    (1 - δ) / (2 - δ) ≤ x := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ F : GCPolicy S A → S → A → S → ℝ,
      ∀ M : CMP S A, SatisfiesAssumption1 M →
      ∀ δ : ℝ, δ < 1 → ∀ π : GCPolicy S A, IsBoundedAgent M π δ n →
      ∀ (s : S) (a : A) (s' : S),
        |F π s a s' - M.P s a s'| ≤
          Real.sqrt (M.P s a s' * (1 - M.P s a s') / ((((n - 1) / 2 : ℕ) : ℝ) * (1 - δ))) := by
  classical
  refine ⟨fun π s a s' => if h : ∃ b, b ≠ a then
    (gl_kstar ((n - 1) / 2) π s a (Classical.choose h) s' : ℝ) / (((n - 1) / 2 : ℕ) : ℝ) else 0, ?_⟩
  intro M hM δ hδ π hπ s a s'
  have hex : ∃ b, b ≠ a := Fintype.exists_ne_of_one_lt_card (by have := hM.2; omega) a
  simp only [dif_pos hex]
  have hab : a ≠ Classical.choose hex := (Classical.choose_spec hex).symm
  generalize Classical.choose hex = b at hab ⊢
  generalize hmdef : (n - 1) / 2 = m
  have hm : 2 * m + 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hδ0 : 0 ≤ δ := hπ.1
  have hp0 : 0 ≤ M.P s a s' := M.nonneg s a s'
  have hp1 : M.P s a s' ≤ 1 := by
    rw [← M.sum_one s a]
    exact single_le_sum (fun x _ => M.nonneg s a x) (mem_univ s')
  set p := M.P s a s' with hp
  have ACI := fun k => theorem1_agent_choice_inequalities M hM π δ hδ n m hm hπ s s' a b hab k s
  set K := gl_kstar m π s a b s' with hK
  have hKle : K ≤ m := gl_kstar_le m π s a b s'
  -- the action at K is a
  have hKa : π (abGoal a b s s' m K) [] s = a := by
    rcases gl_kstar_spec m π s a b s' with h | h
    · exact h
    · by_contra hne
      have hb : π (abGoal a b s s' m K) [] s = b := (ACI K).1.resolve_left hne
      have h2 := (ACI K).2.2 hb
      have hKm : K = m := le_antisymm hKle h
      rw [hKm, gl_binGE_top] at h2
      have h3 := gl_binLE_add_binGE m m p le_rfl
      rw [gl_binGE_top] at h3
      nlinarith
  have hle : (1 - δ) / (2 - δ) ≤ binLE m p K :=
    gl_ratio_le _ _ δ hδ (gl_binLE_add_binGE m K p hKle) ((ACI K).2.1 hKa)
  have hge : (1 - δ) / (2 - δ) ≤ binGE m p K := by
    rcases Nat.eq_zero_or_eq_succ_pred K with h0 | hs
    · rw [h0, gl_binGE_zero, div_le_one (by linarith)]
      linarith
    · have hj : K - 1 < K := by omega
      have hne := gl_kstar_min m π s a b s' (K - 1) hj
      have hb := (ACI (K - 1)).1.resolve_left hne
      have h2 := (ACI (K - 1)).2.2 hb
      have hsum := gl_binLE_add_binGE m (K - 1) p (by omega)
      rw [hs]
      have := gl_ratio_le _ _ δ hδ (by linarith [hsum]) h2
      simpa using this
  have hQ := theorem1_binomial_quantile_bound m p δ hp0 hp1 hδ0 hδ K hle hge
  -- rescale by m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have h1d : 0 < 1 - δ := by linarith
  have hX : 0 ≤ (m : ℝ) * p * (1 - p) / (1 - δ) := by
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hY : 0 ≤ p * (1 - p) / ((m : ℝ) * (1 - δ)) := by
    have : 0 ≤ 1 - p := by linarith
    positivity
  rw [Real.le_sqrt (abs_nonneg _) hY, sq_abs]
  have hsq : ((K : ℝ) - m * p) ^ 2 ≤ (m : ℝ) * p * (1 - p) / (1 - δ) := by
    have := (Real.le_sqrt (abs_nonneg _) hX).1 hQ
    rwa [sq_abs] at this
  have e1 : (K : ℝ) / m - p = ((K : ℝ) - m * p) / m := by field_simp
  have e2 : p * (1 - p) / ((m : ℝ) * (1 - δ)) = ((m : ℝ) * p * (1 - p) / (1 - δ)) / m ^ 2 := by
    field_simp
  rw [e1, div_pow, e2]
  exact div_le_div_of_nonneg_right hsq (by positivity)
