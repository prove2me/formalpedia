-- Prove2me | solution 1 for FedergruenZheng1992.thm1_with_step0_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:45:30.147103+00:00
-- url     : https://prove2.me/submissions/b5a6cd67-fcff-47ef-a146-73f4d6a97b02

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

open FedergruenZhengRQ.OPT

namespace FZh87

noncomputable def G : ℤ → ℝ := fun y => if y ≤ 0 then 5 - (y : ℝ) else if y = 1 then 5 else (y : ℝ) - 2

lemma G_neg1 : G (-1) = 6 := by norm_num [G]
lemma G_0 : G 0 = 5 := by norm_num [G]
lemma G_1 : G 1 = 5 := by norm_num [G]
lemma G_2 : G 2 = 0 := by norm_num [G]
lemma G_3 : G 3 = 1 := by norm_num [G]
lemma G_4 : G 4 = 2 := by norm_num [G]
lemma G_5 : G 5 = 3 := by norm_num [G]

lemma G_le (y : ℤ) : (y : ℝ) - 2 ≤ G y ∧ -(y : ℝ) ≤ G y := by
  unfold G
  split_ifs with h1 h2
  · have : (y : ℝ) ≤ 0 := by exact_mod_cast h1
    constructor <;> linarith
  · subst h2; norm_num
  · have : (1 : ℝ) ≤ y := by exact_mod_cast (show (1 : ℤ) ≤ y by omega)
    constructor <;> linarith

lemma Gmin (t : ℤ) : G 2 ≤ G t := by
  rw [G_2]
  unfold G
  split_ifs with h1 h2
  · have : (t : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  · norm_num
  · have : (2 : ℝ) ≤ t := by exact_mod_cast (show (2 : ℤ) ≤ t by omega)
    linarith

lemma unimodal : NegUnimodal G := by
  refine ⟨2, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Iic] at ha hb
    rcases (show b ≤ 0 ∨ b = 1 ∨ b = 2 by omega) with h | h | h
    · have ha0 : a ≤ 0 := by omega
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      simp only [G, if_pos h, if_pos ha0]; linarith
    · subst h
      rcases (show a ≤ 0 ∨ a = 1 by omega) with h' | h'
      · have : (a : ℝ) ≤ 0 := by exact_mod_cast h'
        simp only [G, if_pos h']; norm_num; linarith
      · subst h'; exact le_rfl
    · subst h; exact Gmin a
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    have h1 : ¬ a ≤ 0 := by omega
    have h2 : ¬ b ≤ 0 := by omega
    have h3 : ¬ a = 1 := by omega
    have h4 : ¬ b = 1 := by omega
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [G, if_neg h1, if_neg h2, if_neg h3, if_neg h4]; linarith

lemma coercive : Coercive G := by
  constructor
  · refine Filter.tendsto_atTop_mono (fun y => (G_le y).2) ?_
    exact Filter.tendsto_neg_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 Filter.tendsto_id)
  · refine Filter.tendsto_atTop_mono (fun y => (G_le y).1) ?_
    exact Filter.tendsto_atTop_add_const_right _ _ tendsto_intCast_atTop_atTop

lemma run (k : ℕ) : optRun 1 G 0 (k + 5) = some (-1, 5) := by
  simp only [optRun, optInit, optLoop, optStep]
  norm_num [G_neg1, G_0, G_1, G_2, G_3, G_4, G_5]

end FZh87

theorem solution : ¬ (∀ (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G)
    (hpos : ∃ y₁ : ℤ, 0 < y₁ ∧ ∀ t, G y₁ ≤ G t)
    (L₀ : ℤ) (hL₀ : 0 ≤ L₀) (hscan : ∀ j : ℤ, 0 ≤ j → j < L₀ → G (j + 1) < G j)
    (hstop : G L₀ ≤ G (L₀ + 1)),
    ∃ N : ℕ, ∀ n ≥ N, ∃ r : ℤ, ∃ Q : ℕ, optRun κ G L₀ n = some (r, Q) ∧ 1 ≤ Q ∧
      ∀ r' : ℤ, ∀ Q' : ℕ, 1 ≤ Q' → cost κ G r Q ≤ cost κ G r' Q') := by
  intro h
  have hmin : ∀ t, FZh87.G 2 ≤ FZh87.G t := FZh87.Gmin
  obtain ⟨N, hN⟩ := h 1 one_pos FZh87.G FZh87.unimodal FZh87.coercive ⟨2, by norm_num, hmin⟩ 0 le_rfl
    (fun j hj hj' => absurd hj' (by omega)) (by rw [zero_add, FZh87.G_0, FZh87.G_1])
  obtain ⟨r, Q, hrun, -, hopt⟩ := hN (N + 5) (by omega)
  rw [FZh87.run N] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  have := hopt 1 1 le_rfl
  simp only [cost] at this
  have e1 : Finset.Ioc (-1 : ℤ) (-1 + ((5 : ℕ) : ℤ)) = {0, 1, 2, 3, 4} := by decide
  have e2 : Finset.Ioc (1 : ℤ) (1 + ((1 : ℕ) : ℤ)) = {2} := by decide
  rw [e1, e2] at this
  simp [FZh87.G_0, FZh87.G_1, FZh87.G_2, FZh87.G_3, FZh87.G_4] at this
  norm_num at this
