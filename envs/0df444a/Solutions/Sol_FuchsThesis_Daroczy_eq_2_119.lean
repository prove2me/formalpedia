-- Prove2me | solution 1 for FuchsThesis.Daroczy.eq_2_119
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:36:52.268244+00:00
-- url     : https://prove2.me/submissions/f1a2afd2-07b9-4ee0-a253-5c4cc62878a7

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace Aux_Dar119

open FuchsThesis.Daroczy

/-- One application of the recursion to `(a, 1 - c - a, c)`. -/
lemma rec3 (α : ℝ) (H : (n : ℕ) → (Fin n → ℝ) → ℝ) (hsym : IsSymmetric H)
    (hrec : SatisfiesRecursion α H) (a c : ℝ) (ha : 0 ≤ a) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hac : a + c ≤ 1) :
    H 3 ![a, 1 - c - a, c] =
      H 2 ![c, 1 - c] + (1 - c) ^ α * H 2 ![a / (1 - c), 1 - a / (1 - c)] := by
  have hc : (0 : ℝ) < 1 - c := by linarith
  obtain ⟨p, hpd⟩ : ∃ p : Fin 3 → ℝ, p = ![a, 1 - c - a, c] := ⟨_, rfl⟩
  have hp0 : p 0 = a := by rw [hpd]; rfl
  have hp1 : p 1 = 1 - c - a := by rw [hpd]; rfl
  have hp2 : p 2 = c := by rw [hpd]; rfl
  have hp : IsDist p := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · show 0 ≤ p 0; rw [hp0]; exact ha
      · show 0 ≤ p 1; rw [hp1]; linarith
      · show 0 ≤ p 2; rw [hp2]; exact hc0
    · rw [Fin.sum_univ_three, hp0, hp1, hp2]; ring
  have hs : p 0 + p 1 = 1 - c := by rw [hp0, hp1]; ring
  have r1 : H 3 p = H 2 (Fin.cons (p 0 + p 1) (fun i : Fin 1 => p i.succ.succ) : Fin 2 → ℝ)
      + (p 0 + p 1) ^ α * H 2 ![p 0 / (p 0 + p 1), p 1 / (p 0 + p 1)] :=
    hrec 1 p hp (by rw [hs]; exact hc)
  have e1 : (Fin.cons (p 0 + p 1) (fun i : Fin 1 => p i.succ.succ) : Fin 2 → ℝ) = ![1 - c, c] := by
    funext i
    fin_cases i
    · show p 0 + p 1 = 1 - c; exact hs
    · show p 2 = c; exact hp2
  have e2 : p 1 / (p 0 + p 1) = 1 - a / (1 - c) := by
    rw [hs, hp1, sub_div, div_self hc.ne']
  rw [e1, e2, hs, hp0] at r1
  -- symmetry for H 2
  have hd2 : IsDist ![c, 1 - c] := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i
      · show (0 : ℝ) ≤ c; exact hc0
      · show (0 : ℝ) ≤ 1 - c; linarith
    · rw [Fin.sum_univ_two]; show c + (1 - c) = 1; ring
  have hsw : (![c, 1 - c] ∘ Equiv.swap (0 : Fin 2) 1) = ![1 - c, c] := by
    funext i; fin_cases i <;> simp
  have h2 := hsym 2 (Equiv.swap 0 1) _ hd2
  rw [hsw] at h2
  rw [← hpd, r1, h2]

end Aux_Dar119

open FuchsThesis.Daroczy in
theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) (hxy : x + y ≤ 1) :
    H 2 ![x, 1 - x] + (1 - x) ^ α * H 2 ![y / (1 - x), 1 - y / (1 - x)]
      = H 2 ![y, 1 - y] + (1 - y) ^ α * H 2 ![x / (1 - y), 1 - x / (1 - y)] := by
  rw [← Aux_Dar119.rec3 α H hsym hrec y x hy0 hx0 hx1 (by linarith),
    ← Aux_Dar119.rec3 α H hsym hrec x y hx0 hy0 hy1 hxy]
  have hd : IsDist ![y, 1 - x - y, x] := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i
      · show (0 : ℝ) ≤ y; exact hy0
      · show (0 : ℝ) ≤ 1 - x - y; linarith
      · show (0 : ℝ) ≤ x; exact hx0
    · rw [Fin.sum_univ_three]; show y + (1 - x - y) + x = 1; ring
  have h := hsym 3 (Equiv.swap 0 2) _ hd
  have hsw : (![y, 1 - x - y, x] ∘ Equiv.swap (0 : Fin 3) 2) = ![x, 1 - y - x, y] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def] <;> ring
  rw [hsw] at h
  exact h.symm
