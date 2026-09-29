-- Prove2me | solution 1 for Freiman.middle_compatible_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:51:04.268208+00:00
-- url     : https://prove2.me/submissions/1858609a-2758-4dd6-a8c6-0749e9879eb4

import Definitions.Def_Freiman_middleRoots

open Freiman

private theorem prefix_bound (w u : List ℕ+) (b : ℕ → ℕ+)
    (hu : middleDigits123 u)
    (hp : ∀ n, n < (w ++ u).length → b n = (w ++ u).getD n 1)
    (ht : ∀ n, (w ++ u).length ≤ n → (b n : ℕ) ≤ 3) :
    (∀ n, n < w.length → b n = w.getD n 1) ∧
    (∀ n, w.length ≤ n → (b n : ℕ) ≤ 3) := by
  constructor
  · intro n hn
    rw [hp n (by simp only [List.length_append]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hn]
  · intro n hn
    by_cases hnu : n < (w ++ u).length
    · rw [hp n hnu]
      have hi : n - w.length < u.length := by simp only [List.length_append] at hnu; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hn,
        List.getElem?_eq_getElem hi, Option.getD_some]
      exact hu _ (List.getElem_mem hi)
    · exact ht n (by omega)

theorem solution :
    ∀ (c d : MiddleCore) (a : ℤ→ℕ+), middleProper c d → middleCompatible d a → middleCompatible c a := by
  intro c d a hp ha
  obtain ⟨u, v, hu, hv, hl, hr, _⟩ := hp
  rcases ha with ⟨h0, hal, har, htl, htr⟩
  rw [hl] at hal htl
  rw [hr] at har htr
  have hleft := prefix_bound c.left u (fun n => a (-(n : ℤ) - 1)) hu hal htl
  have hright := prefix_bound c.right v (fun n => a ((n : ℤ) + 1)) hv har htr
  exact ⟨h0, hleft.1, hright.1, hleft.2, hright.2⟩

#print axioms solution
