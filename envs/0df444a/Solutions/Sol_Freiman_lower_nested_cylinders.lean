-- Prove2me | solution 1 for Freiman.lower_nested_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:20.805462+00:00
-- url     : https://prove2.me/submissions/20b297b8-0d52-456c-a1b9-b86fbb5be4f7

import Theorems.Thm_Freiman_lower_cylinder_nonempty
import Theorems.Thm_Freiman_bounded_words_subsequence
import Theorems.Thm_Freiman_lower_cylinder_limit_closed
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (h : ℕ → LowerPair) (ha : ∀ n, lowerAdmissible (h n))
    (he : ∀ n, lowerExtends (h n) (h (n+1))) :
    ∃ a : ℤ → ℕ+, LowerModel a ∧ ∀ n, lowerCylinder (h n) a := by
  choose A hA using fun n => lower_cylinder_nonempty (h n) (ha n)
  have hb : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, (A n i : ℕ) ≤ 4 := by
    intro i
    exact Filter.Eventually.of_forall (fun n => (hA n).2.2 i)
  rcases bounded_words_subsequence A 4 hb with ⟨v,hv,a,_,hc⟩
  exact ⟨a, lower_cylinder_limit_closed h he A (fun n => ⟨(hA n).1,(hA n).2.1⟩) v hv a hc⟩
