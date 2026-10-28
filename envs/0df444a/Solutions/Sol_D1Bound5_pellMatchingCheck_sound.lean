-- Prove2me | solution 1 for D1Bound5.pellMatchingCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:58.839374+00:00
-- url     : https://prove2.me/submissions/581382c4-b574-4a09-911b-c93ea779a3ce

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Theorems.Thm_D1Bound5_pellPairChecks_sound

section
namespace D1Bound5





























theorem _root_.solution (d : ℤ) (ms : List PellSquareMasks)
    (hvalid : ∀ m ∈ ms, m.Valid d) (xs : List ℤ)
    (wss : List (List (ℕ × ℕ))) (hcheck : pellMatchingCheck ms xs wss = true)
    (x y : ℤ) (hx : x ∈ xs) (hy : y ∈ xs) (hne : x ≠ y) :
    (¬∃ r : ℤ, r*r = x*y+1) ∧ (¬∃ r : ℤ, d*r*r = x*y-1) := by
  induction xs generalizing wss with
  | nil => simp at hx
  | cons z zs ih =>
      cases wss with
      | nil => simp [pellMatchingCheck] at hcheck
      | cons ws wss =>
          simp only [pellMatchingCheck, Bool.and_eq_true] at hcheck
          rcases List.mem_cons.mp hx with hxz | hxt
          · have hyt : y ∈ zs := (List.mem_cons.mp hy).resolve_left
              (fun hyz => hne (hxz.trans hyz.symm))
            simpa only [hxz] using
              pellPairChecks_sound d ms hvalid z zs ws hcheck.1 y hyt
          · rcases List.mem_cons.mp hy with hyz | hyt
            · simpa only [hyz, mul_comm x z] using
                pellPairChecks_sound d ms hvalid z zs ws hcheck.1 x hxt
            · exact ih wss hcheck.2 hxt hyt















end D1Bound5
end
