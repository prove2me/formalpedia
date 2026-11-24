-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.rat_four_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:01.07501+00:00
-- url     : https://prove2.me/submissions/0f77d09b-46f3-43ed-85c3-b0b581536b8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
theorem _root_.solution (p : ℚ) (hp : 0 ≤ p) : ∃ a b c d : ℚ, p = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨x, y, z, w, hs⟩ := Nat.sum_four_squares (p.num.toNat * p.den)
  refine ⟨x / p.den, y / p.den, z / p.den, w / p.den, ?_⟩
  have hnum : (0 : ℤ) ≤ p.num := Rat.num_nonneg.mpr hp
  have hd : (p.den : ℚ) ≠ 0 := by positivity
  have hn : ((p.num.toNat : ℕ) : ℚ) = (p.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum
  have key : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 + (z : ℚ) ^ 2 + (w : ℚ) ^ 2 = (p.num : ℚ) * p.den := by
    have h1 : ((x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 : ℕ) : ℚ) = ((p.num.toNat * p.den : ℕ) : ℚ) := by rw [hs]
    push_cast at h1
    rw [h1, hn]
  calc p = (p.num : ℚ) / p.den := (Rat.num_div_den p).symm
    _ = ((p.num : ℚ) * p.den) / (p.den : ℚ) ^ 2 := by field_simp
    _ = _ := by rw [← key]; field_simp
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
