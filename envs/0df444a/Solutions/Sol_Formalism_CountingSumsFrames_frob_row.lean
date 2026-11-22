-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frob_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:10.075029+00:00
-- url     : https://prove2.me/submissions/d4054b76-ee0b-4dee-9560-f2f5e2d223e6

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds

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
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] {k : ℕ}
    (h : Matrix (Fin k) (Fin k) F) (a s : ℕ) (ha : a ≤ s) (t : Fin k → F) (c : Fin k) :
    ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
      ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c := by
  haveI : ExpChar F p := ExpChar.prime (Fact.out)
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le ha]
end Formalism.CountingSumsFrames
