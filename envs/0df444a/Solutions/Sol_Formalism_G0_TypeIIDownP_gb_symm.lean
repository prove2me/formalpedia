-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.gb_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:31.538957+00:00
-- url     : https://prove2.me/submissions/8f950d0c-4156-44c8-b250-326fa2cb9a0c

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_TypeIIDownP_gb_self
import Theorems.Thm_Formalism_G0_TypeIIDownP_pascal2
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_succ_succ
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_right
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_succ_succ
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution (q : ℕ) : ∀ a b : ℕ, gaussBinom q (a + b) a = gaussBinom q (a + b) b
  | 0, b => by rw [Nat.zero_add, gb_zero_right, gb_self]
  | a + 1, 0 => by rw [Nat.add_zero, gb_zero_right, gb_self]
  | a + 1, b + 1 => by
    have hs : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
    rw [hs, gb_succ_succ q (a + b + 1) a, pascal2 q (a + b + 1) b]
    have i1 := solution q a (b + 1)
    have i2 := solution q (a + 1) b
    have h1 : a + (b + 1) = a + b + 1 := by omega
    have h2 : a + 1 + b = a + b + 1 := by omega
    rw [h1] at i1
    rw [h2] at i2
    have h3 : a + b + 1 - b = a + 1 := by omega
    rw [i1, i2, h3]
termination_by a b => a + b
end Formalism.G0.TypeIIDownP
