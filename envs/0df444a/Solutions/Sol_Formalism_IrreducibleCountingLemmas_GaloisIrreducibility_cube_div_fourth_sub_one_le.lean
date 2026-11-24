-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cube_div_fourth_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.603648+00:00
-- url     : https://prove2.me/submissions/a8211383-13de-44c4-8ae5-d614e78b43a8

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (s : ℝ) (hs : 2 ≤ s) : s ^ 3 * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s) := by
  have hs0 : 0 < s := by linarith
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h44 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h16 : 16 ≤ s ^ 4 := by nlinarith
  have h4 : 0 < s ^ 4 - 1 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h4,
    show 2 * (1 / s) * (s ^ 4 - 1) = 2 * (s ^ 4 - 1) / s by ring, le_div_iff₀ hs0]
  have : s ^ 3 * s = s ^ 4 := by ring
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
