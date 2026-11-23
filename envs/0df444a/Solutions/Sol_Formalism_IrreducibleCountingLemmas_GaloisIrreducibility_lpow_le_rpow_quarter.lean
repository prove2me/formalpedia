-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.lpow_le_rpow_quarter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:03.850931+00:00
-- url     : https://prove2.me/submissions/fbbb7191-c591-433e-b478-500ef8fee02c

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible

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
theorem _root_.solution {l v g d : ℕ} (hBB : l ^ (4 * v) ≤ g ^ d) :
    ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : ((l ^ v : ℕ) : ℝ) ^ 4 ≤ ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 := by
    rw [← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)) 4, ← Real.rpow_mul hg0]
    have e : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = d := by push_cast; ring
    rw [e, Real.rpow_natCast]
    have h2 : (l ^ v) ^ 4 ≤ g ^ d := by rw [← pow_mul, mul_comm]; exact hBB
    exact_mod_cast h2
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
