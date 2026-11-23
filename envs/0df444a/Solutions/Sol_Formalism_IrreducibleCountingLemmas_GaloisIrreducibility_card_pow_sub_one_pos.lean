-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:12.956938+00:00
-- url     : https://prove2.me/submissions/7c395285-2c54-4db0-954f-4e3242287fb1

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
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (δ : ℕ) (hδ : 1 ≤ δ) : (0 : ℝ) < (Fintype.card K : ℝ) ^ δ - 1 := by
  have h1 : (1 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have h2 : (1 : ℝ) < (Fintype.card K : ℝ) ^ δ := one_lt_pow₀ h1 (by omega)
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
