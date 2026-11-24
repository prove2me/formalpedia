-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:22.626274+00:00
-- url     : https://prove2.me/submissions/468a4f32-becd-49d9-9415-98be6017bf3c

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_pow_card
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_ne_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hi : Irreducible f) (h0 : f.coeff 0 ≠ 0) {x : L}
    (hx : aeval x f = 0) : x ^ (Fintype.card K ^ f.natDegree - 1) = 1 := by
  have hx0 : x ≠ 0 := root_ne_zero h0 hx
  have h1 := root_pow_card hi hx
  have hpos : 1 ≤ Fintype.card K ^ f.natDegree := Nat.one_le_pow _ _ Fintype.card_pos
  have e : x ^ Fintype.card K ^ f.natDegree = x ^ (Fintype.card K ^ f.natDegree - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [e] at h1
  have := mul_right_cancel₀ hx0 (h1.trans (one_mul x).symm)
  exact this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
