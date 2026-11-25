-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotent_self_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:30.92168+00:00
-- url     : https://prove2.me/submissions/20363c66-301d-4ee8-ba7b-2d0ba157930f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_character_inv
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_centralIdem_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CentralIdemSelfAdjoint := by
  intro G V _ _ _ _ _ ρ g
  refine ⟨character_inv ρ g, ?_⟩
  rw [centralIdem_coeff, centralIdem_coeff, inv_inv, map_mul, character_inv ρ g, map_div₀,
    Complex.conj_natCast, Complex.conj_natCast, Complex.conj_conj]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
