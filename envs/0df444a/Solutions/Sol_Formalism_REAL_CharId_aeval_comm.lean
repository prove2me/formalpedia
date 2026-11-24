-- Prove2me | solution 1 for Formalism.REAL.CharId_aeval_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:50.339858+00:00
-- url     : https://prove2.me/submissions/9a4f0f40-04dd-43bf-a4fc-f4b84a453bce

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (q : ℂ[X]) (c d : Fin n) :
    twistedAction E c d * aeval (CharId_M E) q = aeval (CharId_M E) q * twistedAction E c d := by
  have hc : Commute (twistedAction E c d) (CharId_M E) := CharId_comm E hE c d
  rw [aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (hc.pow_right i).eq]
end Formalism.REAL
