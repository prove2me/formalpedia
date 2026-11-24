-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:44.460483+00:00
-- url     : https://prove2.me/submissions/d3ca1bcb-29da-4054-9e61-5af31cad038a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_card_quot_split
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_intValuation_split
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_split_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution : SplitPrimeLoc := by
  intro F E _ _ _ _ _ p hp hs
  have hF := split_sub (F := F) (E := E) p hp hs
  refine ⟨fun v hv => ⟨card_quot_split p hp hF v hv, ?_⟩, hF⟩
  have h1 := intValuation_split p hp hF v hv
  first
  | exact h1
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; norm_cast; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; rfl)
end Formalism.L2.SG.Pf.SatGramLoc
