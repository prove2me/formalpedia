-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.equiv_det_of_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:04.12083+00:00
-- url     : https://prove2.me/submissions/aceae0c6-2020-4322-b73b-a6f9b9c67321

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellInversePair_invP_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellInversePair_sgs_invP
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.EquivDetOfOnto := by
  intro hOnto k r Wp Wq _ _ _ _ D f f' hf hf' hq g hg
  obtain ⟨p, hp, q, hqD, rfl⟩ := hOnto k r Wp Wq D g hg
  have hx := BigCellInversePair.sgs_invP p (WeylGroupFacts.isUnit_of_uh hp.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.1.1)
    (WeylGroupFacts.isUnit_of_uh hp.2.2.1.1) (WeylGroupFacts.isUnit_of_uh hp.2.2.2.1) (gq D q)
  have hP := BigCellInversePair.invP_inSS D hp
  rw [← hf _ hP _ hg, ← hf' _ hP _ hg]
  unfold rho
  rw [hx, hq q hqD]
end Formalism.FourierDecayAlt.P
