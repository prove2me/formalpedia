-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellInversePair.invP_inSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:58.034801+00:00
-- url     : https://prove2.me/submissions/58cf4532-e705-4e55-b032-3a9e6c92801a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellInversePair_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_uWNormal


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellInversePair
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellInversePair
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : D.inSS (invP p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  refine ⟨uw_inv h1, ?_, uw_inv h3, ?_⟩
  · have := (uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu1] at this
  · have := (uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu3] at this
end Formalism.FourierDecayAlt.P.BigCellInversePair
