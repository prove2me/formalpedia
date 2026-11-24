-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.mem_UH_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:16.942743+00:00
-- url     : https://prove2.me/submissions/5a5ff0b9-5f85-48ca-8faf-9a538e7806f9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_mulVec
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_herm_bvec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (g : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ u w, herm H (g *ᵥ u) (g *ᵥ w) = herm H u w) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  rw [← herm_bvec (gᴴ * H * g), ← herm_mulVec, h, herm_bvec]
end Formalism.FourierDecayAlt.P.B2x4
