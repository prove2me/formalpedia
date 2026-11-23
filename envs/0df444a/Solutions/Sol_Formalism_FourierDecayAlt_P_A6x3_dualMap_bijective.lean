-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.dualMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:25.934391+00:00
-- url     : https://prove2.me/submissions/608766de-db50-4b34-8acd-9eec82dca607

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_exists_charOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    Function.Bijective (dualMap ψ A L) := by
  refine ⟨dualMap_injective hA L, fun χ => ?_⟩
  obtain ⟨z, hz, rfl⟩ := exists_charOf hA b hfin hbL hLA χ
  exact ⟨_, dualMap_mk hA hz⟩
end Formalism.FourierDecayAlt.P.A6x3
