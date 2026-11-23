-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.relIndex_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:59.594704+00:00
-- url     : https://prove2.me/submissions/84fd15dd-0611-49c1-83fb-3d3f4eab3dfb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_card_addChar
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_bijective

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
    A.relIndex (perp ψ L) = L.relIndex A := by
  have hfin' : L.relIndex A ≠ 0 := by
    intro h
    apply hfin
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hbL hLA, h, mul_zero]
  have : Finite (A ⧸ L.addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin'
  have h := Nat.card_eq_of_bijective _ (dualMap_bijective hA b hfin hbL hLA)
  rw [card_addChar] at h
  exact h
end Formalism.FourierDecayAlt.P.A6x3
