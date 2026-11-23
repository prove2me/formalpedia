-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.cq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:22.200964+00:00
-- url     : https://prove2.me/submissions/8ed22c2e-3e9b-4478-a9ce-a262e917ca54

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_q_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (hInv : LatInvN Λ (gaussF ψ L M)) {x x' : Fin m → K} (hx : x' ∈ PL L m)
    (hl : x - x' ∈ PL Λ m) :
    ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) = ψ (Ring.inverse 2 * (x' ⬝ᵥ M *ᵥ x')) := by
  have := q_inv hInv hx hl
  rwa [add_sub_cancel] at this
end Formalism.FourierDecayAlt.P.A6x6
