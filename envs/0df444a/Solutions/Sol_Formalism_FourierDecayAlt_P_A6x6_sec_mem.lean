-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.sec_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:04.956844+00:00
-- url     : https://prove2.me/submissions/b4d5caf5-3632-485c-919f-800cc8bdb0ef

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_sec_prj_sub

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
theorem _root_.solution (hle : PL Λ m ≤ PL L m) {y : Fin m → K ⧸ Λ} (hy : y ∈ (PL L m).map (prj Λ m)) :
    sec Λ y ∈ PL L m := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (PL L m).add_mem (hle (sec_prj_sub Λ x)) hx
  rwa [sub_add_cancel] at this
end Formalism.FourierDecayAlt.P.A6x6
