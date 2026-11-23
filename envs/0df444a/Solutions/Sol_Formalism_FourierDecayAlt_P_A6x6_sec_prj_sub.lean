-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.sec_prj_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:56.326805+00:00
-- url     : https://prove2.me/submissions/69f20a3f-d4a3-4e17-ad78-47e60f2499ef

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_ker_prj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_prj_sec

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
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (Λ : AddSubgroup K) (x : Fin m → K) : sec Λ (prj Λ m x) - x ∈ PL Λ m := by
  rw [← ker_prj, AddMonoidHom.mem_ker, map_sub, prj_sec, sub_self]
end Formalism.FourierDecayAlt.P.A6x6
