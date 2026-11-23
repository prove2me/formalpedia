-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.ker_prj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.57286+00:00
-- url     : https://prove2.me/submissions/acaf44cb-7201-4e88-b790-dadc8c3a8ce6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_prj_apply

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
theorem _root_.solution (Λ : AddSubgroup K) : (prj Λ m).ker = PL Λ m := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_PL, funext_iff]
  exact forall_congr' fun i => by
    rw [prj_apply, Pi.zero_apply, QuotientAddGroup.eq_zero_iff]
end Formalism.FourierDecayAlt.P.A6x6
