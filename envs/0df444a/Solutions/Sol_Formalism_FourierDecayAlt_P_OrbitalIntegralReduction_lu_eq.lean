-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:09.901845+00:00
-- url     : https://prove2.me/submissions/9a1fc9cc-7eb7-4c8c-87ff-064d37817a5e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_EE_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) : 1 + EE (lu_co u) = u := by
  ext i j
  rw [Matrix.add_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [Matrix.one_apply_ne (ne_of_lt h), lu_EE_lt _ h, zero_add]; rfl
  · subst h
    rw [Matrix.one_apply_eq, lu_EE_not_lt _ (lt_irrefl i), add_zero, hu.2 i]
  · rw [Matrix.one_apply_ne (ne_of_gt h), lu_EE_not_lt _ (not_lt.2 h.le), add_zero]
    exact (hu.1 h).symm
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
