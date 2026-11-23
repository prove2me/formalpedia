-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.hessM_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:17.199098+00:00
-- url     : https://prove2.me/submissions/987f44f7-1db4-4405-82d8-df6b41b5deb0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (m : ℕ) (a b : Kˣ) :
    hessM m (a * b ^ 2) = (((b⁻¹ : Kˣ) : K) ^ 2) • hessM m a := by
  have h : (((a * b ^ 2)⁻¹ : Kˣ) : K) = ((b⁻¹ : Kˣ) : K) ^ 2 * ((a⁻¹ : Kˣ) : K) := by
    rw [mul_inv, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val, mul_comm]
  unfold hessM
  rw [smul_smul, h]
end Formalism.FourierDecayAlt.P.A6x7.Hess
