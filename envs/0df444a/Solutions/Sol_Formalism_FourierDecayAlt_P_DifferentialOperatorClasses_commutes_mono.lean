-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.commutes_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:14.465304+00:00
-- url     : https://prove2.me/submissions/f3a03183-2123-4807-8d93-b44a9c357907

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {U V : Set (B.Mat k r)} (hUV : U ⊆ V)
    {Θ : B.DiffOp k r Wp Wq} (h : B.Commutes D V Θ) : B.Commutes D U Θ :=
  fun p hp f hf g hg => h p hp f hf g (hUV hg)
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
