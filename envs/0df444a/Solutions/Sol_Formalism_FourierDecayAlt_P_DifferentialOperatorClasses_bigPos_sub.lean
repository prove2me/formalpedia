-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.bigPos_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:35:01.818288+00:00
-- url     : https://prove2.me/submissions/76fed599-fe52-4b0e-950e-e13a1419a563

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
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : C6.bigPos D ⊆ C6.domL D L :=
  fun _ hg => ⟨hg.1, hg.2.1, fun l _ => hg.2.2 l (Finset.mem_univ l)⟩
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
