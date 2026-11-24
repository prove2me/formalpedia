-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.cut_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:16:48.055477+00:00
-- url     : https://prove2.me/submissions/2d622880-724e-4f5d-bc4e-5db9b594ea14

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
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, C6.cutAll D χ₀ de L F g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by
  intro g hg hne
  apply hF g hg
  intro h0
  apply hne
  simp [C6.cutAll, h0]
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
