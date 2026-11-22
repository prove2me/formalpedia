-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.amp_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:31.449087+00:00
-- url     : https://prove2.me/submissions/69b3b8e4-cc9b-4f7d-9bcc-7868bbb8462a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h h' : Point K) (t₁ ζ z : Kˣ) :
    amp R ψ m γ h h' t₁ ζ (z : K) = γ (z * t₁) * conj (γ (ζ * z * t₁)) *
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * z)) := by
  unfold amp
  rw [dif_pos z.isUnit, IsUnit.unit_of_val_units]
end Formalism.FourierDecayAlt.P.GermSumLattices
