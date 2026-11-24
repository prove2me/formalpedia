-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:37.406384+00:00
-- url     : https://prove2.me/submissions/4e12fbf8-d1e5-4117-ab8a-eb507a97ef55

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_comm
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) (p : SS k r)
    (hp : Matrix.of p.1.1 ∈ UWset k r D.z) (hp' : Matrix.of p.2.1 ∈ UWset k r D.z') :
    rho D (dilation₂ t p) (dilF t F) g = rho D p F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  obtain ⟨⟨h, m⟩, ⟨h', m'⟩⟩ := p
  set H : Mat k r := Matrix.of h
  set M : Mat k r := Matrix.of m
  set H' : Mat k r := Matrix.of h'
  set M' : Mat k r := Matrix.of m'
  set a₁ := aDil k r t.1
  set a₂ := aDil k r t.2
  have u1 : IsUnit a₁.det := d_isUnit_aDil t.1 h1
  have u2 : IsUnit a₂.det := d_isUnit_aDil t.2 h2
  have c1 : a₁ * H⁻¹ = H⁻¹ * a₁ := d_comm D.z t.1 (WeylGroupFacts.uw_inv hp)
  have c2 : a₂ * H' = H' * a₂ := d_comm D.z' t.2 hp'
  have c1' : a₁⁻¹ * H⁻¹ = H⁻¹ * a₁⁻¹ := by
    calc a₁⁻¹ * H⁻¹ = a₁⁻¹ * (H⁻¹ * a₁) * a₁⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ u1, Matrix.mul_one]
      _ = a₁⁻¹ * (a₁ * H⁻¹) * a₁⁻¹ := by rw [c1]
      _ = H⁻¹ * a₁⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]
  have key : a₁⁻¹ * (H⁻¹ * (a₁ * M * a₁⁻¹)⁻¹ * g * (a₂ * M' * a₂⁻¹) * H') * a₂ =
      H⁻¹ * M⁻¹ * (a₁⁻¹ * g * a₂) * M' * H' := by
    have i1 : (a₁ * M * a₁⁻¹)⁻¹ = a₁ * M⁻¹ * a₁⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u1, Matrix.mul_assoc]
    rw [i1]
    calc a₁⁻¹ * (H⁻¹ * (a₁ * M⁻¹ * a₁⁻¹) * g * (a₂ * M' * a₂⁻¹) * H') * a₂
        = (a₁⁻¹ * H⁻¹) * a₁ * M⁻¹ * a₁⁻¹ * g * a₂ * M' * a₂⁻¹ * (H' * a₂) := by
          simp only [Matrix.mul_assoc]
      _ = H⁻¹ * (a₁⁻¹ * a₁) * M⁻¹ * a₁⁻¹ * g * a₂ * M' * (a₂⁻¹ * a₂) * H' := by
          rw [c1', ← c2]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [Matrix.nonsing_inv_mul _ u1, Matrix.nonsing_inv_mul _ u2]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
  show (D.π H).comp ((F (a₁⁻¹ * (H⁻¹ * (a₁ * M * a₁⁻¹)⁻¹ * g * (a₂ * M' * a₂⁻¹) * H') * a₂)).comp (D.π' H'⁻¹)) =
    (D.π H).comp ((F (H⁻¹ * M⁻¹ * (a₁⁻¹ * g * a₂) * M' * H')).comp (D.π' H'⁻¹))
  rw [key]
end Formalism.FourierDecayAlt.P.B7
