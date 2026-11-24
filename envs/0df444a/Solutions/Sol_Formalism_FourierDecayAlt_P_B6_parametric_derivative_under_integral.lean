-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.parametric_derivative_under_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:47:39.730307+00:00
-- url     : https://prove2.me/submissions/159cd54a-82e2-4076-a8f3-bb06835534b9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_pairing_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_hilbertSchmidt_inner_contraction_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_pairing_deriv

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (hL : ∀ T, ‖L T‖ ≤ ‖T‖)
    {u v u' v' : ℝ → X → (Wq →L[ℂ] Wp)} {y₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 y₀) {m : X → ℝ} {C : ℝ}
    (hm : Integrable (fun g => m g * m g) μ)
    (mu : ∀ y ∈ s, AEStronglyMeasurable (u y) μ) (mv : ∀ y ∈ s, AEStronglyMeasurable (v y) μ)
    (mu' : ∀ y ∈ s, AEStronglyMeasurable (u' y) μ) (mv' : ∀ y ∈ s, AEStronglyMeasurable (v' y) μ)
    (du : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => u y g) (u' y g) y)
    (dv : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => v y g) (v' y g) y)
    (bu : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u y g‖ ≤ C * m g) (bv : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v y g‖ ≤ C * m g)
    (bu' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u' y g‖ ≤ C * m g) (bv' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v' y g‖ ≤ C * m g) :
    HasDerivAt (fun y => ∫ g, hsInner (L (u y g)) (v y g) ∂μ)
      (∫ g, (hsInner (L (u' y₀ g)) (v y₀ g) + hsInner (L (u y₀ g)) (v' y₀ g)) ∂μ) y₀ := by
  have hy₀ : y₀ ∈ s := mem_of_mem_nhds hs
  have c1 : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (fun g => hsInner (L (u y g)) (v y g)) μ := by
    filter_upwards [hs] with y hy using hilbert_schmidt_pairing_measurable L (mu y hy) (mv y hy)
  have c2 : Integrable (fun g => hsInner (L (u y₀ g)) (v y₀ g)) μ := by
    refine Integrable.mono' (hm.const_mul ((Module.finrank ℂ Wq : ℝ) * C ^ 2))
      (hilbert_schmidt_pairing_measurable L (mu y₀ hy₀) (mv y₀ hy₀)) ?_
    filter_upwards [bu, bv] with g h1 h2
    exact norm_hilbertSchmidt_inner_contraction_le L hL (h1 y₀ hy₀) (h2 y₀ hy₀)
  have c3 : AEStronglyMeasurable
      (fun g => hsInner (L (u' y₀ g)) (v y₀ g) + hsInner (L (u y₀ g)) (v' y₀ g)) μ :=
    (hilbert_schmidt_pairing_measurable L (mu' y₀ hy₀) (mv y₀ hy₀)).add (hilbert_schmidt_pairing_measurable L (mu y₀ hy₀) (mv' y₀ hy₀))
  have c4 : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)‖ ≤
      2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g) := by
    filter_upwards [bu, bv, bu', bv'] with g h1 h2 h3 h4
    intro y hy
    calc ‖hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)‖
        ≤ ‖hsInner (L (u' y g)) (v y g)‖ + ‖hsInner (L (u y g)) (v' y g)‖ := norm_add_le _ _
      _ ≤ (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (m g * m g) + (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (m g * m g) :=
          add_le_add (norm_hilbertSchmidt_inner_contraction_le L hL (h3 y hy) (h2 y hy)) (norm_hilbertSchmidt_inner_contraction_le L hL (h1 y hy) (h4 y hy))
      _ = 2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g) := by ring
  have c5 : Integrable (fun g => 2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g)) μ := hm.const_mul _
  have c6 : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => hsInner (L (u y g)) (v y g))
      (hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)) y := by
    filter_upwards [du, dv] with g h1 h2
    intro y hy
    exact hilbert_schmidt_pairing_deriv L (h1 y hy) (h2 y hy)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs c1 c2 c3 c4 c5 c6).2
end Formalism.FourierDecayAlt.P.B6
