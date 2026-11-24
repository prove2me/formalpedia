-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.phase_dilation_deriv_x
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:25:42.259099+00:00
-- url     : https://prove2.me/submissions/7e4faf12-8b10-4658-8f64-8d1aa00e45f2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rr_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_curveL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_gN_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_pairing_derivative_locally_dominated
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Ll A)) (hB : admitted α cB B) (hB' : admitted α cB (Ll B)) (dA : DL A) (dB : DL B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => Ph D A B (dilation₂ (x', y) p))
      (((-(rr r / x) : ℝ) : ℂ) * (Ph D (Ll A) B (dilation₂ (x, y) p) + Ph D A (Ll B) (dilation₂ (x, y) p))) x := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := x / 2) (b := 2 * x) (by linarith)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (x / 2) (2 * x), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DL f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun t => f (aDil k r t * z * (aDil k r y)⁻¹))
        ((-(rr r / t)) • Ll f (aDil k r t * z * (aDil k r y)⁻¹)) t := by
    intro f df z hz t ht
    have h := curveL f (z * (aDil k r y)⁻¹) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (aDil_mem k r (hpos t ht)) (WeylGroupFacts.uh_mul hz (aDil_inv_mem k r hy))))
    simpa only [Matrix.mul_assoc] using h
  have key := pairing_derivative_locally_dominated H hA hA' hB hB' hp (a := fun t => aDil k r t) (b := fun _ => (aDil k r y)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN ((aDil k r y)⁻¹)⁻¹ + 2 * rr r / x)
    (fun t ht => aDil_mem k r (hpos t ht)) (fun t _ => aDil_inv_mem k r hy)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).2
      linarith)
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / x := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hx]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [ph_dil H (Ll A) B hp hx hy, ph_dil H A (Ll B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact ph_dil H A B hp (hpos t ht) hy
end Formalism.FourierDecayAlt.P.B6
