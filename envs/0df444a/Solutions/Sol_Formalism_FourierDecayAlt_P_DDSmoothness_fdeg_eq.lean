-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:01.11726+00:00
-- url     : https://prove2.me/submissions/5832db10-400b-4581-b03a-6f58ccbb415a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {σ : Mx k r → (H →L[ℂ] H)} {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} {d : ℝ} (hd : 0 < d)
    (hS : ∀ v w v' w' : H,
      Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {u : H} (hu : u ≠ 0) : PI.BesselPeriodGGP.fdegH μG σ u = d := by
  obtain ⟨-, hI⟩ := hS u u u u
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r, ⟪u, σ (Matrix.of x) u⟫_ℂ * star ⟪u, σ (Matrix.of x) u⟫_ℂ =
      ((‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hpt] at hI
  rw [integral_complex_ofReal] at hI
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hu4 : (0 : ℝ) < ‖u‖ ^ 4 := pow_pos hn 4
  have huu : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    · rw [Complex.ofReal_im]
      exact inner_self_im (𝕜 := ℂ) u
  have hreal : ∫ x, ‖⟪u, σ (Matrix.of x) u⟫_ℂ‖ ^ 2 ∂μG = ‖u‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hI, huu]
    push_cast
    ring
  unfold PI.BesselPeriodGGP.fdegH
  rw [hreal]
  field_simp
end Formalism.FourierDecayAlt.P.DDSmoothness
