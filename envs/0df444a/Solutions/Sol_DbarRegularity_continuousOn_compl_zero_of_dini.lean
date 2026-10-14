-- Prove2me | solution 1 for DbarRegularity.continuousOn_compl_zero_of_dini
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:22:45.329997+00:00
-- url     : https://prove2.me/submissions/4c0f977d-b889-426e-83e8-d9c776387154

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_exists_modulus_lt_of_dini



namespace DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- A function `Ω` on `ℝ^d`, homogeneous of degree `0`, whose spherical modulus of continuity
satisfies the Dini condition `∫₀¹ w(δ) / δ dδ < ∞`, is continuous on `ℝ^d \ {0}`. -/
theorem continuousOn_compl_zero_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ContinuousOn Ω {0}ᶜ := by
  set n : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => ‖x‖⁻¹ • x with hn
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → ‖n x‖ = 1 := by
    intro x hx
    simp only [hn, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  have hΩn : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → Ω (n x) = Ω x := fun x hx =>
    hhom x _ (inv_pos.mpr (norm_pos_iff.mpr hx))
  intro x₀ hx₀
  have hx₀' : x₀ ≠ 0 := hx₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hw⟩ := exists_modulus_lt_of_dini Ω hdini ε hε
  have hnc : ContinuousAt n x₀ :=
    ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hx₀')).smul continuousAt_id
  obtain ⟨η, hη, hηn⟩ := Metric.continuousAt_iff.mp hnc δ hδ
  refine ⟨η, hη, fun {x} hx hxd => ?_⟩
  have hx' : x ≠ 0 := hx
  have hle : ‖Ω (n x) - Ω (n x₀)‖ₑ ≤ ⨆ (x : EuclideanSpace ℝ (Fin d))
      (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1) (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ),
      ‖Ω x - Ω x'‖ₑ := by
    refine le_iSup_of_le (n x) (le_iSup_of_le (n x₀) (le_iSup_of_le (hnorm x hx')
      (le_iSup_of_le (hnorm x₀ hx₀') (le_iSup_of_le ?_ le_rfl))))
    rw [← dist_eq_norm]; exact (hηn hxd).le
  rw [hΩn x hx', hΩn x₀ hx₀'] at hle
  have h2 := hle.trans_lt hw
  rw [dist_eq_norm, ← ofReal_norm_eq_enorm] at *
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h2

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

theorem solution {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ContinuousOn Ω {0}ᶜ :=
  continuousOn_compl_zero_of_dini Ω hhom hdini
