-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_real_square_lintegral_fatou_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:46:12.06791+00:00
-- url     : https://prove2.me/submissions/13c1d97d-528c-4d26-a5d4-faee3f79bc23

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_fatou_eventual_lintegral_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal

/-! An eventual finite ENNReal bound yields square integrability of the a.e. limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (K : ENNReal) (hK : K ≠ ⊤)
    (hm : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable Z P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω)))
    (hB : ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂P) ≤ K) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ K := by
  have hfatou : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ K := by
    apply avram_p2_j_ui_fatou_eventual_lintegral_bound
      P (fun n ω => ENNReal.ofReal ((Y n ω) ^ 2))
      (fun ω => ENNReal.ofReal ((Z ω) ^ 2)) K
    · intro n
      exact ((hm n).pow_const 2).ennreal_ofReal
    · filter_upwards [hae] with ω hω
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    · exact hB
  have hnorm : ∀ ω, ‖(Z ω) ^ 2‖ₑ =
      ENNReal.ofReal ((Z ω) ^ 2) := fun ω =>
    Real.enorm_of_nonneg (by positivity)
  refine ⟨⟨hz.pow 2, ?_⟩, hfatou⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [hnorm]
  exact lt_of_le_of_lt hfatou (lt_top_iff_ne_top.mpr hK)
