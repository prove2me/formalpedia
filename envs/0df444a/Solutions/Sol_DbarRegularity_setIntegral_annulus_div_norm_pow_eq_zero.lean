-- Prove2me | solution 1 for DbarRegularity.setIntegral_annulus_div_norm_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:19:33.251383+00:00
-- url     : https://prove2.me/submissions/751dc562-ddcb-40c6-b700-6722b5e41eee

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- If `Ω` on `ℝ^d` is homogeneous of degree `0` and has mean zero on the unit sphere, then
`Ω(x) / |x|^d` has integral zero over every annulus `{R₁ < |x| < R₂}`. -/
theorem setIntegral_annulus_div_norm_pow_eq_zero {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) :
    ∫ x in {x : EuclideanSpace ℝ (Fin d) | R₁ < ‖x‖ ∧ ‖x‖ < R₂},
      Ω x / ((‖x‖ ^ d : ℝ) : ℂ) = 0 := by
  set S : Set (EuclideanSpace ℝ (Fin d)) := {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  set h : ℝ → ℂ := fun r => (Ioo R₁ R₂).indicator (fun r => ((r ^ d : ℝ) : ℂ)⁻¹) r with hh
  set G : EuclideanSpace ℝ (Fin d) → ℂ := S.indicator (fun x => Ω x / ((‖x‖ ^ d : ℝ) : ℂ)) with hG
  set g : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) → ℂ := fun z => Ω z.1 * h z.2 with hg
  have hpt : ∀ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))), G x.1 = g (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d)) x) := by
    rintro ⟨x, hx⟩
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [hG, hg, hh, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe]
    rw [hhom x _ (inv_pos.mpr hx0)]
    by_cases hxS : x ∈ S
    · have : ‖x‖ ∈ Ioo R₁ R₂ := hxS
      rw [indicator_of_mem hxS, indicator_of_mem this, div_eq_mul_inv]
    · have : ‖x‖ ∉ Ioo R₁ R₂ := hxS
      rw [indicator_of_notMem hxS, indicator_of_notMem this, mul_zero]
  calc ∫ x in S, Ω x / ((‖x‖ ^ d : ℝ) : ℂ) = ∫ x, G x := (integral_indicator hSm).symm
    _ = ∫ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))), G x.1
        ∂(volume.comap (Subtype.val : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set _) → _)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => G x]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have h0 : ∀ x : EuclideanSpace ℝ (Fin 0), G x = 0 := by
          intro x
          have hx : x = 0 := Subsingleton.elim x 0
          have : x ∉ S := by
            subst hx; simp only [hS, mem_setOf_eq, norm_zero, not_and, not_lt]
            intro h1; linarith
          rw [hG, indicator_of_notMem this]
        have hG0 : G = 0 := funext h0
        rw [hG0]; simp
      · haveI : NeZero d := ⟨hd.ne'⟩
        rw [restrict_compl_singleton]
    _ = ∫ z, g z ∂(volume.toSphere.prod (Measure.volumeIoiPow
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1))) := by
      rw [← (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (EuclideanSpace ℝ (Fin d)))).integral_comp
        (Homeomorph.measurableEmbedding _) g]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = 0 := by
      rw [hg, integral_prod_mul (fun x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => Ω x) (fun r : Ioi (0 : ℝ) => h r),
        hmean, zero_mul]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) :
    ∫ x in {x : EuclideanSpace ℝ (Fin d) | R₁ < ‖x‖ ∧ ‖x‖ < R₂},
      Ω x / ((‖x‖ ^ d : ℝ) : ℂ) = 0 :=
  setIntegral_annulus_div_norm_pow_eq_zero Ω hhom hmean R₁ R₂ hR₁
