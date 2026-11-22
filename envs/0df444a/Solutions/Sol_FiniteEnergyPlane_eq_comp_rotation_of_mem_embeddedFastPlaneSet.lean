-- Prove2me | solution 1 for FiniteEnergyPlane.eq_comp_rotation_of_mem_embeddedFastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T11:12:55.420197+00:00
-- url     : https://prove2.me/submissions/9b3aa549-1c04-449d-ad0d-cd831a6c290e

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_shiftA_comp_affine_of_range_eq
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_comp_mul
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_lt_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul



/-!
# Hryniewicz Lemma 7.1 (`eq_comp_rotation_of_mem_embeddedFastPlaneSet`)

* 6.24 + 6.23: the projected images of `u, v ∈ Λ({y₀}, P)` share `proj y₀`, so they are equal;
* 6.25: `u (A z + B) = e^{2c} v z`; `u 0 = v 0 = y₀` and injectivity of `proj ∘ u` give `B = 0`,
  and the `a`-coordinate gives `c = 0`;
* the `dλ`-energy of `u (A ·)` on `{1 < |z|}` is that of `u` on `{|A| < |w|}`; the density of a fast
  plane is positive and continuous, so equal energies `γ` force `|A| = 1`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem ur_image (A : ℂ) (hA : A ≠ 0) :
    (fun y => A * y) '' {z : ℂ | 1 < ‖z‖} = {w : ℂ | ‖A‖ < ‖w‖} := by
  have hA' : 0 < ‖A‖ := norm_pos_iff.2 hA
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_mul]
    nlinarith
  · intro hw
    refine ⟨w / A, ?_, by field_simp⟩
    rw [norm_div, lt_div_iff₀ hA', one_mul]
    exact hw

/-- `proj ∘ u` is smooth for a finite-energy plane. -/
theorem ur_proj_contDiff (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J Set.univ u) :
    ContDiff ℝ ∞ (fun y => proj H (u y)) := by
  have hs : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  exact (contDiffAt_aCoord_proj H hH (u z) (hu.2.1 z trivial)).2.comp z hs.contDiffAt

theorem eq_comp_rotation_of_mem_embeddedFastPlaneSet_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y₀ : V 1) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P {y₀} γ) (hv : v ∈ embeddedFastPlaneSet H J P {y₀} γ) :
    ∃ θ : ℝ, ∀ z, u (Complex.exp ((θ : ℂ) * Complex.I) * z) = v z := by
  obtain ⟨⟨hu, huP, hu0, huE⟩, hue⟩ := hu
  obtain ⟨⟨hv, hvP, hv0, hvE⟩, hve⟩ := hv
  rw [Set.mem_singleton_iff] at hu0 hv0
  have humiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz u hu huP hue
  have hvmiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz v hv hvP hve
  have hrange : Set.range (proj H ∘ u) = Set.range (proj H ∘ v) := by
    rcases range_eq_or_disjoint_of_isFastPlane H hH J hJ P u v hu huP hue hv hvP hve humiss
      hvmiss with h | h
    · exact h
    · exact absurd h (Set.not_disjoint_iff.2
        ⟨proj H y₀, ⟨0, by simp [hu0]⟩, ⟨0, by simp [hv0]⟩⟩)
  obtain ⟨c, A, B, hA, hAB⟩ :=
    exists_shiftA_comp_affine_of_range_eq H hH J hJ P hcz u v hu huP hue hv hvP hve hrange
  have hne : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z trivial
  have h0 : u B = Real.exp (2 * c) • u 0 := by
    have := hAB 0
    simp only [mul_zero, zero_add, shiftA] at this
    rw [this, hv0, ← hu0]
  obtain ⟨hp, ha⟩ := proj_aCoord_exp_smul H hH c (u 0) (hne 0)
  have hB : B = 0 := injective_proj_of_isEmbeddedPlane H hH J hJ P u hu huP hue
    (show proj H (u B) = proj H (u 0) by rw [h0, hp])
  have hc : c = 0 := by
    have : aCoord H (u 0) = aCoord H (u 0) + c := by rw [← ha, ← h0, hB]
    linarith
  subst hB hc
  have hAv : ∀ z, u (A * z) = v z := fun z => by
    have := hAB z
    simpa [shiftA] using this
  have hvA : ∀ z, v (A⁻¹ * z) = u z := fun z => by
    rw [← hAv, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  have hwu := (ur_proj_contDiff H hH J u hu.1).differentiable (by simp)
  have hwv := (ur_proj_contDiff H hH J v hv.1).differentiable (by simp)
  have hmeas : MeasurableSet {z : ℂ | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hEu : dlambdaEnergy H {w | ‖A‖ < ‖w‖} u = ENNReal.ofReal γ := by
    rw [← hvE, ← ur_image A hA, ← dlambdaEnergy_comp_mul H u A hA hwu _ hmeas]
    congr 1; funext z; exact hAv z
  have hAi : A⁻¹ ≠ 0 := inv_ne_zero hA
  have hEv : dlambdaEnergy H {w | ‖A⁻¹‖ < ‖w‖} v = ENNReal.ofReal γ := by
    rw [← huE, ← ur_image A⁻¹ hAi, ← dlambdaEnergy_comp_mul H v A⁻¹ hAi hwv _ hmeas]
    congr 1; funext z; exact hvA z
  have hn : ‖A‖ = 1 := by
    have hA' : 0 < ‖A‖ := norm_pos_iff.2 hA
    rcases lt_trichotomy ‖A‖ 1 with h | h | h
    · exfalso
      have hgt : 1 < ‖A⁻¹‖ := by rw [norm_inv]; exact one_lt_inv₀ hA' |>.2 h
      have := dlambdaEnergy_lt_of_isFastPlane H hH J hJ v hv 1 _ zero_le_one hgt
        (by rw [hvE]; exact ENNReal.ofReal_ne_top)
      rw [hvE, hEv] at this
      exact lt_irrefl _ this
    · exact h
    · have := dlambdaEnergy_lt_of_isFastPlane H hH J hJ u hu 1 _ zero_le_one h
        (by rw [huE]; exact ENNReal.ofReal_ne_top)
      rw [huE, hEu] at this
      exact (lt_irrefl _ this).elim
  refine ⟨Complex.arg A, fun z => ?_⟩
  have hexp : Complex.exp ((Complex.arg A : ℂ) * Complex.I) = A := by
    have := Complex.norm_mul_exp_arg_mul_I A
    rwa [hn, Complex.ofReal_one, one_mul] at this
  rw [hexp, hAv]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y₀ : V 1) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P {y₀} γ) (hv : v ∈ embeddedFastPlaneSet H J P {y₀} γ) :
    ∃ θ : ℝ, ∀ z, u (Complex.exp ((θ : ℂ) * Complex.I) * z) = v z :=
  eq_comp_rotation_of_mem_embeddedFastPlaneSet_aux H hH J hJ P hcz γ y₀ u v hu hv
