-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fourth_weight_density_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:43:29.416988+00:00
-- url     : https://prove2.me/submissions/c15dbf28-6729-44dd-892a-7f80569fc8de

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.SliceDensityOfChangeOfVariables := by
  intro hR hL s M t φ hs hM ht hφ
  obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, M = q + 2 := ⟨M - 2, by omega⟩
  have e1 : p + 1 - 1 = p := by omega
  have e2 : q + 2 - 2 = q := by omega
  have e3 : q + 2 + (p + 1) - 2 = q + p + 1 := by omega
  have e4 : q + 2 + (p + 1) - 3 = q + p := by omega
  simp only [e1, e2, e3, e4]
  set T := ‖t‖ with hT
  have hTpos : 0 < T := norm_pos_iff.mpr ht
  have hsR : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * p ^ 2)) * φ z with hf
  set S : ℂ → ℝ≥0∞ := fun D => ((Polynomial.nthRoots (p + 1) D).map f).sum with hS
  set ψ : ℂ → ℝ≥0∞ := fun D =>
    ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * (ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D) with hψ

  have hA : ∀ c : ℂ, ENNReal.ofReal (T ^ (2 * p * (q + p + 1)) * ‖c‖ ^ (2 * q) * (T ^ (2 * p ^ 2))⁻¹ *
      ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) * ((Polynomial.nthRoots (p + 1) (c * t ^ p)).map f).sum = ψ (t ^ p * c) := by
    intro c
    simp only [hψ, hS, mul_comm c (t ^ p)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← hT]
    have : T ^ (2 * p * (q + p + 1)) = T ^ (2 * p) * T ^ (2 * p ^ 2) * T ^ (p * (2 * q)) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [this]
    have hT2 : T ^ (2 * p ^ 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    field_simp
  simp only [hA]

  have htp : t ^ p ≠ 0 := pow_ne_zero _ ht
  rw [hL (t ^ p) ψ htp]

  have hC : ∫⁻ D, ψ D = ENNReal.ofReal (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) *
      ∫⁻ D, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D := by
    simp only [hψ]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hC, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hconst : (‖t ^ p‖ ^ 2)⁻¹ * (T ^ (2 * p) * ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹) = ((((p + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
    rw [norm_pow, ← hT, ← pow_mul]
    have : T ^ (p * 2) ≠ 0 := pow_ne_zero _ hTpos.ne'
    rw [mul_comm p 2]; field_simp
  rw [hconst]

  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (2 * (p + 1) * q + 2 * p ^ 2)) * φ z with hg
  have hD : ∀ D : ℂ, ENNReal.ofReal (‖D‖ ^ (2 * q)) * S D = ((Polynomial.nthRoots (p + 1) D).map g).sum := by
    intro D
    simp only [hS]
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    rw [Polynomial.mem_nthRoots (by omega : 0 < p + 1)] at hz
    simp only [hf, hg]
    rw [← hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_pow, ← pow_mul, ← pow_add]
    congr 3
    ring
  simp only [hD]

  have hgm : Measurable g := by
    simp only [hg]
    exact (Measurable.ennreal_ofReal ((continuous_norm.pow _).measurable)).mul hφ
  rw [hR (p + 1) g (by omega) hgm]
  simp only [e1]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [hg]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hs2 : ((((p + 1 : ℕ) : ℝ)) ^ 2) ≠ 0 := by positivity
  rw [show (((p + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (((p + 1 : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * p)) = ‖z‖ ^ (2 * p) by
      field_simp, ← pow_add]
  congr 1
  ring
end Formalism.FourierDecayAlt.P
