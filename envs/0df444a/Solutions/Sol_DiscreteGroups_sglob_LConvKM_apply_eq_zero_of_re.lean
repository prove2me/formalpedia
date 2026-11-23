-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.apply_eq_zero_of_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:40.796324+00:00
-- url     : https://prove2.me/submissions/bee213da-25fb-43a6-8a06-a65e2d9810a7

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_im_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (u : M) (hu : (B u u).re = 0) (y : M) : B u y = 0 := by
  by_contra ha
  have hN : 0 < Complex.normSq (B u y) := Complex.normSq_pos.mpr ha
  have hN' : Complex.normSq (B u y) ≠ 0 := hN.ne'
  have huu : B u u = 0 := Complex.ext (by simpa using hu) (by simpa using im_diag B herm u)
  have hyu : B y u = (starRingEnd ℂ) (B u y) := (herm u y).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B u y) = (B y y).re + 1 :=
    ⟨((B y y).re + 1) / (2 * Complex.normSq (B u y)), by field_simp⟩
  have ex : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((t : ℂ) * B u y) * B y u - (starRingEnd ℂ) ((t : ℂ) * B u y) * B u y
        + (starRingEnd ℂ) ((t : ℂ) * B u y) * ((t : ℂ) * B u y) * B u u := by
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  have key : B (y - ((t : ℂ) * B u y) • u) (y - ((t : ℂ) * B u y) • u)
      = B y y - ((2 * t * Complex.normSq (B u y) : ℝ) : ℂ) := by
    rw [ex, hyu, huu, map_mul, Complex.conj_ofReal]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h := psd (y - ((t : ℂ) * B u y) • u)
  rw [key, Complex.sub_re, Complex.ofReal_re, ht] at h
  linarith
end DiscreteGroups.sglob.LConvKM
