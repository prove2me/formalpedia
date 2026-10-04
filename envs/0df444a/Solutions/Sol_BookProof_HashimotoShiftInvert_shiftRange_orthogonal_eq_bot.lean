-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.shiftRange_orthogonal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:22:53.60771+00:00
-- url     : https://prove2.me/submissions/4b3159b2-24a7-4676-b5d5-438eeed17ac9

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterComplexShiftCore
set_option autoImplicit false

open BookProof.QgOuterFockFL BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : (shiftRange A γ)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hip : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) ((-(γ : ℂ)) • w) := by
    intro v
    have hmem : shiftMap A γ v ∈ shiftRange A γ := ⟨v, rfl⟩
    have h0 : (inner ℂ (shiftMap A γ v) w : ℂ) = 0 := hw _ hmem
    have happ : shiftMap A γ v = A v + (γ : ℂ) • (v : F) := rfl
    rw [happ, inner_add_left, inner_smul_left] at h0
    rw [inner_smul_right]
    simp only [Complex.conj_ofReal] at h0
    linear_combination h0
  obtain ⟨hwmem, hAw⟩ := hsa w ((-(γ : ℂ)) • w) hip
  have hq := hpos ⟨w, hwmem⟩
  unfold quadForm at hq
  rw [hAw] at hq
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K] at hq
  have hq' : -γ * ‖w‖ ^ 2 ≥ 0 := by
    simpa [← Complex.ofReal_pow, Complex.mul_re] using hq
  have hn : ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖w‖]
  have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  simpa using this
