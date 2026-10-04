-- Prove2me | solution 3 for BookProof.HashimotoShiftInvert.shiftMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:34:01.646967+00:00
-- url     : https://prove2.me/submissions/867d20d0-a6b5-42da-b259-00bbd3ff57cf

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore

set_option autoImplicit false




open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_4d0030b0_shift_ge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) {γ : ℝ} (hγ : 0 < γ) (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hre : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    have : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl
    rw [this, inner_add_right, inner_smul_right, Complex.add_re, inner_self_eq_norm_sq_to_K]
    simp [quadForm, ← Complex.ofReal_pow]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [hre] at h2
  have hq := hpos x
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]; simp
  · have : γ * ‖(x : F)‖ ^ 2 ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ := by linarith
    have h3 : ‖(x : F)‖ * (γ * ‖(x : F)‖) ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ := by nlinarith
    exact le_of_mul_le_mul_left h3 hpx

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_4d0030b0_closed {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) := by
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (γ * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : γ * ‖((x m - x n : Dom) : F)‖ ≤ ‖shiftMap A γ (x m - x n)‖ :=
      P2M_4d0030b0_shift_ge hpos hγ _
    rw [map_sub, hx m, hx n] at hb
    have hlt : ‖u m - u n‖ < γ * eps := by
      have hd := hN m hm n hn
      rwa [dist_eq_norm] at hd
    have hkey : γ * ‖((x m : F)) - ((x n : F))‖ < γ * eps := by
      refine lt_of_le_of_lt ?_ hlt
      simpa using hb
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_left hkey hγ.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hAconv : Tendsto (fun n => A (x n)) atTop (nhds (p - (γ : ℂ) • w)) := by
    have hval : ∀ n, A (x n) = u n - (γ : ℂ) • ((x n : F)) := by
      intro n
      have hn : A (x n) + (γ : ℂ) • ((x n : F)) = u n := hx n
      rw [← hn]; abel
    simp only [hval]
    exact hup.sub (hw.const_smul (γ : ℂ))
  obtain ⟨hwmem, hAw⟩ := closed_of_selfAdjointCriterion hsym hsa hw hAconv
  refine ⟨⟨w, hwmem⟩, ?_⟩
  show A ⟨w, hwmem⟩ + (γ : ℂ) • w = p
  rw [hAw]
  abel


open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_4d0030b0_orth {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : Function.Surjective (shiftMap A γ) := by
  have hclosed : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) :=
    P2M_4d0030b0_closed hsym hpos hsa hγ
  haveI : CompleteSpace (shiftRange A γ) := hclosed.completeSpace_coe
  have htop : shiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (shiftRange A γ)
    rw [P2M_4d0030b0_orth hpos hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ shiftRange A γ := by rw [htop]; trivial
  exact hmem

