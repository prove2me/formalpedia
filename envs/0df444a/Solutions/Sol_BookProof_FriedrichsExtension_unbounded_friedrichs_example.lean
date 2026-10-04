-- Prove2me | solution 1 for BookProof.FriedrichsExtension.unbounded_friedrichs_example
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T18:10:54.11437+00:00
-- url     : https://prove2.me/submissions/0f94fdb7-7093-4603-bb1b-d87dc989a072

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs

set_option autoImplicit false

open BookProof.HashimotoShiftInvert in
theorem p2m_369face2_adj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y)) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hpre : ∀ x : F, ∀ hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F),
      preim R ⟨R x, hx⟩ = x := by
    intro x hx
    apply hinj
    rw [preim_spec]
  set z : F := w - (γ : ℂ) • R w - R u with hz
  have hkey : ∀ x : F, inner ℂ x z = 0 := by
    intro x
    have hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨x, rfl⟩
    have h := hw ⟨R x, hx⟩
    have hT : invShiftOperator R hinj γ ⟨R x, hx⟩ = x - (γ : ℂ) • R x := by
      show preim R ⟨R x, hx⟩ - (γ : ℂ) • R x = x - (γ : ℂ) • R x
      rw [hpre]
    rw [hT] at h
    simp only at h
    rw [hz, inner_sub_right, inner_sub_right, inner_smul_right, ← hsym, ← hsym,
      ← h, inner_sub_left, inner_smul_left]
    simp [Complex.conj_ofReal]
  have hz0 : z = 0 := by
    have := hkey z
    exact inner_self_eq_zero.mp this
  have hwR : w = R ((γ : ℂ) • w + u) := by
    rw [map_add, map_smul]
    have : w - (γ : ℂ) • R w - R u = 0 := hz0
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have hmem : w ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨(γ : ℂ) • w + u, hwR.symm⟩
  refine ⟨hmem, ?_⟩
  show preim R ⟨w, hmem⟩ - (γ : ℂ) • w = u
  have hp : preim R ⟨w, hmem⟩ = (γ : ℂ) • w + u := by
    apply hinj
    rw [preim_spec]
    exact hwR
  rw [hp]
  abel

open BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert in
theorem p2m_369face2_ext {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ)
    (hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y))
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) := by
  have hT : ∀ y : LinearMap.range (R : F →ₗ[ℂ] F),
      invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := fun y => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hD x.2, (hH x).symm⟩
  · intro y z
    rw [hT, hT, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    have e1 : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
      conv_lhs => rw [← preim_spec R z]
      rw [← hsym, preim_spec]
    rw [e1]
    simp [Complex.conj_ofReal]
  · intro y
    show 0 ≤ (inner ℂ (y : F) (invShiftOperator R hinj γ y) : ℂ).re
    rw [hT, inner_sub_right, inner_smul_right]
    have h := hposR (preim R y)
    rw [preim_spec] at h
    have e : (inner ℂ (y : F) (preim R y) : ℂ).re = (inner ℂ (R (preim R y)) (preim R y) : ℂ).re := by
      rw [preim_spec]
    have e2 : (inner ℂ (y : F) (y : F) : ℂ) = ((‖(y : F)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [Complex.sub_re, e, e2, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [preim_spec] at e ⊢
    linarith
  · intro w u hw
    exact p2m_369face2_adj R hinj γ hsym w u hw

open scoped InnerProductSpace ENNReal lp in
open BookProof.HashimotoShiftInvert in
theorem p2m_369face2_diag_sym {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x y : ℓ²(ℕ, ℂ)) :
    inner ℂ (diagCLM hc x) y = inner ℂ x (diagCLM hc y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  rw [diagCLM_apply, diagCLM_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

open scoped InnerProductSpace ENNReal lp in
open BookProof.HashimotoShiftInvert in
theorem p2m_369face2_sqrt_abs (n : ℕ) : |Real.sqrt (invCoeff n)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_le_one]
  exact invCoeff_le_one n

open scoped InnerProductSpace ENNReal lp in
open BookProof.HashimotoShiftInvert in
theorem p2m_369face2_R_eq (u : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert u = diagCLM p2m_369face2_sqrt_abs (diagCLM p2m_369face2_sqrt_abs u) := by
  apply lp.ext
  funext n
  rw [ell2ShiftInvert, diagCLM_apply, diagCLM_apply, diagCLM_apply, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (invCoeff_pos n))]

open scoped InnerProductSpace ENNReal lp in
open BookProof.HashimotoShiftInvert in
theorem p2m_369face2_pos (u : ℓ²(ℕ, ℂ)) :
    (1 : ℝ) * ‖ell2ShiftInvert u‖ ^ 2 ≤ (inner ℂ (ell2ShiftInvert u) u : ℂ).re := by
  set S := diagCLM p2m_369face2_sqrt_abs with hS
  have h1 : (inner ℂ (ell2ShiftInvert u) u : ℂ) = inner ℂ (S u) (S u) := by
    rw [p2m_369face2_R_eq, hS, p2m_369face2_diag_sym]
  have h2 : ‖ell2ShiftInvert u‖ ≤ ‖S u‖ := by
    rw [p2m_369face2_R_eq, hS]
    exact diagLin_norm_le p2m_369face2_sqrt_abs _
  rw [h1]
  have h4 : (inner ℂ (S u) (S u) : ℂ).re = ‖S u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [h4, one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

open scoped InnerProductSpace ENNReal lp in
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert in
theorem p2m_369face2_basis_val (k : ℕ) :
    ell2ExampleMatrix ⟨ell2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩
      = ((k : ℂ)) • (ell2Basis k : ℓ²(ℕ, ℂ)) := by
  have hmem : (ell2Basis k : ℓ²(ℕ, ℂ))
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) := ell2Basis_mem_range k
  have hp : preim ell2ShiftInvert ⟨ell2Basis k, hmem⟩ = ((k : ℂ) + 1) • (ell2Basis k : ℓ²(ℕ, ℂ)) := by
    apply ell2ShiftInvert_injective
    rw [preim_spec]
    show (ell2Basis k : ℓ²(ℕ, ℂ)) = _
    rw [ell2Basis_apply, ell2ShiftInvert_smul_single]
  show preim ell2ShiftInvert ⟨ell2Basis k, hmem⟩ - ((1 : ℝ) : ℂ) • (ell2Basis k : ℓ²(ℕ, ℂ)) = _
  rw [hp, add_smul, Complex.ofReal_one, one_smul]
  abel

open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension BookProof.FarisLavine BookProof.HashimotoShiftInvert InnerProductSpace ENNReal lp in
theorem solution :
    (∃ (Dom : Submodule ℂ (ℓ²(ℕ, ℂ))) (A : Dom →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsPositiveSelfAdjointExtension ell2ExampleMatrix A) ∧
      ∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  refine ⟨⟨_, ell2UnboundedExample, ?_⟩, ?_⟩
  · exact p2m_369face2_ext ell2ShiftInvert ell2ShiftInvert_injective 1
      (fun x y => p2m_369face2_diag_sym invCoeff_abs_le_one x y)
      p2m_369face2_pos finiteModeDomain_le_range ell2ExampleMatrix (fun x => rfl)
  · intro C
    obtain ⟨k, hk⟩ := exists_nat_gt C
    refine ⟨⟨ell2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    rw [p2m_369face2_basis_val, norm_smul]
    have h1 : ‖(ell2Basis k : ℓ²(ℕ, ℂ))‖ = 1 := ell2Basis.orthonormal.1 k
    simp only [h1, mul_one, Complex.norm_natCast]
    exact hk
