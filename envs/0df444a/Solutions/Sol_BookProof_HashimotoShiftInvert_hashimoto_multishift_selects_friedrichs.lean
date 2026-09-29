-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-15T12:50:27.285574+00:00
-- url     : https://prove2.me/submissions/de2d2e44-a3b5-45c3-83db-2399cfc8a887

import Definitions.Def_ChapterComplexShiftCore
-- Generated from ChapterHashimotoComplexShifts.lean — solution of BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_opNorm_le
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_dom_eq_range
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_determines
import Theorems.Thm_BookProof_HashimotoShiftInvert_exists_isShiftInvertC
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_resolvent_identity
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_commute
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvertC_comp_one_sub
import Theorems.Thm_BookProof_HashimotoShiftInvert_sirkDen_rkVec
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinCompression_tendsto
open BookProof.HashimotoShiftInvert



















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → F →L[ℂ] F,
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : F →ₗ[ℂ] F))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by

  obtain ⟨-, hsym, -, hsa⟩ := hA
  choose X hX using fun j : ℕ =>
    exists_isShiftInvertC hsym (hγ j) (cshiftMap_surjective hsym hsa (hγ j))
  refine ⟨X, hX, fun j => (hX j).opNorm_le hsym (hγ j), fun j => (hX j).dom_eq_range,
    fun j k u => shiftInvertC_resolvent_identity (hX j) (hX k) u,
    fun j k => shiftInvertC_commute (hX j) (hX k),
    fun j m => shiftInvertC_comp_one_sub (hX j) (hX m),
    fun m v k => sirkDen_rkVec m hX v k,
    fun j u => galerkinCompression_tendsto (X j) b u, ?_⟩
  intro j Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvertC_determines hA' (hX j)
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
