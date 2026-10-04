-- Prove2me | solution 3 for BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:45:28.051672+00:00
-- url     : https://prove2.me/submissions/d90442d0-c68b-43bc-a7c3-06a29a0693b6

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftMap_surjective
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_opNorm_le
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_isSelfAdjoint
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_inner_nonneg
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftInvert_determines
import Theorems.Thm_BookProof_HashimotoShiftInvert_exists_isShiftInvert
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinCompression_tendsto
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinResolvent_tendsto
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : F →L[ℂ] F,
      IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
      (∀ u : F, 0 ≤ (inner ℂ u (R u) : ℂ).re) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds (R u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
          (nhds (resolvent R z u))) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by

  obtain ⟨-, hsym, hpos, hsa⟩ := hA
  obtain ⟨R, hR⟩ := exists_isShiftInvert hpos hγ (shiftMap_surjective hsym hpos hsa hγ)
  have hRsa : IsSelfAdjoint R := hR.isSelfAdjoint hsym
  refine ⟨R, hR, hR.opNorm_le hpos hγ, hRsa, hR.inner_nonneg hpos hγ,
    fun u => galerkinCompression_tendsto R b u,
    fun z hz u => galerkinResolvent_tendsto hRsa b hz u, ?_⟩
  intro Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvert_determines hA' hR
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
