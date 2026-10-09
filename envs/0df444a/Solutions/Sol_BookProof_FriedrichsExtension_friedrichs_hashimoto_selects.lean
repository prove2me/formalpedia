-- Prove2me | solution 1 for BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:37:23.601988+00:00
-- url     : https://prove2.me/submissions/f6cdd14b-5af6-44f8-b361-8816313c1bb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists
import Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_shiftInvert_selects_friedrichs
import Theorems.Thm_BookProof_HermiteGalerkin_finiteModeDomain_dense
open Filter Topology
open BookProof.FriedrichsExtension




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R b k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨Dom, A, hA⟩ :=
    friedrichs_extension_exists ⟨finiteModeDomain b, H, hsym, hpos⟩ (finiteModeDomain_dense b)
  obtain ⟨R, hR, hnorm, hsa, -, hstrong, hres, huniq⟩ :=
    hashimoto_shiftInvert_selects_friedrichs b H A hA hγ
  exact ⟨Dom, A, R, hA, hR, hnorm, hsa, hstrong, hres, huniq⟩
