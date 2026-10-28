-- Prove2me | solution 2 for BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:14:34.095827+00:00
-- url     : https://prove2.me/submissions/827a0816-d51a-4dc3-8882-2927d3bf1110

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_shiftInvert_selects_friedrichs
import Theorems.Thm_BookProof_HermiteGalerkin_finiteModeDomain_dense
-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp


open Filter Topology
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
  let P : BookProof.FriedrichsExtension.PosSymOp F :=
    { dom := finiteModeDomain b, op := H, sym := hsym, pos := hpos }
  have hA := BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension P
    (BookProof.HermiteGalerkin.finiteModeDomain_dense b)
  obtain ⟨R, h1, h2, h3, _, h5, h6, h7⟩ :=
    BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs b H _ hA hγ
  exact ⟨_, _, R, hA, h1, h2, h3, h5, h6, h7⟩
