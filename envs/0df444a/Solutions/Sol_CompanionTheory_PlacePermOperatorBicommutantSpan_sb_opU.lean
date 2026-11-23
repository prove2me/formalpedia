-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.sb_opU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:29.219845+00:00
-- url     : https://prove2.me/submissions/06d2ec75-c02b-4bac-9f31-19bccc64cc4c

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_bsym
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_CO_inf
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_perp
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_isOpen_coset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (b : R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opU ψ h B b φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have := H.1
  refine sb_mul ((IsLocallyConstant.iff_exists_open _).2 fun u => ?_) hφ
  obtain ⟨L₀, hL₀, -⟩ := co_cpt hD isCompact_empty
  obtain ⟨L, hL, hKL⟩ := co_cpt hD ((hL₀.1.image (continuous_const_smul (b * h))).insert (b • u))
  refine ⟨{y | y - u ∈ L₀ ⊓ perpG hD L}, isOpen_coset u (hL₀.inf (co_perp hD hL).2).2, by simp, fun y hy => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, y = u + l := ⟨y - u, by abel⟩
  simp only [mem_setOf_eq, add_sub_cancel_left] at hy
  have h1 : chiB ψ B (b • u) l = 1 := hy.2 _ (hKL (mem_insert _ _))
  have h2 : chiB ψ B ((b * h) • l) l = 1 := hy.2 _ (hKL (mem_insert_of_mem _ ⟨l, hy.1, rfl⟩))
  have e : b * qf h B (u + l) = b * qf h B u + (b • u) ⬝ᵥ (B *ᵥ l) + ((b * h) • l) ⬝ᵥ (B *ᵥ l) := by
    simp only [qf, mulVec_add, add_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul, bsym H.2.2.2.2.1 l u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ l))) * H.2.1
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  exact (congrArg₂ _ (congrArg _ h1) h2).trans (by simp)
end CompanionTheory.PlacePermOperatorBicommutantSpan
