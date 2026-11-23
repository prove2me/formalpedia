-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.schur
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:19.213921+00:00
-- url     : https://prove2.me/submissions/546210b8-b8d3-48ce-8973-2e991f863646

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_not
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_congr
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_add
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_CO_inf
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_ind
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_span
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_level
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_perp_perp
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_map_sum_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hch : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) : ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  have h1 : ∀ L : AddSubgroup V, CO L → ∀ a, T (ind a L) = T (ind 0 L) 0 • ind a L := by
    intro L hL a
    have e : ind a L = fun u => ind 0 L (u + -a) := funext fun u => ind_congr (by rw [sub_zero, sub_eq_add_neg])
    rw [e, htr _ _ (sb_ind 0 hL)]
    funext u
    generalize_proofs
    simp only [Pi.smul_apply, smul_eq_mul]
    generalize u + -a = v
    by_cases hv : v ∈ L
    · have e2 : (fun u => ind 0 L (u + v)) = ind 0 L := funext fun u => ind_add u hv
      have := congrFun (htr v _ (sb_ind 0 hL)) 0
      rw [e2, zero_add] at this
      rw [ind_of_mem (by simpa using hv), mul_one, this]
    · rw [ind_of_not (by simpa using hv), mul_zero]
      by_contra hne
      refine hv ((perp_perp h hL v).1 fun y hy => ?_)
      have e2 : (fun u => χ u y * ind 0 L u) = ind 0 L := by
        funext u
        by_cases hu : u ∈ L
        · rw [hy u hu, one_mul]
        · rw [ind_of_not (by simpa using hu), mul_zero]
      have := congrFun (hch y _ (sb_ind 0 hL)) v
      rw [e2] at this
      rw [chi_sym h]
      exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  have h2 : ∀ L : AddSubgroup V, CO L → ∀ φ, SB φ → (∀ x, ∀ l ∈ L, φ (x + l) = φ x) → T φ = T (ind 0 L) 0 • φ := by
    intro L hL φ hφ hinv
    obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [map_sum_sb hadd hsm s φ fun a => sb_ind a hL, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [h1 L hL a, smul_comm]
  obtain ⟨L₀, hL₀, -⟩ := co_cpt h isCompact_empty
  refine ⟨T (ind 0 L₀) 0, fun φ hφ => ?_⟩
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  have h3 := congrFun (h2 _ (hL₀.inf hL.2) (ind 0 L₀) (sb_ind 0 hL₀) fun x l hl => ind_add x hl.1) 0
  rw [Pi.smul_apply, ind_of_mem (by simp), smul_eq_mul, mul_one] at h3
  rw [h3]
  exact h2 _ (hL₀.inf hL.2) φ hφ fun x l hl => hinv x l hl.2
end CompanionTheory.PlacePermOperatorBicommutantSpan
