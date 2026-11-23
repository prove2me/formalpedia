-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.impl_uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:42.093799+00:00
-- url     : https://prove2.me/submissions/ea354ce6-4568-48c9-a05b-e484aa8f5323

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_heis
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sq_pos_of_ne
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_add
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_ind
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_smul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_schur


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
theorem _root_.solution {g : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g T') : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, SB φ → T' φ = c • T φ := by
  classical
  have hD := H.2.2.2.2.2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hT'
  have inj : ∀ φ φ', SB φ → SB φ' → T φ = T φ' → φ = φ' := fun φ φ' h1 h2 e => by
    have h3 := sb_add h1 (sb_smul (-1) h2)
    by_contra hne
    refine sq_pos_of_ne H h3 (fun h0 => hne (by simpa [← sub_eq_add_neg, sub_eq_zero] using h0)) ?_
    rw [← a5 _ h3, a3 _ _ h1 (sb_smul _ h2), a4 _ _ h2, e]
    simp
  choose! I hI1 hI2 using a2
  have hIT : ∀ φ, SB φ → I (T φ) = φ := fun φ hφ => inj _ _ (hI1 _ (a1 φ hφ)) hφ (hI2 _ (a1 φ hφ))
  have hH : ∀ x y φ, SB φ → T' (I (Heisenberg₂ ψ h B x y φ)) = Heisenberg₂ ψ h B x y (T' (I φ)) := fun x y φ hφ => by
    conv_lhs => rw [← hI2 φ hφ, a6 x y _ (hI1 φ hφ), hIT _ (sb_heis H _ _ (hI1 φ hφ)), ← b6 x y _ (hI1 φ hφ)]
  obtain ⟨c, hc⟩ := schur hD (T := fun φ => T' (I φ))
    (fun φ φ' h1 h2 => by
      conv_lhs => rw [← hI2 φ h1, ← hI2 φ' h2, ← a3 _ _ (hI1 φ h1) (hI1 φ' h2), hIT _ (sb_add (hI1 φ h1) (hI1 φ' h2)),
        b3 _ _ (hI1 φ h1) (hI1 φ' h2)])
    (fun c φ h1 => by
      conv_lhs => rw [← hI2 φ h1, ← a4 _ _ (hI1 φ h1), hIT _ (sb_smul c (hI1 φ h1)), b4 _ _ (hI1 φ h1)])
    (fun y φ h1 => by
      have e : ∀ f : (ι → R) → ℂ, Heisenberg₂ ψ h B 0 y f = fun u => chiB ψ B u y * f u := fun f => by
        funext u; simp [Heisenberg₂, chiB]
      simpa only [e] using hH 0 y φ h1)
    (fun x φ h1 => by
      have e : ∀ f : (ι → R) → ℂ, Heisenberg₂ ψ h B x 0 f = fun u => f (u + x) := fun f => by funext u; simp [Heisenberg₂]
      simpa only [e] using hH x 0 φ h1)
  have hc' : ∀ φ, SB φ → T' φ = c • T φ := fun φ hφ => by rw [← hc _ (a1 φ hφ), hIT φ hφ]
  refine ⟨c, ?_, hc'⟩
  obtain ⟨L, hL, -⟩ := co_cpt hD isCompact_empty
  have := hD.1
  have := hD.2.1
  have hs := sb_ind 0 hL
  have hne := sq_pos_of_ne H hs fun h0 => by simpa [ind_of_mem] using congrFun h0 0
  have h1 := b5 _ hs
  rw [hc' _ hs] at h1
  simp only [Pi.smul_apply, norm_smul, mul_pow, integral_const_mul, a5 _ hs] at h1
  have h2 : ‖c‖ ^ 2 = 1 := mul_right_cancel₀ hne (h1.trans (one_mul _).symm)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 h2
end CompanionTheory.PlacePermOperatorBicommutantSpan
