-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:03.604001+00:00
-- url     : https://prove2.me/submissions/e3efb268-918e-4d08-8eda-e52ff41e8aee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_rename_mul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_splitIndex_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {σ : Type} (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K), (∀ τ, LinearIndependent K (b τ)) →
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  induction n with
  | zero =>
    intro ι _ _ hι σ κ b hb
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    haveI : Unique (∀ τ, κ τ) := Pi.uniqueOfIsEmpty κ
    rw [linearIndependent_unique_iff]
    simp
  | succ n ih =>
    intro ι _ _ hι σ κ b hb
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hcard : Fintype.card {τ // τ ≠ τ₀} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι]; omega
    have hW := ih {τ // τ ≠ τ₀} hcard (fun τ => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1)
    have hP := linearIndependent_rename_mul (b τ₀) _ (hb τ₀) hW
    have hR := hP.map' (rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap
      (LinearMap.ker_eq_bot.2 (rename_injective _ (splitIndex_injective τ₀)))
    have h2 := hR.comp (Equiv.piSplitAt τ₀ κ) (Equiv.piSplitAt τ₀ κ).injective
    have key : ∀ g : (∀ τ, κ τ), ∏ τ, rename (Prod.mk τ) (b τ (g τ)) =
        rename (sumComplementToProduct (σ := σ) τ₀) (rename Sum.inl (b τ₀ (g τ₀)) *
          rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ.1)))) := by
      intro g
      simp only [map_mul, map_prod, rename_rename]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ τ₀]
      rfl
    have hfun : (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) =
        ((rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap ∘ (fun p : κ τ₀ × (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
          rename Sum.inl (b τ₀ p.1) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (p.2 τ))))) ∘
          (Equiv.piSplitAt τ₀ κ) := by
      funext g
      rw [key g]
      rfl
    rw [hfun]
    exact h2
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
