-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.factorMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:46.268127+00:00
-- url     : https://prove2.me/submissions/c5f53b57-3682-4310-9b91-4840d589be71

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_splitIndex_injective
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_prod_rename_of_forall
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_eq_zero_of_sum_rename_mul

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
variable {K : Type*} [Field K]
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ)) :
    Function.Injective (mvPolynomialProductExtension τ₀ κ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hW : LinearIndependent K (fun g : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
      ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) :=
    linearIndependent_prod_rename_of_forall (fun τ : {τ // τ ≠ τ₀} => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1 τ.2)
  have key : mvPolynomialProductExtension τ₀ κ b h = rename (sumComplementToProduct (σ := σ) τ₀) (∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))) := by
    simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, rename_rename]
    rfl
  rw [key] at hh
  have hh' : ∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) = 0 :=
    rename_injective _ (splitIndex_injective τ₀) (by rw [hh, map_zero])
  exact eq_zero_of_sum_rename_mul _ hW h hh'
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
