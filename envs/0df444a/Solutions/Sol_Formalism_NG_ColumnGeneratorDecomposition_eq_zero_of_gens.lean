-- Prove2me | solution 1 for Formalism.NG.ColumnGeneratorDecomposition.eq_zero_of_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:45.173809+00:00
-- url     : https://prove2.me/submissions/40264b75-4ea4-4f72-87f7-38f5375165bc

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_free_decomp
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace Formalism.NG.ColumnGeneratorDecomposition
theorem _root_.solution [Fintype ι] {e₁ : A} {δ : T'} {D : ι → Subgroup G}
    {Kc : ∀ l, Fin (j l) → G → A} {k0 : ι → G → A}
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M)
    (hY : ∀ y : Ymod r χ E, φ (Submodule.Quotient.mk ((y, 0) : ColFreeJ A r χ E ι j)) = 0)
    (hν : ∀ l, φ (Submodule.Quotient.mk (fNu l)) = 0)
    (hσ : ∀ l a, φ (Submodule.Quotient.mk (fSig l a)) = 0)
    (hσ₀ : ∀ l, φ (Submodule.Quotient.mk (fSig0 l)) = 0) : φ = 0 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    let ψ := φ ∘ₗ (colRelJ r χ E e₁ δ D j Kc k0).mkQ
    have : ψ z = 0 := by
      have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
      rw [free_decomp z, map_add, map_sum]
      refine (congrArg₂ (· + ·) (hY z.1) (Finset.sum_eq_zero fun l _ => ?_)).trans (add_zero 0)
      rw [map_colGenJ]
      have h1 : ψ (fNu l) = 0 := hν l
      have h2 : ∀ a, ψ (fSig l a) = 0 := hσ l
      have h3 : ψ (fSig0 l) = 0 := hσ₀ l
      simp only [h0, h1, h2, h3, smul_zero, Finset.sum_const_zero, add_zero]
    simpa [ψ] using this
end Formalism.NG.ColumnGeneratorDecomposition
