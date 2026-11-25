-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.num_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:47.380288+00:00
-- url     : https://prove2.me/submissions/300bab9c-2252-46c0-9f77-e6ace4d1a391

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
open WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
theorem _root_.solution (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g = g0 ∧ t = t0
  · obtain ⟨rfl, rfl⟩ := hg
    simp only [le_refl, true_and, and_true, Finset.sum_ite_eq', Finset.mem_Icc]
    split_ifs <;> first | omega | simp
  · rw [if_neg (fun h => hg h.2.2.1), smul_zero, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hg ⟨h1.symm, h2.symm⟩
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
