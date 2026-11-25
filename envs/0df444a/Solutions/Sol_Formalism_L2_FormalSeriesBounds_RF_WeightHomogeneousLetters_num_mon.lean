-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.num_mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:48.707429+00:00
-- url     : https://prove2.me/submissions/70308ed7-bd5c-4244-9065-7cdf29347d23

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
theorem _root_.solution (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g0 = g
  · subst hg
    rw [Fintype.sum_eq_single t0]
    · simp only [eq_self_iff_true, true_and, and_true, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro t ht
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    all_goals first
      | (intro k _; rw [if_neg (fun h => hg h.1)])
      | (intro t _; exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hg h.2.2.1.1.symm), smul_zero])
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
