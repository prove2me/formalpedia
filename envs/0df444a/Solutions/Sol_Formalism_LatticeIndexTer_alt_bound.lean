-- Prove2me | solution 1 for Formalism.LatticeIndexTer.alt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:28.231933+00:00
-- url     : https://prove2.me/submissions/e503d49b-c093-4e7d-999b-fe0c5ccdd15d

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution {α : Type*} [Preorder α] (f : α → ℝ) (hf : Monotone f) :
    ∀ (k : ℕ) (a : Fin (k + 1) → α) (b : Fin k → α),
      (∀ i : Fin k, b i ≤ a i.castSucc ∧ a i.succ ≤ b i) →
      f (a (Fin.last k)) ≤ (∑ i, f (a i)) - ∑ i, f (b i) ∧
      (∑ i, f (a i)) - ∑ i, f (b i) ≤ f (a 0) := by
  intro k
  induction k with
  | zero =>
    intro a b _
    refine ⟨?_, ?_⟩ <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, sub_zero] <;> exact le_rfl
  | succ k ih =>
    intro a b hab
    have ih' := ih (fun i => a i.castSucc) (fun i => b i.castSucc)
      (fun i => ⟨(hab i.castSucc).1, (hab i.castSucc).2⟩)
    simp only [Fin.castSucc_zero] at ih'
    obtain ⟨h1, h2⟩ := hab (Fin.last k)
    have m1 := hf h1
    have m2 := hf h2
    rw [Fin.succ_last] at m2
    rw [Fin.sum_univ_castSucc (fun i => f (a i)), Fin.sum_univ_castSucc (fun i => f (b i))]
    constructor <;> linarith [ih'.1, ih'.2]
end Formalism.LatticeIndexTer
