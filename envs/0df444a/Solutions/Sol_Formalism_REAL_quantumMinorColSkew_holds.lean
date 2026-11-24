-- Prove2me | solution 1 for Formalism.REAL.quantumMinorColSkew_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:15:24.225182+00:00
-- url     : https://prove2.me/submissions/583f98a8-b288-45a7-b2d4-885e03502c87

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Theorems.Thm_Formalism_REAL_quantumMinor_adjacent_col_swap

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
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : QSkewCol := by
  intro A _ _ n t E hE a b τ u
  cases t with
  | zero =>
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    revert b
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b
      have hs : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
      rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap hs]
      simp
    | one =>
      intro b
      simp
    | mul x y _ _ hx hy =>
      intro b
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy (b ∘ ⇑x), hx b, ← mul_assoc,
        Equiv.Perm.sign_mul, mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul]
end Formalism.REAL
