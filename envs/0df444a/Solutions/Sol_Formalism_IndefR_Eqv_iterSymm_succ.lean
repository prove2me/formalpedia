-- Prove2me | solution 1 for Formalism.IndefR.Eqv.iterSymm_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:27.689943+00:00
-- url     : https://prove2.me/submissions/6f4345c0-c399-4c60-8960-8b3e7e9da64d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Theorems.Thm_P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad
import Theorems.Thm_Formalism_IndefR_Eqv_iterated_fderiv_swap_first_two
import Theorems.Thm_Formalism_IndefR_Eqv_fderiv_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution (m : ℕ) (IH : ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (x : E) (v : Fin (m + 1) → E) (σ : Equiv.Perm (Fin (m + 1))),
      iteratedFDeriv ℝ (m + 1) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 1) g x v)
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H) (hg : ContDiff ℝ ∞ g) (x : E)
    (v : Fin (m + 2) → E) (σ : Equiv.Perm (Fin (m + 2))) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 2) g x v := by
  have hgen : σ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  revert v
  induction hgen using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    intro v
    cases i using Fin.cases with
    | zero => exact iterated_fderiv_swap_first_two hg m x v
    | succ a =>
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have hΦ : Differentiable ℝ (iteratedFDeriv ℝ (m + 1) g) :=
        hg.differentiable_iteratedFDeriv (natCast_lt_inf' (m + 1))
      have hne0 : ∀ j : Fin (m + 2), j ≠ 0 → True := fun _ _ => trivial
      have h0 : (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => by have := congrArg Fin.val h; simp at this)
          (fun h => by have := congrArg Fin.val h; simp at this)]
      have ht : Fin.tail (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) =
          Fin.tail v ∘ Equiv.swap a.castSucc a.succ := by
        funext j
        simp only [Fin.tail, Function.comp_apply]
        congr 1
        rw [show a.succ.castSucc = a.castSucc.succ from rfl]
        exact (Fin.succ_injective _).swap_apply _ _ _
      rw [h0, ht]
      exact fderiv_inv hΦ _ (fun y u => IH H g hg y u _) x (v 0) (Fin.tail v)
  | one => intro v; rfl
  | mul τ ρ _ _ hτ hρ =>
    intro v
    have e : v ∘ ⇑(τ * ρ) = (v ∘ τ) ∘ ρ := rfl
    rw [e, hρ (v ∘ τ), hτ v]
end Formalism.IndefR.Eqv
