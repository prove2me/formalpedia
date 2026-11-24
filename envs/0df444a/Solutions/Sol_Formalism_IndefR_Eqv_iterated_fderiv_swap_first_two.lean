-- Prove2me | solution 1 for Formalism.IndefR.Eqv.iterated_fderiv_swap_first_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:48.964454+00:00
-- url     : https://prove2.me/submissions/555a54e8-7e37-4078-9cbf-5cd65a0ca0e6

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Theorems.Thm_Formalism_IndefR_Eqv_two_le_inf
import Theorems.Thm_Formalism_IndefR_Eqv_inf_add_nat

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
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {g : E → H} (hg : ContDiff ℝ ∞ g) (m : ℕ)
    (x : E) (v : Fin (m + 2) → E) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (m + 2) g x v := by
  have key : ∀ u : Fin (m + 2) → E, iteratedFDeriv ℝ (m + 2) g x u =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m g)) x (u 0) (u 1) (Fin.tail (Fin.tail u)) := by
    intro u
    rw [iteratedFDeriv_succ_apply_left]
    have hL : iteratedFDeriv ℝ (m + 1) g =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) H).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ m g) := by
      rw [iteratedFDeriv_succ_eq_comp_left]
    rw [hL, LinearIsometryEquiv.comp_fderiv]
    rfl
  rw [key, key]
  have hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ m g) x :=
    ((hg.iteratedFDeriv_right (m := ∞) (i := m) (inf_add_nat m)).contDiffAt).isSymmSndFDerivAt two_le_inf
  have e0 : (v ∘ Equiv.swap 0 1) 0 = v 1 := by simp
  have e1 : (v ∘ Equiv.swap 0 1) 1 = v 0 := by simp
  have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext j
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => by
      have := congrArg Fin.val h; simp at this)]
  rw [e0, e1, e2, hs (v 1) (v 0)]
end Formalism.IndefR.Eqv
