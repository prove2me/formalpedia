-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.rk_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:21.329864+00:00
-- url     : https://prove2.me/submissions/357838f3-6636-4f04-a382-f3d5c81d8fb3

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_sign_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_sign_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_le_of_map_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (s : ℕ) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) + finrank ℤ (eig E A (s + 1)) = finrank ℤ (zsub E A) := by
  have hd : Disjoint (eig E A s) (eig E A (s + 1)) := by
    rw [Submodule.disjoint_def]
    intro t h1 h2
    have e1 := ((mem_eig E A s t).mp h1).2
    have e2 := ((mem_eig E A (s + 1) t).mp h2).2
    rw [pow_succ] at e2
    have : (2 : E) * t = 0 := by linear_combination e1 + e2
    simpa using this
  rw [← finrank_sup E _ _ hd]
  apply le_antisymm
  · exact Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  · have : Module.Finite ℤ ↥(eig E A s ⊔ eig E A (s + 1)) :=
      finite_of_le E _ A (sup_le inf_le_left inf_le_left)
    refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (2 : E))
      (mul_right_injective₀ two_ne_zero) _ _ ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ A := ha
    have hc := sign_mem E A s _ (hA _ ha')
    have h1 : a + (-1) ^ s * complexConj E a ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem ha' hc, ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-a) * sign_sq E s
    have h2 : a - (-1) ^ s * complexConj E a ∈ eig E A (s + 1) := by
      rw [mem_eig]
      refine ⟨A.val.sub_mem ha' hc, ?_⟩
      simp only [map_sub, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply, pow_succ]
      linear_combination (-a) * sign_sq E s
    have h3 : LinearMap.mulLeft ℤ (2 : E) a
        = (a + (-1) ^ s * complexConj E a) + (a - (-1) ^ s * complexConj E a) := by
      rw [LinearMap.mulLeft_apply]; ring
    rw [h3]
    exact Submodule.add_mem_sup h1 h2
end Formalism.FourierDecayAlt.P.S6x3
