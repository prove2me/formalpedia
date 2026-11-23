-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.tw_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:33.077907+00:00
-- url     : https://prove2.me/submissions/03501306-f9af-498b-805a-8e5d35eecdc0

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_exists_theta
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mul_mem_FI
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_sign_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_sign_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_gA
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_gA_le

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
theorem _root_.solution (A : FI E) (g s : ℕ) (hA : ConjStable E A) (hg : 0 < g) (hU : UnramAbove E g) :
    twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s
      = eig E A s ⊔ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := (mem_twLat E _ _ s t).mp ht
    obtain ⟨θ, w, hθ⟩ := exists_theta E g hg hU
    have h1 : (θ : E) * t ∈ A := mul_mem_FI E A θ t ht1
    have h2 : (θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t) ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem h1 (sign_mem E A s _ (hA _ h1)), ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-(θ : E) * t) * sign_sq E s
    have h3 : complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)
        ∈ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
      refine Submodule.sub_mem _ ?_ ?_
      · exact mul_mem_FI E _ (ringOfIntegersComplexConj E θ) _ ht2
      · exact (mem_gA E A g _).mpr ⟨_, mul_mem_FI E A w t ht1, rfl⟩
    have h4 : t = ((θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t)) +
        (complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)) := by
      rw [map_mul]
      linear_combination (-t) * hθ
    rw [h4]
    exact Submodule.add_mem_sup h2 h3
  · refine sup_le ?_ ?_
    · intro t ht
      obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
      rw [mem_twLat, ht2]
      exact ⟨ht1, Submodule.zero_mem _⟩
    · intro t ht
      rw [mem_twLat]
      refine ⟨gA_le E A g t ht, ?_⟩
      obtain ⟨a, ha, rfl⟩ := (mem_gA E A g t).mp ht
      refine (mem_gA E A g _).mpr ⟨a - (-1) ^ s * complexConj E a,
        A.val.sub_mem ha (sign_mem E A s _ (hA _ ha)), ?_⟩
      rw [map_mul, map_natCast]
      ring
end Formalism.FourierDecayAlt.P.S6x3
