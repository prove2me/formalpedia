-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.inf_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:37.046835+00:00
-- url     : https://prove2.me/submissions/ee31ca19-0af0-4266-b3c6-57cfc83807ba

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig
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
theorem _root_.solution (A : FI E) (g s : ℕ) (hg : 0 < g) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ⊓
        (eig E A s).toAddSubgroup
      = (eig E A s).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  have hg' : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx1
    obtain ⟨-, h2⟩ := (mem_eig E A s _).mp hx2
    refine ⟨a, (mem_eig E A s a).mpr ⟨ha, ?_⟩, by simp⟩
    rw [map_mul, map_natCast] at h2
    apply mul_left_cancel₀ hg'
    linear_combination h2
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_eig E A s a).mp ha
    have e : nsmulAddMonoidHom (α := E) g a = (g : E) * a := by simp
    rw [e]
    refine ⟨(mem_gA E A g _).mpr ⟨a, h1, rfl⟩, (mem_eig E A s _).mpr ⟨?_, ?_⟩⟩
    · exact gA_le E A g _ ((mem_gA E A g _).mpr ⟨a, h1, rfl⟩)
    · rw [map_mul, map_natCast]
      linear_combination (g : E) * h2
end Formalism.FourierDecayAlt.P.S6x3
