-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.gA_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:31.503701+00:00
-- url     : https://prove2.me/submissions/b7ffc4da-0501-4e4a-957e-ae2eb6d150c9

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_gA

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
theorem _root_.solution (A : FI E) (g : ℕ) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup
      = (zsub E A).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  ext x
  rw [AddSubgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
    exact ⟨a, ha, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact (mem_gA E A g _).mpr ⟨a, ha, by simp⟩
end Formalism.FourierDecayAlt.P.S6x3
