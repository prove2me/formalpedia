-- Prove2me | solution 1 for Formalism.L2.DIV.c_inv_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:23.344038+00:00
-- url     : https://prove2.me/submissions/aac3fb8c-982c-42a1-9af1-0b8cb1f89633

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.DIV
theorem _root_.solution (x : (AfE F E)ˣ) (k : ℕ) : ∀ y ∈ (c_lat x) ^ k,
    ((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ k * ιE y ∈ RInt F E := by
  induction k with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hy
    rw [pow_zero, one_mul]; exact Formalism.UG.CS.incl_int b
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn
      have : ((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ (k + 1) * ιE (m * n) =
          (((x⁻¹ : (AfE F E)ˣ) : AfE F E) ^ k * ιE m) * (((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE n) := by
        rw [map_mul]; ring
      rw [this]; exact mul_mem (ih m hm) hn
    · intro a b ha hb
      rw [map_add, mul_add]; exact add_mem ha hb
end Formalism.L2.DIV
