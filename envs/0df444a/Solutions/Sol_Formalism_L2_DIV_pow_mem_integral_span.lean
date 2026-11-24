-- Prove2me | solution 1 for Formalism.L2.DIV.pow_mem_integral_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:01.637876+00:00
-- url     : https://prove2.me/submissions/dd13c1d8-d764-4056-bb62-9864ea28169a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_c_decomp
import Theorems.Thm_Formalism_L2_DIV_c_T_mul

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
theorem _root_.solution (x : (AfE F E)ˣ) (k : ℕ) : (x : AfE F E) ^ k ∈ integralAdeleSpan (F := F) ((c_lat x) ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Submodule.subset_span ⟨1, Submodule.mem_one.mpr ⟨1, map_one _⟩, map_one _⟩
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine c_T_mul _ _ ih ?_
    obtain ⟨e₁, h₁, e₂, h₂, _, t, ht, hx⟩ := c_decomp x
    rw [hx]
    refine add_mem (Submodule.subset_span ⟨e₁, h₁, rfl⟩) ?_
    have : ιE e₂ * t = (⟨t, ht⟩ : RInt F E) • ιE e₂ := by
      rw [Subring.smul_def, smul_eq_mul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e₂, h₂, rfl⟩)
end Formalism.L2.DIV
