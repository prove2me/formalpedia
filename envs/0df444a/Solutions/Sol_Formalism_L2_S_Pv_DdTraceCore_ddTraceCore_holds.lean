-- Prove2me | solution 1 for Formalism.L2.S.Pv.DdTraceCore.ddTraceCore_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:12.855028+00:00
-- url     : https://prove2.me/submissions/c0c88f55-947e-48e9-818a-c7a5822d29d6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_DdTraceCore
import Theorems.Thm_Formalism_L2_S_Pv_DdTraceCore_relTrace_mem_inv_different

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.DdTraceCore
namespace Formalism.L2.S.Pv.DdTraceCore
theorem _root_.solution : Formalism.L2.SG.Pf.DdTraceCore := by
  intro F E _ _ _ _ _ y hy o
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
  have hne : ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
      Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero, ne_eq, Ideal.map_eq_bot_iff_of_injective hinj]
    exact differentIdeal_ne_bot
  have hyF : ∀ d ∈ differentIdeal ℤ (𝓞 F),
      ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F) := by
    intro d hd
    have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d) ∈
        ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
          Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, Ideal.mem_map_of_mem _ hd, rfl⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff hne).mp hy _ hmem)
    exact ⟨a, ha⟩
  have h1 := relTrace_mem_inv_different F E y hyF o
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _
  rw [coeIdeal_differentIdeal (K := ℚ), inv_inv, FractionalIdeal.mem_dual h10] at h1
  obtain ⟨m, hm⟩ := h1 1 (FractionalIdeal.one_mem_one _)
  refine ⟨m, ?_⟩
  rw [← Algebra.trace_trace (S := F)]
  rw [Algebra.traceForm_apply, mul_one] at hm
  rw [← hm]
  rfl
end Formalism.L2.S.Pv.DdTraceCore
