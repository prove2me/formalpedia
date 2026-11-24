-- Prove2me | solution 1 for Formalism.L2.S.Pv.DdTraceCore.relTrace_mem_inv_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:18.312026+00:00
-- url     : https://prove2.me/submissions/a339f1a9-b093-41ea-b687-98129ee324ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_DdTraceCore

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
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (y : E)
    (hy : ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F))
    (o : 𝓞 E) :
    Algebra.trace F E ((o : E) * y) ∈
      ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))⁻¹ := by
  have hD : ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  rw [FractionalIdeal.mem_inv_iff hD]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
  obtain ⟨a, ha⟩ := hy d hd
  rw [FractionalIdeal.mem_one_iff]
  have key : Algebra.trace F E ((o : E) * y) * algebraMap (𝓞 F) F d =
      Algebra.trace F E (algebraMap (𝓞 E) E (o * a)) := by
    rw [map_mul (algebraMap (𝓞 E) E), ha]
    change _ = Algebra.trace F E ((o : E) * (y * algebraMap F E (d : F)))
    rw [← mul_assoc]
    generalize (o : E) * y = z
    have h := (Algebra.trace F E).map_smul (d : F) z
    rw [Algebra.smul_def, smul_eq_mul] at h
    rw [mul_comm z, h, mul_comm]
  have hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E (o * a))) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe (o * a))
  exact ⟨⟨_, hint⟩, key.symm⟩
end Formalism.L2.S.Pv.DdTraceCore
