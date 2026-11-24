-- Prove2me | solution 1 for Formalism.L2.DIV.auxiliary_primes_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:21.485616+00:00
-- url     : https://prove2.me/submissions/5ca9226e-d5a9-4766-8346-4bc150fb6e51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_eps_mul_unit
import Theorems.Thm_Formalism_L2_DIV_b_loc_inv
import Theorems.Thm_Formalism_L2_DIV_b_intU

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution : QprimeFinite := by
  intro F E _ _ _ _ _ L _ ξ hξ
  obtain ⟨N, hN, hker⟩ := hξ
  have hN0 : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hN.ne'
  apply (Ideal.finite_factors hN0).subset
  intro v hv
  rw [Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hNv
  apply hv
  refine le_trans ?_ hker
  rintro x ⟨hx1, hx2⟩
  obtain ⟨u, rfl⟩ := b_intU x hx1
  refine ⟨u, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_kerRed, ← b_eps_mul_unit v u hx2]
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v _ hNv
  rw [← hρ, map_natCast, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end Formalism.L2.DIV
