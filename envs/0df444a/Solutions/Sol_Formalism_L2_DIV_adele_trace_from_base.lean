-- Prove2me | solution 1 for Formalism.L2.DIV.adele_trace_from_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:44:14.685392+00:00
-- url     : https://prove2.me/submissions/12cffa17-9599-4300-ba78-92d63a9f06e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_conjugation_tmul

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
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (z : AfE F E) :
    ∃ t : 𝔸, (1 : E) ⊗ₜ[F] t = z + sigR σ 𝔸 z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e a =>
    obtain ⟨c, hc⟩ := hf (e + σ e) (by rw [map_add, h, add_comm])
    refine ⟨c • a, ?_⟩
    rw [conjugation_tmul, ← TensorProduct.add_tmul, ← hc, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [TensorProduct.tmul_add, hs, ht, map_add]; ring⟩
end Formalism.L2.DIV
