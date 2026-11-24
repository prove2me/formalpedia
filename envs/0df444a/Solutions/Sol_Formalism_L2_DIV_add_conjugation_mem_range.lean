-- Prove2me | solution 1 for Formalism.L2.DIV.add_conjugation_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:44:12.507504+00:00
-- url     : https://prove2.me/submissions/a1c34b88-5d50-40af-98a0-e5e70c44df23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_tensor_conjugation_tmul

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    z + sigR σ R z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e r =>
    obtain ⟨a, ha⟩ := hσ.2.2 (e + σ e) (by rw [map_add, hσ.2.1, add_comm])
    refine ⟨a • r, ?_⟩
    show (1 : E) ⊗ₜ[F] (a • r) = e ⊗ₜ[F] r + sigR σ R (e ⊗ₜ[F] r)
    rw [tensor_conjugation_tmul, ← TensorProduct.add_tmul, ← ha, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    have : x + y + sigR σ R (x + y) = (x + sigR σ R x) + (y + sigR σ R y) := by rw [map_add]; ring
    rw [this]; exact add_mem hx hy
end Formalism.L2.DIV
