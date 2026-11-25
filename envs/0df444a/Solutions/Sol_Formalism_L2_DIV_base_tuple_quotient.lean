-- Prove2me | solution 1 for Formalism.L2.DIV.base_tuple_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:56.982485+00:00
-- url     : https://prove2.me/submissions/222b0bf1-c129-4b9e-abe7-ebc6f71a2dce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_finite_order_automorphism
import Theorems.Thm_Formalism_L2_DIV_mem_kills


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
namespace Formalism.L2.DIV
theorem _root_.solution : Mu0Quot := by
  intro F E _ _ _ _ _ L _ σ Ψ e G μ μ' h h'
  have h1 : μ * μ'⁻¹ ∈ kills Lˣ (ratId F E).range ⊓ openChr F E L := by
    refine Subgroup.mem_inf.mpr ⟨?_, (openChr F E L).mul_mem h.isOpen ((openChr F E L).inv_mem h'.isOpen)⟩
    rw [mem_kills]
    rintro _ ⟨a, rfl⟩
    have h2 : μ (ratId F E a) = μ' (ratId F E a) := Units.ext (by rw [h.rat, h'.rat])
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, h2, mul_inv_cancel]
  exact Subgroup.mem_inf.mpr ⟨h1, finite_order_automorphism F E L h1⟩
end Formalism.L2.DIV
