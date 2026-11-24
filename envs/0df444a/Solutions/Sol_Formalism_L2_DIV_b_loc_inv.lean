-- Prove2me | solution 1 for Formalism.L2.DIV.b_loc_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:16.767585+00:00
-- url     : https://prove2.me/submissions/32513b66-4ca4-4194-9249-7806d1b8d43e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_alg
import Theorems.Thm_Formalism_L2_DIV_b_eps_val
import Theorems.Thm_Formalism_L2_DIV_b_inv_int
import Theorems.Thm_Formalism_L2_DIV_b_alg_ne_zero
import Theorems.Thm_Formalism_UG_P_afsplitI_mem_intAd
import Theorems.Thm_Formalism_UG_P_afsplitI_ne
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem


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
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = bEps E v := by
  refine ⟨⟨(1 : E) ⊗ₜ[F] afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 (afsplitI_mem_intAd v _ (b_inv_int v r hr))
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    by_cases h : w = v
    · subst h
      rw [afsplit_mul_apply, afsplitI_self, afsplitI_self]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r hr)
    · rw [afsplit_mul_apply, afsplitI_ne v w h, afsplitI_ne v w h, mul_zero]
end Formalism.L2.DIV
