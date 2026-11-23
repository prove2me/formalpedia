-- Prove2me | solution 1 for Formalism.UG.P.levelv_denom_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:26.561803+00:00
-- url     : https://prove2.me/submissions/bf50cbd0-7451-4555-bc6f-36b76424c3cc

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {ι : Type*} [Fintype ι] (a : ι → E ⊗[F] v.adicCompletion F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i, N • a i ∈ lvS F E v := by
  classical
  choose M hM0 hM using fun i => levelv_denom v (a i)
  refine ⟨∏ i, M i, Finset.prod_ne_zero_iff.mpr fun i _ => hM0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ M (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hM i) _
end Formalism.UG.P
