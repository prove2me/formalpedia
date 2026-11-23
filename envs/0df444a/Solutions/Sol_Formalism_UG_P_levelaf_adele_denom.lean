-- Prove2me | solution 1 for Formalism.UG.P.levelaf_adele_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.259379+00:00
-- url     : https://prove2.me/submissions/2ac5edde-b2df-47bf-a464-3018cc3da4f5

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem_v
import Theorems.Thm_Formalism_UG_P_levelaf_local_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.UG.P
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * a ∈ intAd F := by
  classical
  have hP : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose d hd0 hd using fun v : HeightOneSpectrum (𝓞 F) => levelaf_local_denom v (a v)
  refine ⟨∏ v ∈ hP.toFinset, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun w => ?_⟩
  show algebraMap (𝓞 F) (w.adicCompletion F) (∏ v ∈ hP.toFinset, d v) * a w ∈ _
  by_cases hw : w ∈ hP.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, map_mul, mul_comm (algebraMap _ _ (d w)), mul_assoc]
    exact mul_mem (levelaf_int_mem_v w _) (hd w)
  · have : a w ∈ w.adicCompletionIntegers F := by simpa using hw
    exact mul_mem (levelaf_int_mem_v w _) this
end Formalism.UG.P
