-- Prove2me | solution 1 for Formalism.UG.P.levelaf_local_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:01.579961+00:00
-- url     : https://prove2.me/submissions/0c7f97c1-b50d-4fab-beb5-4e789172f983

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem_v

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (v.adicCompletion F) d * x ∈ v.adicCompletionIntegers F := by
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨a, ha⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at ha
  obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) a
  refine ⟨(den : 𝓞 F), nonZeroDivisors.ne_zero den.2, ?_⟩
  have h1 : algebraMap (𝓞 F) (v.adicCompletion F) num =
      algebraMap F (v.adicCompletion F) a * algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) num, ← hnd, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have e : algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * x =
      algebraMap (𝓞 F) (v.adicCompletion F) num -
        algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * (algebraMap F _ a - x) := by
    rw [h1]; ring
  rw [e]
  refine sub_mem (levelaf_int_mem_v v _) (mul_mem (levelaf_int_mem_v v _) ?_)
  rw [mem_adicCompletionIntegers]; exact ha.le
end Formalism.UG.P
