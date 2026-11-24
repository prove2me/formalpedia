-- Prove2me | solution 1 for Formalism.L2.DIV.b_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:26.504719+00:00
-- url     : https://prove2.me/submissions/d7981591-893e-4961-a33a-b90d4e384b5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_val
import Theorems.Thm_Formalism_L2_DIV_b_map_shape
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_csGlob_int


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
theorem _root_.solution (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0) (hD : algebraMap (𝓞 F) (𝓞 E) D ∈ I)
    (c : 𝓞 E) (hc : toRInt F E c ∈ I.map (toRInt F E)) : c ∈ I := by
  obtain ⟨c', hc', t, h⟩ := b_map_shape I D hD0 _ hc
  have hDE : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E]
    exact adelstab_algebraMap_ne_zero D hD0
  set d : E := algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D) with hd
  have h1 : ((t : RInt F E) : AfE F E) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    have h2 := congrArg (fun z : RInt F E => (z : AfE F E)) h
    simp only [Subring.coe_add, Subring.coe_mul, b_toRInt_val] at h2
    have h3 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d * (t : AfE F E) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d *
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
      rw [← map_mul, mul_div_cancel₀ _ hDE, map_sub, h2]
      ring
    have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) d) := (IsUnit.mk0 d hDE).map _
    exact hu.mul_left_cancel h3
  have hint : IsIntegral ℤ ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d) := by
    apply csGlob_int (F := F)
    rw [← h1]
    exact t.2
  let m : 𝓞 E := ⟨_, hint⟩
  have hm : c - c' = algebraMap (𝓞 F) (𝓞 E) D * m := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (c - c') = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) D * m)
    rw [map_sub, map_mul]
    show _ = d * ((algebraMap (𝓞 E) E c - algebraMap (𝓞 E) E c') / d)
    rw [mul_div_cancel₀ _ hDE]
  have : c = c' + algebraMap (𝓞 F) (𝓞 E) D * m := by rw [← hm]; ring
  rw [this]
  exact I.add_mem hc' (I.mul_mem_right _ hD)
end Formalism.L2.DIV
