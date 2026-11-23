-- Prove2me | solution 1 for Formalism.UG.P.csGlob_intAdApprox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:44.711689+00:00
-- url     : https://prove2.me/submissions/a50d6452-c57b-4fd8-b932-023ecf28cd08

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Theorems.Thm_Formalism_UG_P_csGlobApprox_vD
import Theorems.Thm_Formalism_UG_P_csGlobApprox_local
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section
variable {F : Type} [Field F] [NumberField F]
end
private theorem exists_not_mem_asIdeal_pow_of_ne_zero {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (z : 𝓞 F) (hz : z ≠ 0) :
    ∃ n : ℕ, z ∉ w.asIdeal ^ n := by
  by_contra h
  push_neg at h
  have hmem : z ∈ ⨅ i : ℕ, w.asIdeal ^ i := Submodule.mem_iInf _ |>.2 h
  rw [Ideal.iInf_pow_eq_bot_of_isDomain] at hmem
  · exact hz ((Submodule.mem_bot _).1 hmem)
  · exact w.isPrime.ne_top
private theorem intValuation_lt_of_mem_pow_of_not_mem_pow {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {z D : 𝓞 F} {n : ℕ}
    (hDn : D ∉ w.asIdeal ^ n) (hz : z ∈ w.asIdeal ^ n) : w.intValuation z < w.intValuation D :=
  lt_of_le_of_lt ((w.intValuation_le_pow_iff_mem z n).2 hz)
    (not_le.1 fun h => hDn ((w.intValuation_le_pow_iff_mem D n).1 h))
private theorem valued_v_algebraMap_adicCompletion {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k := by
  first
  | exact w.valuedAdicCompletion_eq_valuation' k
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  classical
  have ha' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F := ha
  have hfin : {w : HeightOneSpectrum (𝓞 F) | D ∈ w.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {D})
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hD)
    simpa only [Ideal.dvd_span_singleton] using h
  choose r hr using fun w : HeightOneSpectrum (𝓞 F) => csGlobApprox_local w D hD (a w) (ha' w)
  choose e he using fun w : HeightOneSpectrum (𝓞 F) => exists_not_mem_asIdeal_pow_of_ne_zero w D hD
  obtain ⟨r0, hr0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun w => w.asIdeal) e (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun w => r w.1)
  have hγ : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation D ≠ 0 := fun w =>
    (lt_of_le_of_lt zero_le' (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) (Submodule.zero_mem _))).ne'
  have hbound : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
    intro w
    by_cases hw : D ∈ w.asIdeal
    · have hmem := hr0 w (hfin.mem_toFinset.2 hw)
      have h1 := hr w
      rw [csGlobApprox_vD] at h1
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) (r w) -
          algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
        rw [Valuation.map_sub_swap, ← map_sub, csGlobApprox_vD]
        exact (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) hmem).le
      rw [← sub_add_sub_cancel (a w) (algebraMap (𝓞 F) (w.adicCompletion F) (r w))]
      exact Valuation.map_add_le _ h1 h2
    · have h1 : w.intValuation D = 1 := by
        refine le_antisymm (w.intValuation_le_one D) ?_
        by_contra hlt
        push_neg at hlt
        first
        | exact hw ((w.intValuation_lt_one_iff_mem D).1 hlt)
        | exact hw (Ideal.dvd_span_singleton.1 ((w.intValuation_lt_one_iff_dvd D).1 hlt))
      rw [h1]
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · exact ha' w
      · rw [csGlobApprox_vD]
        exact w.intValuation_le_one r0
  have hd : algebraMap (𝓞 F) F D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
  have hsc : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D) := by
    first
    | exact IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D
    | rfl
  have hunit : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ = 1 := by
    rw [hsc, ← map_mul, mul_inv_cancel₀ hd, map_one]
  obtain ⟨Y, hY⟩ : ∃ Y : FiniteAdeleRing (𝓞 F) F, Y =
      (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ := ⟨_, rfl⟩
  refine ⟨r0, Y, (fun w => ?_ : ∀ w : HeightOneSpectrum (𝓞 F), Y w ∈ w.adicCompletionIntegers F), ?_⟩
  · have hcoord : Y w = (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ := by
      rw [hY]
      first
      | rfl
      | simp
    rw [hcoord]
    have hle : Valued.v ((a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹) ≤ 1 := by
      rw [map_mul, valued_v_algebraMap_adicCompletion, map_inv₀, w.valuation_of_algebraMap]
      calc _ ≤ w.intValuation D * (w.intValuation D)⁻¹ := by
            first
            | exact mul_le_mul_right (hbound w) _
            | exact mul_le_mul_of_nonneg_right (hbound w) zero_le'
            | (gcongr; exact hbound w)
        _ = 1 := mul_inv_cancel₀ (hγ w)
    exact hle
  · rw [hY]
    linear_combination (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0 - a) * hunit
end Formalism.UG.P
