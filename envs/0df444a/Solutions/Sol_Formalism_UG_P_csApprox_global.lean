-- Prove2me | solution 1 for Formalism.UG.P.csApprox_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:58.852029+00:00
-- url     : https://prove2.me/submissions/faa386a1-8bf4-4696-9108-af934137a868

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Theorems.Thm_Formalism_UG_P_csApprox_val_int
import Theorems.Thm_Formalism_UG_P_csApprox_local
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places
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
open scoped WithZero
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.UG.P
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  have hP := levelaf_finite_places D hD
  choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hP.toFinset
  · have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.intValuation_eq_exp_neg_multiplicity hD] at h1
    have e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r =
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) +
          -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v)) := by
      rw [map_sub]; ring
    rw [e1, csApprox_val_int]
    refine Valuation.map_add_le _ (hs v).le ?_
    rw [Valuation.map_neg, csApprox_val_int]
    exact h1
  · have hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by simpa using hv
    have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
      le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')
    rw [h1]
    exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))
end Formalism.UG.P
