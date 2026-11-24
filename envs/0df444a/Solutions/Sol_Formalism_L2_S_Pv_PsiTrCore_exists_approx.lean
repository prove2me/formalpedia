-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:10.2941+00:00
-- url     : https://prove2.me/submissions/c7619cfe-266f-4ccb-973e-87dc11da16a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap_int
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_exists_int_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∀ v, Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
  classical
  have hspan : Ideal.span {n} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn
  set T := (Ideal.finite_factors hspan).toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ n ∈ v.asIdeal := fun v ↦ by
    simp [T, Set.Finite.mem_toFinset, Ideal.dvd_span_singleton]
  have hw : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (n : F) ≠ 0 := by
    intro v h
    have := valued_algebraMap_int v n
    rw [h, map_zero, intValuation_if_neg v hn] at this
    exact WithZero.exp_ne_zero this.symm
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      Valued.v (a v - algebraMap F (v.adicCompletion F) (r : F)) <
        Valued.v (algebraMap F (v.adicCompletion F) (n : F)) := fun v ↦
    exists_int_near v (a v) _ ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) (hw v)
      (by rw [valued_algebraMap_int]; exact intValuation_le_one v n)
  choose r hr using hr
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal)
    (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors)
    (fun v _ ↦ v.prime) (fun i _ j _ hij h ↦ hij (HeightOneSpectrum.ext h)) (fun i ↦ r i.1)
  refine ⟨b, fun v ↦ ?_⟩
  have hb1 : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1 := by
    rw [valued_algebraMap_int]; exact intValuation_le_one v b
  by_cases hv : v ∈ T
  · have h1 := (hr v).le
    rw [valued_algebraMap_int] at h1
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (r v : F) -
        algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
      rw [← map_sub, show (r v : F) - (b : F) = ((r v - b : 𝓞 F) : F) from
        (map_sub (algebraMap (𝓞 F) F) _ _).symm, valued_algebraMap_int, ← Valuation.map_neg,
        neg_sub, intValuation_if_neg v hn]
      exact (intValuation_le_pow_iff_mem v _ _).mpr (hb v hv)
    have e : a v - algebraMap F (v.adicCompletion F) (b : F) =
        (a v - algebraMap F (v.adicCompletion F) (r v : F)) +
          (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
  · have hn1 : v.intValuation n = 1 := le_antisymm (intValuation_le_one v n)
      (not_lt.mp fun h ↦ hv ((hmemT v).mpr ((intValuation_lt_one_iff_mem v n).mp h)))
    rw [hn1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) hb1)
end Formalism.L2.S.Pv.PsiTrCore
