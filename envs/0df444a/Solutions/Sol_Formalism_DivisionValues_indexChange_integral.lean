-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:42:34.533188+00:00
-- url     : https://prove2.me/submissions/f805d18a-6131-4262-8d9b-c3732ab453f6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_unit
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mem
import Theorems.Thm_Formalism_DivisionValues_idxChange_unif
import Theorems.Thm_Formalism_DivisionValues_indexChange_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_idxChange_Dg_mul
import Theorems.Thm_Formalism_DivisionValues_indexChange_cancel
import Theorems.Thm_Formalism_DivisionValues_indexChange_unit
import Theorems.Thm_Formalism_DivisionValues_indexChange_uniformizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) (i : Fin d) :
    ∀ n : ℕ, ∀ a : R, a ≠ 0 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) = n →
      IdxChangeP v (idxChangeDg i (algebraMap R K a)) := by
  obtain ⟨ϖ, _, hϖ0, hcntϖ, t, htp, ht⟩ := idxChange_unif (K := K) v
  have hinj := IsFractionRing.injective R K
  have hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).mpr hb
  intro n
  induction n with
  | zero =>
    intro a ha hc
    have hap : a ∉ v.asIdeal := by
      intro h
      have := idxChange_cnt_mem (K := K) v ha h
      omega
    exact indexChange_unit v i hap
  | succ n ih =>
    intro a ha hc
    have hap : a ∈ v.asIdeal := by
      by_contra h
      rw [idxChange_cnt_unit v h] at hc
      omega
    obtain ⟨a', ha'⟩ := ht a hap
    have ht0 : t ≠ 0 := fun h => htp (h ▸ v.asIdeal.zero_mem)
    have ha'0 : a' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ha'
      rcases mul_eq_zero.mp ha' with h | h
      · exact ht0 h
      · exact ha h
    have hc' : FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a')) =
        n := by
      have e1 := idxChange_cnt_mul v (hne t ht0) (hne a ha)
      have e2 := idxChange_cnt_mul v (hne ϖ hϖ0) (hne a' ha'0)
      rw [← map_mul, ha', map_mul] at e1
      rw [e1, idxChange_cnt_unit v htp, hc, hcntϖ] at e2
      push_cast at e2
      linarith
    have Pa' := ih a' ha'0 hc'
    have Pϖa' : IdxChangeP v (idxChangeDg i (algebraMap R K ϖ * algebraMap R K a')) := by
      rw [← idxChange_Dg_mul]
      exact indexChange_mul v (by rw [idxChange_det_Dg]; exact hne ϖ hϖ0)
        (by rw [idxChange_det_Dg]; exact hne a' ha'0) (indexChange_uniformizer v i hcntϖ htp ht) Pa'
    have Pta : IdxChangeP v (idxChangeDg i (algebraMap R K t * algebraMap R K a)) := by
      rw [← map_mul, ha', map_mul]; exact Pϖa'
    exact indexChange_cancel v i (hne t ht0) (hne a ha) (indexChange_unit v i htp) Pta
end Formalism.DivisionValues
