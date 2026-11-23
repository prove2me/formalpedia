-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:06.943559+00:00
-- url     : https://prove2.me/submissions/4fd9ad79-cfc0-4272-bd5e-b08499fadaaf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_ideal_zero
import Theorems.Thm_Formalism_DivisionValues_idxChange_span_alg

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
  [IsFractionRing R K]
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) :
    ∃ ϖ : R, ϖ ∈ v.asIdeal ∧ ϖ ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K ϖ)) = 1 ∧
      ∃ t : R, t ∉ v.asIdeal ∧ ∀ x ∈ v.asIdeal, ∃ u : R, t * x = ϖ * u := by
  have hp1 : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  obtain ⟨ϖ, hϖ1, hϖ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot hp1 1
  rw [pow_one] at hϖ1
  have hϖ0 : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Ideal.zero_mem _)
  have hdvd : v.asIdeal ∣ Ideal.span {ϖ} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hϖ1
  obtain ⟨J, hJ⟩ := hdvd
  have hJp : ¬ J ≤ v.asIdeal := by
    intro hle
    apply hϖ2
    have : Ideal.span {ϖ} ≤ v.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self ϖ)
  have hspan0 : Ideal.span {ϖ} ≠ 0 := by simpa [Ideal.span_singleton_eq_bot] using hϖ0
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hspan0
    rw [hJ]; simp
  obtain ⟨t, htJ, htp⟩ := Set.not_subset.mp hJp
  refine ⟨ϖ, hϖ1, hϖ0, ?_, t, htp, ?_⟩
  · rw [idxChange_span_alg, hJ, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K v ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr v.ne_bot)
        ((FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr hJ0),
      FractionalIdeal.count_self, idxChange_cnt_ideal_zero v J hJ0 hJp]
    simp
  · intro x hx
    have hmem : x * t ∈ Ideal.span {ϖ} := by
      rw [hJ]; exact Ideal.mul_mem_mul hx htJ
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨u, by rw [mul_comm t x, ← hu, mul_comm]⟩
end Formalism.DivisionValues
