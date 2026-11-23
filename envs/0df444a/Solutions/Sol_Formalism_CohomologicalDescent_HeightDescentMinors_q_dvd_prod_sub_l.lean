-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_prod_sub_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:54.975859+00:00
-- url     : https://prove2.me/submissions/ea1761f5-e928-41e4-bfe7-f96383f3e801

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_cyclotomic_dvd_prod_X_pow_sub_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ (∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l]) := by
  obtain ⟨s, hs⟩ := cyclotomic_dvd_prod_X_pow_sub_one_sub l hl2
  have h := congrArg (Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧)) hs
  simp only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C,
    map_mul] at h
  have hc : Polynomial.aeval (1 + X : ℤ_[l]⟦X⟧) (Polynomial.cyclotomic l ℤ) = q l ℤ_[l] := by
    rw [Polynomial.cyclotomic_prime, map_sum]
    simp only [map_pow, Polynomial.aeval_X]
    apply mul_left_cancel₀ (X_ne_zero (R := ℤ_[l]))
    rw [(hq l ℤ_[l]).1]
    have h2 := mul_geom_sum (1 + X : ℤ_[l]⟦X⟧) l
    simpa using h2
  have hl : (algebraMap ℤ ℤ_[l]⟦X⟧) (l : ℤ) = C (l : ℤ_[l]) := by simp
  rw [hc, hl] at h
  exact ⟨_, h⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
