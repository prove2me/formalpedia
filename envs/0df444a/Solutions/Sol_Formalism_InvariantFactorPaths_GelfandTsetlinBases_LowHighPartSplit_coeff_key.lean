-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.coeff_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:53.132791+00:00
-- url     : https://prove2.me/submissions/479a21f1-0fec-490b-9a1e-0bc00908bfb5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_supp_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {σ τ L : Type*} [CommRing L] (Lo : Set σ) (T : Finset τ) (A : τ → MvPolynomial σ L)
    (m : τ → σ →₀ ℕ) (hA : ∀ β ∈ T, A β ∈ supported L Lo) (hm : ∀ β ∈ T, ∀ x ∈ Lo, m β x = 0)
    (hinj : ∀ β ∈ T, ∀ γ ∈ T, m β = m γ → β = γ) {β : τ} (hβ : β ∈ T) {e : σ →₀ ℕ} (he : e ∈ (A β).support) :
    e + m β ∈ (∑ γ ∈ T, A γ * monomial (m γ) 1).support := by
  rw [mem_support_iff, coeff_sum, Finset.sum_eq_single β]
  · rw [coeff_mul_monomial, mul_one]
    exact mem_support_iff.mp he
  · intro γ hγ hne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · rw [mul_one]
      by_contra hc
      have hf : e + m β - m γ ∈ (A γ).support := mem_support_iff.mpr hc
      apply hne
      apply hinj γ hγ β hβ
      ext x
      by_cases hx : x ∈ Lo
      · rw [hm β hβ x hx, hm γ hγ x hx]
      · have h1 := supp_zero (hA γ hγ) hf hx
        have h2 := supp_zero (hA β hβ) he hx
        have h3 := Finsupp.le_def.mp hle x
        rw [Finsupp.tsub_apply, Finsupp.add_apply, h2] at h1
        rw [Finsupp.add_apply, h2] at h3
        omega
    · rfl
  · intro h
    exact absurd hβ h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
