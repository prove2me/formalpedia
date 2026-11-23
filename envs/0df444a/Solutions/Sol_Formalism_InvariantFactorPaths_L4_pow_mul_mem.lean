-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:44.771734+00:00
-- url     : https://prove2.me/submissions/126e97af-83c9-46d2-b02f-efdd2c34d38f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (Q : Set (σ →₀ ℕ)) (g : MvPolynomial σ ℚ_[p]) :
    X v ^ e * g ∈ restrictSupport ℚ_[p] Q ↔ g ∈ restrictSupport ℚ_[p] {m | Finsupp.single v e + m ∈ Q} := by
  classical
  have c1 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff m (X v ^ e * g') =
      if e ≤ m v then coeff (m - Finsupp.single v e) g' else 0 := by
    intro m g'
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  have c2 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff (m + Finsupp.single v e) (X v ^ e * g') = coeff m g' := by
    intro m g'
    rw [c1, if_pos (by simp), add_tsub_cancel_right]
  rw [mem_restrictSupport_iff, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    have h1 : coeff (m + Finsupp.single v e) (X v ^ e * g) ≠ 0 := by
      rwa [c2, ← mem_support_iff]
    have h2 := h (mem_support_iff.mpr h1)
    show Finsupp.single v e + m ∈ Q
    rwa [add_comm]
  · intro h m hm
    rw [Finset.mem_coe, mem_support_iff, c1] at hm
    split_ifs at hm with hle
    · have h2 : m - Finsupp.single v e ∈ {m | Finsupp.single v e + m ∈ Q} := h (mem_support_iff.mpr hm)
      simp only [Set.mem_setOf_eq] at h2
      rwa [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hle)] at h2
    · exact absurd rfl hm
end Formalism.InvariantFactorPaths.L4
