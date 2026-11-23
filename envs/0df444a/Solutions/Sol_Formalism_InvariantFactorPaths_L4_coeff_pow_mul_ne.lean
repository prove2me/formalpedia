-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.coeff_pow_mul_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:04.538807+00:00
-- url     : https://prove2.me/submissions/36683f36-8f4e-4dbb-adcb-5b80dd472c4e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (y : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) (m : σ →₀ ℕ)
    (hm : m v ≠ e) : coeff m (X v ^ e * y) = 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [one_mul]
    by_contra hc
    have hmem : (m - Finsupp.single v e) ∈ y.support := mem_support_iff.mpr hc
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    have h0 : (m - Finsupp.single v e) v = 0 := hy (Finset.mem_coe.mpr hmem)
    have hle : Finsupp.single v e v ≤ m v := (Finsupp.le_def.1 h) v
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at h0 hle
    omega
  · rfl
end Formalism.InvariantFactorPaths.L4
