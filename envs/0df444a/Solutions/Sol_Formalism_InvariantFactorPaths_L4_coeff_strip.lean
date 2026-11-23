-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.coeff_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:04.6788+00:00
-- url     : https://prove2.me/submissions/55708e9c-cb21-4538-8ffa-6bbb0d85b5a2

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


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type}
private theorem coeff_initPart_eq_ite (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (n : σ →₀ ℕ) :
    coeff n (initPart v e f) = if n v = e then coeff n f else 0 := by
  classical
  unfold initPart
  rw [coeff_sum]
  simp only [apply_ite (coeff n), coeff_monomial, coeff_zero]
  rw [Finset.sum_eq_single n]
  · by_cases h : n v = e <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro hn
    have h0 : coeff n f = 0 := by simpa [mem_support_iff] using hn
    simp [h0]
end Gen
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (n : σ →₀ ℕ) (f : MvPolynomial σ ℚ_[p]) :
    coeff n (strip p v e f) = if n v = 0 then coeff (Finsupp.single v e + n) f else 0 := by
  classical
  show coeff n ((initPart v e f).divMonomial (Finsupp.single v e)) = _
  rw [coeff_divMonomial, coeff_initPart_eq_ite]
  by_cases h : n v = 0 <;> simp [h]
end Formalism.InvariantFactorPaths.L4
