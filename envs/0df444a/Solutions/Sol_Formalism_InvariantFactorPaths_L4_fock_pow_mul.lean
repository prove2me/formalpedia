-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.fock_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:05.989319+00:00
-- url     : https://prove2.me/submissions/07a2efd0-0e10-46c0-a12e-c404305e7b1f

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
private theorem prod_factorial_single_add_eq_mul (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    ((Finsupp.single v e + m).prod fun _ k => (k.factorial : ℚ_[p])) =
      (e.factorial : ℚ_[p]) * m.prod fun _ k => (k.factorial : ℚ_[p]) := by
  classical
  have hdisj : Disjoint (Finsupp.single v e).support m.support := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' := Finsupp.support_single_subset ha
    rw [Finset.mem_singleton] at ha'
    subst ha'
    exact (Finsupp.mem_support_iff.mp hb) hm
  rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]
private theorem fock_eq_sum_coeff_mul_factorial (F G : MvPolynomial σ ℚ_[p]) (S : Finset (σ →₀ ℕ)) (hS : F.support ⊆ S) :
    fock p F G = ∑ m ∈ S, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  unfold fock
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa [mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]
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
theorem _root_.solution (v : σ) (e : ℕ) (y z : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) :
    fock p (X v ^ e * y) (X v ^ e * z) = (e.factorial : ℚ_[p]) * fock p y z := by
  classical
  have hy' : ∀ m ∈ y.support, m v = 0 := by
    intro m hm
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    exact hy (Finset.mem_coe.mpr hm)
  have hcoeff : ∀ (u : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ),
      coeff (Finsupp.single v e + m) (X v ^ e * u) = coeff m u := by
    intro u m
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
  have hsub : (X v ^ e * y).support ⊆ y.support.image (fun m => Finsupp.single v e + m) := by
    intro m hm
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
    split_ifs at hm with h
    · rw [Finset.mem_image]
      refine ⟨m - Finsupp.single v e, mem_support_iff.mpr (by simpa using hm), ?_⟩
      exact add_tsub_cancel_of_le h
    · exact absurd rfl hm
  rw [fock_eq_sum_coeff_mul_factorial _ _ _ hsub, Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hcoeff, hcoeff, prod_factorial_single_add_eq_mul v e m (hy' m hm)]
  ring
end Formalism.InvariantFactorPaths.L4
