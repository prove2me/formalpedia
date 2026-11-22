-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtComp_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:26.195797+00:00
-- url     : https://prove2.me/submissions/c9826956-3f32-4015-b45e-6ef7f7f1563c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
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
section EProj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem coeff_filt_lemma {σ R : Type*} [CommSemiring R] [DecidableEq σ] (P : (σ →₀ ℕ) → Prop)
    (dec : ∀ m, Decidable (P m)) (x : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (∑ m ∈ x.support, @ite _ (P m) (dec m) (monomial m (coeff m x)) 0) =
      @ite _ (P n) (dec n) (coeff n x) 0 := by
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (coeff n), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  by_cases hn : n ∈ x.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hn h
  · have h0 : coeff n x = 0 := by simpa using hn
    rw [h0, ite_self]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := fun h => hn (h ▸ hb)
    simp [hbn]
end EProj
section WtComp
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end WtComp
section MulX
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end MulX
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (v : Fin N × Fin r) (e : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (wtComp p LL j w x) = wtComp p LL j w (resL p v e x) := by
  ext n
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart wtComp compP
  beta_reduce
  rw [coeff_filt_lemma (fun m => m v = e) _]
  erw [coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _, coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _]
  rw [coeff_filt_lemma (fun m => m v = e) _]
  split_ifs <;> rfl
end Formalism.InvariantFactorPaths.L4
