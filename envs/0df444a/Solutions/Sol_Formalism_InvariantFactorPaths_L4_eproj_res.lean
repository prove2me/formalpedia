-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:42.637302+00:00
-- url     : https://prove2.me/submissions/23cba321-f26b-4ed1-ac09-b8451aa4f37d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_comm
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
private theorem glAct_slice_lemma_2 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (Q : Set ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
  have hmono : ∀ (a b : Fin r), a ≠ ρ → b ≠ ρ → ∀ (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N),
      n (i, ρ) ∈ Q →
      X (i', a) * pderiv (i', b) (monomial n t) ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
    intro a b ha hb n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
    rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have h1 : (i', a) ≠ (i, ρ) := fun h => ha (Prod.mk.inj h).2
    have h2 : (i', b) ≠ (i, ρ) := fun h => hb (Prod.mk.inj h).2
    simpa [Finsupp.single_apply, h1, h2] using hn
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnQ : n (i, ρ) ∈ Q := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d hc hd n _ i' hnQ
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c hd hc n _ i' hnQ)
  · exact Submodule.zero_mem _
private theorem resL_keep_lemma_4 (v : Fin N × Fin r) (e : ℕ) (S : Set (Fin N × Fin r →₀ ℕ))
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] S) :
    resL p v e y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hy (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _
private theorem resL_glAct_lemma_3 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (e : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p (i, ρ) e (glAct p LL j c d x) = glAct p LL j c d (resL p (i, ρ) e x) := by
  have hres : ∀ (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (n : Fin N × Fin r →₀ ℕ),
      coeff n (resL p (i, ρ) e y) = if n (i, ρ) = e then coeff n y else 0 := by
    intro y n
    simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
    unfold initPart
    exact coeff_filt_lemma (fun m => m (i, ρ) = e) _ y n
  have hmem : resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_contra h
    exact hn (if_neg h)
  have hrest : x - resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)},
      resL p (i, ρ) e y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h (hy (Finset.mem_coe.mpr hn))
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)},
      resL p (i, ρ) e y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => hy (Finset.mem_coe.mpr hn) h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hsplit : x = resL p (i, ρ) e x + (x - resL p (i, ρ) e x) := by abel
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, hid _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hmem),
    hzero _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hrest), add_zero]
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
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (i : Fin N) (e : ℕ) :
    ∀ F ∈ WtSpC p LL j univ w, PE (resL p (i, ρ) e F) = resL p (i, ρ) e (PE F) := by
  intro F hF
  exact eproj_comm LL j ρ w w PE PE hPE hPE (resL p (i, ρ) e)
    (fun c hc d hd x => resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hc) (Finset.ne_of_mem_erase hd) i e x)
    (fun x hx => resL_keep_lemma_4 (i, ρ) e _ x hx) F hF
end Formalism.InvariantFactorPaths.L4
