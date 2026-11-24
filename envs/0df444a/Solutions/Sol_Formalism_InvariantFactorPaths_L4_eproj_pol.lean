-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:35.239301+00:00
-- url     : https://prove2.me/submissions/b3b53889-1cca-4de4-be72-aa142aa13949

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
private theorem glAct_md_lemma_5 (LL : Letters N) (j : ℕ) (c d : Fin r) (B : Prop)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
  have hs : ∀ (i' : Fin N) (a' : Fin r) (i'' : Fin N),
      ∑ c', (Finsupp.single (i', a') 1 : Fin N × Fin r →₀ ℕ) (i'', c') = if i'' = i' then 1 else 0 := by
    intro i' a' i''
    by_cases h : i'' = i'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hmono : ∀ (a b : Fin r) (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N), (MultiDeg LL n ↔ B) →
      X (i', a) * pderiv (i', b) (monomial n t) ∈
        MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
    intro a b n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : n (i', b) = 0
    · rw [h0]
      simp
    · have hle : Finsupp.single (i', b) 1 ≤ n := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
      rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
      have hsum : ∀ i'', ∑ c', ((Finsupp.single (i', a) 1 + (n - Finsupp.single (i', b) 1) : Fin N × Fin r →₀ ℕ)) (i'', c') =
          ∑ c', n (i'', c') := by
        intro i''
        have hn' : n = (n - Finsupp.single (i', b) 1) + Finsupp.single (i', b) 1 :=
          (tsub_add_cancel_of_le hle).symm
        conv_rhs => rw [hn']
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hs]
        ring
      show MultiDeg LL _ ↔ B
      rw [← hn]
      unfold MultiDeg
      simp only [hsum]
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnB : (MultiDeg LL n ↔ B) := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d n _ i' hnB
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c n _ i' hnB)
  · exact Submodule.zero_mem _
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
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ F ∈ Pol p r LL, F ∈ WtSpC p LL j univ w → PE F ∈ Pol p r LL := by
  classical
  intro F hFP hFW
  let Pm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    { toFun := fun x => ∑ m ∈ x.support, if MultiDeg LL m then monomial m (coeff m x) else 0
      map_add' := fun x y => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_add, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp
      map_smul' := fun t x => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_smul, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp }
  have hπ : ∀ y n, coeff n (Pm y) = if MultiDeg LL n then coeff n y else 0 :=
    fun y n => coeff_filt_lemma (fun m => MultiDeg LL m) _ y n
  have hsupp : ∀ (S : Set (Fin N × Fin r →₀ ℕ)) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      y ∈ MvPolynomial.restrictSupport ℚ_[p] S → Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
    intro S y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    apply hy
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
    intro h0
    exact hn (by rw [h0, ite_self])
  have hmemT : ∀ y, Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_true]
    by_contra h
    exact hn (if_neg h)
  have hrest : ∀ y, y - Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_false]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)}, Pm y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h ((hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ True).mpr trivial)
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)}, Pm y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => (hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ False).mp h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      Pm (glAct p LL j c d x) = glAct p LL j c d (Pm x) := by
    intro c _ d _ x
    have hsplit : x = Pm x + (x - Pm x) := by abel
    conv_lhs => rw [hsplit]
    rw [map_add, map_add, hid _ (glAct_md_lemma_5 LL j c d True _ (hmemT x)),
      hzero _ (glAct_md_lemma_5 LL j c d False _ (hrest x)), add_zero]
  have key := eproj_comm LL j ρ w w PE PE hPE hPE Pm hQ (fun x hx => hsupp _ x hx) F hFW
  have hF : Pm F = F := hid F (by
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hFP
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    simpa using hFP hn)
  rw [hF] at key
  rw [key]
  have hT := hmemT (PE F)
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  rw [MvPolynomial.mem_restrictSupport_iff] at hT
  intro n hn
  simpa using hT hn
end Formalism.InvariantFactorPaths.L4
