-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.fock_pairing_initial_minor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.559801+00:00
-- url     : https://prove2.me/submissions/76208da5-1fd9-4903-bfe2-94b1ac4e236e

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
namespace Formalism.BranchingDeterminantCap
section XiA
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
end XiA
section XiB
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
private lemma prod_factorial_single_add_eq_mul' (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ) :
    (∏ k ∈ (Finsupp.single v 1 + m).support,
      ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial) =
      (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  set T := insert v m.support with hTdef
  have hT : ∀ u : (Fin r × Fin n) →₀ ℕ, u.support ⊆ T →
      ∏ k ∈ u.support, (u k).factorial = (u v).factorial * ∏ k ∈ T.erase v, (u k).factorial := by
    intro u hu
    rw [Finset.mul_prod_erase T (fun k => (u k).factorial) (Finset.mem_insert_self v _)]
    refine Finset.prod_subset hu fun k _ hk => ?_
    have h0 : u k = 0 := by simpa using hk
    rw [h0, Nat.factorial_zero]
  have hsub : (Finsupp.single v 1 + m).support ⊆ T := by
    intro k hk
    by_contra hc
    have hkv : k ≠ v := by
      rintro rfl
      exact hc (Finset.mem_insert_self _ _)
    have hkm : m k = 0 := by
      by_contra hm
      exact hc (Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 hm))
    have h5 : (Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k = 0 := by simp [Finsupp.single_apply, Ne.symm hkv, hkm]
    exact (Finsupp.mem_support_iff.1 hk) h5
  rw [hT _ hsub, hT m (Finset.subset_insert _ _)]
  have hrest : ∏ k ∈ T.erase v, ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial =
      ∏ k ∈ T.erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.single_apply, Ne.symm hkv]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1, Nat.factorial_succ]
  ring
private lemma coeff_pderiv_eq_mul_coeff_single_add (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ)
    (H : MvPolynomial (Fin r × Fin n) ℂ) :
    (pderiv v H).coeff m = ((m v + 1 : ℕ) : ℂ) * H.coeff (Finsupp.single v 1 + m) := by
  induction H using MvPolynomial.induction_on'
  next u a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hu : u = Finsupp.single v 1 + m
    · subst hu
      rw [add_tsub_cancel_left, if_pos rfl, if_pos rfl]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · rw [if_neg hu, mul_zero]
      split_ifs with h2
      · have h3 : u v = 0 := by
          by_contra h4
          apply hu
          rw [← h2]
          ext k
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with h5
          · subst h5
            omega
          · omega
        rw [h3]
        simp
      · rfl
  next p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]
private lemma fockF_X_mul_eq_pderiv (v : Fin r × Fin n) (G H : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (X v * G) H = fockF G (pderiv v H) := by
  unfold fockF
  rw [MvPolynomial.support_X_mul, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul, coeff_pderiv_eq_mul_coeff_single_add, prod_factorial_single_add_eq_mul', star_mul']
  push_cast
  rw [show star ((m v : ℂ) + 1) = (m v : ℂ) + 1 by simp]
  ring
private lemma fockF_sum_right' {ι' : Type*} (s : Finset ι') (F : MvPolynomial (Fin r × Fin n) ℂ)
    (G : ι' → MvPolynomial (Fin r × Fin n) ℂ) :
    fockF F (∑ i ∈ s, G i) = ∑ i ∈ s, fockF F (G i) := by
  unfold fockF
  simp only [MvPolynomial.coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
private lemma fockF_C_mul_right (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF F (C c * G) = star c * fockF F G := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, star_mul']
  ring
end XiB
section XiC
variable {r n : ℕ}
end XiC
section XiD
end XiD
section XiE
variable {r n : ℕ}
end XiE
section XiF
end XiF
end Formalism.BranchingDeterminantCap
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (g : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ a : Fin p → κ, fockF (xnMono ι hp a * g) (initMinor ℂ (ι ∘ a) hp * f) =
      ((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF g f := by
  induction p generalizing g with
  | zero =>
    simp [xnMono, xnC, initMinor]
  | succ p ih =>
    have hp0 : p ≤ n := Nat.le_of_succ_le hp
    have hre : ∀ F : (Fin (p + 1) → κ) → ℂ,
        ∑ a, F a = ∑ a' : Fin p → κ, ∑ b : κ, F (Fin.snoc a' b : Fin (p + 1) → κ) := by
      intro F
      rw [← Fintype.sum_prod_type']
      symm
      refine Fintype.sum_bijective (fun x : (Fin p → κ) × κ => (Fin.snoc x.1 x.2 : Fin (p + 1) → κ))
        ⟨?_, ?_⟩ _ _ fun x => rfl
      · intro x y hxy
        have h1 := congrArg Fin.init hxy
        have h2 := congrFun hxy (Fin.last p)
        simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
        exact Prod.ext h1 h2
      · intro a
        exact ⟨(Fin.init a, a (Fin.last p)), Fin.snoc_init_self a⟩
    have hmono : ∀ (a' : Fin p → κ) (b : κ), xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) =
        xnMono ι hp0 a' * X (ι b, (⟨p, hp⟩ : Fin n)) := by
      intro a' b
      unfold xnMono
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    have hstep : ∀ a' : Fin p → κ, ∑ b : κ, fockF (xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g)
        (initMinor ℂ (ι ∘ (Fin.snoc a' b : Fin (p + 1) → κ)) hp * f) =
        star ((Fintype.card κ : ℂ) - p + ((m p : ℕ) : ℂ)) *
          fockF (xnMono ι hp0 a' * g) (initMinor ℂ (ι ∘ a') hp0 * f) := by
      intro a'
      have hE : ∀ b : κ, xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g =
          X (ι b, (⟨p, hp⟩ : Fin n)) * (xnMono ι hp0 a' * g) := fun b => by rw [hmono]; ring
      simp only [hE, fockF_X_mul_eq_pderiv]
      rw [← fockF_sum_right', xn_key ι hι hp a' f ((m p : ℕ) : ℂ) (fun t ht => hR t ⟨p, hp⟩ ht) (hW ⟨p, hp⟩),
        fockF_C_mul_right]
    rw [hre]
    simp only [hstep, ← Finset.mul_sum]
    rw [ih]
    simp only [xnC, Finset.prod_range_succ, star_add, star_sub, star_natCast]
    push_cast
    ring
end Formalism.BranchingDeterminantCap
