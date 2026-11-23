-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.256982+00:00
-- url     : https://prove2.me/submissions/7b95d381-8b51-4746-ae36-1a3080109def

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnSg_mul_self
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnSg_star
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_sum
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_perm
import Theorems.Thm_Formalism_BranchingDeterminantCap_fock_pairing_initial_minor
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
private lemma fockF_C_mul_right (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF F (C c * G) = star c * fockF F G := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, star_mul']
  ring
private lemma fockF_eq_sum_coeff_factorial_of_support_subset (F G : MvPolynomial (Fin r × Fin n) ℂ)
    (S : Finset ((Fin r × Fin n) →₀ ℕ)) (hS : F.support ⊆ S) :
    fockF F G = ∑ m ∈ S, F.coeff m * star (G.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]
private lemma fockF_sum_left' {ι' : Type*} (s : Finset ι') (F : ι' → MvPolynomial (Fin r × Fin n) ℂ)
    (G : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (∑ i ∈ s, F i) G = ∑ i ∈ s, fockF (F i) G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (∑ i ∈ s, F i) G _ MvPolynomial.support_sum]
  rw [Finset.sum_congr rfl fun i hi => fockF_eq_sum_coeff_factorial_of_support_subset (F i) G (s.biUnion fun i => (F i).support)
    (Finset.subset_biUnion_of_mem (fun i => (F i).support) hi)]
  simp only [MvPolynomial.coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
private lemma fockF_C_mul_left (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF (C c * F) G = c * fockF F G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (C c * F) G F.support ?_]
  · unfold fockF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_C_mul]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    exact MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hm)
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
    (p : ℕ) (hp : p ≤ n) :
    ∑ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      (p.factorial : ℂ) * (((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF f f) := by
  have hT := fock_pairing_initial_minor ι hι m f hR hW p hp f
  have hterm : ∀ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      ∑ π : Equiv.Perm (Fin p),
        fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
    intro a
    have e := xn_minor_sum ι hp a
    calc fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f)
        = fockF ((∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π)) * f)
            (initMinor ℂ (ι ∘ a) hp * f) := by rw [← e]
      _ = ∑ π : Equiv.Perm (Fin p),
            xnSg π * fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ a) hp * f) := by
          rw [Finset.sum_mul, fockF_sum_left']
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [mul_assoc, fockF_C_mul_left]
      _ = ∑ π : Equiv.Perm (Fin p),
            fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          have e2 : initMinor ℂ (ι ∘ a) hp = C (xnSg π) * initMinor ℂ (ι ∘ (a ∘ π)) hp := by
            rw [xn_minor_perm ι hp a π, ← mul_assoc, ← map_mul, xnSg_mul_self, map_one, one_mul]
          rw [e2, mul_assoc, fockF_C_mul_right, xnSg_star, ← mul_assoc, xnSg_mul_self, one_mul]
  have hperm : ∀ π : Equiv.Perm (Fin p),
      ∑ a : Fin p → κ, fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) =
        ∑ a : Fin p → κ, fockF (xnMono ι hp a * f) (initMinor ℂ (ι ∘ a) hp * f) := by
    intro π
    exact Fintype.sum_bijective (fun a : Fin p → κ => a ∘ π)
      ⟨fun x y h => by
        funext i
        simpa using congrFun h (π.symm i),
       fun b => ⟨b ∘ π.symm, by funext i; simp⟩⟩ _ _ fun a => rfl
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm,
    Finset.sum_congr rfl fun π _ => hperm π, hT, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
end Formalism.BranchingDeterminantCap
