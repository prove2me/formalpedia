-- Prove2me | solution 1 for BraidsLinksMCG.artin_hurwitz_norm_reduction
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T00:13:11.698683+00:00
-- url     : https://prove2.me/submissions/c286946f-9c73-4067-99b4-6b30103e6e8f

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_hurwitz_local_cancellation

/-!
`artin_hurwitz_norm_reduction` from the free-group cancellation statement: the braid
generator `σ_k^{±1}` realises the Hurwitz move at the adjacent pair `(k, k+1)`.
-/

namespace HurwitzStep

open BraidsLinksMCG

private lemma sum_pair_split {n : ℕ} (f : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b) :
    ∑ i : Fin n, f i = f a + f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
  have h1 : ∑ i : Fin n, f i = f a + ∑ i ∈ Finset.univ.erase a, f i :=
    (Finset.add_sum_erase _ f (Finset.mem_univ a)).symm
  have h2 : ∑ i ∈ Finset.univ.erase a, f i
      = f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i :=
    (Finset.add_sum_erase _ f (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)).symm
  rw [h1, h2, add_assoc]

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)) :
    ∃ c : ArtinBraidGroup n,
      (∑ i : Fin n, FreeGroup.norm (beta (xi c (FreeGroup.of i))))
        < ∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)) := by
  obtain ⟨mu, A, hA⟩ := hconj
  have hprod : (List.ofFn fun i : Fin n => beta (FreeGroup.of i)).prod = freeWordProd n := by
    rw [← hword]
    conv_rhs => rw [freeWordProd]
    rw [map_list_prod, List.map_ofFn]
    rfl
  obtain ⟨a, b, hb, hcase⟩ :=
    hurwitz_local_cancellation n (fun i => beta (FreeGroup.of i)) mu A hA hprod hnotperm
  have hab : a ≠ b := by intro h; rw [h] at hb; omega
  have hk : (a : ℕ) < n - 1 := by have := b.isLt; omega
  set k : Fin (n - 1) := ⟨(a : ℕ), hk⟩ with hkdef
  have ha : strandIdx k = a := Fin.eq_of_val_eq rfl
  have hbk : strandIdxSucc k = b := Fin.eq_of_val_eq hb.symm
  -- the action of `σ_k` on the three kinds of generator
  have hEa : xi (sigma k) (FreeGroup.of a)
      = FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ := by
    rw [hxi k]
    simp [artinEndo, FreeGroup.lift_apply_of, ha, hbk]
  have hEb : xi (sigma k) (FreeGroup.of b) = FreeGroup.of a := by
    rw [hxi k]
    simp [artinEndo, FreeGroup.lift_apply_of, ha, hbk, Ne.symm hab]
  have hEi : ∀ i : Fin n, i ≠ a → i ≠ b →
      xi (sigma k) (FreeGroup.of i) = FreeGroup.of i := by
    intro i hia hib
    rw [hxi k]
    simp [artinEndo, FreeGroup.lift_apply_of, ha, hbk, hia, hib]
  have hmem : ∀ i ∈ (Finset.univ.erase a).erase b, i ≠ a ∧ i ≠ b := by
    intro i hi
    exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1, (Finset.mem_erase.1 hi).1⟩
  rcases hcase with hlt | hlt
  · refine ⟨sigma k, ?_⟩
    rw [sum_pair_split (fun i => FreeGroup.norm (beta (xi (sigma k) (FreeGroup.of i)))) a b hab,
      sum_pair_split (fun i => FreeGroup.norm (beta (FreeGroup.of i))) a b hab]
    have hrest : (∑ i ∈ (Finset.univ.erase a).erase b,
          FreeGroup.norm (beta (xi (sigma k) (FreeGroup.of i))))
        = ∑ i ∈ (Finset.univ.erase a).erase b, FreeGroup.norm (beta (FreeGroup.of i)) :=
      Finset.sum_congr rfl fun i hi => by rw [hEi i (hmem i hi).1 (hmem i hi).2]
    rw [hrest, hEa, hEb, map_mul, map_mul, map_inv]
    omega
  · refine ⟨(sigma k)⁻¹, ?_⟩
    have hIa : xi ((sigma k)⁻¹) (FreeGroup.of a) = FreeGroup.of b := by
      rw [map_inv]
      show (xi (sigma k)).symm (FreeGroup.of a) = FreeGroup.of b
      rw [MulEquiv.symm_apply_eq, hEb]
    have hIb : xi ((sigma k)⁻¹) (FreeGroup.of b)
        = (FreeGroup.of b)⁻¹ * FreeGroup.of a * FreeGroup.of b := by
      rw [map_inv]
      show (xi (sigma k)).symm (FreeGroup.of b) = _
      rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, hEa, hEb]
      group
    have hIi : ∀ i : Fin n, i ≠ a → i ≠ b →
        xi ((sigma k)⁻¹) (FreeGroup.of i) = FreeGroup.of i := by
      intro i hia hib
      rw [map_inv]
      show (xi (sigma k)).symm (FreeGroup.of i) = _
      rw [MulEquiv.symm_apply_eq, hEi i hia hib]
    rw [sum_pair_split
        (fun i => FreeGroup.norm (beta (xi ((sigma k)⁻¹) (FreeGroup.of i)))) a b hab,
      sum_pair_split (fun i => FreeGroup.norm (beta (FreeGroup.of i))) a b hab]
    have hrest : (∑ i ∈ (Finset.univ.erase a).erase b,
          FreeGroup.norm (beta (xi ((sigma k)⁻¹) (FreeGroup.of i))))
        = ∑ i ∈ (Finset.univ.erase a).erase b, FreeGroup.norm (beta (FreeGroup.of i)) :=
      Finset.sum_congr rfl fun i hi => by rw [hIi i (hmem i hi).1 (hmem i hi).2]
    rw [hrest, hIa, hIb, map_mul, map_mul, map_inv]
    omega

end HurwitzStep

#print axioms solution
