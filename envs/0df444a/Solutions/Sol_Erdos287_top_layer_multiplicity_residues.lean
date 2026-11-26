-- Prove2me | solution 1 for Erdos287.top_layer_multiplicity_residues
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:43:25.21862+00:00
-- url     : https://prove2.me/submissions/4aa5d591-b2aa-4d71-9bdc-203139979ded

import Mathlib
import Theorems.Thm_Erdos287_cofactor_translation_residues

open Finset Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem clear_weighted_inverses {K ι : Type} [Field K] [DecidableEq ι]
    (U : Finset ι) (f w : ι → K) (hn : ∀ a ∈ U, f a ≠ 0) :
    (∑ a ∈ U, w a * ∏ b ∈ U.erase a, f b) =
      (∏ b ∈ U, f b) * ∑ a ∈ U, w a / f a := by
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [← prod_erase_mul U f ha]
  field_simp [hn a ha]

private theorem sum_inv_grouped (p : ℕ) [Fact p.Prime] (T : Finset ℕ) (x : ZMod p) :
    let w (u : ZMod p) : ZMod p := (T.filter (fun d : ℕ => (d : ZMod p) = u)).card
    let U := (univ : Finset (ZMod p)).filter (fun u => w u ≠ 0)
    (∑ d ∈ T, (1 : ZMod p) / (x + (Nat.cast d : ZMod p))) = ∑ u ∈ U, w u / (x + u) := by
  classical
  intro w U
  have hw (u : ZMod p) : (∑ d ∈ T.filter (fun d : ℕ => (d : ZMod p) = u),
      (1 : ZMod p) / (x + (Nat.cast d : ZMod p))) = w u / (x + u) := by
    calc
      _ = ∑ _d ∈ T.filter (fun d : ℕ => (d : ZMod p) = u), (1 : ZMod p) / (x + u) := by
        exact sum_congr rfl (fun d hd => by rw [(mem_filter.mp hd).2])
      _ = _ := by simp [w, div_eq_mul_inv, nsmul_eq_mul]
  calc
    _ = ∑ u ∈ (univ : Finset (ZMod p)), ∑ d ∈ T.filter (fun d : ℕ => (d : ZMod p) = u),
        (1 : ZMod p) / (x + (Nat.cast d : ZMod p)) :=
      (sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _).symm
    _ = ∑ u ∈ (univ : Finset (ZMod p)), w u / (x + u) := sum_congr rfl fun u _ => hw u
    _ = _ := by
      symm
      exact sum_subset (filter_subset _ _) (fun u hu hnu => by
        have hw0 : w u = 0 := by
          by_contra h
          exact hnu (mem_filter.mpr ⟨hu, h⟩)
        simp [hw0])

/-- For the top layer, cofactor offsets with multiplicity zero modulo the
prime cancel. Root counting uses only the surviving residue classes. -/
theorem solution (p : ℕ) (hp : p.Prime) (T : Finset ℕ) :
    ∃ (U R : Finset (ZMod p)),
      (∀ u : ZMod p, u ∈ U ↔ ((T.filter (fun d : ℕ => (d : ZMod p) = u)).card : ZMod p) ≠ 0) ∧
      R.card ≤ U.card - 1 ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        (∀ n ∈ D, ¬ p ^ (e + 1) ∣ n) →
        T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
        U.Nonempty → (c : ZMod p) ∈ R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let w (u : ZMod p) : ZMod p := (T.filter (fun d : ℕ => (d : ZMod p) = u)).card
  let U := (univ : Finset (ZMod p)).filter (fun u => w u ≠ 0)
  let f (b : ZMod p) : (ZMod p)[X] := X + C b
  let P : (ZMod p)[X] := ∑ a ∈ U, C (w a) * ∏ b ∈ U.erase a, f b
  let R := P.roots.toFinset
  have hdegree : P.natDegree ≤ U.card - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro a ha
    calc
      _ ≤ (C (w a)).natDegree + (∏ b ∈ U.erase a, f b).natDegree :=
        natDegree_mul_le
      _ = _ := by
        rw [natDegree_C, zero_add, natDegree_prod_of_monic (U.erase a) f
          (fun b _ => monic_X_add_C b)]
        simp only [f, natDegree_X_add_C]
        simp [card_erase_of_mem ha]
  have heval (x : ZMod p) :
      P.eval x = ∑ a ∈ U, w a * ∏ b ∈ U.erase a, (x + b) := by
    simp [P, f, eval_finsetSum, eval_prod]
  have hP (hne : U.Nonempty) : P ≠ 0 := by
    obtain ⟨a, ha⟩ := hne
    have hsingle : P.eval (-a) = w a * ∏ b ∈ U.erase a, (-a + b) := by
      rw [heval]
      refine sum_eq_single a (fun b hb hba => ?_) (fun h => (h ha).elim)
      have hm : a ∈ U.erase b := mem_erase.mpr ⟨hba.symm, ha⟩
      rw [Finset.prod_eq_zero hm (neg_add_cancel a), mul_zero]
    have hn : w a * ∏ b ∈ U.erase a, (-a + b) ≠ 0 :=
      mul_ne_zero (mem_filter.mp ha).2 (Finset.prod_ne_zero_iff.mpr
        (fun b hb hz => by
          apply ne_of_mem_erase hb
          simpa [← add_assoc] using congrArg (fun y => a + y) hz))
    intro hz
    exact hn (hsingle.symm.trans (by simp [hz]))
  refine ⟨U, R, (fun u => by simp [U, w]),
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hdegree), ?_⟩
  intro D e c he hc hpos hsum hmax hshape hne
  let x : ZMod p := c
  have hno (d : ℕ) (hd : d ∈ T) : x + (d : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ c + d := (ZMod.natCast_eq_zero_iff _ p).mp
      (by simpa only [Nat.cast_add] using hz)
    have hh : (c + d) * p ^ e ∈ D.filter (fun n => p ^ e ∣ n) :=
      hshape ▸ mem_image.mpr ⟨d, hd, rfl⟩
    apply hmax _ (mem_filter.mp hh).1
    rw [pow_succ']
    exact mul_dvd_mul hdvd (dvd_refl _)
  have hUunit (u : ZMod p) (hu : u ∈ U) : x + u ≠ 0 := by
    have hw0 : w u ≠ 0 := (mem_filter.mp hu).2
    have hcard : (T.filter (fun d : ℕ => (d : ZMod p) = u)).card ≠ 0 :=
      fun h => hw0 (by simp [w, h])
    obtain ⟨d, hd⟩ := card_ne_zero.mp hcard
    obtain ⟨hdT, heq⟩ := mem_filter.mp hd
    exact heq ▸ hno d hdT
  have hz := (Erdos287.cofactor_translation_residues p hp).1 D T e c he hc hpos hsum hshape
  change (∑ a ∈ T, ∏ b ∈ T.erase a, (x + (Nat.cast b : ZMod p))) = 0 at hz
  have hclear := clear_weighted_inverses T (fun d => x + (d : ZMod p)) (fun _ => 1) hno
  simp only [one_mul] at hclear
  have hsum0 : (∑ d ∈ T, (1 : ZMod p) / (x + (Nat.cast d : ZMod p))) = 0 :=
    (mul_eq_zero.mp (hclear.symm.trans hz)).resolve_left
      (Finset.prod_ne_zero_iff.mpr hno)
  have hgrp : (∑ u ∈ U, w u / (x + u)) = 0 :=
    (sum_inv_grouped p T x).symm.trans hsum0
  have hX : P.eval x = 0 := by
    rw [heval, clear_weighted_inverses U (fun u => x + u) w hUunit, hgrp, mul_zero]
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hP hne)).mpr hX)

