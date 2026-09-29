-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ae702ecd-8a93-5a93-8c08-a43c33664b7f

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

namespace FactorSetAux

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]

theorem aux
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} (n : ℕ) :
    ∀ (f : ↥S → K), f ∈ holOn K S → ∀ (hfin : Set.Finite {z : ↥S | f z = 0}), hfin.toFinset.card ≤ n →
      (∀ z : ↥S, f z = 0 → ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - (z : K)) ≤ Valued.v r → w ∈ S) →
      ∃ (Z : Finset ↥S) (k : ↥S → ℕ) (u : ↥S → K),
        u ∈ holOn K S ∧ (∀ z : ↥S, u z ≠ 0) ∧
        (∀ p : ↥S, p ∈ Z ↔ 1 ≤ k p) ∧
        ∀ z : ↥S, f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by
  classical
  induction n with
  | zero =>
    intro f hf hfin hcard hdisc
    refine ⟨∅, fun _ => 0, f, hf, fun z hz => ?_, fun p => by simp, fun z => by simp⟩
    have : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr hz
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
    simp at this
  | succ n ih =>
    intro f hf hfin hcard hdisc
    by_cases hno : ∀ z : ↥S, f z ≠ 0
    · exact ⟨∅, fun _ => 0, f, hf, hno, fun p => by simp, fun z => by simp⟩
    push_neg at hno
    obtain ⟨p, hp⟩ := hno
    obtain ⟨r, hr, hD⟩ := hdisc p hp
    obtain ⟨k₀, g, hg, hgp, hfg⟩ :=
      CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero K hrk hf hfin p r hr hD
    have hk₀ : 1 ≤ k₀ := by
      by_contra h
      push_neg at h
      have : k₀ = 0 := by omega
      rw [hfg p, this, pow_zero, one_mul] at hp
      exact hgp hp

    have hgz : ∀ z : ↥S, g z = 0 → f z = 0 := fun z hz => by rw [hfg z, hz, mul_zero]
    have hfin' : Set.Finite {z : ↥S | g z = 0} := hfin.subset (fun z hz => hgz z hz)
    have hcard' : hfin'.toFinset.card ≤ n := by
      have hsub : hfin'.toFinset ⊆ hfin.toFinset.erase p := by
        intro z hz
        rw [Finset.mem_erase, Set.Finite.mem_toFinset]
        rw [Set.Finite.mem_toFinset] at hz
        exact ⟨fun h => hgp (h ▸ hz), hgz z hz⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (hfin.mem_toFinset.mpr hp)] at this
      omega
    obtain ⟨Z', k', u, hu, hu0, hZ', hgprod⟩ := ih g hg hfin' hcard' (fun z hz => hdisc z (hgz z hz))

    have hpZ' : p ∉ Z' := by
      intro hpZ
      apply hgp
      rw [hgprod p, ← Finset.mul_prod_erase _ _ hpZ, sub_self, zero_pow (by have := (hZ' p).mp hpZ; omega)]
      simp
    have hk'p : k' p = 0 := by
      have := (hZ' p).not.mp hpZ'
      omega
    refine ⟨insert p Z', fun z => k' z + (if z = p then k₀ else 0), u, hu, hu0, fun q => ?_, fun z => ?_⟩
    · rw [Finset.mem_insert]
      by_cases hq : q = p
      · subst hq; simp [hk'p, hk₀]
      · simp only [hq, if_false, add_zero, false_or]
        exact hZ' q
    · rw [Finset.prod_insert hpZ', hfg z, hgprod z]
      simp only [if_true, hk'p, zero_add]
      rw [mul_assoc]
      congr 1
      congr 1
      refine Finset.prod_congr rfl fun q hq => ?_
      have : q ≠ p := fun h => hpZ' (h ▸ hq)
      simp [this]

end FactorSetAux

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})

    (hdisc : ∀ z : ↥S, f z = 0 → ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - (z : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (Z : Finset ↥S) (k : ↥S → ℕ) (u : ↥S → K),
      u ∈ holOn K S ∧ (∀ z : ↥S, u z ≠ 0) ∧
      (∀ p : ↥S, p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥S, f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by
  classical
  exact FactorSetAux.aux hrk _ f hf hfin le_rfl hdisc

end S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero (solution)
