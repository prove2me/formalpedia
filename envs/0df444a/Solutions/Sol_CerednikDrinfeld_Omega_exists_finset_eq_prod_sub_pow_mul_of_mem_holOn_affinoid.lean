-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/741db6cf-29fa-5089-b82a-de2648f11ade

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : ∃ z : ↥(affinoid ϖ n), f z ≠ 0) :
    ∃ (Z : Finset ↥(affinoid ϖ n)) (k : ↥(affinoid ϖ n) → ℕ) (u : ↥(affinoid ϖ n) → K),
      u ∈ holOn K (affinoid ϖ n) ∧ (∀ z : ↥(affinoid ϖ n), u z ≠ 0) ∧
      (∀ p : ↥(affinoid ϖ n), p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥(affinoid ϖ n), f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by
  classical

  suffices key : ∀ (m : ℕ) (f : ↥(affinoid ϖ n) → K), f ∈ holOn K (affinoid ϖ n) → (∃ z, f z ≠ 0) →
      ∀ hZ : Set.Finite {z : ↥(affinoid ϖ n) | f z = 0}, hZ.toFinset.card ≤ m →
      ∃ (Z : Finset ↥(affinoid ϖ n)) (k : ↥(affinoid ϖ n) → ℕ) (u : ↥(affinoid ϖ n) → K),
        u ∈ holOn K (affinoid ϖ n) ∧ (∀ z : ↥(affinoid ϖ n), u z ≠ 0) ∧
        (∀ p : ↥(affinoid ϖ n), p ∈ Z ↔ 1 ≤ k p) ∧
        ∀ z : ↥(affinoid ϖ n), f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z by
    have hne' : f ≠ 0 := by obtain ⟨z, hz⟩ := hne; exact fun h0 => hz (by rw [h0]; rfl)
    have hZ := CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid K₀ K ϖ hrk n hfin hf hne'
    exact key _ f hf hne hZ le_rfl
  intro m
  induction m with
  | zero =>
    intro f hf hne hZ hcard
    have hempty : ∀ z : ↥(affinoid ϖ n), f z ≠ 0 := by
      intro z hz
      have : z ∈ hZ.toFinset := hZ.mem_toFinset.2 hz
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at this
      exact absurd this (Finset.notMem_empty _)
    exact ⟨∅, fun _ => 0, f, hf, hempty, fun p => by simp, fun z => by simp⟩
  | succ m ih =>
    intro f hf hne hZ hcard
    by_cases hex0 : ∃ p : ↥(affinoid ϖ n), f p = 0
    swap
    · push Not at hex0
      exact ⟨∅, fun _ => 0, f, hf, hex0, fun p => by simp, fun z => by simp⟩
    obtain ⟨p, hp⟩ := hex0
    obtain ⟨k, g, hg, hgp, hfg⟩ :=
      CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid K₀ K ϖ hrk n hfin hf hne p
    have hk : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [hfg p, this, pow_zero, one_mul] at hp
      exact hgp hp
    have hgne : ∃ z, g z ≠ 0 := ⟨p, hgp⟩

    have hzero : ∀ z : ↥(affinoid ϖ n), g z = 0 ↔ (f z = 0 ∧ z ≠ p) := by
      intro z
      constructor
      · intro h0
        refine ⟨by rw [hfg z, h0, mul_zero], fun hzp => hgp (by rwa [hzp] at h0)⟩
      · rintro ⟨h0, hzp⟩
        rw [hfg z] at h0
        rcases mul_eq_zero.1 h0 with h1 | h1
        · exact absurd (pow_eq_zero_iff (by omega) |>.1 h1) (sub_ne_zero.2 fun h => hzp (Subtype.ext h))
        · exact h1
    have hZg : Set.Finite {z : ↥(affinoid ϖ n) | g z = 0} :=
      hZ.subset fun z hz => ((hzero z).1 hz).1
    have hcardg : hZg.toFinset.card ≤ m := by
      have hsub : hZg.toFinset ⊆ hZ.toFinset.erase p := by
        intro z hz
        rw [Finset.mem_erase, Set.Finite.mem_toFinset]
        have := (hzero z).1 (hZg.mem_toFinset.1 hz)
        exact ⟨this.2, this.1⟩
      have hpZ : p ∈ hZ.toFinset := hZ.mem_toFinset.2 hp
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hpZ] at this
      omega
    obtain ⟨Z', k', u', hu', hu'0, hk', hgeq⟩ := ih g hg hgne hZg hcardg
    have hpZ' : p ∉ Z' := by
      intro hpZ'
      have h1 : 1 ≤ k' p := (hk' p).1 hpZ'
      apply hgp
      rw [hgeq p]
      have : (∏ q ∈ Z', ((p : K) - (q : K)) ^ k' q) = 0 :=
        Finset.prod_eq_zero hpZ' (by rw [sub_self, zero_pow (by omega)])
      rw [this, zero_mul]
    refine ⟨insert p Z', fun q => if q = p then k else k' q, u', hu', hu'0, fun q => ?_, fun z => ?_⟩
    · show q ∈ insert p Z' ↔ 1 ≤ (if q = p then k else k' q)
      by_cases hq : q = p
      · subst hq; simp [hk]
      · rw [Finset.mem_insert, if_neg hq]; simp [hq, hk' q]
    · show f z = (∏ x ∈ insert p Z', ((z : K) - (x : K)) ^ (if x = p then k else k' x)) * u' z
      rw [hfg z, hgeq z, Finset.prod_insert hpZ', if_pos rfl, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqp : q ≠ p := fun h => hpZ' (by rw [← h]; exact hq)
      rw [if_neg hqp]

end S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid (solution)
