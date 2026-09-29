-- Prove2me | solution 1 for CerednikDrinfeld.Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fa76abeb-2346-51f7-bb1e-c23ff3767589

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn

set_option autoImplicit false

open CerednikDrinfeld.Omega
open Filter Topology

namespace PoleOrder10

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem IsHolOn.restrict {S T : Set K} (hTS : T ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K T (fun z => f ⟨z, hTS z.2⟩) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hTS hz), ⟨b, fun k z => hb k ⟨z, hTS z.2⟩⟩, ?_⟩
  exact hlim.comp (fun z : ↥T => (⟨z, hTS z.2⟩ : ↥S))

theorem coordSub_mem_holOn (T : Set K) (p r : K) (hT : ∀ z ∈ T, Valued.v (z - p) ≤ Valued.v r) :
    (fun z : ↥T => (z : K) - p) ∈ holOn K T := by
  have h := isHolOn_ratPair (S := T) ⟨Polynomial.X - Polynomial.C p, 1⟩ (fun z _ => by simp)
    ⟨r, fun z hz => by simpa [RatPair.evalAt] using hT z hz⟩
  rw [mem_holOn_iff]
  convert h using 2 with z
  simp [RatPair.evalAt]

theorem not_lt
    [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ S)
    (π : K) (hπ0 : π ≠ 0) (hπ : Valued.v π < 1)
    (F : ↥S → K) {φ φ' : ↥S → K} (hφ : φ ∈ holOn K S) (hφ' : φ' ∈ holOn K S)
    {e e' : ℕ} (he' : e' = 0 ∨ φ' p ≠ 0)
    (Z : Set ↥S) (hZ : Z.Finite)
    (h : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e * F z = φ z)
    (h' : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e' * F z = φ' z)
    (hlt : e < e') : False := by
  classical
  have hφ'p : φ' p ≠ 0 := he'.resolve_left (by omega)

  let D : Set K := {z | Valued.v (z - (p : K)) ≤ Valued.v r}
  have hDS : D ⊆ S := fun z hz => hD z hz
  have hpD : (p : K) ∈ D := by simp [D]
  let ι : ↥D → ↥S := fun z => ⟨z, hDS z.2⟩
  let g : ↥D → K := fun z => φ' (ι z) - ((z : K) - (p : K)) ^ (e' - e) * φ (ι z)
  have hg : g ∈ holOn K D := by
    have h1 : (fun z : ↥D => φ' (ι z)) ∈ holOn K D := IsHolOn.restrict hDS hφ'
    have h2 : (fun z : ↥D => φ (ι z)) ∈ holOn K D := IsHolOn.restrict hDS hφ
    have h3 : (fun z : ↥D => (z : K) - (p : K)) ∈ holOn K D := coordSub_mem_holOn D p r (fun z hz => hz)
    have : g = (fun z : ↥D => φ' (ι z)) - (fun z : ↥D => (z : K) - (p : K)) ^ (e' - e) * (fun z : ↥D => φ (ι z)) := by
      funext z; simp [g]
    rw [this]
    exact (holOn K D).sub_mem h1 ((holOn K D).mul_mem ((holOn K D).pow_mem h3 _) h2)

  have hgp : g ⟨p, hpD⟩ ≠ 0 := by
    have hd : e' - e ≠ 0 := by omega
    simp [g, ι, sub_self, zero_pow hd, hφ'p]
  obtain ⟨c, hc0, hc⟩ :=
    CerednikDrinfeld.Omega.exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn K hg ⟨p, hpD⟩ hgp

  have hg0 : ∀ z : ↥D, ι z ∉ Z → g z = 0 := by
    intro z hz
    have a := h (ι z) hz
    have a' := h' (ι z) hz
    simp only [g]
    rw [← a', ← a, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le, sub_self]

  let w : ℕ → K := fun n => (p : K) + r * π ^ n
  have hwD : ∀ n, w n ∈ D := by
    intro n
    simp only [D, Set.mem_setOf_eq, w, add_sub_cancel_left, map_mul, map_pow]
    exact mul_le_of_le_one_right' (pow_le_one' hπ.le n)
  have hvr : Valued.v r ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 hr
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 hc0
  have hv0 : (0 : Γ₀) < Valued.v π := zero_lt_iff.2 ((Valuation.ne_zero_iff Valued.v).2 hπ0)
  have hanti : StrictAnti (fun n : ℕ => Valued.v π ^ n) := pow_right_strictAnti₀ hv0 hπ
  have hw_inj : Function.Injective w := by
    intro i j hij
    apply hanti.injective
    have := congrArg (fun x => Valued.v (x - (p : K))) hij
    simp only [w, add_sub_cancel_left, map_mul, map_pow] at this
    exact mul_left_cancel₀ hvr this

  obtain ⟨n₀, hn₀⟩ := hrk π (c * π / r) hπ (by simp [hc0, hπ0, hr])
  have hsmall : ∀ n, n₀ ≤ n → Valued.v (w n - (p : K)) < Valued.v c := by
    intro n hn
    have h1 : Valued.v π ^ n ≤ Valued.v π ^ n₀ := hanti.antitone hn
    have h2 : Valued.v r * Valued.v (c * π / r) = Valued.v c * Valued.v π := by
      rw [map_div₀, map_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hvr]
    have h3 : Valued.v c * Valued.v π < Valued.v c := by
      have := mul_lt_mul_of_pos_left hπ (zero_lt_iff.2 hvc)
      simpa using this
    simp only [w, add_sub_cancel_left, map_mul, map_pow]
    calc Valued.v r * Valued.v π ^ n ≤ Valued.v r * Valued.v π ^ n₀ := mul_le_mul_right h1 _
      _ ≤ Valued.v r * Valued.v (c * π / r) := mul_le_mul_right hn₀ _
      _ = Valued.v c * Valued.v π := h2
      _ < Valued.v c := h3

  let wS : ℕ → ↥S := fun n => ⟨w n, hDS (hwD n)⟩
  have hwS_inj : Function.Injective wS := fun i j hij => hw_inj (congrArg Subtype.val hij)
  have hfin : (wS ⁻¹' Z).Finite := hZ.preimage (hwS_inj.injOn)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  let n := max n₀ (N + 1)
  have hnZ : wS n ∉ Z := by
    intro hmem
    have : n ≤ N := hN hmem
    omega
  have hz0 : g ⟨w n, hwD n⟩ = 0 := hg0 ⟨w n, hwD n⟩ hnZ
  exact hc ⟨w n, hwD n⟩ (hsmall n (le_max_left _ _)) hz0

end PoleOrder10

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ S)
    (π : K) (hπ0 : π ≠ 0) (hπ : Valued.v π < 1)
    (F : ↥S → K) {φ φ' : ↥S → K} (hφ : φ ∈ holOn K S) (hφ' : φ' ∈ holOn K S)
    {e e' : ℕ} (he : e = 0 ∨ φ p ≠ 0) (he' : e' = 0 ∨ φ' p ≠ 0)
    (Z : Set ↥S) (hZ : Z.Finite)
    (h : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e * F z = φ z)
    (h' : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e' * F z = φ' z) :
    e = e' := by
  rcases Nat.lt_trichotomy e e' with hlt | heq | hgt
  · exact (PoleOrder10.not_lt hrk p r hr hD π hπ0 hπ F hφ hφ' he' Z hZ h h' hlt).elim
  · exact heq
  · exact (PoleOrder10.not_lt hrk p r hr hD π hπ0 hπ F hφ' hφ he Z hZ h' h hgt).elim

end S_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn (solution)
