-- Prove2me | solution 1 for ErschlerZheng.ncard_wSet_and_ncard_vSet_and_getLast_eq_false
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T04:20:40.316643+00:00
-- url     : https://prove2.me/submissions/b6065e8c-346b-488a-af52-c5d0c51ef537

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

section
/-!
# The index sets `W^n_k` and `V^j_k` (Erschler–Zheng p. 37)

`|W^n_k| = 2^{k/D}` for `D ∣ n`, `D ∣ k`; `|V^j_k| = 2^{k/D}` and every `v ∈ V^j_k` ends with `0`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrW

theorem frM_spec (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (ℓ : ℕ) :
    frM D ω ℓ + 3 ≤ D ∧ ω (ℓ * D + frM D ω ℓ) = 2 ∧ ω (ℓ * D + frM D ω ℓ + 2) = 1 ∧
      (ω (ℓ * D + frM D ω ℓ + 1) = 0 ∨ ω (ℓ * D + frM D ω ℓ + 1) = 1) := by
  have hne : {m | m + 3 ≤ D ∧ ω (ℓ * D + m) = 2 ∧ ω (ℓ * D + m + 2) = 1 ∧
      (ω (ℓ * D + m + 1) = 0 ∨ ω (ℓ * D + m + 1) = 1)}.Nonempty := hω ℓ
  exact Nat.sInf_mem hne

/-- The positions `i < q D` with `p D + (i + 1) ∈ I_ω` are `ℓ D + m_{p+ℓ} + 2`, `ℓ < q`. -/
theorem mem_frI_iff (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (p q i : ℕ)
    (hi : i < q * D) :
    p * D + (i + 1) ∈ frI D ω ↔ ∃ ℓ < q, i = ℓ * D + frM D ω (p + ℓ) + 2 := by
  constructor
  · rintro ⟨ℓ', hℓ'⟩
    have h1 := (frM_spec D ω hω ℓ').1
    -- ℓ' ≥ p
    have hp : p ≤ ℓ' := by
      by_contra hlt
      push Not at hlt
      have : (ℓ' + 1) * D ≤ p * D := Nat.mul_le_mul_right D hlt
      have : (ℓ' + 1) * D = ℓ' * D + D := by ring
      omega
    have hq : ℓ' < p + q := by
      by_contra hge
      push Not at hge
      have : (p + q) * D ≤ ℓ' * D := Nat.mul_le_mul_right D hge
      have : (p + q) * D = p * D + q * D := by ring
      omega
    refine ⟨ℓ' - p, by omega, ?_⟩
    have e : p + (ℓ' - p) = ℓ' := by omega
    rw [e]
    have : ℓ' * D = p * D + (ℓ' - p) * D := by
      rw [← Nat.add_mul, e]
    omega
  · rintro ⟨ℓ, hℓ, rfl⟩
    refine ⟨p + ℓ, ?_⟩
    have : (p + ℓ) * D = p * D + ℓ * D := by ring
    omega

/-- The set of free positions of `W^{pD}_{qD}`. -/
def freePos (D : ℕ) (ω : ℕ → Fin 3) (n k : ℕ) : Set ℕ := {i | i < k ∧ n + (i + 1) ∈ frI D ω}

theorem ncard_freePos (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (p q : ℕ) :
    (freePos D ω (p * D) (q * D)).ncard = q := by
  have hD : 3 ≤ D := by have := (frM_spec D ω hω 0).1; omega
  have key : freePos D ω (p * D) (q * D) =
      (fun ℓ => ℓ * D + frM D ω (p + ℓ) + 2) '' Set.Iio q := by
    ext i
    simp only [freePos, Set.mem_setOf_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hi, hmem⟩
      obtain ⟨ℓ, hℓ, rfl⟩ := (mem_frI_iff D ω hω p q i hi).1 hmem
      exact ⟨ℓ, hℓ, rfl⟩
    · rintro ⟨ℓ, hℓ, rfl⟩
      have h1 := (frM_spec D ω hω (p + ℓ)).1
      have hlt : ℓ * D + frM D ω (p + ℓ) + 2 < q * D := by
        have : (ℓ + 1) * D ≤ q * D := Nat.mul_le_mul_right D hℓ
        have : (ℓ + 1) * D = ℓ * D + D := by ring
        omega
      exact ⟨hlt, (mem_frI_iff D ω hω p q _ hlt).2 ⟨ℓ, hℓ, rfl⟩⟩
  rw [key, Set.InjOn.ncard_image]
  · rw [show Set.Iio q = ((Finset.range q : Finset ℕ) : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  · intro ℓ1 _ ℓ2 _ h
    simp only at h
    have h1 := (frM_spec D ω hω (p + ℓ1)).1
    have h2 := (frM_spec D ω hω (p + ℓ2)).1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (ℓ1 + 1) * D ≤ ℓ2 * D := Nat.mul_le_mul_right D hlt
      have : (ℓ1 + 1) * D = ℓ1 * D + D := by ring
      omega
    · have : (ℓ2 + 1) * D ≤ ℓ1 * D := Nat.mul_le_mul_right D hlt
      have : (ℓ2 + 1) * D = ℓ2 * D + D := by ring
      omega

open Classical in
/-- `W^n_k` is in bijection with the functions on its free positions. -/
noncomputable def wSetEquiv (D : ℕ) (ω : ℕ → Fin 3) (n k : ℕ) :
    wSet D ω n k ≃ (freePos D ω n k → Bool) where
  toFun u := fun i => u.1.getD i.1 true
  invFun t := ⟨List.ofFn (fun i : Fin k => if h : i.1 ∈ freePos D ω n k then t ⟨i.1, h⟩ else true),
    by simp, fun i hi hnot => by
      simp only [List.getElem_ofFn]
      rw [dif_neg]
      rintro ⟨_, h2⟩
      exact hnot h2⟩
  left_inv u := by
    obtain ⟨u, hlen, hu⟩ := u
    apply Subtype.ext
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      split_ifs with h
      · rw [List.getD_eq_getElem _ _ h2]
      · have hi : i < k := by simpa using h1
        symm
        apply hu i h2
        intro hm
        exact h ⟨hi, hm⟩
  right_inv t := by
    funext ⟨i, hi⟩
    show (List.ofFn _).getD i true = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi.1)]
    simp only [List.getElem_ofFn]
    rw [dif_pos hi]

theorem ncard_wSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (n k : ℕ) (hn : D ∣ n)
    (hk : D ∣ k) : (wSet D ω n k).ncard = 2 ^ (k / D) := by
  have hD : 0 < D := by have := (frM_spec D ω hω 0).1; omega
  obtain ⟨p, rfl⟩ := hn
  obtain ⟨q, rfl⟩ := hk
  have hfin : (freePos D ω (D * p) (D * q)).Finite :=
    (Set.finite_lt_nat (D * q)).subset fun i hi => hi.1
  have := hfin.to_subtype
  rw [Set.ncard_def, Set.encard, ENat.card_congr (wSetEquiv D ω (D * p) (D * q))]
  rw [ENat.card_eq_coe_natCard, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool]
  · have h := ncard_freePos D ω hω p q
    rw [mul_comm p D, mul_comm q D] at h
    simp only [ENat.toNat_natCast]
    rw [Nat.card_coe_set_eq, h, Nat.mul_div_cancel_left _ hD]

end ConstrW

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrW
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) :
    (∀ n k, D ∣ n → D ∣ k → (wSet D ω n k).ncard = 2 ^ (k / D)) ∧
    ∀ j k, D ∣ k →
      (vSet D ω j k).ncard = 2 ^ (k / D) ∧ ∀ v ∈ vSet D ω j k, v.getLast? = some false := by
  have hD : 0 < D := by have := (frM_spec D ω hω 0).1; omega
  refine ⟨fun n k hn hk => ncard_wSet D ω hω n k hn hk, fun j k hk => ⟨?_, ?_⟩⟩
  · have hdiv : D ∣ j + D - j % D := by
      have h1 : j + D - j % D = D * (j / D) + D := by
        have := Nat.div_add_mod j D
        omega
      rw [h1]
      exact Dvd.dvd.add (Dvd.intro _ rfl) (dvd_refl D)
    have himg : vSet D ω j k = (fun u => List.replicate (D - j % D) true ++ u ++
        List.replicate (frM D ω (ellIndex D k j) + 2) true ++ [false]) ''
          wSet D ω (j + D - j % D) k := by
      ext v
      simp only [vSet, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    rw [himg, Set.ncard_image_of_injective]
    · exact ncard_wSet D ω hω _ k hdiv hk
    · intro u1 u2 h
      simp only [List.append_assoc, List.append_cancel_left_eq] at h
      have hl : (u1 ++ (List.replicate (frM D ω (ellIndex D k j) + 2) true ++ [false])).length =
          (u2 ++ (List.replicate (frM D ω (ellIndex D k j) + 2) true ++ [false])).length := by
        rw [h]
      simp only [List.length_append] at hl
      exact List.append_inj_left h (by omega)
  · rintro v ⟨u, _, rfl⟩
    simp
end
