-- Prove2me | solution 1 for Erdos338Proof.nsmul_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:45.362134+00:00
-- url     : https://prove2.me/submissions/f05ad991-ae09-42e2-b7c2-a1965fd56e5c

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering
public import Theorems.Thm_Erdos338Proof_kneser_nsmul

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace Erdos338Proof
theorem _root_.solution [Fintype G] {s : Finset G} (h0 : (0 : G) ∈ s)
    (hgen : AddSubgroup.closure (s : Set G) = ⊤) {h : ℕ} (hh : 1 ≤ h)
    (hcard : 2 * Fintype.card G ≤ h * #s) : h • s = univ := by
  by_contra hne
  have hs : s.Nonempty := ⟨0, h0⟩
  set T := h • s with hTdef
  have hT : T.Nonempty := hs.nsmul
  set H := T.addStab with hHdef
  have hH0 : (0 : G) ∈ H := hT.zero_mem_addStab
  have hHstab : (H : Set G) = AddAction.stabilizer G (T : Set G) := coe_addStab hT
  have mem_H : ∀ {k : G}, k ∈ H ↔ k ∈ AddAction.stabilizer G (T : Set G) := by
    intro k; rw [← Finset.mem_coe, hHstab, SetLike.mem_coe]
  -- `T` is a union of `H`-cosets that misses a coset, so `|T| + |H| ≤ |G|`
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hall
    exact hne (eq_univ_of_forall fun x ↦ by by_contra hx; exact hall ⟨x, hx⟩)
  have hdisj : Disjoint T (y +ᵥ H) := by
    rw [Finset.disjoint_left]
    intro z hzT hzH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.1 hzH
    have hnk : -k ∈ AddAction.stabilizer G (T : Set G) := neg_mem (mem_H.1 hk)
    have : -k +ᵥ (y +ᵥ k) ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hnk]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 hzT)
    apply hy
    have e : -k +ᵥ (y +ᵥ k) = y := by simp [vadd_eq_add]
    rw [e] at this
    exact Finset.mem_coe.1 this
  have hTH : #T + #H ≤ Fintype.card G := by
    rw [← card_vadd_finset y H, ← card_union_of_disjoint hdisj]
    exact card_le_univ _
  -- `s + H` is a union of at least two `H`-cosets
  have hsub : s ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨x, hx, 0, hH0, add_zero x⟩
  have hHsub : H ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨0, h0, x, hx, zero_add x⟩
  have hdvd : #H ∣ #(s + H) := card_addStab_dvd_card_add_addStab s T
  have hHpos : 0 < #H := card_pos.2 ⟨0, hH0⟩
  have hne2 : #(s + H) ≠ #H := by
    intro heq
    have hsH : s + H = H := (eq_of_subset_of_card_le hHsub heq.le).symm
    have hsH' : (s : Set G) ⊆ AddAction.stabilizer G (T : Set G) := by
      intro x hx
      exact mem_H.1 (hsH ▸ hsub (Finset.mem_coe.1 hx))
    have htop : AddAction.stabilizer G (T : Set G) = ⊤ :=
      eq_top_iff.2 (hgen ▸ (AddSubgroup.closure_le _).2 hsH')
    apply hne
    apply eq_univ_of_forall
    intro g
    obtain ⟨t, ht⟩ := hT
    have hg : g - t ∈ AddAction.stabilizer G (T : Set G) := htop ▸ AddSubgroup.mem_top _
    have : (g - t) +ᵥ t ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hg]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 ht)
    simpa [vadd_eq_add] using this
  have h2H : 2 * #H ≤ #(s + H) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c ≠ 1 := by rintro rfl; exact hne2 (by rw [hc, mul_one])
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hne' : (s + H).Nonempty := hs.add ⟨0, hH0⟩
      rw [mul_zero, card_eq_zero] at hc
      exact hne'.ne_empty hc
    rw [hc]
    have : 2 ≤ c := by omega
    nlinarith
  have hsle : #s ≤ #(s + H) := card_le_card hsub
  have hK := kneser_nsmul hh s hs
  rw [← hTdef, ← hHdef] at hK
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hK
  have h3 : k * (2 * #H) ≤ k * #(s + H) := Nat.mul_le_mul_left k h2H
  have h4 : (k + 1) * #s ≤ (k + 1) * #(s + H) := Nat.mul_le_mul_left _ hsle
  nlinarith
end Erdos338Proof
