-- Prove2me | solution 1 for Erdos338Proof.kneser_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:14.906882+00:00
-- url     : https://prove2.me/submissions/dad940b1-b8e3-482b-8851-3ffd1f53ab9c

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering
public import Theorems.Thm_Erdos338Proof_nsmul_add_stab
public import Theorems.Thm_Finset_mul_kneser


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace Erdos338Proof
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) :
    ∀ s : Finset G, s.Nonempty →
      h * #(s + (h • s).addStab) ≤ #(h • s) + (h - 1) * #(h • s).addStab := by
  induction h, hh using Nat.le_induction with
  | base =>
    intro s _
    simp [add_addStab]
  | succ n hn ih =>
    intro s hs
    set H := ((n + 1) • s).addStab with hHdef
    have hns : (n • s).Nonempty := hs.nsmul
    have hn1 : ((n + 1) • s).Nonempty := hs.nsmul
    have hHH : H + H = H := addStab_add_addStab _
    have hsH : (s + H).Nonempty := hs.add hn1.addStab
    -- the stabilizer of `n • (s + H) = n • s + H` is `H`
    have hnsH : n • (s + H) = n • s + H := nsmul_add_stab s H hHH hn
    have hstab : (n • (s + H)).addStab = H := by
      rw [hnsH]
      apply le_antisymm
      · calc (n • s + H).addStab ⊆ (n • s + H + s).addStab := subset_addStab_add_left hs
          _ = ((n + 1) • s + H).addStab := by rw [succ_nsmul]; congr 1; abel
          _ = H := by rw [add_addStab]
      · calc H = H.addStab := (addStab_idem _).symm
          _ ⊆ (n • s + H).addStab := subset_addStab_add_right hns
    have key := ih (s + H) hsH
    rw [hstab, hnsH, add_assoc, hHH] at key
    -- Kneser for `n • s` and `s` (via `Finset.mul_kneser` on `Multiplicative G`)
    have hk : #(n • s + (n • s + s).addStab) + #(s + (n • s + s).addStab) ≤
        #(n • s + s) + #(n • s + s).addStab := by
      let f : Finset G → Finset (Multiplicative G) :=
        Finset.map Multiplicative.ofAdd.toEmbedding
      have hf_inj : Function.Injective f := Finset.map_injective _
      have hf_add : ∀ A B : Finset G, f (A + B) = f A * f B := by
        intro A B
        ext z
        obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective z
        simp only [f, Finset.mem_map, Finset.mem_add, Finset.mem_mul, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, hw⟩
          exact ⟨Multiplicative.ofAdd a, ⟨a, ha, rfl⟩, Multiplicative.ofAdd b, ⟨b, hb, rfl⟩, hw⟩
        · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hw⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, hw⟩
      have hf_sub : ∀ A B : Finset G, f (A - B) = f A / f B := by
        intro A B
        ext z
        obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective z
        simp only [f, Finset.mem_map, Finset.mem_sub, Finset.mem_div, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, hw⟩
          exact ⟨Multiplicative.ofAdd a, ⟨a, ha, rfl⟩, Multiplicative.ofAdd b, ⟨b, hb, rfl⟩, hw⟩
        · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hw⟩
          exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, hw⟩
      have hf_vadd : ∀ (a : G) (A : Finset G), Multiplicative.ofAdd a • f A = f (a +ᵥ A) := by
        intro a A
        ext z
        obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective z
        simp only [f, Finset.mem_smul_finset, Finset.mem_map, Finset.mem_vadd_finset,
          Equiv.toEmbedding_apply, smul_eq_mul, vadd_eq_add]
        constructor
        · rintro ⟨_, ⟨b, hb, rfl⟩, hw⟩
          exact ⟨a + b, ⟨b, hb, rfl⟩, hw⟩
        · rintro ⟨_, ⟨b, hb, rfl⟩, hw⟩
          exact ⟨Multiplicative.ofAdd b, ⟨b, hb, rfl⟩, hw⟩
      have hf_mem : ∀ (x : G) (B : Finset G), Multiplicative.ofAdd x ∈ f B ↔ x ∈ B := by
        intro x B
        simp only [f, Finset.mem_map, Equiv.toEmbedding_apply,
          Multiplicative.ofAdd.injective.eq_iff, exists_eq_right]
      have hf_stab : ∀ A : Finset G, f A.addStab = (f A).mulStab := by
        intro A
        ext z
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective z
        simp only [Finset.addStab, Finset.mulStab, Finset.mem_filter, ← hf_sub, hf_vadd,
          hf_mem, hf_inj.eq_iff]
      have hkm := Finset.mul_kneser (f (n • s)) (f s)
      rw [← hf_add, ← hf_stab, ← hf_add, ← hf_add] at hkm
      simpa only [f, Finset.card_map] using hkm
    rw [← succ_nsmul] at hk
    rw [← hHdef] at hk
    -- combine
    have hsub : (n - 1) * #H + #H = n * #H := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    have hexp : (n + 1) * #(s + H) = n * #(s + H) + #(s + H) := by ring
    simp only [Nat.add_sub_cancel]
    omega
end Erdos338Proof
