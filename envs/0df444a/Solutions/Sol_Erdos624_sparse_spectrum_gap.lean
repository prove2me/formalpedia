-- Prove2me | solution 1 for Erdos624.sparse_spectrum_gap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:54.740714+00:00
-- url     : https://prove2.me/submissions/a747f24f-cf03-4722-a2cd-35389c13aaba

import Mathlib
open Finset

namespace E624R14S
open Finset

lemma wt_add_le {U : Type*} [Fintype U] [DecidableEq U] (f g : U → ZMod 2) :
    #(univ.filter (fun x => (f + g) x ≠ 0)) ≤
      #(univ.filter (fun x => f x ≠ 0)) + #(univ.filter (fun x => g x ≠ 0)) := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro x hx
  simp only [mem_filter, mem_univ, true_and, mem_union, Pi.add_apply] at hx ⊢
  by_contra hc; push Not at hc; rw [hc.1, hc.2, add_zero] at hx; exact hx rfl

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem sparse {U : Type*} [Fintype U] [DecidableEq U] (Q : Submodule (ZMod 2) (U → ZMod 2))
    (a K : ℕ) (hK : 2 * K ≤ a)
    (hgap : ∀ f ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => f x ≠ 0)) ≤ K) :
    (∀ f ∈ Q, ∀ g ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => g x ≠ 0)) ≤ a → #(univ.filter (fun x => (f + g) x ≠ 0)) ≤ K) ∧
    (∀ T : Finset U, (∀ x ∈ T, ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #T ≤ 2 * K) ∧
    (∀ g ∈ Q, (∀ x, g x ≠ 0 → ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #(univ.filter (fun x => g x ≠ 0)) ≤ K) := by
  classical
  have hadd : ∀ f ∈ Q, ∀ g ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => g x ≠ 0)) ≤ a → #(univ.filter (fun x => (f + g) x ≠ 0)) ≤ K := by
    intro f hf g hg hfa hga
    apply hgap (f + g) (Q.add_mem hf hg)
    have := wt_add_le f g
    have := hgap f hf hfa; have := hgap g hg hga
    omega
  set wt := fun f : U → ZMod 2 => #(univ.filter (fun x => f x ≠ 0)) with hwt
  set Fs := (univ : Finset (U → ZMod 2)).filter (fun f => f ∈ Q ∧ wt f ≤ a) with hFs
  have hTcard : ∀ T : Finset U, (∀ x ∈ T, ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧
      f x ≠ 0) → #T ≤ 2 * K := by
    intro T hT
    -- each support coordinate is nonzero on exactly half of Fs
    have hhalf : ∀ x ∈ T, #Fs = 2 * #(Fs.filter (fun f => f x ≠ 0)) := by
      intro x hx
      obtain ⟨f0, hf0Q, hf0a, hf0x⟩ := hT x hx
      have hf01 : f0 x = 1 := (zmod2_cases _).resolve_left hf0x
      have hsplit := card_filter_add_card_filter_not (s := Fs) (fun f => f x ≠ 0)
      have hbij : #(Fs.filter (fun f => f x ≠ 0)) = #(Fs.filter (fun f => ¬ f x ≠ 0)) := by
        refine card_nbij' (fun f => f + f0) (fun f => f + f0) ?_ ?_ ?_ ?_
        · intro f hf
          simp only [coe_filter, hFs, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
          refine ⟨⟨Q.add_mem hf.1.1 hf0Q, (hadd f hf.1.1 f0 hf0Q hf.1.2 hf0a).trans (by omega)⟩, ?_⟩
          have := (zmod2_cases (f x)).resolve_left hf.2
          simp only [Pi.add_apply, this, hf01]; decide
        · intro f hf
          simp only [coe_filter, hFs, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
          refine ⟨⟨Q.add_mem hf.1.1 hf0Q, (hadd f hf.1.1 f0 hf0Q hf.1.2 hf0a).trans (by omega)⟩, ?_⟩
          push Not at hf
          simp only [Pi.add_apply, hf.2, hf01]; decide
        · intro f _; simp only; rw [add_assoc, ZModModule.add_self, add_zero]
        · intro f _; simp only; rw [add_assoc, ZModModule.add_self, add_zero]
      omega
    have hsum : ∑ f ∈ Fs, wt f = ∑ x : U, #(Fs.filter (fun f => f x ≠ 0)) := by
      simp only [hwt, card_filter]; exact sum_comm
    have hup : ∑ f ∈ Fs, wt f ≤ #Fs * K := by
      calc ∑ f ∈ Fs, wt f ≤ ∑ _f ∈ Fs, K := sum_le_sum fun f hf => by
            have := (mem_filter.1 hf).2; exact hgap f this.1 this.2
        _ = #Fs * K := by rw [sum_const, smul_eq_mul]
    have hlow : #T * #Fs ≤ 2 * ∑ f ∈ Fs, wt f := by
      rw [hsum, mul_sum]
      calc #T * #Fs = ∑ x ∈ T, 2 * #(Fs.filter (fun f => f x ≠ 0)) := by
            rw [sum_congr rfl fun x hx => (hhalf x hx).symm, sum_const, smul_eq_mul]
        _ ≤ ∑ x : U, 2 * #(Fs.filter (fun f => f x ≠ 0)) :=
            sum_le_sum_of_subset (subset_univ _)
    have hpos : 0 < #Fs := card_pos.2 ⟨0, by
      simp only [hFs, mem_filter, mem_univ, true_and, hwt]
      exact ⟨Q.zero_mem, by simp⟩⟩
    have : #T * #Fs ≤ 2 * K * #Fs := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  refine ⟨hadd, hTcard, ?_⟩
  intro g hg hsupp
  apply hgap g hg
  have := hTcard (univ.filter (fun x => g x ≠ 0)) (fun x hx => hsupp x (mem_filter.1 hx).2)
  omega
end E624R14S

namespace Erdos624

theorem sparse_spectrum_gap {U : Type*} [Fintype U] [DecidableEq U] (Q : Submodule (ZMod 2) (U → ZMod 2))
    (a K : ℕ) (hK : 2 * K ≤ a)
    (hgap : ∀ f ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => f x ≠ 0)) ≤ K) :
    (∀ f ∈ Q, ∀ g ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => g x ≠ 0)) ≤ a → #(univ.filter (fun x => (f + g) x ≠ 0)) ≤ K) ∧
    (∀ T : Finset U, (∀ x ∈ T, ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #T ≤ 2 * K) ∧
    (∀ g ∈ Q, (∀ x, g x ≠ 0 → ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #(univ.filter (fun x => g x ≠ 0)) ≤ K) := by
  exact E624R14S.sparse Q a K hK hgap

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] (Q : Submodule (ZMod 2) (U → ZMod 2))
    (a K : ℕ) (hK : 2 * K ≤ a)
    (hgap : ∀ f ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => f x ≠ 0)) ≤ K) :
    (∀ f ∈ Q, ∀ g ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => g x ≠ 0)) ≤ a → #(univ.filter (fun x => (f + g) x ≠ 0)) ≤ K) ∧
    (∀ T : Finset U, (∀ x ∈ T, ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #T ≤ 2 * K) ∧
    (∀ g ∈ Q, (∀ x, g x ≠ 0 → ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #(univ.filter (fun x => g x ≠ 0)) ≤ K) :=
  Erdos624.sparse_spectrum_gap Q a K hK hgap
