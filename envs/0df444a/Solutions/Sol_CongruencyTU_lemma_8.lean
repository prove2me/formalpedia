-- Prove2me | solution 1 for CongruencyTU.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:34:41.838625+00:00
-- url     : https://prove2.me/submissions/4dd7cf9d-aa82-410b-9591-13be3d777471

import Mathlib
import Definitions.Def_CongruencyTU_Pattern

open CongruencyTU in
theorem solution (m : ℕ) (hm : 0 < m) (R : Finset ℕ) (hR : ∀ r ∈ R, r < m) (ℓ : ℕ)
    (r : Fin ℓ → ℤ) (hsum : InRes m R (∑ i, r i))
    (hno : ¬ ∃ i₁ i₂ : Fin ℓ, i₁ ≤ i₂ ∧
      InRes m R (∑ i ∈ Finset.univ.filter (fun i => ¬ (i₁ ≤ i ∧ i ≤ i₂)), r i)) :
    ℓ ≤ m - R.card := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ; exact Nat.zero_le _
  obtain ⟨w, hw⟩ : ∃ w : Fin ℓ → ℤ, ∀ b, w b = ∑ i ∈ Finset.univ.filter (fun i => b < i), r i :=
    ⟨_, fun _ => rfl⟩
  have hw1 : ∀ b, ¬ InRes m R (w b) := by
    intro b hb
    apply hno
    refine ⟨⟨0, hℓ⟩, b, Fin.le_def.mpr (Nat.zero_le _), ?_⟩
    have hf : Finset.univ.filter (fun i : Fin ℓ => ¬ ((⟨0, hℓ⟩ : Fin ℓ) ≤ i ∧ i ≤ b)) =
        Finset.univ.filter (fun i => b < i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.lt_def, Fin.val_mk]
      constructor
      · intro h; omega
      · intro h; omega
    rw [hf, ← hw]
    exact hb
  have hcomp : ∀ a b c : Fin ℓ, a < b → c.val = a.val + 1 →
      ∑ i ∈ Finset.univ.filter (fun i => ¬ (c ≤ i ∧ i ≤ b)), r i =
        (∑ i, r i) - (w a - w b) := by
    intro a b c hab hc
    rw [hw a, hw b]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hab' := Fin.lt_def.mp hab
    split_ifs <;> simp only [Fin.le_def, Fin.lt_def, not_and, not_le,
      not_lt] at * <;> first | ring1 | omega
  have key : ∀ a b : Fin ℓ, a < b → ¬ (w a ≡ w b [ZMOD (m : ℤ)]) := by
    intro a b hab hmod
    have hab' := Fin.lt_def.mp hab
    have hc : a.val + 1 < ℓ := by have := b.isLt; omega
    apply hno
    refine ⟨⟨a.val + 1, hc⟩, b, ?_, ?_⟩
    · exact Fin.le_def.mpr (by show a.val + 1 ≤ b.val; omega)
    · rw [hcomp a b ⟨a.val + 1, hc⟩ hab rfl]
      obtain ⟨r₀, hr₀, hS⟩ := hsum
      refine ⟨r₀, hr₀, ?_⟩
      have h1 : w a - w b ≡ 0 [ZMOD (m : ℤ)] := by
        have := Int.ModEq.sub_right (w b) hmod
        simpa using this
      have h2 : (∑ i, r i) - (w a - w b) ≡ (∑ i, r i) - 0 [ZMOD (m : ℤ)] :=
        Int.ModEq.sub_left _ h1
      rw [sub_zero] at h2
      exact h2.trans hS
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  obtain ⟨v, hv⟩ : ∃ v : Fin ℓ → ℕ, ∀ b, v b = (w b % (m : ℤ)).toNat := ⟨_, fun _ => rfl⟩
  have hv_cast : ∀ b, ((v b : ℕ) : ℤ) = w b % (m : ℤ) := by
    intro b
    rw [hv b]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hmZ.ne')
  have hv_lt : ∀ b, v b < m := by
    intro b
    have h1 := Int.emod_lt_of_pos (w b) hmZ
    have h2 := hv_cast b
    omega
  have hv_notin : ∀ b, v b ∉ R := by
    intro b hvR
    apply hw1 b
    refine ⟨v b, hvR, ?_⟩
    rw [hv_cast]
    exact (Int.mod_modEq (w b) m).symm
  have hinj : Function.Injective v := by
    intro a b hab
    have hmod : w a ≡ w b [ZMOD (m : ℤ)] := by
      show w a % (m : ℤ) = w b % (m : ℤ)
      rw [← hv_cast, ← hv_cast, hab]
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hmod (key a b h)
    · exact h
    · exact absurd hmod.symm (key b a h)
  have hsub : Finset.univ.image v ⊆ Finset.range m \ R := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (hv_lt b), hv_notin b⟩
  have hRsub : R ⊆ Finset.range m := fun x hx => Finset.mem_range.mpr (hR x hx)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
    Finset.card_sdiff_of_subset hRsub, Finset.card_range] at h1
  exact h1
