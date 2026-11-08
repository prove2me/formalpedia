-- Prove2me | solution 1 for Chi2QEC.corrupted_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:17:55.891201+00:00
-- url     : https://prove2.me/submissions/9cf253f5-e719-41a2-a190-d23bb1b1f694

import Mathlib
import Definitions.Def_Chi2QEC_lossError
import Definitions.Def_Chi2QEC_pumpSubspace
import Definitions.Def_Chi2QEC_corruptedSubspace

namespace Aux_C2Q

open Chi2QEC

def P (q : ℕ) (t : Fin 3 → Fin q) : Prop :=
  ((t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1) ∨
  ((t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1) ∨
  ((t 1 : ℕ) + 1 = t 0 ∧ (t 0 : ℕ) + t 2 = q - 1) ∨
  ((t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 + 1 = q - 1)

open Classical in
noncomputable def T (q : ℕ) : Finset (Fin 3 → Fin q) := Finset.univ.filter (P q)

theorem card_T (q : ℕ) : (T q).card ≤ 4 * q - 3 := by
  classical
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have : (T 0) = ∅ := by
      ext t; simp only [Finset.notMem_empty, iff_false]; exact fun _ => (t 0).elim0
    rw [this]; simp
  -- split into four pieces, each injecting into a small Fin type
  have hsplit : T q ⊆ (Finset.univ.filter (fun t : Fin 3 → Fin q =>
      (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 1 : ℕ) + 1 = t 0 ∧ (t 0 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 + 1 = q - 1)) := by
    intro t ht
    simp only [T, P, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hext : ∀ t s : Fin 3 → Fin q, (t 0 : ℕ) = s 0 → (t 1 : ℕ) = s 1 → (t 2 : ℕ) = s 2 → t = s := by
    intro t s h0 h1 h2
    funext i; fin_cases i
    · exact Fin.ext h0
    · exact Fin.ext h1
    · exact Fin.ext h2
  have c0 : (Finset.univ.filter (fun t : Fin 3 → Fin q =>
      (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1)).card ≤ q := by
    calc _ ≤ (Finset.range (q)).card := by
          apply Finset.card_le_card_of_injOn (fun t => ((t 0 : Fin q) : ℕ))
          · intro t ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
            simp only [Finset.coe_range, Set.mem_Iio]
            exact (t 0).2
          · intro t ht s hs h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht hs
            simp only at h
            exact hext t s h (by omega) (by omega)
      _ = q := by simp
  have c1 : (Finset.univ.filter (fun t : Fin 3 → Fin q =>
      (t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1)).card ≤ q - 1 := by
    calc _ ≤ (Finset.range (q - 1)).card := by
          apply Finset.card_le_card_of_injOn (fun t => ((t 0 : Fin q) : ℕ))
          · intro t ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
            simp only [Finset.coe_range, Set.mem_Iio]
            have := (t 1).2; omega
          · intro t ht s hs h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht hs
            simp only at h
            exact hext t s h (by omega) (by omega)
      _ = q - 1 := by simp
  have c2 : (Finset.univ.filter (fun t : Fin 3 → Fin q =>
      (t 1 : ℕ) + 1 = t 0 ∧ (t 0 : ℕ) + t 2 = q - 1)).card ≤ q - 1 := by
    calc _ ≤ (Finset.range (q - 1)).card := by
          apply Finset.card_le_card_of_injOn (fun t => ((t 1 : Fin q) : ℕ))
          · intro t ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
            simp only [Finset.coe_range, Set.mem_Iio]
            have := (t 0).2; omega
          · intro t ht s hs h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht hs
            simp only at h
            exact hext t s (by omega) h (by omega)
      _ = q - 1 := by simp
  have c3 : (Finset.univ.filter (fun t : Fin 3 → Fin q =>
      (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 + 1 = q - 1)).card ≤ q - 1 := by
    calc _ ≤ (Finset.range (q - 1)).card := by
          apply Finset.card_le_card_of_injOn (fun t => ((t 0 : Fin q) : ℕ))
          · intro t ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · intro t ht s hs h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht hs
            simp only at h
            exact hext t s h (by omega) (by omega)
      _ = q - 1 := by simp
  have := Finset.card_le_card hsplit
  have u1 := Finset.card_union_le
    ((Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 1 : ℕ) + 1 = t 0 ∧ (t 0 : ℕ) + t 2 = q - 1)))
    (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 + 1 = q - 1))
  have u2 := Finset.card_union_le
    ((Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1)) ∪
      (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1)))
    (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 1 : ℕ) + 1 = t 0 ∧ (t 0 : ℕ) + t 2 = q - 1))
  have u3 := Finset.card_union_le
    (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) = t 1 ∧ (t 0 : ℕ) + t 2 = q - 1))
    (Finset.univ.filter (fun t : Fin 3 → Fin q => (t 0 : ℕ) + 1 = t 1 ∧ (t 1 : ℕ) + t 2 = q - 1))
  omega

theorem apply_single {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (x z : ι) :
    (Matrix.toEuclideanLin M (EuclideanSpace.single x (1 : ℂ))) z = M z x := by
  change (Matrix.mulVec M (EuclideanSpace.single x (1 : ℂ)).ofLp) z = M z x
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.single, Pi.single_apply]

theorem support_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (S' : Finset ι)
    (v : EuclideanSpace ℂ ι) (hv : ∀ z, z ∉ S' → v z = 0) :
    v ∈ Submodule.span ℂ ((S'.image (fun x => EuclideanSpace.single x (1 : ℂ)) : Finset _) :
      Set (EuclideanSpace ℂ ι)) := by
  have hv' : v = ∑ z, v z • EuclideanSpace.single z (1 : ℂ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply]
  rw [hv']
  apply Submodule.sum_mem
  intro z _
  by_cases hz : z ∈ S'
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨z, hz, rfl⟩
  · rw [hv z hz, zero_smul]; exact Submodule.zero_mem _

end Aux_C2Q

open Chi2QEC Aux_C2Q in
theorem solution (n q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q)))
    (hC : C ≤ pumpSubspace n q) :
    Module.finrank ℂ (corruptedSubspace C (lossError n q)) ≤ (4 * q - 3) ^ n := by
  classical
  set R' : Finset (FockIdx n q) := Fintype.piFinset (fun _ : Fin n => T q) with hR'
  set Fs := R'.image (fun x => EuclideanSpace.single x (1 : ℂ)) with hFs
  have hmemR : ∀ y : FockIdx n q, y ∈ R' ↔ ∀ ℓ, P q (y ℓ) := by
    intro y
    simp [hR', T, Fintype.mem_piFinset]
  have hpump : ∀ x ∈ pumpIndex n q, x ∈ R' := by
    intro x hx
    rw [hmemR]
    intro ℓ
    left
    exact ⟨congrArg Fin.val (hx ℓ).1, (hx ℓ).2⟩
  have himg : ∀ h, ∀ x ∈ pumpIndex n q,
      Matrix.toEuclideanLin (lossError n q h) (EuclideanSpace.single x (1 : ℂ)) ∈
        Submodule.span ℂ (Fs : Set (EuclideanSpace ℂ (FockIdx n q))) := by
    intro h x hx
    apply support_mem
    intro z hz
    rw [apply_single]
    cases h with
    | none =>
      simp only [lossError, Matrix.one_apply]
      rw [if_neg]
      intro e; exact hz (e ▸ hpump x hx)
    | some p =>
      obtain ⟨ℓ, k⟩ := p
      simp only [lossError, annihilation]
      rw [if_neg]
      rintro ⟨hagree, hdec⟩
      apply hz
      rw [hmemR]
      intro ℓ'
      have hxℓ := hx ℓ'
      by_cases hl : ℓ' = ℓ
      · subst hl
        have e : ∀ k', k' ≠ k → z ℓ' k' = x ℓ' k' := fun k' hk' =>
          hagree ℓ' k' (by intro h; exact hk' (Prod.mk.inj h).2)
        obtain ⟨h01, h02⟩ := hxℓ
        have h01' : (x ℓ' 0 : ℕ) = x ℓ' 1 := congrArg Fin.val h01
        unfold P
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
        rcases hk with rfl | rfl | rfl
        · have e1 := congrArg Fin.val (e 1 (by decide))
          have e2 := congrArg Fin.val (e 2 (by decide))
          right; left; omega
        · have e0 := congrArg Fin.val (e 0 (by decide))
          have e2 := congrArg Fin.val (e 2 (by decide))
          right; right; left; omega
        · have e0 := congrArg Fin.val (e 0 (by decide))
          have e1 := congrArg Fin.val (e 1 (by decide))
          right; right; right; omega
      · have e : z ℓ' = x ℓ' := by
          funext k'
          exact hagree ℓ' k' (by intro h; exact hl (Prod.mk.inj h).1)
        rw [e]
        left
        exact ⟨congrArg Fin.val hxℓ.1, hxℓ.2⟩
  have hle : corruptedSubspace C (lossError n q) ≤
      Submodule.span ℂ (Fs : Set (EuclideanSpace ℂ (FockIdx n q))) := by
    unfold corruptedSubspace
    apply iSup_le
    intro h
    rw [Submodule.map_le_iff_le_comap]
    refine hC.trans ?_
    unfold pumpSubspace
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact himg h x hx
  calc Module.finrank ℂ (corruptedSubspace C (lossError n q))
      ≤ Module.finrank ℂ (Submodule.span ℂ (Fs : Set (EuclideanSpace ℂ (FockIdx n q)))) :=
        Submodule.finrank_mono hle
    _ ≤ Fs.card := finrank_span_finset_le_card Fs
    _ ≤ R'.card := Finset.card_image_le
    _ = (T q).card ^ n := by rw [hR', Fintype.card_piFinset_const]
    _ ≤ (4 * q - 3) ^ n := Nat.pow_le_pow_left (card_T q) n
