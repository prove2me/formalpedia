-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:34:41.774052+00:00
-- url     : https://prove2.me/submissions/2b3e9909-8844-4990-a388-1d16ffa95bc8

import Mathlib

theorem gg_A_apply {k m : ℕ} (φ : Fin k → Fin m) (S : Finset (Fin k)) (x : Fin m) :
    (∑ i ∈ S, Finsupp.single (φ i) 1 : Fin m →₀ ℕ) x = (S.filter (fun i => φ i = x)).card := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, Finset.sum_boole]

theorem gg_A_le {k m : ℕ} (φ : Fin k → Fin m) (hφ : Function.Injective φ) (S : Finset (Fin k))
    (x : Fin m) : (∑ i ∈ S, Finsupp.single (φ i) 1 : Fin m →₀ ℕ) x ≤ 1 := by
  rw [gg_A_apply]
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact hφ (ha.2.trans hb.2.symm)

theorem gg_A_zero {k m : ℕ} (φ : Fin k → Fin m) (S : Finset (Fin k))
    (x : Fin m) (hx : ∀ i, φ i ≠ x) : (∑ i ∈ S, Finsupp.single (φ i) 1 : Fin m →₀ ℕ) x = 0 := by
  rw [gg_A_apply, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; exact hx i

theorem gg_A_self {k m : ℕ} (φ : Fin k → Fin m) (hφ : Function.Injective φ) (S : Finset (Fin k))
    (j : Fin k) : (∑ i ∈ S, Finsupp.single (φ i) 1 : Fin m →₀ ℕ) (φ j) = if j ∈ S then 1 else 0 := by
  classical
  rw [gg_A_apply]
  have : S.filter (fun i => φ i = φ j) = S.filter (fun i => i = j) := by
    apply Finset.filter_congr; intro i _; exact hφ.eq_iff
  rw [this, Finset.filter_eq']
  split_ifs <;> simp

theorem gg_s_val (k t : ℕ) (hi : t < k) :
    (2 * t + 2) % (2 * k) = if t + 1 < k then 2 * t + 2 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · have : 2 * t + 2 = 2 * k := by omega
    rw [this, Nat.mod_self]

theorem solution (k : ℕ) (I I' : Finset (Fin k)) (hI : I.Nonempty) (hIk : I ≠ Finset.univ) :
    let a : Fin (2 * k) →₀ ℕ := ∑ i ∈ I,
      (Finsupp.single (⟨2 * i.val, by omega⟩ : Fin (2 * k)) 1 +
        Finsupp.single (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k)) 1)
    let a' : Fin (2 * k) →₀ ℕ := ∑ i ∈ I',
      (Finsupp.single (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k)) 1 +
        Finsupp.single (⟨(2 * i.val + 2) % (2 * k), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2 * k)) 1)
    a ≠ a' ∧ (∀ x, a x ≤ 1) ∧ (∀ x, a' x ≤ 1) := by
  classical
  intro a a'
  let e : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val, by omega⟩
  let o : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val + 1, by omega⟩
  let s : Fin k → Fin (2 * k) := fun i =>
    ⟨(2 * i.val + 2) % (2 * k), Nat.mod_lt _ (by have := i.isLt; omega)⟩
  have he : Function.Injective e := by
    intro i j h; simp only [e, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  have ho : Function.Injective o := by
    intro i j h; simp only [o, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  have hs : Function.Injective s := by
    intro i j h; simp only [s, Fin.mk.injEq] at h
    rw [gg_s_val k i.val i.isLt, gg_s_val k j.val j.isLt] at h
    have := i.isLt; have := j.isLt
    apply Fin.ext; split_ifs at h <;> omega
  have hoe : ∀ i j, o i ≠ e j := by
    intro i j h; simp only [o, e, Fin.mk.injEq] at h; omega
  have hos : ∀ i j, o i ≠ s j := by
    intro i j h; simp only [o, s, Fin.mk.injEq] at h
    rw [gg_s_val k j.val j.isLt] at h; split_ifs at h <;> omega
  have ha : a = (∑ i ∈ I, Finsupp.single (e i) 1) + ∑ i ∈ I, Finsupp.single (o i) 1 :=
    Finset.sum_add_distrib
  have ha' : a' = (∑ i ∈ I', Finsupp.single (o i) 1) + ∑ i ∈ I', Finsupp.single (s i) 1 :=
    Finset.sum_add_distrib
  -- every x is e j or o j
  have hx : ∀ x : Fin (2 * k), (∃ j, e j = x) ∨ (∃ j, o j = x) := by
    intro x
    have hx := x.isLt
    rcases Nat.even_or_odd x.val with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; exact ⟨⟨r, by omega⟩, Fin.ext (by simp [e]; omega)⟩
    · right; exact ⟨⟨r, by omega⟩, Fin.ext (by simp [o]; omega)⟩
  -- every even is s j
  have hes : ∀ j, ∃ i, s i = e j := by
    intro j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · refine ⟨⟨k - 1, by omega⟩, Fin.ext ?_⟩
      simp only [s, e]; rw [gg_s_val k _ (by omega)]; split_ifs <;> simp_all <;> omega
    · refine ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
      simp only [s, e]; rw [gg_s_val k _ (by omega)]; split_ifs <;> simp_all <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    -- derive: j ∈ I ↔ j ∈ I', and s-shift
    have hodd : ∀ j, (j ∈ I ↔ j ∈ I') := by
      intro j
      have h1 : a (o j) = a' (o j) := by rw [hEq]
      rw [ha, ha', Finsupp.add_apply, Finsupp.add_apply, gg_A_zero e I (o j) (fun i h => hoe j i h.symm),
        gg_A_zero s I' (o j) (fun i h => hos j i h.symm), gg_A_self o ho, gg_A_self o ho] at h1
      constructor <;> intro h <;> by_contra h' <;> simp_all
    have hshift : ∀ i j, s i = e j → (i ∈ I → j ∈ I) := by
      intro i j hij hi
      have h1 : a (e j) = a' (e j) := by rw [hEq]
      rw [ha, ha', Finsupp.add_apply, Finsupp.add_apply, gg_A_zero o I (e j) (fun i h => hoe i j h),
        gg_A_zero o I' (e j) (fun i h => hoe i j h), gg_A_self e he, ← hij, gg_A_self s hs] at h1
      have hi' : i ∈ I' := (hodd i).1 hi
      by_contra h'; simp_all
    -- closure under successor
    have hsucc : ∀ t : ℕ, ∀ ht : t < k, (⟨t, ht⟩ : Fin k) ∈ I →
        ∀ ht' : (t + 1) % k < k, (⟨(t + 1) % k, ht'⟩ : Fin k) ∈ I := by
      intro t ht hmem ht'
      apply hshift ⟨t, ht⟩ _ _ hmem
      apply Fin.ext
      simp only [s, e]
      rw [gg_s_val k t ht]
      split_ifs with h
      · rw [Nat.mod_eq_of_lt h]; ring
      · have : t + 1 = k := by simp at h; omega
        rw [this, Nat.mod_self]
    obtain ⟨i0, hi0⟩ := hI
    have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
    have hall : ∀ t : ℕ, (⟨(i0.val + t) % k, Nat.mod_lt _ hk⟩ : Fin k) ∈ I := by
      intro t
      induction t with
      | zero =>
        have : (⟨(i0.val + 0) % k, Nat.mod_lt _ hk⟩ : Fin k) = i0 :=
          Fin.ext (by simp [Nat.mod_eq_of_lt i0.isLt])
        rw [this]; exact hi0
      | succ t ih =>
        have := hsucc _ (Nat.mod_lt _ hk) ih (Nat.mod_lt _ hk)
        have heq : ((i0.val + t) % k + 1) % k = (i0.val + (t + 1)) % k := by
          rw [← Nat.add_assoc, Nat.add_mod (i0.val + t) 1 k, Nat.add_mod ((i0.val + t) % k) 1 k,
            Nat.mod_mod]
        simp only [heq] at this
        exact this
    apply hIk
    apply Finset.eq_univ_of_forall
    intro j
    have := hall (j.val + k - i0.val)
    have h2 : (i0.val + (j.val + k - i0.val)) % k = j.val := by
      have : i0.val + (j.val + k - i0.val) = j.val + k := by have := i0.isLt; omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    have h3 : (⟨(i0.val + (j.val + k - i0.val)) % k, Nat.mod_lt _ hk⟩ : Fin k) = j := Fin.ext h2
    rw [h3] at this; exact this
  · intro x
    rw [ha, Finsupp.add_apply]
    rcases hx x with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [gg_A_zero o I (e j) (fun i h => hoe i j h)]; simpa using gg_A_le e he I (e j)
    · rw [gg_A_zero e I (o j) (fun i h => hoe j i h.symm)]; simpa using gg_A_le o ho I (o j)
  · intro x
    rw [ha', Finsupp.add_apply]
    rcases hx x with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [gg_A_zero o I' (e j) (fun i h => hoe i j h)]; simpa using gg_A_le s hs I' (e j)
    · rw [gg_A_zero s I' (o j) (fun i h => hos j i h.symm)]; simpa using gg_A_le o ho I' (o j)
