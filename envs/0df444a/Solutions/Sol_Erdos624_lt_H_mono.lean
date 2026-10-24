-- Prove2me | solution 1 for Erdos624.lt_H_mono
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:47:21.090818+00:00
-- url     : https://prove2.me/submissions/f2d23e7d-e90b-49a7-b38a-70ae6d2abf86

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624
open Finset Erdos624

lemma ees_mono {n m m' : ℕ} (h : ExistsEventuallySurjective n m) (hm : m ≤ m') :
    ExistsEventuallySurjective n m' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun Y hY => hf Y (le_trans hm hY)⟩

lemma ees_succ {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (n + 1) := by
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  intro Y hY
  have : #Y ≤ n := by simpa using Finset.card_le_univ Y
  omega

lemma H_spec {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (H n) := by
  unfold H; rw [if_pos hn]
  exact Nat.sInf_mem (s := {m : ℕ | ExistsEventuallySurjective n m}) ⟨n + 1, ees_succ hn⟩

lemma H_le {n m : ℕ} (hn : 0 < n) (h : ExistsEventuallySurjective n m) : H n ≤ m := by
  unfold H; rw [if_pos hn]; exact Nat.sInf_le h

/-- `m < H n` iff no `f` is `m`-good. -/
theorem lt_H_iff {n m : ℕ} (hn : 0 < n) : m < H n ↔ ¬ ExistsEventuallySurjective n m := by
  constructor
  · intro h1 h2; have := H_le hn h2; omega
  · intro h1; by_contra h2; push Not at h2; exact h1 (ees_mono (H_spec hn) h2)

/-- B1 (image bound): the image of the subsets of `Y` has at most `2^|Y|` elements. -/
lemma image_card_le {n : ℕ} (f : Finset (Fin n) → Fin n) (Y : Finset (Fin n)) :
    #(Y.powerset.image f) ≤ 2 ^ #Y := by
  calc #(Y.powerset.image f) ≤ #Y.powerset := Finset.card_image_le
    _ = 2 ^ #Y := Finset.card_powerset Y

/-- B1: counting barrier `n ≤ 2^{H(n)}`. -/
theorem le_two_pow_H {n : ℕ} (hn : 0 < n) : n ≤ 2 ^ H n := by
  obtain ⟨f, hf⟩ := H_spec hn
  by_cases hle : H n ≤ n
  · obtain ⟨Y, -, hY⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (n := H n) (by simpa using hle)
    have h1 := hf Y (by omega)
    have h2 := image_card_le f Y
    rw [h1, hY] at h2
    simpa using h2
  · push Not at hle
    calc n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ H n := Nat.pow_le_pow_right (by norm_num) hle.le

/-- B1 in `clog` form: `⌈log₂ n⌉ ≤ H n`. -/
theorem clog_le_H {n : ℕ} (hn : 0 < n) : Nat.clog 2 n ≤ H n :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 (le_two_pow_H hn)

/-- B2 core: an `m`-good map on `Fin N` induces an `m`-good map on `Fin n` for `0 < n ≤ N`. -/
theorem ees_restrict {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (h : ExistsEventuallySurjective N m) : ExistsEventuallySurjective n m := by
  obtain ⟨f, hf⟩ := h
  let ι : Fin n ↪ Fin N := Fin.castLEEmb hnN
  let π : Fin N → Fin n := fun x => if hx : x.val < n then ⟨x.val, hx⟩ else ⟨0, hn⟩
  have hπ : ∀ u : Fin n, π (ι u) = u := by
    intro u; simp [π, ι, u.isLt]
  refine ⟨fun A => π (f (A.map ι)), ?_⟩
  intro Y hY
  apply Finset.eq_univ_of_forall
  intro u
  have h1 := hf (Y.map ι) (by simpa using hY)
  have h2 : ι u ∈ (Y.map ι).powerset.image f := by rw [h1]; exact Finset.mem_univ _
  obtain ⟨B, hB, hfB⟩ := Finset.mem_image.1 h2
  rw [Finset.mem_powerset, Finset.subset_map_iff] at hB
  obtain ⟨A, hAY, rfl⟩ := hB
  exact Finset.mem_image.2 ⟨A, Finset.mem_powerset.2 hAY, by simp only [hfB, hπ]⟩

/-- B2: if `H(n) > m` and `n ≤ N` then `H(N) > m`. -/
theorem lt_H_mono {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N) (h : m < H n) : m < H N := by
  have hN : 0 < N := by omega
  rw [lt_H_iff hn] at h
  rw [lt_H_iff hN]
  exact fun h' => h (ees_restrict hn hnN h')

/-- B2 corollary: `H` is monotone on positive integers. -/
theorem H_mono {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) : H n ≤ H N := by
  by_contra h; push Not at h
  have := lt_H_mono hn hnN h
  omega

/-- B4 (track amplification). If `n ≥ 1` and for every family of maps
`g_B : 𝒫(Fin n) → Fin n` indexed by `B ⊆ Fin s` there are an `m`-set `Y` and a common
omitted value `u`, then `H(n+s) > m+s`. -/
theorem track_amplification {n m s : ℕ} (hn : 0 < n)
    (h : ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u) :
    m + s < H (n + s) := by
  rw [lt_H_iff (by omega)]
  rintro ⟨f, hf⟩
  let ιL : Fin n ↪ Fin (n + s) := ⟨Fin.castAdd s, Fin.castAdd_injective n s⟩
  let ιR : Fin s ↪ Fin (n + s) := ⟨Fin.natAdd n, Fin.natAdd_injective s n⟩
  let π : Fin (n + s) → Fin n := fun x => if hx : x.val < n then ⟨x.val, hx⟩ else ⟨0, hn⟩
  have hπ : ∀ u : Fin n, π (ιL u) = u := by intro u; simp [π, ιL, u.isLt]
  obtain ⟨Y, hYm, u, hu⟩ := h (fun B A => π (f (A.map ιL ∪ B.map ιR)))
  have hdisj : ∀ (A : Finset (Fin n)) (B : Finset (Fin s)), Disjoint (A.map ιL) (B.map ιR) := by
    intro A B
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨b, -, hb⟩ := Finset.mem_map.1 hx'
    have := congrArg Fin.val hb
    simp [ιL, ιR] at this
    omega
  set Y' := Y.map ιL ∪ (Finset.univ : Finset (Fin s)).map ιR with hY'
  have hcard : #Y' = m + s := by
    rw [hY', Finset.card_union_of_disjoint (hdisj _ _)]; simp [hYm]
  have h1 := hf Y' (by omega)
  have h2 : ιL u ∈ Y'.powerset.image f := by rw [h1]; exact Finset.mem_univ _
  obtain ⟨C, hC, hfC⟩ := Finset.mem_image.1 h2
  rw [Finset.mem_powerset] at hC
  set A := Y.filter (fun y => ιL y ∈ C)
  set B := (Finset.univ : Finset (Fin s)).filter (fun z => ιR z ∈ C)
  have hCAB : C = A.map ιL ∪ B.map ιR := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, A, B, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have := hC hx
      rw [hY', Finset.mem_union, Finset.mem_map, Finset.mem_map] at this
      rcases this with ⟨y, hy, rfl⟩ | ⟨z, -, rfl⟩
      · exact Or.inl ⟨y, ⟨hy, hx⟩, rfl⟩
      · exact Or.inr ⟨z, hx, rfl⟩
    · rintro (⟨y, ⟨-, hy⟩, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact hy
      · exact hz
  have hA : A ∈ Y.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  apply hu B A hA
  show π (f (A.map ιL ∪ B.map ιR)) = u
  rw [← hCAB, hfC, hπ]

end E624



namespace Erdos624

theorem lt_H_mono {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N) (h : m < H n) : m < H N :=
  E624.lt_H_mono hn hnN h

end Erdos624

open Erdos624 in
theorem solution {n N m : ℕ} (hn : 0 < n) (hnN : n ≤ N) (h : m < H n) : m < H N :=
  Erdos624.lt_H_mono hn hnN h

#print axioms solution
