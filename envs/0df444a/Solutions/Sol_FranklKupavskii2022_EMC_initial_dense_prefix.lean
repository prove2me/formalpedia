-- Prove2me | solution 1 for FranklKupavskii2022.EMC.initial_dense_prefix
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:04:39.359989+00:00
-- url     : https://prove2.me/submissions/e0bd04cf-18ba-490e-9771-18f2f0892a4a

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

namespace FranklKupavskii2022.EMC

/-- The arithmetic progression embedding `j ↦ a + j * d`. -/
def aux_idp_emb (a d : ℕ) (hd : 0 < d) : ℕ ↪ ℕ :=
  ⟨fun j => a + j * d, fun x y h => by
    have h' : x * d = y * d := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right hd h'⟩

theorem aux_idp_emb_apply (a d : ℕ) (hd : 0 < d) (j : ℕ) :
    aux_idp_emb a d hd j = a + j * d := rfl

theorem aux_idp_emb_strictMono (a d : ℕ) (hd : 0 < d) : StrictMono (aux_idp_emb a d hd) := by
  intro x y hxy
  simp only [aux_idp_emb_apply]
  have := Nat.mul_lt_mul_of_pos_right hxy hd
  omega

theorem aux_idp_sort_map (k a d : ℕ) (hd : 0 < d) :
    ((Finset.range k).map (aux_idp_emb a d hd)).sort
      = (List.range k).map (aux_idp_emb a d hd) := by
  rw [← ((aux_idp_emb_strictMono a d hd).strictMonoOn
    ((Finset.range k : Finset ℕ) : Set ℕ)).map_finsetSort, Finset.sort_range]

theorem aux_idp_sort_length (k a d : ℕ) (hd : 0 < d) :
    ((Finset.range k).map (aux_idp_emb a d hd)).sort.length = k := by
  simp [Finset.length_sort]

theorem aux_idp_sort_get (k a d : ℕ) (hd : 0 < d) (j : ℕ)
    (h : j < ((Finset.range k).map (aux_idp_emb a d hd)).sort.length) :
    ((Finset.range k).map (aux_idp_emb a d hd)).sort[j] = a + j * d := by
  rw [List.getElem_of_eq (aux_idp_sort_map k a d hd) h]
  simp [aux_idp_emb_apply]

theorem aux_idp_mem (m k : ℕ) (F : Finset (Finset ℕ)) (hinit : IsInitial m k F)
    (G F' : Finset ℕ) (hG : G ∈ (Finset.Icc 1 m).powersetCard k) (hF' : F' ∈ F)
    (h : List.Forall₂ (· ≤ ·) G.sort F'.sort) : G ∈ F := by
  by_cases hGF : G = F'
  · subst hGF; exact hF'
  · exact hinit G hG F' hF' ⟨h, hGF⟩

theorem aux_idp_resid (s c c' j j' : ℕ) (hc : c < s + 1) (hc' : c' < s + 1)
    (h : c + j * (s + 1) = c' + j' * (s + 1)) : c = c' := by
  have h2 := congrArg (· % (s + 1)) h
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h2
  exact h2

theorem aux_idp_T_eq (k s : ℕ) :
    (Finset.Icc 1 k).image (fun j => j * (s + 1)) =
      (Finset.range k).map (aux_idp_emb (s + 1) (s + 1) (Nat.succ_pos s)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
    aux_idp_emb_apply]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact ⟨j', by omega, by ring⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j + 1, ⟨by omega, by omega⟩, by ring⟩

theorem aux_idp_part1 (m k s : ℕ) (hk : 1 ≤ k) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k F)
    (hν : matchingNumber F ≤ s) :
    (Finset.range k).map (aux_idp_emb (s + 1) (s + 1) (Nat.succ_pos s)) ∉ F := by
  intro hT
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hTm : s + 1 + k' * (s + 1) ≤ m := by
    have h1 := hF hT
    rw [Finset.mem_powersetCard] at h1
    have hx : s + 1 + k' * (s + 1) ∈
        (Finset.range (k' + 1)).map (aux_idp_emb (s + 1) (s + 1) (Nat.succ_pos s)) :=
      Finset.mem_map.2 ⟨k', by simp, rfl⟩
    exact (Finset.mem_Icc.1 (h1.1 hx)).2
  set B : ℕ → Finset ℕ := fun c =>
    (Finset.range (k' + 1)).map (aux_idp_emb (c + 1) (s + 1) (Nat.succ_pos s)) with hBdef
  have hmemB : ∀ c x, x ∈ B c ↔ ∃ j, j < k' + 1 ∧ c + 1 + j * (s + 1) = x := by
    intro c x
    simp [hBdef, aux_idp_emb_apply]
  have hBF : ∀ c, c < s + 1 → B c ∈ F := by
    intro c hc
    apply aux_idp_mem m (k' + 1) F hinit (B c) _ _ hT
    · simp only [hBdef]
      rw [List.forall₂_iff_get]
      refine ⟨by rw [aux_idp_sort_length, aux_idp_sort_length], ?_⟩
      intro j h1 h2
      simp only [List.get_eq_getElem]
      rw [aux_idp_sort_get, aux_idp_sort_get]
      omega
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, by simp [hBdef]⟩
      intro x hx
      obtain ⟨j, hj, rfl⟩ := (hmemB c x).1 hx
      have : j * (s + 1) ≤ k' * (s + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [Finset.mem_Icc]
      constructor <;> omega
  have hinj : Set.InjOn B (Finset.range (s + 1) : Set ℕ) := by
    intro c hc c' hc' hcc
    simp only [Finset.coe_range, Set.mem_Iio] at hc hc'
    have hmem : c + 1 ∈ B c := (hmemB c _).2 ⟨0, by omega, by simp⟩
    rw [hcc] at hmem
    obtain ⟨j, _, hj⟩ := (hmemB c' _).1 hmem
    exact (aux_idp_resid s c' c j 0 hc' hc (by omega)).symm
  set M := (Finset.range (s + 1)).image B with hMdef
  have hMcard : M.card = s + 1 := by
    rw [hMdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hMmem : M ∈ F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro X hX
      rw [hMdef, Finset.mem_image] at hX
      obtain ⟨c, hc, rfl⟩ := hX
      exact hBF c (Finset.mem_range.1 hc)
    · intro X hX Y hY hXY
      rw [hMdef, Finset.mem_image] at hX hY
      obtain ⟨c, hc, rfl⟩ := hX
      obtain ⟨c', hc', rfl⟩ := hY
      rw [Finset.mem_range] at hc hc'
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨j, _, hj⟩ := (hmemB c x).1 hx
      obtain ⟨j', _, hj'⟩ := (hmemB c' x).1 hx'
      have : c = c' := aux_idp_resid s c c' j j' hc hc' (by omega)
      exact hXY (by rw [this])
  have hle : M.card ≤ matchingNumber F := by
    unfold matchingNumber
    exact Finset.le_sup (f := Finset.card) hMmem
  omega

theorem aux_idp_sort_lb (A : Finset ℕ) (hA : ∀ x ∈ A, 1 ≤ x) (N j : ℕ)
    (hj : j < A.sort.length) (hcard : (A ∩ Finset.Icc 1 N).card < j + 1) :
    N < A.sort[j] := by
  by_contra hle
  push Not at hle
  set l := A.sort with hl
  have hnd : (l.take (j + 1)).Nodup := (Finset.sort_nodup A _).sublist (List.take_sublist _ _)
  have hcS : (l.take (j + 1)).toFinset.card = j + 1 := by
    rw [List.toFinset_card_of_nodup hnd, List.length_take]
    omega
  have hsub : (l.take (j + 1)).toFinset ⊆ A ∩ Finset.Icc 1 N := by
    intro x hx
    rw [List.mem_toFinset, List.mem_take_iff_getElem] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htl : t < l.length := by omega
    have hmemA : l[t] ∈ A := (Finset.mem_sort (α := ℕ) (· ≤ ·)).1 (List.getElem_mem htl)
    have hle2 : l[t] ≤ l[j] :=
      (Finset.sortedLT_sort A).getElem_le_getElem_iff.2 (by omega)
    rw [Finset.mem_inter, Finset.mem_Icc]
    exact ⟨hmemA, hA _ hmemA, le_trans hle2 hle⟩
  have := Finset.card_le_card hsub
  omega

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC

theorem solution (m k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k F)
    (hν : matchingNumber F ≤ s) :
    (Finset.Icc 1 k).image (fun j => j * (s + 1)) ∉ F ∧
      ∀ A ∈ F, ∃ i, 1 ≤ i ∧ i ≤ k ∧ i ≤ (A ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by
  have hP1 := aux_idp_part1 m k s hk F hF hinit hν
  rw [aux_idp_T_eq]
  refine ⟨hP1, ?_⟩
  intro A hA
  by_contra hcon
  push Not at hcon
  have hAF := hF hA
  rw [Finset.mem_powersetCard] at hAF
  have hA1 : ∀ x ∈ A, 1 ≤ x := fun x hx => (Finset.mem_Icc.1 (hAF.1 hx)).1
  have hAlen : A.sort.length = k := by rw [Finset.length_sort, hAF.2]
  have hbound : ∀ j (hj : j < A.sort.length), s + 1 + j * (s + 1) ≤ A.sort[j] := by
    intro j hj
    have hc := hcon (j + 1) (by omega) (by omega)
    have h := aux_idp_sort_lb A hA1 ((j + 1) * (s + 1) - 1) j hj hc
    have e : (j + 1) * (s + 1) = s + 1 + j * (s + 1) := by ring
    omega
  apply hP1
  apply aux_idp_mem m k F hinit _ A _ hA
  · rw [List.forall₂_iff_get]
    refine ⟨by rw [aux_idp_sort_length, hAlen], ?_⟩
    intro j h1 h2
    simp only [List.get_eq_getElem]
    rw [aux_idp_sort_get]
    exact hbound j h2
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, by simp⟩
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_range] at hj
    rw [aux_idp_emb_apply, Finset.mem_Icc]
    have hj' : j < A.sort.length := by omega
    have h1 := hbound j hj'
    have hmemA : A.sort[j] ∈ A := (Finset.mem_sort (α := ℕ) (· ≤ ·)).1 (List.getElem_mem hj')
    have h2 := (Finset.mem_Icc.1 (hAF.1 hmemA)).2
    constructor <;> omega
