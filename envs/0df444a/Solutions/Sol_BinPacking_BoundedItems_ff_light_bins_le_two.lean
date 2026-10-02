-- Prove2me | solution 1 for BinPacking.BoundedItems.ff_light_bins_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:47:03.735172+00:00
-- url     : https://prove2.me/submissions/e066dd1a-8d80-4256-8385-4bf4739a79c3

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

set_option autoImplicit false

namespace P2M49c4899d

open BinPacking.BoundedItems

/-- Every item of the later bin `C` failed to fit into the earlier bin `B`. -/
def Rl (B C : List ℝ) : Prop := ∀ x ∈ C, 1 < level B + x

lemma mem_ffInsert (a : ℝ) : ∀ (P : List (List ℝ)) (C : List ℝ), C ∈ ffInsert a P →
    ∀ x ∈ C, x = a ∨ ∃ C0 ∈ P, x ∈ C0
  | [], C, hC, x, hx => by
    simp [ffInsert] at hC
    subst hC
    simp at hx
    exact Or.inl hx
  | B :: Bs, C, hC, x, hx => by
    simp only [ffInsert] at hC
    split_ifs at hC with h
    · rcases List.mem_cons.1 hC with rfl | hC
      · rcases List.mem_append.1 hx with hx | hx
        · exact Or.inr ⟨B, by simp, hx⟩
        · simp at hx
          exact Or.inl hx
      · exact Or.inr ⟨C, by simp [hC], hx⟩
    · rcases List.mem_cons.1 hC with rfl | hC
      · exact Or.inr ⟨C, by simp, hx⟩
      · rcases mem_ffInsert a Bs C hC x hx with h1 | ⟨C0, hC0, hx0⟩
        · exact Or.inl h1
        · exact Or.inr ⟨C0, by simp [hC0], hx0⟩

lemma perm_ffInsert (a : ℝ) : ∀ P : List (List ℝ), (ffInsert a P).flatten.Perm (a :: P.flatten)
  | [] => by simp [ffInsert]
  | B :: Bs => by
    simp only [ffInsert]
    split_ifs with h
    · simp only [List.flatten_cons, List.append_assoc, List.singleton_append]
      exact List.perm_middle
    · simp only [List.flatten_cons]
      exact ((perm_ffInsert a Bs).append_left B).trans List.perm_middle

lemma ne_nil_ffInsert (a : ℝ) : ∀ P : List (List ℝ), (∀ C ∈ P, C ≠ []) →
    ∀ C ∈ ffInsert a P, C ≠ []
  | [], _, C, hC => by
    simp [ffInsert] at hC
    simp [hC]
  | B :: Bs, hP, C, hC => by
    simp only [ffInsert] at hC
    split_ifs at hC with h
    · rcases List.mem_cons.1 hC with rfl | hC
      · simp
      · exact hP C (by simp [hC])
    · rcases List.mem_cons.1 hC with rfl | hC
      · exact hP C (by simp)
      · exact ne_nil_ffInsert a Bs (fun C hC => hP C (by simp [hC])) C hC

lemma pw_ffInsert (a : ℝ) (ha : 0 ≤ a) : ∀ P : List (List ℝ), P.Pairwise Rl →
    (ffInsert a P).Pairwise Rl
  | [], _ => by simp [ffInsert]
  | B :: Bs, hP => by
    rw [List.pairwise_cons] at hP
    simp only [ffInsert]
    split_ifs with h
    · refine List.pairwise_cons.2 ⟨fun C hC x hx => ?_, hP.2⟩
      have := hP.1 C hC x hx
      simp only [level, List.sum_append, List.sum_singleton] at this ⊢
      linarith
    · refine List.pairwise_cons.2 ⟨fun C hC x hx => ?_, pw_ffInsert a ha Bs hP.2⟩
      rcases mem_ffInsert a Bs C hC x hx with hxa | ⟨C0, hC0, hx0⟩
      · rw [hxa]
        exact lt_of_not_ge h
      · exact hP.1 C0 hC0 x hx0

lemma fold_inv : ∀ (L' : List ℝ) (P : List (List ℝ)), (∀ a ∈ L', 0 ≤ a) → P.Pairwise Rl →
    (∀ C ∈ P, C ≠ []) →
    (L'.foldl (fun P a => ffInsert a P) P).Pairwise Rl ∧
    (∀ C ∈ L'.foldl (fun P a => ffInsert a P) P, C ≠ []) ∧
    (L'.foldl (fun P a => ffInsert a P) P).flatten.Perm (L' ++ P.flatten)
  | [], P, _, h1, h2 => ⟨h1, h2, by simp⟩
  | a :: L', P, hL, h1, h2 => by
    simp only [List.foldl_cons]
    obtain ⟨r1, r2, r3⟩ := fold_inv L' (ffInsert a P) (fun x hx => hL x (by simp [hx]))
      (pw_ffInsert a (hL a (by simp)) P h1) (ne_nil_ffInsert a P h2)
    refine ⟨r1, r2, r3.trans ?_⟩
    exact ((perm_ffInsert a P).append_left L').trans List.perm_middle


lemma tail_light (m : ℕ) (hm : 1 ≤ m) :
    ∀ P : List (List ℝ), P.Pairwise Rl → (∀ C ∈ P, C ≠ []) →
    (∀ C ∈ P, ∀ x ∈ C, 1 / ((m : ℝ) + 1) < x ∧ x ≤ 1 / (m : ℝ)) →
    (P.filter (fun B => decide (level B < (m : ℝ) / (m + 1)))).length ≤ 1
  | [], _, _, _ => by simp
  | C :: Cs, hpw, hne, hx => by
    rw [List.pairwise_cons] at hpw
    rw [List.filter_cons]
    by_cases hC : level C < (m : ℝ) / (m + 1)
    · have hCs : Cs = [] := by
        rcases Cs with _ | ⟨D, Ds⟩
        · rfl
        · exfalso
          have hD : D ≠ [] := hne D (by simp)
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil D hD
          have h1 : 1 < level C + y := hpw.1 D (by simp) y hy
          have hy2 : y ≤ 1 / (m : ℝ) := (hx D (by simp) y hy).2
          have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
          have hup : level C ≤ C.length * (1 / (m : ℝ)) := by
            unfold level
            have := List.sum_le_card_nsmul C (1 / (m : ℝ)) (fun x hx' => (hx C (by simp) x hx').2)
            simpa [nsmul_eq_mul] using this
          have hlow : (C.length : ℝ) * (1 / ((m : ℝ) + 1)) ≤ level C := by
            unfold level
            have := List.card_nsmul_le_sum C (1 / ((m : ℝ) + 1))
              (fun x hx' => (hx C (by simp) x hx').1.le)
            simpa [nsmul_eq_mul] using this
          have hlt : (C.length : ℝ) < m := by
            have e : (C.length : ℝ) * (1 / ((m : ℝ) + 1)) < (m : ℝ) * (1 / ((m : ℝ) + 1)) := by
              calc _ ≤ level C := hlow
                _ < (m : ℝ) / (m + 1) := hC
                _ = _ := by ring
            exact lt_of_mul_lt_mul_right e (by positivity)
          have hlen : C.length + 1 ≤ m := by
            have : C.length < m := by exact_mod_cast hlt
            omega
          have hlen' : (C.length : ℝ) + 1 ≤ m := by exact_mod_cast hlen
          have : level C + y ≤ 1 := by
            calc level C + y ≤ C.length * (1 / (m : ℝ)) + 1 / (m : ℝ) := by linarith
              _ = ((C.length : ℝ) + 1) / m := by ring
              _ ≤ 1 := by rw [div_le_one hmpos]; exact hlen'
          linarith
      subst hCs
      split_ifs <;> simp
    · simp only [hC, decide_false]
      exact tail_light m hm Cs hpw.2 (fun D hD => hne D (by simp [hD]))
        (fun D hD => hx D (by simp [hD]))

lemma all_light (m : ℕ) (hm : 1 ≤ m) :
    ∀ P : List (List ℝ), P.Pairwise Rl → (∀ C ∈ P, C ≠ []) →
    (∀ C ∈ P, ∀ x ∈ C, 0 < x ∧ x ≤ 1 / (m : ℝ)) →
    (P.filter (fun B => decide (level B < (m : ℝ) / (m + 1)))).length ≤ 2
  | [], _, _, _ => by simp
  | B :: Bs, hpw, hne, hx => by
    rw [List.pairwise_cons] at hpw
    rw [List.filter_cons]
    by_cases hB : level B < (m : ℝ) / (m + 1)
    · simp only [hB, decide_true, if_true, List.length_cons]
      have hbig : ∀ D ∈ Bs, ∀ x ∈ D, 1 / ((m : ℝ) + 1) < x ∧ x ≤ 1 / (m : ℝ) := by
        intro D hD x hxD
        refine ⟨?_, (hx D (by simp [hD]) x hxD).2⟩
        have := hpw.1 D hD x hxD
        have e : (1 : ℝ) / ((m : ℝ) + 1) = 1 - (m : ℝ) / (m + 1) := by
          field_simp
          ring
        rw [e]
        linarith
      have := tail_light m hm Bs hpw.2 (fun D hD => hne D (by simp [hD])) hbig
      omega
    · simp only [hB, decide_false]
      have := all_light m hm Bs hpw.2 (fun D hD => hne D (by simp [hD]))
        (fun D hD => hx D (by simp [hD]))
      simpa using this

end P2M49c4899d

open P2M49c4899d in
open BinPacking.BoundedItems in
theorem solution (m : ℕ) (hm : 1 ≤ m) (L : List ℝ) (hL : IsList L)
    (hLm : ∀ a ∈ L, a ≤ 1 / (m : ℝ)) :
    ((ffPack L).filter (fun B => decide (level B < (m : ℝ) / (m + 1)))).length ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := fold_inv L [] (fun a ha => (hL a ha).1.le) (by simp) (by simp)
  have hP : ∀ C ∈ L.foldl (fun P a => ffInsert a P) [], ∀ x ∈ C, 0 < x ∧ x ≤ 1 / (m : ℝ) := by
    intro C hC x hx
    have hxf : x ∈ (L.foldl (fun P a => ffInsert a P) []).flatten :=
      List.mem_flatten.2 ⟨C, hC, hx⟩
    have hxL : x ∈ L := by simpa using h3.subset hxf
    exact ⟨(hL x hxL).1, hLm x hxL⟩
  exact all_light m hm _ h1 h2 hP
