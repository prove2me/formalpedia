-- Prove2me | solution 1 for BinPacking.BoundedItems.ff_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:47:26.381+00:00
-- url     : https://prove2.me/submissions/f0b1a855-403d-4497-a0c8-6b1a6d7a1a4d

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

set_option autoImplicit false

namespace P2M114c8e6c

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

lemma big (α : ℝ) (m : ℕ) (hα : 0 < α) (hmα : (m : ℝ) * α ≤ 1) :
    ∀ P : List (List ℝ), P.Pairwise Rl → (∀ C ∈ P, C ≠ []) →
    (∀ C ∈ P, ∀ x ∈ C, 1 / ((m : ℝ) + 1) < x ∧ x ≤ α) →
    ((P.length : ℝ) - 1) * ((m : ℝ) / (m + 1)) ≤ (P.map level).sum
  | [], _, _, _ => by
    simp
    positivity
  | C :: Cs, hpw, hne, hx => by
    rw [List.pairwise_cons] at hpw
    have ih := big α m hα hmα Cs hpw.2 (fun D hD => hne D (by simp [hD]))
      (fun D hD => hx D (by simp [hD]))
    have hpos : 0 ≤ level C := by
      unfold level
      exact List.sum_nonneg (fun x hx' => (lt_trans (by positivity) (hx C (by simp) x hx').1).le)
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rcases Cs with _ | ⟨D, Ds⟩
    · simpa using hpos
    · have hD : D ≠ [] := hne D (by simp)
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil D hD
      have h1 : 1 < level C + y := hpw.1 D (by simp) y hy
      have hyα : y ≤ α := (hx D (by simp) y hy).2
      have hup : level C ≤ C.length * α := by
        unfold level
        have := List.sum_le_card_nsmul C α (fun x hx' => (hx C (by simp) x hx').2)
        simpa [nsmul_eq_mul] using this
      have hlow : (C.length : ℝ) * (1 / ((m : ℝ) + 1)) ≤ level C := by
        unfold level
        have := List.card_nsmul_le_sum C (1 / ((m : ℝ) + 1))
          (fun x hx' => (hx C (by simp) x hx').1.le)
        simpa [nsmul_eq_mul] using this
      have hc : (m : ℝ) ≤ C.length := by
        have hlt : (m : ℝ) < C.length + 1 := by
          by_contra hcon
          rw [not_lt] at hcon
          have := mul_le_mul_of_nonneg_right hcon hα.le
          nlinarith
        have : m < C.length + 1 := by exact_mod_cast hlt
        exact_mod_cast Nat.lt_succ_iff.1 this
      have ht : (m : ℝ) / (m + 1) ≤ level C := by
        calc (m : ℝ) / (m + 1) = m * (1 / ((m : ℝ) + 1)) := by ring
          _ ≤ C.length * (1 / ((m : ℝ) + 1)) := by gcongr
          _ ≤ level C := hlow
      simp only [List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
      push_cast at ih ⊢
      nlinarith

lemma count (α : ℝ) (m : ℕ) (hα : 0 < α) (hmα : (m : ℝ) * α ≤ 1) :
    ∀ P : List (List ℝ), P.Pairwise Rl → (∀ C ∈ P, C ≠ []) →
    (∀ C ∈ P, ∀ x ∈ C, 0 < x ∧ x ≤ α) →
    ((P.length : ℝ) - 2) * ((m : ℝ) / (m + 1)) ≤ (P.map level).sum
  | [], _, _, _ => by
    simp
    positivity
  | B :: Bs, hpw, hne, hx => by
    rw [List.pairwise_cons] at hpw
    have hposB : 0 ≤ level B := by
      unfold level
      exact List.sum_nonneg (fun x hx' => (hx B (by simp) x hx').1.le)
    have ht0 : 0 ≤ (m : ℝ) / (m + 1) := by positivity
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    by_cases hB : (m : ℝ) / (m + 1) ≤ level B
    · have ih := count α m hα hmα Bs hpw.2 (fun D hD => hne D (by simp [hD]))
        (fun D hD => hx D (by simp [hD]))
      push_cast
      nlinarith
    · rw [not_le] at hB
      have hbig : ∀ D ∈ Bs, ∀ x ∈ D, 1 / ((m : ℝ) + 1) < x ∧ x ≤ α := by
        intro D hD x hxD
        refine ⟨?_, (hx D (by simp [hD]) x hxD).2⟩
        have := hpw.1 D hD x hxD
        have e : (1 : ℝ) / ((m : ℝ) + 1) = 1 - (m : ℝ) / (m + 1) := by
          field_simp
          ring
        rw [e]
        linarith
      have hb := big α m hα hmα Bs hpw.2 (fun D hD => hne D (by simp [hD])) hbig
      push_cast
      nlinarith

lemma sum_le_opt (L : List ℝ) (hL : IsList L) : L.sum ≤ optBins L := by
  unfold optBins
  have hne : ({b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}).Nonempty := by
    refine ⟨L.length, id, fun j => ?_⟩
    have : Finset.univ.filter (fun i => (id i : Fin L.length) = j) = {j} := by
      ext i
      simp
    rw [this, Finset.sum_singleton]
    exact (hL _ (List.get_mem L j)).2
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  have key : L.sum = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i := by
    rw [Finset.sum_fiberwise]
    simp
  rw [key]
  calc _ ≤ ∑ _j : Fin (sInf {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hf j)
    _ = _ := by simp

end P2M114c8e6c

open P2M114c8e6c in
open BinPacking.BoundedItems in
theorem solution (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (L : List ℝ) (hL : IsList L) (hLα : ∀ a ∈ L, a ≤ α) :
    (FF L : ℝ) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) + 2 := by
  have hmα : (m : ℝ) * α ≤ 1 := by
    rw [hm]
    have := Nat.floor_le (inv_nonneg.2 hα.le)
    calc (⌊α⁻¹⌋₊ : ℝ) * α ≤ α⁻¹ * α := by gcongr
      _ = 1 := inv_mul_cancel₀ hα.ne'
  have hm2 : 2 ≤ m := by
    rw [hm]
    apply Nat.le_floor
    have : (1 / 2 : ℝ)⁻¹ ≤ α⁻¹ := inv_anti₀ hα hα2
    norm_num at this ⊢
    exact this
  obtain ⟨h1, h2, h3⟩ := fold_inv L [] (fun a ha => (hL a ha).1.le) (by simp) (by simp)
  have hFF : FF L = (L.foldl (fun P a => ffInsert a P) []).length := rfl
  have hP : ∀ C ∈ L.foldl (fun P a => ffInsert a P) [], ∀ x ∈ C, 0 < x ∧ x ≤ α := by
    intro C hC x hx
    have hxf : x ∈ (L.foldl (fun P a => ffInsert a P) []).flatten :=
      List.mem_flatten.2 ⟨C, hC, hx⟩
    have hxL : x ∈ L := by simpa using h3.subset hxf
    exact ⟨(hL x hxL).1, hLα x hxL⟩
  have hcount := count α m hα hmα _ h1 h2 hP
  have hsum : ((L.foldl (fun P a => ffInsert a P) []).map level).sum = L.sum := by
    have e1 := h3.sum_eq
    simp only [List.flatten_nil, List.append_nil, List.sum_flatten] at e1
    exact e1
  have hopt := sum_le_opt L hL
  rw [hFF]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set k : ℝ := ((L.foldl (fun P a => ffInsert a P) []).length : ℝ)
  have hk : (k - 2) * ((m : ℝ) / (m + 1)) ≤ (optBins L : ℝ) := by
    rw [← hsum] at hopt
    exact hcount.trans hopt
  have e1 : (k - 2) * ((m : ℝ) / (m + 1)) * (m + 1) = (k - 2) * m := by
    field_simp
  have h4 : (k - 2) * m ≤ (optBins L : ℝ) * (m + 1) := by
    rw [← e1]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  rw [div_mul_eq_mul_div, ← sub_le_iff_le_add, le_div_iff₀ hmpos]
  linarith
