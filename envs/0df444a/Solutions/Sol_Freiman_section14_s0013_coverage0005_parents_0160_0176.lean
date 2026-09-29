-- Prove2me | solution 1 for Freiman.section14_s0013_coverage0005_parents_0160_0176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T03:00:59.783993+00:00
-- url     : https://prove2.me/submissions/af35c9a5-088d-4c92-94f1-c6d6eb2ee3d9

import Mathlib
import Definitions.Def_Freiman_section14Data

/-! 5463e743 Freiman.section14_s0013_coverage0005_parents_0160_0176: finite catalog check, decided by kernel evaluation.
  * every parent branch except 170 in the slice has a record (state 13, goal 153 = the plan's
    excluded goal, branch -1) located in `section14DataRecords2Part3`;
  * parent 170: every non-automatic goal branch of the plan's 84 specs is recorded; checked by a
    merge-walk (`chkBr`) of each spec's branch list against the sorted recorded pairs. -/

set_option autoImplicit false

namespace S14C_5463e743
open Freiman

/-- recorded `(goal, branch)` pairs of a record list at state `si` for parent `n` -/
def recPairsOf (R : List Section14Record) (si n : ℕ) : List (ℕ × ℤ) :=
  (R.filter (fun r => decide (si ∈ r.states) && decide (n ∈ r.parents))).map (fun r => (r.goal, r.branch))

theorem recorded_of_mem {R : List Section14Record} (hR : ∀ r ∈ R, r ∈ section14Catalog.records)
    {si n g : ℕ} {j : ℤ} (h : (g, j) ∈ recPairsOf R si n) :
    section14Recorded section14Catalog si n g j := by
  unfold recPairsOf at h
  obtain ⟨r, hr, he⟩ := List.mem_map.1 h
  rw [List.mem_filter] at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  simp only [Prod.mk.injEq] at he
  exact ⟨r, hR r hr.1, hr.2.1, hr.2.2, he.1, he.2⟩

theorem records_eq : section14Catalog.records = section14DataRecords1 ++
    (section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++
      section14DataRecords2Part4) ++ section14DataRecords3 ++ section14DataRecords4 := rfl

theorem sub_all : ∀ r ∈ section14Catalog.records, r ∈ section14Catalog.records := fun _ h => h

theorem sub_part3 : ∀ r ∈ section14DataRecords2Part3, r ∈ section14Catalog.records := by
  intro r hr
  rw [records_eq]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr hr))))

/-- drop the entries of a sorted pair list that precede `(g, j)` -/
def skipLt (g : ℕ) (j : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => []
  | p :: L => if p.1 < g ∨ (p.1 = g ∧ p.2 < j) then skipLt g j L else p :: L

theorem skipLt_sub (g : ℕ) (j : ℤ) : ∀ (L : List (ℕ × ℤ)) (x : ℕ × ℤ), x ∈ skipLt g j L → x ∈ L
  | [], x, hx => by simp [skipLt] at hx
  | p :: L, x, hx => by
    unfold skipLt at hx
    split at hx
    · exact List.mem_cons_of_mem _ (skipLt_sub g j L x hx)
    · exact hx

abbrev Br := List CertBound × LowerHistoryComparison

/-- walk a goal's branch list (index `j` onwards) against the sorted recorded pairs `L`:
each branch must be recorded as `(g, j)` or be automatic -/
def chkBr (g : ℕ) : List Br → ℕ → List (ℕ × ℤ) → Bool
  | [], _, _ => true
  | x :: xs, j, L =>
    match skipLt g j L with
    | [] => decide (x.2 = .automatic) && chkBr g xs (j+1) []
    | p :: L' => if p.1 = g ∧ p.2 = (j : ℤ) then chkBr g xs (j+1) L'
      else decide (x.2 = .automatic) && chkBr g xs (j+1) (p :: L')

theorem chkBr_sound (g : ℕ) : ∀ (xs : List Br) (j : ℕ) (L : List (ℕ × ℤ)), chkBr g xs j L = true →
    ∀ (k : ℕ) (hk : k < xs.length), xs[k].2 = .automatic ∨ (g, ((j + k : ℕ) : ℤ)) ∈ L
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | x :: xs, j, L, h, k, hk => by
    unfold chkBr at h
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      cases k with
      | zero => exact Or.inl h.1
      | succ k =>
        have hk' : k < xs.length := by simpa using hk
        rcases chkBr_sound g xs (j+1) [] h.2 k hk' with h1 | h1
        · exact Or.inl (by simpa using h1)
        · simp at h1
    · rename_i p L' hs
      have hsub : ∀ y, y ∈ p :: L' → y ∈ L := fun y hy => skipLt_sub g (j : ℤ) L y (hs ▸ hy)
      split at h
      · rename_i hp
        cases k with
        | zero =>
          refine Or.inr (hsub _ ?_)
          have : p = (g, (j : ℤ)) := Prod.ext hp.1 hp.2
          simp [this]
        | succ k =>
          have hk' : k < xs.length := by simpa using hk
          rcases chkBr_sound g xs (j+1) L' h k hk' with h1 | h1
          · exact Or.inl (by simpa using h1)
          · refine Or.inr (hsub _ (List.mem_cons_of_mem _ ?_))
            have e : j + 1 + k = j + (k + 1) := by omega
            rw [e] at h1
            exact h1
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        cases k with
        | zero => exact Or.inl h.1
        | succ k =>
          have hk' : k < xs.length := by simpa using hk
          rcases chkBr_sound g xs (j+1) (p :: L') h.2 k hk' with h1 | h1
          · exact Or.inl (by simpa using h1)
          · refine Or.inr (hsub _ ?_)
            have e : j + 1 + k = j + (k + 1) := by omega
            rw [e] at h1
            exact h1

/-- recorded pairs at state 13 for parent 170, from the first goal ≥ 154 on (drop 759) -/
def L170 : List (ℕ × ℤ) := [
  (155,0), (155,1), (155,2), (155,3), (155,4), (155,5), (155,6), (155,7), (155,8), (155,9), (155,10), (155,11), (155,12), (155,13), (155,14), (155,15),
  (155,16), (155,17), (155,18), (155,19), (155,20), (155,21), (155,22), (155,23), (155,24), (157,0), (157,1), (157,2), (157,3), (157,4), (157,5), (157,6),
  (157,7), (157,8), (157,9), (157,10), (157,11), (157,12), (157,13), (157,14), (157,15), (157,16), (157,17), (157,18), (157,19), (157,20), (157,21), (157,22),
  (157,23), (157,24), (160,0), (160,1), (160,2), (160,3), (160,4), (160,5), (160,6), (160,7), (160,8), (160,9), (160,10), (160,11), (160,12), (160,13),
  (160,14), (160,15), (163,0), (163,1), (163,2), (163,3), (163,4), (163,5), (163,6), (163,7), (163,8), (163,9), (163,10), (163,11), (163,12), (163,13),
  (163,14), (163,15), (166,0), (166,1), (166,2), (166,3), (166,4), (166,5), (166,6), (166,7), (166,8), (166,9), (166,10), (166,11), (166,12), (166,13),
  (166,14), (166,15), (167,0), (167,1), (167,2), (167,3), (167,4), (167,5), (167,6), (167,7), (167,8), (167,9), (167,10), (167,11), (167,12), (167,13),
  (167,14), (167,15), (171,0), (171,1), (171,2), (171,3), (172,0), (172,1), (172,2), (172,3), (172,4), (172,5), (172,6), (172,7), (172,8), (172,9),
  (172,10), (172,11), (172,12), (172,13), (172,14), (172,15), (175,0), (175,1), (175,2), (175,3), (175,4), (175,5), (175,6), (175,7), (175,8), (175,9),
  (175,10), (175,11), (175,12), (175,13), (175,14), (175,15), (178,0), (178,1), (178,2), (178,3), (178,4), (178,5), (178,6), (178,7), (178,8), (178,9),
  (178,10), (178,11), (178,12), (178,13), (178,14), (178,15), (180,0), (180,1), (180,2), (180,3), (180,4), (180,5), (180,6), (180,7), (180,8), (180,9),
  (180,10), (180,11), (180,12), (180,13), (180,14), (180,15), (183,0), (183,1), (183,2), (183,3), (183,4), (183,5), (183,6), (183,7), (183,8), (183,9),
  (183,10), (183,11), (183,12), (183,13), (183,14), (183,15), (185,0), (185,1), (185,2), (185,3), (185,4), (185,5), (185,6), (185,7), (185,8), (185,9),
  (185,10), (185,11), (185,12), (185,13), (185,14), (185,15), (188,0), (188,1), (188,2), (188,3), (188,4), (188,5), (188,6), (188,7), (188,8), (188,9),
  (188,10), (188,11), (188,12), (188,13), (188,14), (188,15), (190,0), (190,1), (190,2), (190,3), (190,4), (190,5), (190,6), (190,7), (190,8), (190,9),
  (190,10), (190,11), (190,12), (190,13), (190,14), (190,15), (190,16), (190,17), (190,18), (190,19), (190,20), (190,21), (190,22), (190,23), (190,24), (192,0),
  (192,1), (192,2), (192,3), (192,4), (192,5), (192,6), (192,7), (192,8), (192,9), (192,10), (192,11), (192,12), (192,13), (192,14), (192,15), (192,16),
  (192,17), (192,18), (192,19), (192,20), (192,21), (192,22), (192,23), (192,24), (195,0), (195,1), (195,2), (195,3), (195,4), (195,5), (195,6), (195,7),
  (195,8), (195,9), (197,0), (197,1), (197,2), (197,3), (197,4), (197,5), (197,6), (197,7), (197,8), (197,9), (197,10), (197,11), (197,12), (197,13),
  (197,14), (197,15), (197,16), (197,17), (197,18), (197,19), (197,20), (197,21), (197,22), (197,23), (197,24), (200,0), (200,1), (200,2), (200,3), (200,4),
  (200,5), (200,6), (200,7), (200,8), (200,9), (200,10), (200,11), (200,12), (200,13), (200,14), (200,15), (200,16), (200,17), (200,18), (200,19), (200,20),
  (200,21), (200,22), (200,23), (200,24), (202,0), (202,1), (202,2), (202,3), (202,4), (202,5), (202,6), (202,7), (202,8), (202,9), (202,10), (202,11),
  (202,12), (202,13), (202,14), (202,15), (202,16), (202,17), (202,18), (202,19), (202,20), (202,21), (202,22), (202,23), (202,24), (205,0), (205,1), (205,2),
  (205,3), (205,4), (205,5), (205,6), (205,7), (205,8), (205,9), (205,10), (205,11), (205,12), (205,13), (205,14), (205,15), (205,16), (205,17), (205,18),
  (205,19), (205,20), (205,21), (205,22), (205,23), (205,24), (207,0), (207,1), (207,2), (207,3), (207,4), (207,5), (207,6), (207,7), (207,8), (207,9),
  (207,10), (207,11), (207,12), (207,13), (207,14), (207,15), (207,16), (207,17), (207,18), (207,19), (207,20), (207,21), (207,22), (207,23), (207,24), (210,0),
  (210,1), (210,2), (210,3), (210,4), (210,5), (210,6), (210,7), (210,8), (210,9), (210,10), (210,11), (210,12), (210,13), (210,14), (210,15), (213,0),
  (213,1), (213,2), (213,3), (213,4), (213,5), (213,6), (213,7), (213,8), (213,9), (213,10), (213,11), (213,12), (213,13), (213,14), (213,15), (220,0),
  (220,1), (220,2), (220,3), (220,4), (220,5), (220,6), (220,7), (220,8), (220,9), (220,10), (220,11), (220,12), (220,13), (220,14), (220,15), (220,16),
  (220,17), (220,18), (220,19), (221,0), (221,1), (221,2), (221,3), (221,4), (221,5), (221,6), (221,7), (221,8), (221,9), (221,10), (221,11), (221,12),
  (221,13), (221,14), (221,15), (221,16), (221,17), (221,18), (221,19), (221,20), (221,21), (221,22), (221,23), (221,24), (222,0), (222,1), (222,2), (222,3),
  (222,4), (222,5), (222,6), (222,7), (222,8), (222,9), (222,10), (222,11), (222,12), (222,13), (222,14), (222,15), (222,16), (222,17), (222,18), (222,19),
  (222,20), (222,21), (222,22), (222,23), (222,24), (224,0), (224,1), (224,2), (224,3), (224,4), (224,5), (224,6), (224,7), (224,8), (224,9), (224,10),
  (224,11), (224,12), (224,13), (224,14), (224,15), (224,16), (224,17), (224,18), (224,19), (224,20), (224,21), (224,22), (224,23), (224,24), (225,0), (225,1),
  (225,2), (225,3), (225,4), (225,5), (225,6), (225,7), (225,8), (225,9), (225,10), (225,11), (225,12), (225,13), (225,14), (225,15), (225,16), (225,17),
  (225,18), (225,19), (225,20), (225,21), (225,22), (225,23), (225,24), (226,0), (226,1), (226,2), (226,3), (226,4), (226,5), (226,6), (226,7), (226,8),
  (226,9), (227,0), (227,1), (227,2), (227,3), (227,4), (227,5), (227,6), (227,7), (227,8), (227,9), (227,10), (227,11), (227,12), (227,13), (227,14),
  (227,15), (227,16), (227,17), (227,18), (227,19), (227,20), (227,21), (227,22), (227,23), (227,24), (228,0), (228,1), (228,2), (228,3), (228,4), (228,5),
  (228,6), (228,7), (228,8), (228,9), (228,10), (228,11), (228,12), (228,13), (228,14), (228,15), (228,16), (228,17), (228,18), (228,19), (228,20), (228,21),
  (228,22), (228,23), (228,24), (230,0), (230,1), (230,2), (230,3), (230,4), (230,5), (230,6), (230,7), (230,8), (230,9), (230,10), (230,11), (230,12),
  (230,13), (230,14), (230,15), (230,16), (230,17), (230,18), (230,19), (230,20), (230,21), (230,22), (230,23), (230,24), (231,0), (231,1), (231,2), (231,3),
  (231,4), (231,5), (231,6), (231,7), (231,8), (231,9), (231,10), (231,11), (231,12), (231,13), (231,14), (231,15), (231,16), (231,17), (231,18), (231,19),
  (232,0), (232,1), (232,2), (232,3), (232,4), (232,5), (232,6), (232,7), (232,8), (232,9), (232,10), (232,11), (232,12), (232,13), (232,14), (232,15),
  (232,16), (232,17), (232,18), (232,19), (234,0), (234,1), (234,2), (234,3), (234,4), (234,5), (234,6), (234,7), (234,8), (234,9), (234,10), (234,11),
  (234,12), (234,13), (234,14), (234,15), (235,0), (235,1), (235,2), (235,3), (235,4), (235,5), (235,6), (235,7), (235,8), (235,9), (235,10), (235,11),
  (235,12), (235,13), (235,14), (235,15), (236,0), (236,1), (236,2), (236,3), (237,0), (237,1), (237,2), (237,3), (237,4), (237,5), (237,6), (237,7),
  (237,8), (237,9), (237,10), (237,11), (237,12), (237,13), (237,14), (237,15), (238,0), (238,1), (238,2), (238,3), (238,4), (238,5), (238,6), (238,7),
  (238,8), (238,9), (238,10), (238,11), (238,12), (238,13), (238,14), (238,15), (243,5), (243,7), (243,8), (243,9), (243,15), (243,16), (243,17), (243,19),
  (247,0), (247,1), (247,2), (247,3), (247,4), (247,5), (247,6), (247,7), (247,8), (247,9), (247,10), (247,11), (247,12), (247,13), (247,14), (247,15),
  (247,16), (247,17), (247,18), (247,19), (247,20), (247,21), (247,22), (247,23), (247,24), (249,0), (249,1), (249,2), (249,3), (249,4), (249,5), (249,6),
  (249,7), (249,8), (249,9), (249,10), (249,11), (249,12), (249,13), (249,14), (249,15), (249,16), (249,17), (249,18), (249,19), (249,20), (249,21), (249,22),
  (249,23), (249,24), (253,0), (253,1), (253,2), (253,3), (253,4), (253,5), (253,6), (253,7), (253,8), (253,9), (253,10), (253,11), (253,12), (253,13),
  (253,14), (253,15), (253,16), (253,17), (253,18), (253,19), (253,20), (253,21), (253,22), (253,23), (253,24), (258,5), (258,7), (258,8), (258,9), (258,15),
  (258,16), (258,17), (258,19), (260,-1), (636,0), (636,1), (636,2), (636,3), (636,4), (636,5), (636,6), (636,7), (636,8), (636,9), (639,1), (639,3),
  (639,6), (639,8), (640,1), (640,3), (640,6), (640,8), (643,0), (643,1), (643,2), (643,3), (643,4), (643,5), (643,6), (643,7), (643,8), (643,9)]

set_option maxRecDepth 100000 in
theorem L170_eq : (recPairsOf section14Catalog.records 13 170).drop 759 = L170 := by decide +kernel

theorem cover170 (g : ℕ)
    (hc : chkBr g (section14GoalBranches section14Catalog (section14Goal section14Catalog g)) 0 L170 = true) :
    ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog g)).length,
      (section14Branch section14Catalog (section14Goal section14Catalog g) j).2 = .automatic ∨
      section14Recorded section14Catalog 13 170 g j := by
  intro j hj
  have hk := List.mem_range.1 hj
  have h := chkBr_sound g _ 0 L170 hc j hk
  rw [Nat.zero_add] at h
  unfold section14Branch
  rw [Int.toNat_natCast, List.getElem?_eq_getElem hk, Option.getD_some]
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (recorded_of_mem sub_all ?_)
    rw [← L170_eq] at h
    exact List.mem_of_mem_drop h

set_option maxRecDepth 100000 in
theorem len3 : section14DataRecords2Part3.length = 1152 := by decide +kernel

theorem idx_843 : 843 < section14DataRecords2Part3.length := by rw [len3]; decide

set_option maxRecDepth 100000 in
theorem rec_843_hyp : ∀ n ∈ ([168, 169, 172, 173] : List ℕ), ((153 : ℕ), (-1 : ℤ)) ∈ recPairsOf [section14DataRecords2Part3[843]'idx_843] 13 n := by decide +kernel

set_option maxRecDepth 100000 in
theorem rec_843 : ∀ n ∈ ([168, 169, 172, 173] : List ℕ), section14Recorded section14Catalog 13 n 153 (-1) := by
  intro n hn
  refine recorded_of_mem ?_ (rec_843_hyp n hn)
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact sub_part3 _ (List.getElem_mem _)

theorem idx_844 : 844 < section14DataRecords2Part3.length := by rw [len3]; decide

set_option maxRecDepth 100000 in
theorem rec_844_hyp : ∀ n ∈ ([162, 163, 166, 167] : List ℕ), ((153 : ℕ), (-1 : ℤ)) ∈ recPairsOf [section14DataRecords2Part3[844]'idx_844] 13 n := by decide +kernel

set_option maxRecDepth 100000 in
theorem rec_844 : ∀ n ∈ ([162, 163, 166, 167] : List ℕ), section14Recorded section14Catalog 13 n 153 (-1) := by
  intro n hn
  refine recorded_of_mem ?_ (rec_844_hyp n hn)
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact sub_part3 _ (List.getElem_mem _)

theorem idx_850 : 850 < section14DataRecords2Part3.length := by rw [len3]; decide

set_option maxRecDepth 100000 in
theorem rec_850_hyp : ∀ n ∈ ([171, 175] : List ℕ), ((153 : ℕ), (-1 : ℤ)) ∈ recPairsOf [section14DataRecords2Part3[850]'idx_850] 13 n := by decide +kernel

set_option maxRecDepth 100000 in
theorem rec_850 : ∀ n ∈ ([171, 175] : List ℕ), section14Recorded section14Catalog 13 n 153 (-1) := by
  intro n hn
  refine recorded_of_mem ?_ (rec_850_hyp n hn)
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact sub_part3 _ (List.getElem_mem _)

theorem idx_857 : 857 < section14DataRecords2Part3.length := by rw [len3]; decide

set_option maxRecDepth 100000 in
theorem rec_857_hyp : ∀ n ∈ ([174] : List ℕ), ((153 : ℕ), (-1 : ℤ)) ∈ recPairsOf [section14DataRecords2Part3[857]'idx_857] 13 n := by decide +kernel

set_option maxRecDepth 100000 in
theorem rec_857 : ∀ n ∈ ([174] : List ℕ), section14Recorded section14Catalog 13 n 153 (-1) := by
  intro n hn
  refine recorded_of_mem ?_ (rec_857_hyp n hn)
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact sub_part3 _ (List.getElem_mem _)

theorem idx_905 : 905 < section14DataRecords2Part3.length := by rw [len3]; decide

set_option maxRecDepth 100000 in
theorem rec_905_hyp : ∀ n ∈ ([160, 161, 164, 165] : List ℕ), ((153 : ℕ), (-1 : ℤ)) ∈ recPairsOf [section14DataRecords2Part3[905]'idx_905] 13 n := by decide +kernel

set_option maxRecDepth 100000 in
theorem rec_905 : ∀ n ∈ ([160, 161, 164, 165] : List ℕ), section14Recorded section14Catalog 13 n 153 (-1) := by
  intro n hn
  refine recorded_of_mem ?_ (rec_905_hyp n hn)
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact sub_part3 _ (List.getElem_mem _)

set_option maxRecDepth 100000 in
theorem plan_facts : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 5).take 1,
    pl.excludedGoal = 153 ∧ ∀ gs ∈ pl.specs,
      chkBr gs.1 (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)) 0 L170 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem branches : (((section14Parents section14Catalog (section14State section14Catalog 13)).drop 160).take 16).map Section14Parent.branch = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175] := by decide +kernel

end S14C_5463e743

open Freiman in
theorem solution : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 160).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  intro pl hpl b hb
  have hbr : b.branch ∈ ([160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175] : List ℕ) := by
    rw [← S14C_5463e743.branches]
    exact List.mem_map_of_mem hb
  obtain ⟨hex, hchk⟩ := S14C_5463e743.plan_facts pl hpl
  by_cases h170 : b.branch = 170
  · right
    rw [h170]
    intro gs hgs
    exact S14C_5463e743.cover170 gs.1 (hchk gs hgs)
  · left
    rw [hex]
    have hbr' : b.branch ∈ ([160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr ⊢
      omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr'
    rcases hbr' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h]; exact S14C_5463e743.rec_905 160 (by simp)
    · rw [h]; exact S14C_5463e743.rec_905 161 (by simp)
    · rw [h]; exact S14C_5463e743.rec_844 162 (by simp)
    · rw [h]; exact S14C_5463e743.rec_844 163 (by simp)
    · rw [h]; exact S14C_5463e743.rec_905 164 (by simp)
    · rw [h]; exact S14C_5463e743.rec_905 165 (by simp)
    · rw [h]; exact S14C_5463e743.rec_844 166 (by simp)
    · rw [h]; exact S14C_5463e743.rec_844 167 (by simp)
    · rw [h]; exact S14C_5463e743.rec_843 168 (by simp)
    · rw [h]; exact S14C_5463e743.rec_843 169 (by simp)
    · rw [h]; exact S14C_5463e743.rec_850 171 (by simp)
    · rw [h]; exact S14C_5463e743.rec_843 172 (by simp)
    · rw [h]; exact S14C_5463e743.rec_843 173 (by simp)
    · rw [h]; exact S14C_5463e743.rec_857 174 (by simp)
    · rw [h]; exact S14C_5463e743.rec_850 175 (by simp)
