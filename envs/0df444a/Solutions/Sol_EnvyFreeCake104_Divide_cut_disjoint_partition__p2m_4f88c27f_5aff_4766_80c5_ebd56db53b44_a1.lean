-- Prove2me | solution 1 for EnvyFreeCake104.Divide.cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:51:43.215444+00:00
-- url     : https://prove2.me/submissions/c82f9c23-d8ec-4dd3-a431-66d7dbc8a307

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

private theorem set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2
    (I : Interval) (Q : Piece) : Piece.toSet (I :: Q) = I.toSet ∪ (Piece.toSet Q) := by
  ext y
  simp [Piece.toSet]

private theorem wf_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2
    (I : Interval) (Q : Piece) :
    Piece.WF (I :: Q) ↔
      (0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1) ∧ Piece.WF Q ∧ Disjoint I.toSet (Piece.toSet Q) := by
  constructor
  · rintro ⟨hb, hp⟩
    rcases List.pairwise_cons.mp hp with ⟨hd, ht⟩
    refine ⟨hb I (by simp), ⟨?_, ht⟩, ?_⟩
    · intro J hJ
      exact hb J (by simp [hJ])
    · apply Set.disjoint_left.mpr
      intro y hy hyQ
      rcases hyQ with ⟨J, hJ, hyJ⟩
      exact Set.disjoint_left.mp (hd J hJ) hy hyJ
  · rintro ⟨hI, ⟨hb, ht⟩, hd⟩
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, ht⟩⟩
    · intro J hJ
      rcases List.mem_cons.mp hJ with hJ | hJ
      · subst J
        exact hI
      · exact hb J hJ
    · intro J hJ
      apply Set.disjoint_left.mpr
      intro y hy hyJ
      exact Set.disjoint_left.mp hd hy ⟨J, hJ, hyJ⟩

private theorem interval_split__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2
    (I : Interval) (x : ℝ) (ha : I.a ≤ x) (hb : x ≤ I.b) (h1 : I.b ≤ 1) :
    Disjoint (Interval.toSet ⟨I.a, x⟩) (Interval.toSet ⟨x, I.b⟩) ∧
      (Interval.toSet ⟨I.a, x⟩) ∪ (Interval.toSet ⟨x, I.b⟩) = I.toSet := by
  constructor
  · apply Set.disjoint_left.mpr
    intro y hl hr
    dsimp [Interval.toSet] at hl hr
    split_ifs at hl hr <;>
      simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind
  · ext y
    simp only [Set.mem_union, Interval.toSet]
    split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind

theorem solution
    (Q : Piece) (hQ : Q.WF) (p : Pos) (hp : Q.ValidPos p) :
    (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
    Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
    (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by
  rcases p with ⟨k, x⟩
  revert hQ hp
  induction Q generalizing k with
  | nil =>
    intro hQ hp
    simp [Piece.ValidPos] at hp
  | cons I Q ih =>
    intro hQ hp
    rcases (wf_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2 I Q).mp hQ with
      ⟨hI, hQ', hd⟩
    cases k with
    | zero =>
      have ha : I.a ≤ x := by simpa [Piece.ValidPos] using hp.2.1
      have hb : x ≤ I.b := by simpa [Piece.ValidPos] using hp.2.2
      let L : Interval := ⟨I.a, x⟩
      let R : Interval := ⟨x, I.b⟩
      have hs := interval_split__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2
        I x ha hb hI.2.2
      have hLR : Disjoint L.toSet R.toSet := hs.1
      have hU : L.toSet ∪ R.toSet = I.toSet := hs.2
      have hLsub : L.toSet ⊆ I.toSet := by
        intro y hy
        rw [← hU]
        exact Or.inl hy
      have hRsub : R.toSet ⊆ I.toSet := by
        intro y hy
        rw [← hU]
        exact Or.inr hy
      have hLQ : Disjoint L.toSet (Piece.toSet Q) := Disjoint.mono_left hLsub hd
      have hRQ : Disjoint R.toSet (Piece.toSet Q) := Disjoint.mono_left hRsub hd
      have hpre : prefixList (I :: Q) (0, x) = [L] := by simp [prefixList, L]
      have hsuf : suffixList (I :: Q) (0, x) = R :: Q := by simp [suffixList, R]
      rw [hpre, hsuf]
      have hnil : Piece.WF [] := by simp [Piece.WF]
      have hL : Piece.WF [L] := by
        apply (wf_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2 L []).mpr
        exact ⟨⟨hI.1, ha, hb.trans hI.2.2⟩, hnil, by simp [Piece.toSet]⟩
      have hR : Piece.WF (R :: Q) := by
        apply (wf_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2 R Q).mpr
        exact ⟨⟨hI.1.trans ha, hb, hI.2.2⟩, hQ', hRQ⟩
      have hsingle : Piece.toSet [L] = L.toSet := by
        ext y
        simp [Piece.toSet]
      refine ⟨hL, hR, ?_, ?_⟩
      · rw [hsingle, set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2]
        apply Set.disjoint_left.mpr
        intro y hy hz
        rcases hz with hz | hz
        · exact Set.disjoint_left.mp hLR hy hz
        · exact Set.disjoint_left.mp hLQ hy hz
      · rw [hsingle, set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2,
          ← Set.union_assoc, hU,
          set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2]
    | succ k =>
      have hp' : Piece.ValidPos Q (k, x) := by
        simpa [Piece.ValidPos] using hp
      obtain ⟨hA, hB, hAB, hU⟩ := ih k hQ' hp'
      have hk : k < Q.length := hp'.1
      have hpre : prefixList (I :: Q) (k + 1, x) = I :: prefixList Q (k, x) := by
        simp [prefixList, hk, Nat.succ_lt_succ hk]
      have hsuf : suffixList (I :: Q) (k + 1, x) = suffixList Q (k, x) := by
        simp [suffixList, hk, Nat.succ_lt_succ hk, Nat.add_assoc]
      have hIA : Disjoint I.toSet (prefixList Q (k, x)).toSet := by
        apply Set.disjoint_left.mpr
        intro y hy hz
        apply Set.disjoint_left.mp hd hy
        rw [← hU]
        exact Or.inl hz
      have hIB : Disjoint I.toSet (suffixList Q (k, x)).toSet := by
        apply Set.disjoint_left.mpr
        intro y hy hz
        apply Set.disjoint_left.mp hd hy
        rw [← hU]
        exact Or.inr hz
      rw [hpre, hsuf]
      refine ⟨(wf_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2 _ _).mpr
        ⟨hI, hA, hIA⟩, hB, ?_, ?_⟩
      · rw [set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2]
        apply Set.disjoint_left.mpr
        intro y hy hz
        rcases hy with hy | hy
        · exact Set.disjoint_left.mp hIB hy hz
        · exact Set.disjoint_left.mp hAB hy hz
      · rw [set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2,
          Set.union_assoc, hU,
          set_cons__p2m_2412efb0_419b_4f88_9b27_9423e1e4ae36_a2]
