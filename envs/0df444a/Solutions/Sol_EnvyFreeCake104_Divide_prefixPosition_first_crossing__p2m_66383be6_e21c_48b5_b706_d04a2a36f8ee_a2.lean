-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:48:06.728195+00:00
-- url     : https://prove2.me/submissions/3baefb46-04be-415a-901e-36c12481e41e

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
import Theorems.Thm_EnvyFreeCake104_Divide_alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem solution
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (hrecord : ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (Q : Piece) (hQ : Q.WF) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet) :
    ∃ p : Pos,
      (match findInterval s i Q 0 w with
        | none => if w ≤ 0 then some (Q.length, (0 : ℝ)) else none
        | some (k, r) =>
          if r ≤ 0 then some (k, (Q.getD k default).a)
          else
            match findCell s i
                ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
                  c < (Q.getD k default).b)).sort (· ≤ ·)) r with
            | none => none
            | some (c, t) => some (k, cutAnswer V i c t)) = some p ∧
      (Q = [] ∨ Q.ValidPos p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      ∀ q : Pos, Q.ValidPos q →
        w ≤ (V i).value (prefixList Q q).toSet →
        p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2) := by

  classical
  by_cases hnil : Q = []
  · subst Q
    have hempty : Piece.toSet ([] : Piece) = ∅ := by
      ext x
      simp [Piece.toSet]
    have hzero : (V i).value (Piece.toSet ([] : Piece)) = 0 := by
      simp [hempty, Valuation.value]
    have hw0 : w = 0 := le_antisymm (by simpa only [hzero] using hwQ) hw
    subst w
    refine ⟨(0, 0), ?_, Or.inl rfl, ?_, ?_⟩
    · simp [findInterval]
    · simpa [prefixList] using hzero
    · intro q hq
      exact (Nat.not_lt_zero q.1 hq.1).elim
  · have hbudget : w ≤ s.pieceVal i Q := by
      rw [hrecord Q hQ hQs]
      exact hwQ
    obtain ⟨k, r, hfind, hk, hr, hrI, hbalance, hearlier⟩ :=
      EnvyFreeCake104.Divide.intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2 s i Q hnil w hw hbudget
    have hmem : Q.getD k default ∈ Q := by
      rw [List.getD_eq_getElem Q default hk]
      exact List.getElem_mem hk
    have hI := hQ.1 _ hmem
    have hends := hQs _ hmem
    obtain ⟨x, hsel, hxa, hxb, hval, hleast⟩ :=
      EnvyFreeCake104.Divide.alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
        V N s hs i hi hcut (Q.getD k default) hI hends.1 hends.2 r hr hrI
    have hp : Q.ValidPos (k, x) := ⟨hk, hxa, hxb⟩
    refine ⟨(k, x), ?_, Or.inr hp, ?_, ?_⟩
    · simp only [hfind]
      by_cases hr0 : r ≤ 0
      · rw [if_pos hr0] at hsel ⊢
        exact congrArg (Option.map (fun y : ℝ => (k, y))) hsel
      · rw [if_neg hr0] at hsel ⊢
        cases hc : findCell s i
            ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
              c < (Q.getD k default).b)).sort (· ≤ ·)) r with
        | none =>
          rw [hc] at hsel
          cases hsel
        | some ct =>
          rcases ct with ⟨c, t⟩
          rw [hc] at hsel
          exact congrArg (Option.map (fun y : ℝ => (k, y))) hsel
    · rw [(EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
        V s i hrecord Q hQ hQs (k, x) hp).1]
      change s.pieceVal i (Q.take k) +
        (V i).value (Set.Ico (Q.getD k default).a x) = w
      rw [hval]
      exact hbalance
    · intro q hq hwq
      rcases lt_trichotomy k q.1 with hlt | heq | hgt
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, ?_⟩
        apply hleast q.2
        · change (Q.getD k default).a ≤ q.2 ∧ q.2 ≤ (Q.getD k default).b
          simpa only [heq] using hq.2
        · have hform := (EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
            V s i hrecord Q hQ hQs q hq).1
          rw [← heq] at hform
          linarith
      · have hbound := (EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
          V s i hrecord Q hQ hQs q hq).2
        have hstrict := hearlier q.1 hgt
        exfalso
        linarith

