-- Prove2me | solution 1 for EnvyFreeCake104.Divide.ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:46:29.249766+00:00
-- url     : https://prove2.me/submissions/6801988b-d249-428a-8780-259e57815d54

import Definitions.Def_EnvyFreeCake104_Divide_Model
import Theorems.Thm_EnvyFreeCake104_Divide_valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution (Q : Piece) (hQ : Q.WF) :
    IsSuffix Q.toSet Q ∧
    (∀ S : Set ℝ, IsSuffix S Q → S ⊆ Q.toSet) ∧
    ∀ p : Pos, (prefixList Q p).WF → (suffixList Q p).WF →
      (∀ S : Set ℝ, IsSuffix S (suffixList Q p) → IsSuffix S Q) ∧
      (∀ S : Set ℝ, IsSuffix S Q → S ⊆ (suffixList Q p).toSet →
        IsSuffix S (suffixList Q p)) := by
  classical
  have initialEq : ∀ (I : Interval) (L : Piece),
      suffixList (I :: L) (0, I.a) = I :: L := by
    intro I L
    cases I
    simp [suffixList]
  have whole : ∀ (P : Piece), P.WF → IsSuffix P.toSet P := by
    intro P hP
    cases P with
    | nil =>
        left
        ext x
        simp [Piece.toSet]
    | cons I L =>
        right
        refine ⟨(0, I.a), ?_, ?_⟩
        · exact ⟨by simp, le_rfl, (hP.1 I (by simp)).2.1⟩
        · rw [initialEq]
  refine ⟨whole Q hQ, ?_, ?_⟩
  · intro S hS
    rcases hS with hS | ⟨p, hp, hS⟩
    · rw [hS]
      exact Set.empty_subset _
    · rw [hS]
      cases Q with
      | nil =>
          have hf : False := by simpa [Piece.ValidPos] using hp.1
          exact hf.elim
      | cons I L =>
          have h0 : Piece.ValidPos (I :: L) (0, I.a) :=
            ⟨by simp, le_rfl, (hQ.1 I (by simp)).2.1⟩
          have hle : (0 : ℕ) < p.1 ∨ (0 = p.1 ∧ I.a ≤ p.2) := by
            by_cases hz : p.1 = 0
            · right
              refine ⟨hz.symm, ?_⟩
              simpa [hz] using hp.2.1
            · left
              omega
          have h := valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
            (I :: L) (0, I.a) p h0 hp hle
          simpa only [initialEq] using h
  · intro p hpref hsuf
    by_cases hk : p.1 < Q.length
    · have ha := hpref.1 ⟨(Q.getD p.1 default).a, p.2⟩
          (by simp [prefixList, hk])
      have hb := hsuf.1 ⟨p.2, (Q.getD p.1 default).b⟩
          (by simp [suffixList, hk])
      have hp : Q.ValidPos p := ⟨hk, ha.2.1, hb.2.1⟩
      constructor
      · intro S hS
        rcases hS with he | ⟨q, hq, he⟩
        · exact Or.inl he
        · have ht :=
            suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
              Q p hp q
          exact Or.inr ⟨(p.1 + q.1, q.2), (ht.1.mp hq).1,
            he.trans (congrArg Piece.toSet (ht.2 hq))⟩
      · intro S hS hsub
        rcases hS with he | ⟨q, hq, he⟩
        · exact Or.inl he
        · by_cases hpq : p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)
          · have hsum : p.1 + (q.1 - p.1) = q.1 := by
              rcases hpq with hlt | ⟨heq, _⟩ <;> omega
            have hproj : (p.1 + (q.1 - p.1), q.2) = q := by
              apply Prod.ext
              · exact hsum
              · rfl
            let r : Pos := (q.1 - p.1, q.2)
            have ht :=
              suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
                Q p hp r
            have hr : (suffixList Q p).ValidPos r := by
              apply ht.1.mpr
              constructor
              · change Q.ValidPos (p.1 + (q.1 - p.1), q.2)
                rw [hproj]
                exact hq
              · change q.1 - p.1 = 0 → p.2 ≤ q.2
                intro hz
                rcases hpq with hlt | ⟨_, hle⟩
                · omega
                · exact hle
            have heq := ht.2 hr
            change suffixList (suffixList Q p) r =
              suffixList Q (p.1 + (q.1 - p.1), q.2) at heq
            rw [hproj] at heq
            exact Or.inr ⟨r, hr, he.trans (congrArg Piece.toSet heq).symm⟩
          · have hqp : q.1 < p.1 ∨ (q.1 = p.1 ∧ q.2 ≤ p.2) := by
              by_cases hlt : q.1 < p.1
              · exact Or.inl hlt
              · have hn : ¬ p.1 < q.1 := fun h ↦ hpq (Or.inl h)
                have heq : q.1 = p.1 := by omega
                right
                refine ⟨heq, ?_⟩
                by_contra hnle
                exact hpq (Or.inr ⟨heq.symm, le_of_lt (lt_of_not_ge hnle)⟩)
            have hback : (suffixList Q p).toSet ⊆ S := by
              rw [he]
              exact valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
                Q q p hq hp hqp
            have hEq : S = (suffixList Q p).toSet := Set.Subset.antisymm hsub hback
            rw [hEq]
            exact whole _ hsuf
    · have hem : suffixList Q p = [] := by simp [suffixList, hk]
      constructor
      · intro S hS
        rcases hS with he | ⟨q, hq, _⟩
        · exact Or.inl he
        · have hf : False := by simpa [hem, Piece.ValidPos] using hq.1
          exact hf.elim
      · intro S _ hsub
        left
        apply Set.Subset.antisymm
        · simpa [hem, Piece.toSet] using hsub
        · exact Set.empty_subset _
