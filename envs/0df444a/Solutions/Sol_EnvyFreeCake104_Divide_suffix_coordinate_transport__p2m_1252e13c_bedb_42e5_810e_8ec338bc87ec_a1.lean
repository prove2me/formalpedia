-- Prove2me | solution 1 for EnvyFreeCake104.Divide.suffix_coordinate_transport__p2m_1252e13c_bedb_42e5_810e_8ec338bc87ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:52:23.950759+00:00
-- url     : https://prove2.me/submissions/c483b7c3-09f4-417b-b9eb-9471dd012fd8

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    (Q : Piece) (p : Pos) (hp : Q.ValidPos p) (q : Pos) :
    ((suffixList Q p).ValidPos q ↔
      Q.ValidPos (p.1 + q.1, q.2) ∧ (q.1 = 0 → p.2 ≤ q.2)) ∧
    ((suffixList Q p).ValidPos q →
      suffixList (suffixList Q p) q = suffixList Q (p.1 + q.1, q.2)) := by
  induction Q generalizing p q with
  | nil =>
      simp [Piece.ValidPos] at hp
  | cons I L ih =>
      rcases p with ⟨k, x⟩
      cases k with
      | zero =>
          have hax : I.a ≤ x := by simpa using hp.2.1
          rcases q with ⟨j, y⟩
          cases j with
          | zero =>
              constructor
              · simp [suffixList, Piece.ValidPos]
                constructor
                · rintro ⟨hxy, hyb⟩
                  exact ⟨⟨le_trans hax hxy, hyb⟩, hxy⟩
                · rintro ⟨⟨_, hyb⟩, hxy⟩
                  exact ⟨hxy, hyb⟩
              · simp [suffixList]
          | succ j =>
              simp [suffixList, Piece.ValidPos]
      | succ k =>
          have hp' : Piece.ValidPos L (k, x) := by
            simpa [Piece.ValidPos] using hp
          have hs (n : ℕ) (y : ℝ) :
              suffixList (I :: L) (n + 1, y) = suffixList L (n, y) := by
            simp only [suffixList, Prod.fst, Prod.snd, List.length_cons,
              Nat.succ_lt_succ_iff, List.getD_cons_succ, List.drop_succ_cons]
          have hv (n : ℕ) (y : ℝ) :
              Piece.ValidPos (I :: L) (n + 1, y) ↔ Piece.ValidPos L (n, y) := by
            simp only [Piece.ValidPos, Prod.fst, Prod.snd, List.length_cons,
              Nat.succ_lt_succ_iff, List.getD_cons_succ]
          simp only [Prod.fst, Prod.snd, Nat.succ_add, hs, hv]
          exact ih (k, x) hp' q
