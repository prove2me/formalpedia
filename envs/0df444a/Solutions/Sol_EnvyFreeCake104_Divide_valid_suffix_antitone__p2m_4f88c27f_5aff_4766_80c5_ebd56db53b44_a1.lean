-- Prove2me | solution 1 for EnvyFreeCake104.Divide.valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:34:55.952239+00:00
-- url     : https://prove2.me/submissions/a445eb63-d399-4f32-8dc9-b8350e336eb3

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    (Q : Piece) (p q : Pos) (hp : Q.ValidPos p) (hq : Q.ValidPos q)
    (hpq : p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) :
    (suffixList Q q).toSet ⊆ (suffixList Q p).toSet := by
  -- This also respects the exceptional closed right endpoint at 1.
  have interval_mono (a c b : ℝ) (hac : a ≤ c) :
      (Interval.mk c b).toSet ⊆ (Interval.mk a b).toSet := by
    intro x hx
    simp only [Interval.toSet] at hx ⊢
    split_ifs at hx ⊢ <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind
  have hpidx : p.1 < Q.length := hp.1
  have hqidx : q.1 < Q.length := hq.1
  intro x hx
  change ∃ I ∈ suffixList Q p, x ∈ I.toSet
  change ∃ I ∈ suffixList Q q, x ∈ I.toSet at hx
  rcases hx with ⟨I, hI, hx⟩
  rw [suffixList, if_pos hqidx] at hI
  rcases List.mem_cons.mp hI with hI | hI
  · subst I
    rcases hpq with hlt | ⟨heq, hcoord⟩
    · -- The interval at q occurs in the unchanged tail after p.
      have hmem : Q.getD q.1 default ∈ Q.drop q.1 := by
        rw [List.getD_eq_getElem Q default hqidx, List.drop_eq_getElem_cons hqidx]
        exact List.mem_cons_self
      refine ⟨Q.getD q.1 default, ?_, ?_⟩
      · rw [suffixList, if_pos hpidx]
        apply List.mem_cons_of_mem
        exact List.drop_subset_drop_left Q (by omega : p.1 + 1 ≤ q.1) hmem
      · exact interval_mono (Q.getD q.1 default).a q.2
          (Q.getD q.1 default).b hq.2.1 hx
    · -- At the same index, only the left endpoint advances.
      refine ⟨Interval.mk p.2 (Q.getD p.1 default).b, ?_, ?_⟩
      · rw [suffixList, if_pos hpidx]
        exact List.mem_cons_self
      · apply interval_mono p.2 q.2 (Q.getD p.1 default).b hcoord
        simpa only [← heq] using hx
  · -- All intervals strictly after q are also strictly after p.
    have hle : p.1 + 1 ≤ q.1 + 1 := by
      rcases hpq with hlt | ⟨heq, hcoord⟩ <;> omega
    refine ⟨I, ?_, hx⟩
    rw [suffixList, if_pos hpidx]
    apply List.mem_cons_of_mem
    exact List.drop_subset_drop_left Q hle hI
