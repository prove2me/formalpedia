-- Prove2me | solution 1 for EnvyFreeCake104.Divide.claim_7
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T18:29:00.98826+00:00
-- url     : https://prove2.me/submissions/7a5316e2-4069-4663-8aae-f64a9068416e

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup ∧ ag.toFinset = N)
    (hpc : pc.Nodup ∧ pc.toFinset = N) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ Z : ι → Set ℝ, EnvyFree V N Z →
        (∀ p ∈ ag.zip pc, IsSuffix (Z p.1) (P p.2)) →
        ∀ p ∈ ag.zip pc, Z p.1 ⊆ (Y p.1).toSet := by
  classical
  have hmem : ∀ p ∈ ag.zip pc, p.1 ∈ N ∧ p.2 ∈ N := by
    intro p hp
    have hm := List.of_mem_zip hp
    constructor
    · rw [← hag.2]
      exact List.mem_toFinset.mpr hm.1
    · rw [← hpc.2]
      exact List.mem_toFinset.mpr hm.2
  obtain ⟨Y, R, s', tr, hrun, hmax⟩ :=
    EnvyFreeCake104.Divide.candidate_greedy_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
      V N
      (EnvyFreeCake104.Divide.prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
        V N)
      P hP s hs hPs ag pc hag.1 hmem o
  refine ⟨Y, R, s', tr, hrun, ?_⟩
  intro Z hEF hZ
  have walk : ∀ (rest before : List (ι × ι)),
      ag.zip pc = before ++ rest →
      (∀ q ∈ before, ∀ i ∈ N, (V i).value (Z q.1) ≤
        (V i).value (Y q.1).toSet) →
      ∀ q ∈ rest, Z q.1 ⊆ (Y q.1).toSet := by
    intro rest
    induction rest with
    | nil =>
        intro before heq hprev q hq
        simp at hq
    | cons p tail ih =>
        intro before heq hprev
        have hp : p ∈ ag.zip pc := by
          rw [heq]
          simp
        have hhead :
            Z p.1 ⊆ (Y p.1).toSet ∧
            ∀ i ∈ N, (V i).value (Z p.1) ≤ (V i).value (Y p.1).toSet := by
          apply hmax before p tail heq (Z p.1) (hZ p hp)
          intro q hq
          have hqmem : q ∈ ag.zip pc := by
            rw [heq]
            exact List.mem_append_left _ hq
          exact (hEF q.1 (hmem q hqmem).1 p.1 (hmem p hp).1).trans
            (hprev q hq q.1 (hmem q hqmem).1)
        have htail : ∀ q ∈ tail, Z q.1 ⊆ (Y q.1).toSet := by
          apply ih (before ++ [p])
          · simpa only [List.append_assoc, List.singleton_append] using heq
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hprev q hq
            · have hqp : q = p := List.mem_singleton.mp hq
              subst q
              exact hhead.2
        intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst q
          exact hhead.1
        · exact htail q hq
  apply walk (ag.zip pc) []
  · rfl
  · intro q hq
    simp at hq

