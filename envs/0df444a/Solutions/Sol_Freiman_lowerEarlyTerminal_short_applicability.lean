-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_applicability
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T09:49:42.488325+00:00
-- url     : https://prove2.me/submissions/35578312-6c27-4b55-b5c5-b30c23e3d3ed

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.IntervalCases

open Freiman

namespace M7App

lemma at_list (p : LowerPair) (bs : List CertBound)
    (h : ∀ b ∈ bs, lowerEarlyTerminalAt p [b]) : lowerEarlyTerminalAt p bs := by
  intro x hx
  exact h x hx x (List.mem_singleton_self x)

lemma flip_bound (p : LowerPair) (t : CertThreshold)
    (h : ¬ lowerEarlyTerminalAt p [(⟨true,false,t⟩ : CertBound)]) :
    lowerEarlyTerminalAt p [(⟨false,false,t⟩ : CertBound)] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  have h' : ¬ (certThresholdVal t (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) ≤
      lowerEarlyTerminalQ p) := by
    intro hx
    exact h (fun b hb => by
      simp only [List.mem_singleton] at hb
      subst hb
      exact hx)
  show lowerEarlyTerminalQ p ≤ certThresholdVal t (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)
  exact le_of_lt (lt_of_not_ge h')

/-- the normalized pair has a wide left side, so the base normalization bound holds. -/
lemma wh_nil (hw : LowerHistoryWidthLaw) (p : LowerPair) :
    lowerEarlyTerminalAt p [(⟨false,false,lowerHistoryWH ([],[])⟩ : CertBound)] := by
  have hq := (hw (lowerNormalize p) ([],[])).1
  have hle : lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
    unfold lowerNormalize
    split_ifs with h
    · exact h
    · exact le_of_lt (lt_of_not_ge h)
  exact hq.mp (by simpa using hle)

/-- the three catalogue-independent bounds plus the `A9` bound of a non-`[3]` context. -/
lemma base_holds (hp : LowerEarlyTerminalParameterLaws) (hw : LowerHistoryWidthLaw)
    (p : LowerPair) (hd : lowerEarlyDomain p) (C : LowerEarlyTerminalCatalog) :
    ∀ b ∈ lowerEarlyTerminalBase C, lowerEarlyTerminalAt p [b] := by
  have hH7 : lowerEarlyTerminalAt p [lowerEarlyTerminalH7] := (hp p).1.mpr hd.2.1
  have hH18 : lowerEarlyTerminalAt p [lowerEarlyTerminalH18] := (hp p).2.1.mpr hd.2.2.2.2.2.1
  have hA9 : lowerEarlyTerminalAt p [lowerEarlyTerminalA9] := (hp p).2.2.1.mpr hd.2.2.1
  have hWH := wh_nil hw p
  intro b hb
  unfold lowerEarlyTerminalBase at hb
  rw [List.mem_append] at hb
  rcases hb with hb | hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hH7
    · exact hH18
    · exact hWH
  · split_ifs at hb
    · simp at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      exact hA9

end M7App

open M7App in
theorem solution (hp : LowerEarlyTerminalParameterLaws) (hdomain : LowerEarlyTerminalDomainLaws)
    (hw : LowerHistoryWidthLaw) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode < 2)
    (hbranch : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34) :
    ∃ i : Fin 3, lowerEarlyTerminalApplied p (lowerEarlyTerminalShortCatalog i) mode := by
  obtain ⟨hshort, -⟩ := hdomain t p hs hd
  obtain ⟨i, hmat, hrect⟩ := hshort
  refine ⟨i, hmat, hrect, ?_⟩
  interval_cases mode
  · rw [if_pos rfl] at hbranch
    have hH27 : lowerEarlyTerminalAt p [{lowerEarlyTerminalH27 with lower := true}] :=
      (hp p).2.2.2.1.mpr hbranch
    refine at_list p _ ?_
    intro b hb
    unfold lowerEarlyTerminalHyp at hb
    rw [List.mem_append] at hb
    rcases hb with hb | hb
    · exact base_holds hp hw p hd _ b hb
    · norm_num at hb
      rcases hb with rfl
      exact hH27
  · norm_num at hbranch
    obtain ⟨hb27, hb34⟩ := hbranch
    have hH27 : lowerEarlyTerminalAt p [lowerEarlyTerminalH27] :=
      flip_bound p _ (fun hx => hb27 ((hp p).2.2.2.1.mp hx))
    have hH34 : lowerEarlyTerminalAt p [{lowerEarlyTerminalH34 with lower := true}] :=
      (hp p).2.2.2.2.1.mpr hb34
    refine at_list p _ ?_
    intro b hb
    unfold lowerEarlyTerminalHyp at hb
    rw [List.mem_append] at hb
    rcases hb with hb | hb
    · exact base_holds hp hw p hd _ b hb
    · norm_num at hb
      rcases hb with rfl | rfl
      · exact hH27
      · exact hH34
