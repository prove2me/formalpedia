-- Prove2me | solution 1 for Freiman.lower_h5_right3_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T20:54:45.987481+00:00
-- url     : https://prove2.me/submissions/6f778d5c-9122-4530-a7c3-5bd95cfe5ec0

import Definitions.Def_Freiman_lowerH5Verification
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

private theorem equal_endpoint_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨ lowerNaturalShort p.2 upper = true) :
    lowerEndpoint p upper =
      4 + prefixEval (p.1 ++ lowerEndpointSuffix p.1 upper (lowerNaturalShort p.1 upper)) lowerTau +
        prefixEval (p.2 ++ lowerEndpointSuffix p.2 upper (lowerNaturalShort p.2 upper)) lowerTau := by
  rcases p with ⟨u,v⟩
  simp only [Prod.fst,Prod.snd] at hp hn ⊢
  unfold lowerEndpoint lowerEndpointWords
  simp only [hp,↓reduceIte]
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords,lowerNormalize,hw,hn]
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords,lowerNormalize,hw,hn] <;> ring

private theorem suffix_three_one (u : List ℕ+) : lowerEnds (u++[3,1]) [3,1] := by
  exact List.suffix_append _ _

private theorem suffix_three (u : List ℕ+) : lowerEnds (u++[3]) [3] := by
  exact List.suffix_append _ _

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ lowerEnds (w ++ [2]) [3] := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_312 (w : List ℕ+) :
    ¬ lowerEnds (w ++ [3,1,2]) [3] := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem local_lower_identity (p : LowerPair) (hm : lowerMixed p)
    (hl : lowerL p) (hr : lowerEnds (lowerNormalize p).2 [3]) :
    lowerLocalLower p ([2],[]) = lowerH5ParentLower p := by
  rcases p with ⟨u,v⟩
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · have hn : lowerNormalize (u,v) = (u,v) := by simp [lowerNormalize,hw]
    simp only [lowerL,hn,Prod.fst,Prod.snd] at hl hr
    rcases hl with ⟨u',rfl⟩
    rcases hr with ⟨v',rfl⟩
    have hchild : lowerChild (u'++[3,1],v'++[3]) ([2],[]) =
        (u'++[3,1,2],v'++[3]) := by simp [lowerChild,hn,List.append_assoc]
    have hpar : (u'++[3,1,2]).length % 2 = (v'++[3]).length % 2 := by
      simp only [lowerMixed,Prod.fst,Prod.snd,List.length_append,List.length_cons,List.length_nil] at hm ⊢
      omega
    unfold lowerLocalLower lowerH5ParentLower
    rw [hn,hchild]
    by_cases he : (u'++[3,1]).length % 2 = 0
    · have hu : u'.length % 2 = 0 := by simpa using he
      have hv : v'.length % 2 = 0 := by simp only [List.length_append,List.length_cons,List.length_nil] at hpar; omega
      have hnat : lowerNaturalShort (v'++[3]) false = true := by
        simp [lowerNaturalShort,Nat.add_mod,hv,suffix_three]
      rw [if_pos he,if_pos he,equal_endpoint_natural _ _ hpar (Or.inr hnat)]
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,lowerNaturalShort,
        lowerEndpointSuffix,lowerNormalize,hw,lowerMixed,Nat.add_mod,hu,hv,
        suffix_three,suffix_three_one,not_suffix_three_append_two,not_suffix_three_append_312,List.append_assoc]
    · have hu : u'.length % 2 = 1 := by simp only [List.length_append,List.length_cons,List.length_nil] at he; omega
      have hv : v'.length % 2 = 1 := by simp only [List.length_append,List.length_cons,List.length_nil] at hpar; omega
      have hnat : lowerNaturalShort (v'++[3]) true = true := by
        simp [lowerNaturalShort,Nat.add_mod,hv,suffix_three]
      rw [if_neg he,if_neg he,equal_endpoint_natural _ _ hpar (Or.inr hnat)]
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,lowerNaturalShort,
        lowerEndpointSuffix,lowerNormalize,hw,lowerMixed,Nat.add_mod,hu,hv,
        suffix_three,suffix_three_one,not_suffix_three_append_two,not_suffix_three_append_312,List.append_assoc]
  · have hn : lowerNormalize (u,v) = (v,u) := by simp [lowerNormalize,hw]
    simp only [lowerL,hn,Prod.fst,Prod.snd] at hl hr
    rcases hl with ⟨v',rfl⟩
    rcases hr with ⟨u',rfl⟩
    have hchild : lowerChild (u'++[3],v'++[3,1]) ([2],[]) =
        (v'++[3,1,2],u'++[3]) := by simp [lowerChild,hn,List.append_assoc]
    have hpar : (v'++[3,1,2]).length % 2 = (u'++[3]).length % 2 := by
      simp only [lowerMixed,Prod.fst,Prod.snd,List.length_append,List.length_cons,List.length_nil] at hm ⊢
      omega
    unfold lowerLocalLower lowerH5ParentLower
    rw [hn,hchild]
    by_cases he : (v'++[3,1]).length % 2 = 0
    · have hv : v'.length % 2 = 0 := by simpa using he
      have hu : u'.length % 2 = 0 := by simp only [List.length_append,List.length_cons,List.length_nil] at hpar; omega
      have hnat : lowerNaturalShort (u'++[3]) false = true := by
        simp [lowerNaturalShort,Nat.add_mod,hu,suffix_three]
      rw [if_pos he,if_pos he,equal_endpoint_natural _ _ hpar (Or.inr hnat)]
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,lowerNaturalShort,
        lowerEndpointSuffix,lowerNormalize,hw,lowerMixed,Nat.add_mod,hu,hv,
        suffix_three,suffix_three_one,not_suffix_three_append_two,not_suffix_three_append_312,List.append_assoc]
      ring
    · have hv : v'.length % 2 = 1 := by simp only [List.length_append,List.length_cons,List.length_nil] at he; omega
      have hu : u'.length % 2 = 1 := by simp only [List.length_append,List.length_cons,List.length_nil] at hpar; omega
      have hnat : lowerNaturalShort (u'++[3]) true = true := by
        simp [lowerNaturalShort,Nat.add_mod,hu,suffix_three]
      rw [if_neg he,if_neg he,equal_endpoint_natural _ _ hpar (Or.inr hnat)]
      simp [lowerEndpoint,lowerEndpointWords,lowerNaturalWords,lowerNaturalShort,
        lowerEndpointSuffix,lowerNormalize,hw,lowerMixed,Nat.add_mod,hu,hv,
        suffix_three,suffix_three_one,not_suffix_three_append_two,not_suffix_three_append_312,List.append_assoc]
      ring


private theorem right3_anchor (p : LowerPair) (t : ℝ) (hs : lowerState t p)
    (ha : lowerH5Active p) (hr : lowerEnds (lowerNormalize p).2 [3]) :
    lowerH5LowerBound p t := by
  unfold lowerH5LowerBound
  rw [local_lower_identity p ha.1 ha.2.2.2 hr]
  have ht := hs.2.2.1
  change lowerEndpoint p false ≤ t ∧ t ≤ lowerEndpoint p true at ht
  unfold lowerH5ParentLower lowerLocalCoordinate
  split_ifs
  · exact ht.1
  · exact neg_le_neg ht.2


theorem solution (p : LowerPair) (t : ℝ) (hs : lowerState t p) (ha : lowerH5Active p)
    (hr : lowerEnds (lowerNormalize p).2 [3]) : lowerH5LowerBound p t := by
  exact right3_anchor p t hs ha hr

#print axioms solution
