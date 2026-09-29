-- Prove2me | solution 1 for Freiman.trunk_parameter_state
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:29:09.901231+00:00
-- url     : https://prove2.me/submissions/d3f6cb93-ce87-4d6c-bcbb-31a1f5d1aef0

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Freiman
attribute [local instance] Classical.propDecidable

private def smallEnd (w : List ℕ+) : Prop :=
  lowerEnds w [1] ∨ lowerEnds w [2] ∨ lowerEnds w [3]

private lemma smallEnd_of_last (w : List ℕ+) (hn : w ≠ [])
    (hl : ((w.getLast hn : ℕ)) ≤ 3) : smallEnd w := by
  have hp : 0 < (w.getLast hn : ℕ) := PNat.pos _
  have hd : (w.getLast hn : ℕ) = 1 ∨ (w.getLast hn : ℕ) = 2 ∨
      (w.getLast hn : ℕ) = 3 := by omega
  have hs := List.dropLast_append_getLast hn
  rcases hd with h | h | h
  · have he : w.getLast hn = 1 := by exact_mod_cast h
    left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 2 := by exact_mod_cast h
    right; left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 3 := by exact_mod_cast h
    right; right
    exact ⟨w.dropLast, by simpa [he] using hs⟩

private lemma append_smallEnd (w u : List ℕ+) (hw : smallEnd w)
    (hu : ∀ d ∈ u, (d : ℕ) ≤ 3) : smallEnd (w ++ u) := by
  induction u generalizing w with
  | nil => simpa using hw
  | cons a u ih =>
      rw [show w ++ a :: u = (w ++ [a]) ++ u by simp]
      apply ih (w := w ++ [a])
      · have ha := hu a (by simp)
        have hp : 0 < (a : ℕ) := PNat.pos a
        have : (a : ℕ) = 1 ∨ (a : ℕ) = 2 ∨ (a : ℕ) = 3 := by omega
        rcases this with h | h | h
        · have ha1 : a = 1 := by exact_mod_cast h
          left; exact ⟨w, by simp [ha1]⟩
        · have ha2 : a = 2 := by exact_mod_cast h
          right; left; exact ⟨w, by simp [ha2]⟩
        · have ha3 : a = 3 := by exact_mod_cast h
          right; right; exact ⟨w, by simp [ha3]⟩
      · intro d hd
        exact hu d (by simp [hd])

private lemma admissible_smallEnds (p : LowerPair) (ha : lowerAdmissible p) :
    smallEnd p.1 ∧ smallEnd p.2 := by
  rcases ha.1 with ⟨c, hc, u, v, rfl, hu, hv⟩
  have hbase : smallEnd c.1 ∧ smallEnd c.2 := by
    simp only [lowerCores, lowerBaseCores, List.mem_append, List.mem_cons,
      List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with hc | ⟨d, hd, rfl⟩
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        constructor <;> apply smallEnd_of_last <;> simp
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        constructor <;> apply smallEnd_of_last <;> simp
  exact ⟨append_smallEnd _ _ hbase.1 hu, append_smallEnd _ _ hbase.2 hv⟩

private lemma ratio_bounds (w : List ℕ+) (hb : (1/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) :
    (lowerEnds w [1] → (1/2 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) ∧
    (lowerEnds w [2] → (1/3 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/2) ∧
    (lowerEnds w [3] → (1/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/3) := by
  have one (a : ℕ+) (h : lowerEnds w [a]) :
      lowerRatio w = 1 / ((a : ℝ) + lowerRatio (w.dropLast)) := by
    rcases h with ⟨u, hu⟩
    have hlast : (u ++ [a]).dropLast = u := by simp
    subst w
    rw [lowerEarlyTerminal_ratio_append]
    simp [prefixEval, hlast]
  constructor
  · intro h
    have hr := lowerEarlyTerminal_ratio_range w.dropLast
    have he := one 1 h
    constructor
    · rw [he]; norm_num only [PNat.val_ofNat]
      apply (le_div_iff₀ (by linarith : (0:ℝ) < 1 + lowerRatio w.dropLast)).2
      linarith
    · exact hb.2
  constructor
  · intro h
    have hr := lowerEarlyTerminal_ratio_range w.dropLast
    rw [one 2 h]; norm_num only [PNat.val_ofNat]
    constructor
    · apply (le_div_iff₀ (by linarith : (0:ℝ) < 2 + lowerRatio w.dropLast)).2
      linarith
    · apply (div_le_iff₀ (by linarith : (0:ℝ) < 2 + lowerRatio w.dropLast)).2
      linarith
  · intro h
    have hr := lowerEarlyTerminal_ratio_range w.dropLast
    have he := one 3 h
    constructor
    · exact hb.1
    · rw [he]; norm_num only [PNat.val_ofNat]
      apply (div_le_iff₀ (by linarith : (0:ℝ) < 3 + lowerRatio w.dropLast)).2
      linarith

private lemma ratio_31 (w : List ℕ+) (h : lowerEnds w [3,1]) :
    (3/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5 := by
  rcases h with ⟨u, rfl⟩
  rw [lowerEarlyTerminal_ratio_append]
  have hr := lowerEarlyTerminal_ratio_range u
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, prefixEval,
    PNat.val_ofNat]
  change (3/4 : ℝ) ≤ prefixEval [1,3] (lowerRatio u) ∧
    prefixEval [1,3] (lowerRatio u) ≤ 4/5
  rw [prefixEval, prefixEval, prefixEval]
  norm_num only [PNat.val_ofNat]
  have hd : (0:ℝ) < 3 + lowerRatio u := by linarith
  have he : (0:ℝ) < 1 + 1 / (3 + lowerRatio u) := by positivity
  constructor
  · field_simp [ne_of_gt hd]
    nlinarith
  · field_simp [ne_of_gt hd]
    nlinarith

private lemma incompatible_last {w : List ℕ+} {a b : ℕ+}
    (ha : lowerEnds w [a]) (hb : lowerEnds w [b]) (hne : a ≠ b) : False := by
  rcases ha with ⟨u, hu⟩; rcases hb with ⟨v, hv⟩
  have hh := congrArg List.getLast? (hu.trans hv.symm)
  simp at hh
  exact hne hh

private lemma context_one (w : List ℕ+) (h : lowerEnds w [1])
    (hn : ¬ lowerEnds w [3,1]) : lowerHistorySuffixContext w [1] := by
  refine ⟨h, ?_, ?_⟩
  · constructor
    · intro h3; exact (incompatible_last h h3 (by norm_num)).elim
    · intro hf
      exact (incompatible_last (⟨[], rfl⟩ : lowerEnds ([1] : List ℕ+) [1]) hf
        (by norm_num)).elim
  · constructor
    · exact fun hw => (hn hw).elim
    · intro hf
      rcases hf with ⟨u, hu⟩
      have hl := congrArg List.length hu
      simp at hl

private lemma context_two (w : List ℕ+) (h : lowerEnds w [2]) :
    lowerHistorySuffixContext w [2] := by
  refine ⟨h, ?_, ?_⟩
  · constructor
    · intro h3; exact (incompatible_last h h3 (by norm_num)).elim
    · intro hf
      exact (incompatible_last (⟨[], rfl⟩ : lowerEnds ([2] : List ℕ+) [2]) hf
        (by norm_num)).elim
  · constructor
    · intro h31
      have h1 : lowerEnds w [1] := by rcases h31 with ⟨u,rfl⟩; exact ⟨u ++ [3], by simp⟩
      exact (incompatible_last h h1 (by norm_num)).elim
    · intro hf
      have h2 : lowerEnds ([2] : List ℕ+) [2] := ⟨[], rfl⟩
      have h1 : lowerEnds ([2] : List ℕ+) [1] := by
        rcases hf with ⟨u, hu⟩
        exact ⟨u ++ [3], by simpa using hu⟩
      exact (incompatible_last h2 h1 (by norm_num)).elim

private lemma context_three (w : List ℕ+) (h : lowerEnds w [3]) :
    lowerHistorySuffixContext w [3] := by
  refine ⟨h, ?_, ?_⟩
  · exact ⟨fun _ => ⟨[], rfl⟩, fun _ => h⟩
  · constructor
    · intro h31
      have h1 : lowerEnds w [1] := by rcases h31 with ⟨u,rfl⟩; exact ⟨u ++ [3], by simp⟩
      exact (incompatible_last h h1 (by norm_num)).elim
    · intro hf
      have h3 : lowerEnds ([3] : List ℕ+) [3] := ⟨[], rfl⟩
      have h1 : lowerEnds ([3] : List ℕ+) [1] := by
        rcases hf with ⟨u, hu⟩
        exact ⟨u ++ [3], by simpa using hu⟩
      exact (incompatible_last h3 h1 (by norm_num)).elim

private lemma context_31 (w : List ℕ+) (h : lowerEnds w [3,1]) :
    lowerHistorySuffixContext w [3,1] := by
  refine ⟨h, ?_, ?_⟩
  · constructor
    · intro h3
      have h1 : lowerEnds w [1] := by rcases h with ⟨u,rfl⟩; exact ⟨u ++ [3], by simp⟩
      exact (incompatible_last h1 h3 (by norm_num)).elim
    · intro h3
      have h1 : lowerEnds ([3,1] : List ℕ+) [1] := ⟨[3], rfl⟩
      exact (incompatible_last h1 h3 (by norm_num)).elim
  · exact ⟨fun _ => ⟨[], rfl⟩, fun _ => h⟩

private lemma side_choice (w : List ℕ+)
    (hs : smallEnd w) (hb : (1/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) :
    (lowerHistorySuffixContext w [1] ∧ (1/2 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) ∨
    (lowerHistorySuffixContext w [2] ∧ (1/3 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/2) ∨
    (lowerHistorySuffixContext w [3] ∧ (1/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/3) ∨
    (lowerHistorySuffixContext w [3,1] ∧ (3/4 : ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) := by
  by_cases h31 : lowerEnds w [3,1]
  · exact Or.inr (Or.inr (Or.inr ⟨context_31 w h31, ratio_31 w h31⟩))
  · rcases hs with h1 | h2 | h3
    · exact Or.inl ⟨context_one w h1 h31, (ratio_bounds w hb).1 h1⟩
    · exact Or.inr (Or.inl ⟨context_two w h2, (ratio_bounds w hb).2.1 h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨context_three w h3, (ratio_bounds w hb).2.2 h3⟩))

private theorem trunk_parameter_state_core (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (he : ¬ lowerMixed p) :
    ∃ k : Fin 16, lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context ∧
    certRectangleMem (trunkCatalog.states k).rectangle (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) := by
  let Z := lowerNormalize p
  have hend0 := admissible_smallEnds p hs.1
  have hend : smallEnd Z.1 ∧ smallEnd Z.2 := by
    unfold Z lowerNormalize
    split <;> simp_all
  have hpbox : lowerParameterBox p := hs.2.2.2
  have hbox : lowerParameterBox Z := by
    unfold Z lowerNormalize
    split <;> simp_all [lowerParameterBox]
  have hpar : Z.1.length % 2 = Z.2.length % 2 := by
    unfold lowerMixed at he
    have hp : p.1.length % 2 = p.2.length % 2 := not_ne_iff.mp he
    unfold Z lowerNormalize
    split <;> simp_all
  have hl := side_choice Z.1 hend.1 ⟨hbox.1,hbox.2.1⟩
  have hr := side_choice Z.2 hend.2 ⟨hbox.2.2.1,hbox.2.2.2⟩
  rcases hl with hl | hl | hl | hl <;> rcases hr with hr | hr | hr | hr
  · refine ⟨0, ?_⟩
    change lowerHistoryContextFits Z ⟨([1],[1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/2,4/5,1/2,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨1, ?_⟩
    change lowerHistoryContextFits Z ⟨([1],[2]),(false,false)⟩ ∧
      certRectangleMem ⟨1/2,4/5,1/3,1/2⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨2, ?_⟩
    change lowerHistoryContextFits Z ⟨([1],[3]),(false,false)⟩ ∧
      certRectangleMem ⟨1/2,4/5,1/4,1/3⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨3, ?_⟩
    change lowerHistoryContextFits Z ⟨([1],[3,1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/2,4/5,3/4,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨4, ?_⟩
    change lowerHistoryContextFits Z ⟨([2],[1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/3,1/2,1/2,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨5, ?_⟩
    change lowerHistoryContextFits Z ⟨([2],[2]),(false,false)⟩ ∧
      certRectangleMem ⟨1/3,1/2,1/3,1/2⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨6, ?_⟩
    change lowerHistoryContextFits Z ⟨([2],[3]),(false,false)⟩ ∧
      certRectangleMem ⟨1/3,1/2,1/4,1/3⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨7, ?_⟩
    change lowerHistoryContextFits Z ⟨([2],[3,1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/3,1/2,3/4,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨8, ?_⟩
    change lowerHistoryContextFits Z ⟨([3],[1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/4,1/3,1/2,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨9, ?_⟩
    change lowerHistoryContextFits Z ⟨([3],[2]),(false,false)⟩ ∧
      certRectangleMem ⟨1/4,1/3,1/3,1/2⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨10, ?_⟩
    change lowerHistoryContextFits Z ⟨([3],[3]),(false,false)⟩ ∧
      certRectangleMem ⟨1/4,1/3,1/4,1/3⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨11, ?_⟩
    change lowerHistoryContextFits Z ⟨([3],[3,1]),(false,false)⟩ ∧
      certRectangleMem ⟨1/4,1/3,3/4,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨12, ?_⟩
    change lowerHistoryContextFits Z ⟨([3,1],[1]),(false,false)⟩ ∧
      certRectangleMem ⟨3/4,4/5,1/2,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨13, ?_⟩
    change lowerHistoryContextFits Z ⟨([3,1],[2]),(false,false)⟩ ∧
      certRectangleMem ⟨3/4,4/5,1/3,1/2⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨14, ?_⟩
    change lowerHistoryContextFits Z ⟨([3,1],[3]),(false,false)⟩ ∧
      certRectangleMem ⟨3/4,4/5,1/4,1/3⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))
  · refine ⟨15, ?_⟩
    change lowerHistoryContextFits Z ⟨([3,1],[3,1]),(false,false)⟩ ∧
      certRectangleMem ⟨3/4,4/5,3/4,4/5⟩ (lowerRatio Z.1) (lowerRatio Z.2)
    refine ⟨⟨hl.1,hr.1,by simp [hpar]⟩, ?_⟩
    simpa [certRectangleMem] using And.intro hl.2.1 (And.intro hl.2.2 (And.intro hr.2.1 hr.2.2))


theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (he : ¬ lowerMixed p) :
    ∃ k : Fin 16, lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context ∧
    certRectangleMem (trunkCatalog.states k).rectangle (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) := by
  exact trunk_parameter_state_core t p hs he

#print axioms solution
