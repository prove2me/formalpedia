-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_source_fork_no_ties_from_ranges
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T15:47:59.839997+00:00
-- url     : https://prove2.me/submissions/e8c1cd24-f5fb-4de2-aadd-4740667c4f0e

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

namespace M7FK

lemma pe_nonneg (w : List ℕ+) : ∀ (x : ℝ), 0 ≤ x → 0 ≤ prefixEval w x := by
  induction w with
  | nil => intro x hx; simpa [prefixEval] using hx
  | cons a w ih =>
      intro x hx
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have h := ih x hx
      have hd : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      simp only [prefixEval]
      positivity

lemma pe_mem (w : List ℕ+) : ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
    (prefixEval w 0 ≤ prefixEval w x ∧ prefixEval w x ≤ prefixEval w 1) ∨
    (prefixEval w 1 ≤ prefixEval w x ∧ prefixEval w x ≤ prefixEval w 0) := by
  induction w with
  | nil => intro x h0 h1; exact Or.inl ⟨h0, h1⟩
  | cons a w ih =>
      intro x h0 h1
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
          1/(((a:ℕ):ℝ)+t) ≤ 1/(((a:ℕ):ℝ)+s) := by
        intro s t hs hst
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have n0 := pe_nonneg w 0 le_rfl
      have n1 := pe_nonneg w 1 zero_le_one
      have nx := pe_nonneg w x h0
      simp only [prefixEval]
      rcases ih x h0 h1 with ⟨p, q⟩ | ⟨p, q⟩
      · exact Or.inr ⟨key _ _ nx q, key _ _ n0 p⟩
      · exact Or.inl ⟨key _ _ nx q, key _ _ n1 p⟩

lemma pe_range (w : List ℕ+) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    min (prefixEval w 0) (prefixEval w 1) ≤ prefixEval w x ∧
    prefixEval w x ≤ max (prefixEval w 0) (prefixEval w 1) := by
  rcases pe_mem w x hx0 hx1 with ⟨p,q⟩|⟨p,q⟩
  · exact ⟨le_trans (min_le_left _ _) p, le_trans q (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) p, le_trans q (le_max_left _ _)⟩

lemma ratcf_cast (w : List ℕ+) : ∀ (x : ℚ),
    ((lowerEarlyTerminalRatCF w x : ℚ) : ℝ) = prefixEval w ((x : ℝ)) := by
  induction w with
  | nil => intro x; simp [lowerEarlyTerminalRatCF, prefixEval]
  | cons a w ih =>
      intro x
      have hstep : lowerEarlyTerminalRatCF (a :: w) x
          = 1 / (((a:ℕ):ℚ) + lowerEarlyTerminalRatCF w x) := rfl
      have hpe : prefixEval (a :: w) ((x:ℝ)) = 1 / (((a:ℕ):ℝ) + prefixEval w ((x:ℝ))) := rfl
      rw [hstep, hpe, ← ih x]
      push_cast
      ring

lemma range_lo (w : List ℕ+) :
    (((lowerEarlyTerminalRatioRange w).1 : ℚ) : ℝ)
      = min (prefixEval w 0) (prefixEval w 1) := by
  simp only [lowerEarlyTerminalRatioRange, Rat.cast_min, ratcf_cast]
  norm_num

lemma range_hi (w : List ℕ+) :
    (((lowerEarlyTerminalRatioRange w).2 : ℚ) : ℝ)
      = max (prefixEval w 0) (prefixEval w 1) := by
  simp only [lowerEarlyTerminalRatioRange, Rat.cast_max, ratcf_cast]
  norm_num

lemma range_nonneg (w : List ℕ+) : (0:ℝ) ≤ (((lowerEarlyTerminalRatioRange w).1 : ℚ) : ℝ) := by
  rw [range_lo]
  exact le_min (pe_nonneg w 0 le_rfl) (pe_nonneg w 1 zero_le_one)

lemma ratio_bounds (w : List ℕ+) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (((lowerEarlyTerminalRatioRange w).1 : ℚ) : ℝ) ≤ prefixEval w x ∧
    prefixEval w x ≤ (((lowerEarlyTerminalRatioRange w).2 : ℚ) : ℝ) := by
  rw [range_lo, range_hi]; exact pe_range w x hx0 hx1

lemma reflect_anti (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (4-3*y)/(3+4*y) ≤ (4-3*x)/(3+4*x) := by
  have h1 : (0:ℝ) < 3 + 4*x := by linarith
  have h2 : (0:ℝ) < 3 + 4*y := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

lemma apart_ne (A B : ℚ × ℚ) (h : lowerEarlyTerminalRangesApart A B)
    (u v : ℝ) (hu1 : (A.1:ℝ) ≤ u) (hu2 : u ≤ (A.2:ℝ))
    (hv1 : (B.1:ℝ) ≤ v) (hv2 : v ≤ (B.2:ℝ)) : u ≠ v := by
  rcases h with h | h
  · have hh : (A.2:ℝ) < (B.1:ℝ) := by exact_mod_cast h
    intro he; rw [he] at hu2; linarith
  · have hh : (B.2:ℝ) < (A.1:ℝ) := by exact_mod_cast h
    intro he; rw [he] at hu1; linarith

end M7FK

open M7FK

theorem solution (hf : lowerEarlyTerminalForkRangesValid)
    (hr : ∀ w : List ℕ+, 0 ≤ lowerRatio w ∧ lowerRatio w ≤ 1)
    (ha : ∀ u v : List ℕ+, lowerRatio (u++v) = prefixEval v.reverse (lowerRatio u))
    (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l) :
    ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d) := by
  classical
  -- the generic separation principle
  have master : ∀ (U V : List ℕ+) (cs : LowerEarlyTerminalForkCase),
      cs ∈ lowerEarlyTerminalForkCases →
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      lowerRatio U = prefixEval (lowerEarlyTerminalRatioWords cs).1 x →
      lowerRatio V = prefixEval (lowerEarlyTerminalRatioWords cs).2 y →
      ¬ lowerEarlyTerminalForkExceptional cs →
      lowerWidth U ≠ lowerWidth V := by
    intro U V cs hmem x y hx0 hx1 hy0 hy1 hU hV hexc hw
    obtain ⟨hap1, hap2⟩ := hf cs hmem hexc
    obtain ⟨hU1, hU2⟩ := ratio_bounds (lowerEarlyTerminalRatioWords cs).1 x hx0 hx1
    obtain ⟨hV1, hV2⟩ := ratio_bounds (lowerEarlyTerminalRatioWords cs).2 y hy0 hy1
    rw [← hU] at hU1 hU2
    rw [← hV] at hV1 hV2
    have hA0 : (0:ℝ) ≤ (((lowerEarlyTerminalRatioRange
        (lowerEarlyTerminalRatioWords cs).1).1 : ℚ) : ℝ) := range_nonneg _
    rcases ht U V hw with heq | hrot
    · exact apart_ne _ _ hap1 _ _ hU1 hU2 hV1 hV2 heq
    · have hcast1 : ((lowerEarlyTerminalReflectRatio
          (lowerEarlyTerminalRatioRange (lowerEarlyTerminalRatioWords cs).1).2 : ℚ) : ℝ)
          = (4 - 3*(((lowerEarlyTerminalRatioRange
              (lowerEarlyTerminalRatioWords cs).1).2 : ℚ):ℝ))
            /(3 + 4*(((lowerEarlyTerminalRatioRange
              (lowerEarlyTerminalRatioWords cs).1).2 : ℚ):ℝ)) := by
        simp only [lowerEarlyTerminalReflectRatio]; push_cast; ring
      have hcast2 : ((lowerEarlyTerminalReflectRatio
          (lowerEarlyTerminalRatioRange (lowerEarlyTerminalRatioWords cs).1).1 : ℚ) : ℝ)
          = (4 - 3*(((lowerEarlyTerminalRatioRange
              (lowerEarlyTerminalRatioWords cs).1).1 : ℚ):ℝ))
            /(3 + 4*(((lowerEarlyTerminalRatioRange
              (lowerEarlyTerminalRatioWords cs).1).1 : ℚ):ℝ)) := by
        simp only [lowerEarlyTerminalReflectRatio]; push_cast; ring
      refine (apart_ne _ _ hap2 (lowerRatio V) (lowerRatio V) ?_ ?_ hV1 hV2) rfl
      · show ((lowerEarlyTerminalReflectRatio _ : ℚ) : ℝ) ≤ _
        rw [hcast1, hrot]
        exact reflect_anti _ _ (le_trans hA0 hU1) hU2
      · show _ ≤ ((lowerEarlyTerminalReflectRatio _ : ℚ) : ℝ)
        rw [hcast2, hrot]
        exact reflect_anti _ _ hA0 hU1
  -- structure of the normalized pair
  obtain ⟨⟨⟨core, hcmem, uu, vv, hpc, huu, hvv⟩, -⟩, -, -, -⟩ := hs
  have hcores : ∀ r ∈ lowerCores, r.1 ≠ [] ∧ r.2 ≠ [] ∧
      (∀ b ∈ r.1.getLast?, (b:ℕ) ≤ 3) ∧ (∀ b ∈ r.2.getLast?, (b:ℕ) ≤ 3) := by decide
  obtain ⟨hne1, hne2, hla1, hla2⟩ := hcores core hcmem
  have concat_of : ∀ (cr u : List ℕ+), cr ≠ [] → (∀ b ∈ cr.getLast?, (b:ℕ) ≤ 3) →
      (∀ b ∈ u, (b:ℕ) ≤ 3) → ∃ z : List ℕ+, ∃ a : ℕ+, cr ++ u = z ++ [a] ∧ (a:ℕ) ≤ 3 := by
    intro cr u hcr hlast hu
    rcases List.eq_nil_or_concat u with rfl | ⟨u', a, rfl⟩
    · rcases List.eq_nil_or_concat cr with rfl | ⟨z, a, rfl⟩
      · exact absurd rfl hcr
      · exact ⟨z, a, by simp, hlast a (by simp)⟩
    · exact ⟨cr ++ u', a, by simp, hu a (by simp)⟩
  have hlast1 : ∃ z : List ℕ+, ∃ a : ℕ+, p.1 = z ++ [a] ∧ (a:ℕ) ≤ 3 := by
    rw [hpc]; exact concat_of _ _ hne1 hla1 huu
  have hlast2 : ∃ z : List ℕ+, ∃ a : ℕ+, p.2 = z ++ [a] ∧ (a:ℕ) ≤ 3 := by
    rw [hpc]; exact concat_of _ _ hne2 hla2 hvv
  have hqlast : ∃ z : List ℕ+, ∃ a : ℕ+, (lowerNormalize p).1 = z ++ [a] ∧ (a:ℕ) ≤ 3 := by
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · simpa [lowerNormalize, hh] using hlast1
    · simpa [lowerNormalize, hh] using hlast2
  obtain ⟨q1, cc, hq1, hcc3⟩ := hqlast
  obtain ⟨q2, hq2⟩ := hd.2.2.2.2.1
  have hpar0 : p.1.length % 2 = p.2.length % 2 := by
    have := hd.1; unfold lowerMixed at this; omega
  have hqpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · simpa [lowerNormalize, hh] using hpar0
    · simpa [lowerNormalize, hh] using hpar0.symm
  -- the label is a native one
  have hlnat : l ∈ lowerEarlyTerminalNativeLabels := by
    have hmm := hn
    unfold lowerEarlyTerminalNative lowerEarlyList at hmm
    split_ifs at hmm <;> (fin_cases hmm <;> decide)
  -- the left context digit
  have hccmem : cc ∈ ([1,2,3] : List ℕ+) := by
    have h1 : 1 ≤ (cc:ℕ) := cc.property
    have hcases : (cc:ℕ) = 1 ∨ (cc:ℕ) = 2 ∨ (cc:ℕ) = 3 := by omega
    rcases hcases with h|h|h
    · simp [show cc = 1 from PNat.coe_injective h]
    · simp [show cc = 2 from PNat.coe_injective h]
    · simp [show cc = 3 from PNat.coe_injective h]
  -- shape of the fork pair
  have hFP1 : ∀ dd : ℕ+, (lowerEarlyTerminalForkPair p l true dd).1
      = (lowerNormalize p).1 ++ l.1.reverse := fun _ => rfl
  have hFP2 : ∀ dd : ℕ+, (lowerEarlyTerminalForkPair p l true dd).2
      = (lowerNormalize p).2 ++ (l.2 ++ [dd]) := fun _ => rfl
  have hrat1 : ∀ (e : List ℕ+), lowerRatio ((lowerNormalize p).1 ++ l.1.reverse ++ e)
      = prefixEval (e.reverse ++ l.1 ++ [cc]) (lowerRatio q1) := by
    intro e
    have hsplit : (lowerNormalize p).1 ++ l.1.reverse ++ e = q1 ++ ([cc] ++ l.1.reverse ++ e) := by
      rw [hq1]; simp
    rw [hsplit, ha]
    congr 1
    simp
  have hrat2 : ∀ (dd : ℕ+) (e : List ℕ+),
      lowerRatio ((lowerNormalize p).2 ++ (l.2 ++ [dd]) ++ e)
      = prefixEval (e.reverse ++ [dd] ++ l.2.reverse ++ [1,3]) (lowerRatio q2) := by
    intro dd e
    have hsplit : (lowerNormalize p).2 ++ (l.2 ++ [dd]) ++ e
        = q2 ++ ([3,1] ++ (l.2 ++ [dd]) ++ e) := by
      rw [← hq2]; simp
    rw [hsplit, ha]
    congr 1
    simp
  have mem_case : ∀ (dd : ℕ+) (v : Fin 3), dd ∈ ([1,2] : List ℕ+) →
      v ∈ (if (l.1.length + l.2.length + 1) % 2 = 0 then [0] else ([0,1,2] : List (Fin 3))) →
      (⟨cc, l, dd, v⟩ : LowerEarlyTerminalForkCase) ∈ lowerEarlyTerminalForkCases := by
    intro dd v hdd hv
    simp only [lowerEarlyTerminalForkCases, List.mem_flatMap, List.mem_map]
    exact ⟨cc, hccmem, l, hlnat, dd, hdd, v, hv, rfl⟩
  intro d hdmem
  refine ⟨?_, ?_⟩
  · rw [hFP1 d, hFP2 d]
    intro hwEq
    refine master _ _ ⟨cc, l, d, 0⟩ (mem_case d 0 hdmem (by split_ifs <;> simp))
      (lowerRatio q1) (lowerRatio q2) (hr q1).1 (hr q1).2 (hr q2).1 (hr q2).2
      (by simpa [lowerEarlyTerminalRatioWords] using hrat1 [])
      (by simpa [lowerEarlyTerminalRatioWords] using hrat2 d []) ?_ hwEq
    rintro ⟨hlab, hcase⟩
    rcases hcase with ⟨-, -, hv⟩ | ⟨hc3, hd2, -⟩
    · exact absurd (show (0 : Fin 3) = 2 from hv) (by decide)
    · have hc3' : cc = 3 := hc3
      have hd2' : d = 2 := hd2
      have hlab' : l = ([2,2],[3,2]) := hlab
      rw [hd2'] at hwEq
      refine h3 ⟨hlab', ⟨q1, by rw [hq1, hc3']⟩, ?_⟩
      rw [hFP1, hFP2]
      exact hwEq
  · intro hpardiff
    rw [hFP1 d, hFP2 d] at hpardiff ⊢
    have hodd : ¬ ((l.1.length + l.2.length + 1) % 2 = 0) := by
      simp only [List.length_append, List.length_reverse, List.length_cons,
        List.length_nil] at hpardiff
      omega
    constructor
    · intro hwEq
      refine master _ _ ⟨cc, l, d, 1⟩ (mem_case d 1 hdmem (by rw [if_neg hodd]; simp))
        (lowerRatio q1) (lowerRatio q2) (hr q1).1 (hr q1).2 (hr q2).1 (hr q2).2
        (by simpa [lowerEarlyTerminalRatioWords] using hrat1 [1])
        (by simpa [lowerEarlyTerminalRatioWords] using hrat2 d []) ?_ hwEq
      rintro ⟨-, hcase⟩
      rcases hcase with ⟨-, -, hv⟩ | ⟨-, -, hv⟩
      · exact absurd (show (1 : Fin 3) = 2 from hv) (by decide)
      · exact absurd (show (1 : Fin 3) = 0 from hv) (by decide)
    · intro hwEq
      refine master _ _ ⟨cc, l, d, 2⟩ (mem_case d 2 hdmem (by rw [if_neg hodd]; simp))
        (lowerRatio q1) (lowerRatio q2) (hr q1).1 (hr q1).2 (hr q2).1 (hr q2).2
        (by simpa [lowerEarlyTerminalRatioWords] using hrat1 [])
        (by simpa [lowerEarlyTerminalRatioWords] using hrat2 d [1]) ?_ hwEq
      rintro ⟨hlab, hcase⟩
      rcases hcase with ⟨hc2, hd1, -⟩ | ⟨-, -, hv⟩
      · have hc2' : cc = 2 := hc2
        have hd1' : d = 1 := hd1
        have hlab' : l = ([2,2],[3,2]) := hlab
        rw [hd1'] at hwEq
        refine h2 ⟨hlab', ⟨q1, by rw [hq1, hc2']⟩, ?_⟩
        rw [hFP1, hFP2]
        exact hwEq
      · exact absurd (show (2 : Fin 3) = 0 from hv) (by decide)
