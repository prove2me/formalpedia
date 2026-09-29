-- Prove2me | solution 1 for Freiman.lowerJ_equal_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T17:57:33.569631+00:00
-- url     : https://prove2.me/submissions/7ca209e9-2209-47c0-89e3-54662b34d672

import Definitions.Def_Freiman_lowerJModel
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Freiman

namespace M7EP

lemma sepw_pair (a b : List ℕ+) (upper : Bool) :
    lowerSourceEndpointWords (a, b) upper =
      (if a.length % 2 = b.length % 2 then lowerSourceEqualWords (a,b) upper else
        (if upper = decide (((if lowerWidth b ≤ lowerWidth a then a else b).length) % 2 = 0) then
          lowerSourceEqualWords (if lowerWidth b ≤ lowerWidth a then (a ++ [1], b) else (a, b ++ [1])) upper
        else lowerNaturalWords (a,b) upper)) := rfl

lemma seq_keep (a b : List ℕ+) (upper : Bool) (h : lowerWidth b ≤ lowerWidth a) :
    lowerSourceEqualWords (a,b) upper =
      (a ++ lowerEndpointSuffix a upper (lowerNaturalShort a upper),
       b ++ lowerEndpointSuffix b upper (lowerNaturalShort b upper ||
          (!lowerNaturalShort a upper && !lowerNaturalShort b upper &&
           decide (lowerSourceAuxWidth a (if (a.length % 2 = 0) = ((!upper) = true) then [3] else [1,3])
             ≤ (7/5:ℝ) * lowerSourceAuxWidth b
                 (if (a.length % 2 = 0) = ((!upper) = true) then [3] else [1,3]))))) := by
  have hn : lowerNormalize (a,b) = (a,b) := by simp only [lowerNormalize, if_pos h]
  simp only [lowerSourceEqualWords, hn, if_pos h]

lemma seq_swap (a b : List ℕ+) (upper : Bool) (h : ¬ (lowerWidth b ≤ lowerWidth a)) :
    lowerSourceEqualWords (a,b) upper =
      (a ++ lowerEndpointSuffix a upper (lowerNaturalShort a upper ||
          (!lowerNaturalShort b upper && !lowerNaturalShort a upper &&
           decide (lowerSourceAuxWidth b (if (b.length % 2 = 0) = ((!upper) = true) then [3] else [1,3])
             ≤ (7/5:ℝ) * lowerSourceAuxWidth a
                 (if (b.length % 2 = 0) = ((!upper) = true) then [3] else [1,3])))),
       b ++ lowerEndpointSuffix b upper (lowerNaturalShort b upper)) := by
  have hn : lowerNormalize (a,b) = (b,a) := by simp only [lowerNormalize, if_neg h]
  simp only [lowerSourceEqualWords, hn, if_neg h]

lemma nat_pair (a b : List ℕ+) (upper : Bool) :
    lowerNaturalWords (a,b) upper =
      (a ++ lowerEndpointSuffix a upper (lowerNaturalShort a upper),
       b ++ lowerEndpointSuffix b upper (lowerNaturalShort b upper)) := rfl

lemma nshort_tt (w : List ℕ+) (upper : Bool)
    (hc : ((w.length % 2 = 0) = ((!upper) = true))) (h : lowerEnds w [3,1]) :
    lowerNaturalShort w upper = true := by
  simp only [lowerNaturalShort, if_pos hc]; simp [h]

lemma nshort_tf (w : List ℕ+) (upper : Bool)
    (hc : ((w.length % 2 = 0) = ((!upper) = true))) (h : ¬ lowerEnds w [3,1]) :
    lowerNaturalShort w upper = false := by
  simp only [lowerNaturalShort, if_pos hc]; simp [h]

lemma nshort_ft (w : List ℕ+) (upper : Bool)
    (hc : ¬((w.length % 2 = 0) = ((!upper) = true))) (h : lowerEnds w [3]) :
    lowerNaturalShort w upper = true := by
  simp only [lowerNaturalShort, if_neg hc]; simp [h]

lemma nshort_ff (w : List ℕ+) (upper : Bool)
    (hc : ¬((w.length % 2 = 0) = ((!upper) = true))) (h : ¬ lowerEnds w [3]) :
    lowerNaturalShort w upper = false := by
  simp only [lowerNaturalShort, if_neg hc]; simp [h]

lemma suf_t (w : List ℕ+) (upper short : Bool)
    (hc : ((w.length % 2 = 0) = ((!upper) = true))) :
    lowerEndpointSuffix w upper short = (if short = true then [2,1,3] else [3]) := by
  simp only [lowerEndpointSuffix, if_pos hc]

lemma suf_f (w : List ℕ+) (upper short : Bool)
    (hc : ¬((w.length % 2 = 0) = ((!upper) = true))) :
    lowerEndpointSuffix w upper short = (if short = true then [1,2,1,3] else [1,3]) := by
  simp only [lowerEndpointSuffix, if_neg hc]

lemma auxw3 (w : List ℕ+) : lowerSourceAuxWidth w [3] = lowerWidth (w ++ [3]) := by
  simp only [lowerSourceAuxWidth, if_neg (by decide : ¬ (([3] : List ℕ+) = [1,3]))]


lemma words1 (p : LowerPair) (u0 u1 : Bool)
    (hne : ¬ (u0 = u1))
    (hmix : ¬ ((p.1 ++ [1]).length % 2 = p.2.length % 2))
    (hvL : u0 = decide ((p.1 ++ [1]).length % 2 = 0))
    (hvR : u1 = decide (p.2.length % 2 = 0))
    (cA : (p.2.length % 2 = 0) = ((!u0) = true))
    (cC : ¬(((p.1++[1]).length % 2 = 0) = ((!u0) = true)))
    (cH : (((p.1++[1,1]).length % 2 = 0) = ((!u0) = true)))
    (e1 : ¬ lowerEnds p.2 [3,1])
    (e4 : ¬ lowerEnds (p.1++[1]) [3])
    (e5 : ¬ lowerEnds (p.1++[1,1]) [3,1])
    (w2 : lowerWidth (p.1++[1,1]) < lowerWidth p.2)
    (w3 : (7/5:ℝ) * lowerWidth (p.1++[1,1,3]) < lowerWidth (p.2++[3])) :
    lowerSourceEndpointWords (p.1 ++ [1], p.2) u0 = (p.1 ++ [1,1,3], p.2 ++ [3]) := by
  rw [sepw_pair, if_neg hmix]
  by_cases hlw : lowerWidth p.2 ≤ lowerWidth (p.1 ++ [1])
  · rw [if_pos hlw, if_pos hlw, if_pos hvL]
    have hass : (p.1 ++ [1]) ++ [1] = p.1 ++ [1,1] := by simp
    rw [hass]
    have hnn : ¬ (lowerWidth p.2 ≤ lowerWidth (p.1 ++ [1,1])) := not_le.mpr w2
    rw [seq_swap _ _ _ hnn]
    rw [nshort_tf _ _ cA e1, nshort_tf _ _ cH e5, if_pos cA, auxw3, auxw3,
      show (p.1 ++ [1,1]) ++ [3] = p.1 ++ [1,1,3] from by simp]
    have hdec : decide (lowerWidth (p.2 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (p.1 ++ [1,1,3])) = false := by
      simp [not_le.mpr w3]
    rw [hdec]
    simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or,
      Bool.true_and]
    rw [suf_t _ _ _ cH, suf_t _ _ _ cA]
    simp
  · rw [if_neg hlw, if_neg hlw]
    have : ¬ (u0 = decide (p.2.length % 2 = 0)) := by rw [← hvR]; exact hne
    rw [if_neg this, nat_pair]
    rw [nshort_ff _ _ cC e4, nshort_tf _ _ cA e1]
    rw [suf_f _ _ _ cC, suf_t _ _ _ cA]
    simp


lemma words2 (p : LowerPair) (u0 u1 : Bool)
    (hne : ¬ (u0 = u1))
    (hmix : ¬ ((p.1 ++ [1]).length % 2 = p.2.length % 2))
    (hvL : u0 = decide ((p.1 ++ [1]).length % 2 = 0))
    (hvR : u1 = decide (p.2.length % 2 = 0))
    (cB : ¬((p.2.length % 2 = 0) = ((!u1) = true)))
    (cD : (((p.1++[1]).length % 2 = 0) = ((!u1) = true)))
    (cG : (((p.2++[1]).length % 2 = 0) = ((!u1) = true)))
    (e2 : lowerEnds p.2 [3])
    (e3 : lowerEnds (p.1++[1]) [3,1])
    (e8 : lowerEnds (p.2++[1]) [3,1]) :
    lowerSourceEndpointWords (p.1 ++ [1], p.2) u1 = (p.1 ++ [1,2,1,3], p.2 ++ [1,2,1,3]) := by
  rw [sepw_pair, if_neg hmix]
  by_cases hlw : lowerWidth p.2 ≤ lowerWidth (p.1 ++ [1])
  · rw [if_pos hlw, if_pos hlw]
    have hq : ¬ (u1 = decide ((p.1 ++ [1]).length % 2 = 0)) := by
      rw [← hvL]; exact fun h => hne h.symm
    rw [if_neg hq, nat_pair, nshort_tt _ _ cD e3, nshort_ft _ _ cB e2,
      suf_t _ _ _ cD, suf_f _ _ _ cB]
    simp
  · rw [if_neg hlw, if_neg hlw, if_pos hvR]
    by_cases hY : lowerWidth (p.2 ++ [1]) ≤ lowerWidth (p.1 ++ [1])
    · rw [seq_keep _ _ _ hY, nshort_tt _ _ cD e3, nshort_tt _ _ cG e8]
      simp only [Bool.true_or]
      rw [suf_t _ _ _ cD, suf_t _ _ _ cG]
      simp
    · rw [seq_swap _ _ _ hY, nshort_tt _ _ cD e3, nshort_tt _ _ cG e8]
      simp only [Bool.true_or]
      rw [suf_t _ _ _ cD, suf_t _ _ _ cG]
      simp

lemma words3 (p : LowerPair) (u0 u1 : Bool)
    (hne : ¬ (u0 = u1))
    (hmix2 : ¬ ((p.1 ++ [2]).length % 2 = p.2.length % 2))
    (hvR : u1 = decide (p.2.length % 2 = 0))
    (cA : (p.2.length % 2 = 0) = ((!u0) = true))
    (cE : ¬(((p.1++[2]).length % 2 = 0) = ((!u0) = true)))
    (e1 : ¬ lowerEnds p.2 [3,1])
    (e6 : ¬ lowerEnds (p.1++[2]) [3])
    (w1 : lowerWidth (p.1++[2]) < lowerWidth p.2) :
    lowerSourceEndpointWords (p.1 ++ [2], p.2) u0 = (p.1 ++ [2,1,3], p.2 ++ [3]) := by
  rw [sepw_pair, if_neg hmix2]
  have hlw : ¬ (lowerWidth p.2 ≤ lowerWidth (p.1 ++ [2])) := not_le.mpr w1
  rw [if_neg hlw, if_neg hlw]
  have hq : ¬ (u0 = decide (p.2.length % 2 = 0)) := by rw [← hvR]; exact hne
  rw [if_neg hq, nat_pair, nshort_ff _ _ cE e6, nshort_tf _ _ cA e1,
    suf_f _ _ _ cE, suf_t _ _ _ cA]
  simp

lemma words4 (p : LowerPair) (u0 u1 : Bool)
    (hmix2 : ¬ ((p.1 ++ [2]).length % 2 = p.2.length % 2))
    (hvR : u1 = decide (p.2.length % 2 = 0))
    (cF : (((p.1++[2]).length % 2 = 0) = ((!u1) = true)))
    (cG : (((p.2++[1]).length % 2 = 0) = ((!u1) = true)))
    (e7 : ¬ lowerEnds (p.1++[2]) [3,1])
    (e8 : lowerEnds (p.2++[1]) [3,1])
    (w1 : lowerWidth (p.1++[2]) < lowerWidth p.2) :
    lowerSourceEndpointWords (p.1 ++ [2], p.2) u1 = (p.1 ++ [2,3], p.2 ++ [1,2,1,3]) := by
  rw [sepw_pair, if_neg hmix2]
  have hlw : ¬ (lowerWidth p.2 ≤ lowerWidth (p.1 ++ [2])) := not_le.mpr w1
  rw [if_neg hlw, if_neg hlw, if_pos hvR]
  by_cases hZ : lowerWidth (p.2 ++ [1]) ≤ lowerWidth (p.1 ++ [2])
  · rw [seq_keep _ _ _ hZ, nshort_tf _ _ cF e7, nshort_tt _ _ cG e8]
    simp only [Bool.true_or]
    rw [suf_t _ _ _ cF, suf_t _ _ _ cG]
    simp
  · rw [seq_swap _ _ _ hZ, nshort_tf _ _ cF e7, nshort_tt _ _ cG e8]
    simp only [Bool.not_true, Bool.false_and, Bool.or_false]
    rw [suf_t _ _ _ cF, suf_t _ _ _ cG]
    simp

lemma sep_val (P : LowerPair) (upper : Bool) :
    lowerSourceEndpoint P upper
      = 4 + prefixEval (lowerSourceEndpointWords P upper).1 lowerTau
          + prefixEval (lowerSourceEndpointWords P upper).2 lowerTau := rfl

lemma pe_append (u : List ℕ+) : ∀ (v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => intro v x; simp [prefixEval]
  | cons a u ih => intro v x; simp only [List.cons_append, prefixEval, ih]


end M7EP

open M7EP

theorem solution (haux : ∀ w : List ℕ+, |prefixEval w lowerBeta-prefixEval (w++[1,3]) lowerAlpha| = lowerWidth (w++[1,3])) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) (hc : lowerJEqualContact p) (hw : lowerWidth ((lowerNormalize p).1++[2]) < lowerWidth (lowerNormalize p).2 ∧ lowerWidth ((lowerNormalize p).1++[1,1]) < lowerWidth (lowerNormalize p).2) : lowerJEqualForkFacts p := by
  classical
  have hnorm : lowerNormalize p = p := by simp only [lowerNormalize, if_pos hwide]
  have hpar : p.1.length % 2 = p.2.length % 2 := by unfold lowerMixed at hp; omega
  -- width facts, in unnormalized coordinates
  have hw1 : lowerWidth (p.1 ++ [2]) < lowerWidth p.2 := by
    have h := hw.1; rw [hnorm] at h; exact h
  have hw2 : lowerWidth (p.1 ++ [1,1]) < lowerWidth p.2 := by
    have h := hw.2; rw [hnorm] at h; exact h
  have hcw : (7/5:ℝ) * lowerWidth (p.1 ++ [1,1,3]) < lowerWidth (p.2 ++ [3]) := by
    have h := hc.2; rw [hnorm] at h; exact h
  -- suffix facts
  obtain ⟨U, hU⟩ := hl
  obtain ⟨V, hV⟩ := hr
  have e2 : lowerEnds p.2 [3] := ⟨V, hV⟩
  have e1 : ¬ lowerEnds p.2 [3,1] := by
    rintro ⟨t, ht⟩
    rw [← hV] at ht
    have h2 : (t ++ [3]) ++ [1] = V ++ [3] := (List.append_assoc t [3] [1]).trans ht
    exact absurd (List.append_inj' h2 rfl).2 (by decide)
  have e3 : lowerEnds (p.1 ++ [1]) [3,1] := ⟨U, by rw [← hU]; simp⟩
  have e8 : lowerEnds (p.2 ++ [1]) [3,1] := ⟨V, by rw [← hV]; simp⟩
  have e4 : ¬ lowerEnds (p.1 ++ [1]) [3] := by
    rintro ⟨t, ht⟩
    exact absurd (List.append_inj' ht rfl).2 (by decide)
  have e6 : ¬ lowerEnds (p.1 ++ [2]) [3] := by
    rintro ⟨t, ht⟩
    exact absurd (List.append_inj' ht rfl).2 (by decide)
  have e5 : ¬ lowerEnds (p.1 ++ [1,1]) [3,1] := by
    rintro ⟨t, ht⟩
    exact absurd (List.append_inj' ht rfl).2 (by decide)
  have e7 : ¬ lowerEnds (p.1 ++ [2]) [3,1] := by
    rintro ⟨t, ht⟩
    have h2 : (t ++ [3]) ++ [1] = p.1 ++ [2] := (List.append_assoc t [3] [1]).trans ht
    exact absurd (List.append_inj' h2 rfl).2 (by decide)
  -- lengths
  have len1 : (p.1 ++ [1]).length = p.1.length + 1 := by simp
  have len2 : (p.1 ++ [2]).length = p.1.length + 1 := by simp
  have len11 : (p.1 ++ [1,1]).length = p.1.length + 2 := by simp
  have len21 : (p.2 ++ [1]).length = p.2.length + 1 := by simp
  have hmix : ¬ ((p.1 ++ [1]).length % 2 = p.2.length % 2) := by rw [len1]; omega
  have hmix2 : ¬ ((p.1 ++ [2]).length % 2 = p.2.length % 2) := by rw [len2]; omega
  -- children
  have hch1 : lowerChild p ([1],[]) = (p.1 ++ [1], p.2) := by
    simp only [lowerChild, hnorm]; simp
  have hch2 : lowerChild p ([2],[]) = (p.1 ++ [2], p.2) := by
    simp only [lowerChild, hnorm]; simp
  -- theta unfoldings
  have th3 : lowerTheta 3 = prefixEval [3] lowerTau := rfl
  have th30 : lowerTheta 30 = prefixEval [2,1,3] lowerTau := rfl
  have th63 : lowerTheta 63 = prefixEval [2,3] lowerTau := rfl
  have th66 : lowerTheta 66 = prefixEval [1,1,3] lowerTau := rfl
  have th90 : lowerTheta 90 = prefixEval [1,2,1,3] lowerTau := rfl
  have hact : ∀ x y : ℝ, lowerJActual p x y = 4 + prefixEval p.1 x + prefixEval p.2 y := by
    intro x y; simp only [lowerJActual, hnorm]
  by_cases hev : p.1.length % 2 = 0
  · have hp2 : p.2.length % 2 = 0 := by omega
    have hl1 : (p.1 ++ [1]).length % 2 = 1 := by rw [len1]; omega
    have hl2 : (p.1 ++ [2]).length % 2 = 1 := by rw [len2]; omega
    have hl11 : (p.1 ++ [1,1]).length % 2 = 0 := by rw [len11]; omega
    have hl21 : (p.2 ++ [1]).length % 2 = 1 := by rw [len21]; omega
    have cA : (p.2.length % 2 = 0) = ((!(false:Bool)) = true) := by simp [hp2] <;> omega
    have cB : ¬((p.2.length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hp2] <;> omega
    have cC : ¬(((p.1 ++ [1]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl1] <;> omega
    have cD : (((p.1 ++ [1]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl1] <;> omega
    have cE : ¬(((p.1 ++ [2]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl2] <;> omega
    have cF : (((p.1 ++ [2]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl2] <;> omega
    have cG : (((p.2 ++ [1]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl21] <;> omega
    have cH : (((p.1 ++ [1,1]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl11] <;> omega
    have hvL : (false:Bool) = decide ((p.1 ++ [1]).length % 2 = 0) := by simp [hl1] <;> omega
    have hvR : (true:Bool) = decide (p.2.length % 2 = 0) := by simp [hp2] <;> omega
    have W1 := M7EP.words1 p false true (by decide) hmix hvL hvR cA cC cH e1 e4 e5 hw2 hcw
    have W2 := M7EP.words2 p false true (by decide) hmix hvL hvR cB cD cG e2 e3 e8
    have W3 := M7EP.words3 p false true (by decide) hmix2 hvR cA cE e1 e6 hw1
    have W4 := M7EP.words4 p false true hmix2 hvR cF cG e7 e8 hw1
    have D0 : decide (¬ ((lowerNormalize p).1.length % 2 = 0)) = false := by
      rw [hnorm]; simp [hev]
    have D1 : decide ((lowerNormalize p).1.length % 2 = 0) = true := by
      rw [hnorm]; simp [hev]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hch1, D0, M7EP.sep_val, W1, hact, th66, th3, M7EP.pe_append, M7EP.pe_append]
    · rw [hch1, D1, M7EP.sep_val, W2, hact, th90, M7EP.pe_append, M7EP.pe_append]
    · rw [hch2, D0, M7EP.sep_val, W3, hact, th30, th3, M7EP.pe_append, M7EP.pe_append]
    · rw [hch2, D1, M7EP.sep_val, W4, hact, th63, th90, M7EP.pe_append, M7EP.pe_append]
  · have hp2 : ¬ (p.2.length % 2 = 0) := by omega
    have hl1 : (p.1 ++ [1]).length % 2 = 0 := by rw [len1]; omega
    have hl2 : (p.1 ++ [2]).length % 2 = 0 := by rw [len2]; omega
    have hl11 : (p.1 ++ [1,1]).length % 2 = 1 := by rw [len11]; omega
    have hl21 : (p.2 ++ [1]).length % 2 = 0 := by rw [len21]; omega
    have hp2' : p.2.length % 2 = 1 := by omega
    have cA : (p.2.length % 2 = 0) = ((!(true:Bool)) = true) := by simp [hp2'] <;> omega
    have cB : ¬((p.2.length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hp2'] <;> omega
    have cC : ¬(((p.1 ++ [1]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl1] <;> omega
    have cD : (((p.1 ++ [1]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl1] <;> omega
    have cE : ¬(((p.1 ++ [2]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl2] <;> omega
    have cF : (((p.1 ++ [2]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl2] <;> omega
    have cG : (((p.2 ++ [1]).length % 2 = 0) = ((!(false:Bool)) = true)) := by simp [hl21] <;> omega
    have cH : (((p.1 ++ [1,1]).length % 2 = 0) = ((!(true:Bool)) = true)) := by simp [hl11] <;> omega
    have hvL : (true:Bool) = decide ((p.1 ++ [1]).length % 2 = 0) := by simp [hl1] <;> omega
    have hvR : (false:Bool) = decide (p.2.length % 2 = 0) := by simp [hp2'] <;> omega
    have W1 := M7EP.words1 p true false (by decide) hmix hvL hvR cA cC cH e1 e4 e5 hw2 hcw
    have W2 := M7EP.words2 p true false (by decide) hmix hvL hvR cB cD cG e2 e3 e8
    have W3 := M7EP.words3 p true false (by decide) hmix2 hvR cA cE e1 e6 hw1
    have W4 := M7EP.words4 p true false hmix2 hvR cF cG e7 e8 hw1
    have D0 : decide (¬ ((lowerNormalize p).1.length % 2 = 0)) = true := by
      rw [hnorm]; simp [hev]
    have D1 : decide ((lowerNormalize p).1.length % 2 = 0) = false := by
      rw [hnorm]; simp [hev]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hch1, D0, M7EP.sep_val, W1, hact, th66, th3, M7EP.pe_append, M7EP.pe_append]
    · rw [hch1, D1, M7EP.sep_val, W2, hact, th90, M7EP.pe_append, M7EP.pe_append]
    · rw [hch2, D0, M7EP.sep_val, W3, hact, th30, th3, M7EP.pe_append, M7EP.pe_append]
    · rw [hch2, D1, M7EP.sep_val, W4, hact, th63, th90, M7EP.pe_append, M7EP.pe_append]
