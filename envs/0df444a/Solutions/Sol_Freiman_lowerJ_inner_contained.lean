-- Prove2me | solution 1 for Freiman.lowerJ_inner_contained
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T15:50:01.445603+00:00
-- url     : https://prove2.me/submissions/4ea6eff0-18b8-4ceb-9818-e1d768133cc1

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Freiman

namespace M7JC

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

lemma pe_append (u : List ℕ+) : ∀ (v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => intro v x; simp [prefixEval]
  | cons a u ih => intro v x; simp only [List.cons_append, prefixEval, ih]

lemma pe_mono_le (w : List ℕ+) : ∀ (x y : ℝ), 0 ≤ x → x ≤ y →
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => intro x y hx hxy; exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a w ih =>
      intro x y hx hxy
      have hy : (0:ℝ) ≤ y := le_trans hx hxy
      have nx := pe_nonneg w x hx
      have ny := pe_nonneg w y hy
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have dx : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      have dy : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w y := by linarith
      obtain ⟨he, ho⟩ := ih x y hx hxy
      refine ⟨fun hlen => ?_, fun hlen => ?_⟩
      · have h1 : w.length % 2 = 1 := by simp only [List.length_cons] at hlen; omega
        have hstep := ho h1
        simp only [prefixEval]
        exact one_div_le_one_div_of_le dy (by linarith)
      · have h0 : w.length % 2 = 0 := by simp only [List.length_cons] at hlen; omega
        have hstep := he h0
        simp only [prefixEval]
        exact one_div_le_one_div_of_le dx (by linarith)

lemma equal_words_shape (P : LowerPair) (upper : Bool) (h : lowerWidth P.2 ≤ lowerWidth P.1) :
    ∃ b : Bool, (lowerNaturalShort P.2 upper = true → b = true) ∧
      lowerEqualWords P upper =
        (P.1 ++ lowerEndpointSuffix P.1 upper (lowerNaturalShort P.1 upper),
         P.2 ++ lowerEndpointSuffix P.2 upper b) := by
  classical
  simp only [lowerEqualWords, lowerNormalize, if_pos h]
  refine ⟨_, ?_, rfl⟩
  intro hh
  simp [hh]

end M7JC

open M7JC

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ)
    (hk : 0 < k) (hp : lowerRunParameters p) :
    lowerJInner p k ⊆ lowerCover (lowerRunPair p k) := by
  classical
  -- the three constants
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hlo : (17/10:ℝ) < Real.sqrt 3 := by nlinarith
  have hhi : Real.sqrt 3 < (18/10:ℝ) := by nlinarith
  have hAval : lowerJA = 1 / (2 + Real.sqrt 3) := by
    have : lowerJA = prefixEval [3] lowerTau := rfl
    rw [this]
    norm_num [prefixEval, lowerTau]
    ring
  have hAd : (0:ℝ) < 2 + Real.sqrt 3 := by linarith
  have hA0 : (0:ℝ) < lowerJA := by rw [hAval]; positivity
  have hA1 : lowerJA < (28/100:ℝ) := by rw [hAval, div_lt_iff₀ hAd]; linarith
  have hA2 : (26/100:ℝ) < lowerJA := by rw [hAval, lt_div_iff₀ hAd]; linarith
  have hCval : lowerJC = 1 / (2 + 1/(1 + lowerJA)) := by
    have h1 : lowerJC = prefixEval [2,1,3] lowerTau := rfl
    have h2 : lowerJA = prefixEval [3] lowerTau := rfl
    rw [h1, h2]
    norm_num [prefixEval]
  have h1A : (0:ℝ) < 1 + lowerJA := by linarith
  have hx1 : 1/(1 + lowerJA) < (794/1000:ℝ) := by rw [div_lt_iff₀ h1A]; linarith
  have hx2 : (781/1000:ℝ) < 1/(1 + lowerJA) := by rw [lt_div_iff₀ h1A]; linarith
  have hCd : (0:ℝ) < 2 + 1/(1 + lowerJA) := by linarith
  have hC1 : (357/1000:ℝ) < lowerJC := by rw [hCval, lt_div_iff₀ hCd]; linarith
  have hC2 : lowerJC < (36/100:ℝ) := by rw [hCval, div_lt_iff₀ hCd]; linarith
  have hBval : lowerJB = 1 / (1 + lowerJC) := by
    have h1 : lowerJB = prefixEval [1,2,1,3] lowerTau := rfl
    have h2 : lowerJC = prefixEval [2,1,3] lowerTau := rfl
    rw [h1, h2]
    norm_num [prefixEval]
  have h1C : (0:ℝ) < 1 + lowerJC := by linarith
  have hB1 : (73/100:ℝ) < lowerJB := by rw [hBval, lt_div_iff₀ h1C]; linarith
  have hAC : lowerJA ≤ lowerJC := by linarith
  have hCB : lowerJC ≤ lowerJB := by linarith
  have hAB : lowerJA ≤ lowerJB := by linarith
  have hA0' : (0:ℝ) ≤ lowerJA := le_of_lt hA0
  have hC0' : (0:ℝ) ≤ lowerJC := by linarith
  -- the run pair
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
  have hRsplit : List.replicate (k'+1) (3:ℕ+) = List.replicate k' (3:ℕ+) ++ [3] :=
    List.replicate_succ'
  set q := lowerNormalize p with hqdef
  set u := q.1 ++ List.replicate (k'+1) (3:ℕ+) with hu
  set v := q.2 ++ List.replicate (k'+1) (3:ℕ+) with hv
  have hP : lowerRunPair p (k'+1) = (u, v) := by
    simp only [lowerRunPair, lowerChild, hu, hv, ← hqdef, List.reverse_replicate]
  have hlast : ∀ w : List ℕ+, lowerEnds (w ++ List.replicate (k'+1) (3:ℕ+)) [3] ∧
      ¬ lowerEnds (w ++ List.replicate (k'+1) (3:ℕ+)) [3,1] := by
    intro w
    rw [hRsplit, ← List.append_assoc]
    constructor
    · exact ⟨w ++ List.replicate k' (3:ℕ+), rfl⟩
    · rintro ⟨z, hz⟩
      have h1 : (z ++ [3]) ++ [1] = (w ++ List.replicate k' (3:ℕ+)) ++ [3] := by
        simpa using hz
      have h2 := (List.append_inj' h1 rfl).2
      simp at h2
  have hu3 : lowerEnds u [3] := (hlast q.1).1
  have hu31 : ¬ lowerEnds u [3,1] := (hlast q.1).2
  have hv3 : lowerEnds v [3] := (hlast q.2).1
  have hv31 : ¬ lowerEnds v [3,1] := (hlast q.2).2
  have hpar : u.length % 2 = v.length % 2 := by
    have hm : ¬ lowerMixed p := hr.1
    unfold lowerMixed at hm
    have : q.1.length % 2 = q.2.length % 2 := by
      by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
      · simp only [hqdef, lowerNormalize, if_pos hh]; omega
      · simp only [hqdef, lowerNormalize, if_neg hh]; omega
    simp only [hu, hv, List.length_append]
    omega
  have hwid : lowerWidth v ≤ lowerWidth u := (hp (k'+1) (Nat.succ_pos k')).2.2.2.2.2.2.1
  have hEWeq : ∀ upper : Bool, lowerEndpointWords (u,v) upper = lowerEqualWords (u,v) upper := by
    intro upper; simp only [lowerEndpointWords, if_pos hpar]
  have hep : ∀ (upper : Bool) (A B : List ℕ+), lowerEndpointWords (u,v) upper = (u ++ A, v ++ B) →
      lowerEndpoint (u,v) upper
        = 4 + prefixEval u (prefixEval A lowerTau) + prefixEval v (prefixEval B lowerTau) := by
    intro upper A B h
    simp only [lowerEndpoint, h, pe_append]
  have hns : ∀ (w : List ℕ+), lowerEnds w [3] → ¬ lowerEnds w [3,1] → ∀ upper : Bool,
      (((w.length % 2 = 0) = ((!upper) = true)) → lowerNaturalShort w upper = false) ∧
      (¬((w.length % 2 = 0) = ((!upper) = true)) → lowerNaturalShort w upper = true) := by
    intro w h3 h31 upper
    constructor
    · intro hcond; simp only [lowerNaturalShort, if_pos hcond]; exact decide_eq_false h31
    · intro hcond; simp only [lowerNaturalShort, if_neg hcond]; exact decide_eq_true h3
  have hsfxA : ∀ (w : List ℕ+) (upper b : Bool), ((w.length % 2 = 0) = ((!upper) = true)) →
      lowerEndpointSuffix w upper b = if b then [2,1,3] else [3] := by
    intro w upper b hcond; simp only [lowerEndpointSuffix, if_pos hcond]
  have hsfxB : ∀ (w : List ℕ+) (upper b : Bool), ¬((w.length % 2 = 0) = ((!upper) = true)) →
      lowerEndpointSuffix w upper b = if b then [1,2,1,3] else [1,3] := by
    intro w upper b hcond; simp only [lowerEndpointSuffix, if_neg hcond]
  have e3 : prefixEval [3] lowerTau = lowerJA := rfl
  have e213 : prefixEval [2,1,3] lowerTau = lowerJC := rfl
  have e1213 : prefixEval [1,2,1,3] lowerTau = lowerJB := rfl
  have hIA : lowerJInnerA p (k'+1) = 4 + prefixEval u lowerJA + prefixEval v lowerJC := by
    simp only [lowerJInnerA, lowerJActual, lowerJIter, hu, hv, pe_append, ← hqdef]
  have hIB : lowerJInnerB p (k'+1) = 4 + prefixEval u lowerJB + prefixEval v lowerJB := by
    simp only [lowerJInnerB, lowerJActual, lowerJIter, hu, hv, pe_append, ← hqdef]
  have hpv : v.length % 2 = u.length % 2 := hpar.symm
  -- the branch analysis
  have main : lowerEndpoint (u,v) false ≤ lowerJInnerA p (k'+1) ∧
      lowerEndpoint (u,v) false ≤ lowerJInnerB p (k'+1) ∧
      lowerJInnerA p (k'+1) ≤ lowerEndpoint (u,v) true ∧
      lowerJInnerB p (k'+1) ≤ lowerEndpoint (u,v) true := by
    obtain ⟨bF, hbF, hwF⟩ := equal_words_shape (u,v) false hwid
    obtain ⟨bT, hbT, hwT⟩ := equal_words_shape (u,v) true hwid
    rw [← hEWeq false] at hwF
    rw [← hEWeq true] at hwT
    by_cases hpe : u.length % 2 = 0
    · -- both words of even length
      have hcu : ((u.length % 2 = 0) = ((!false) = true)) := by simp [hpe]
      have hcv : ((v.length % 2 = 0) = ((!false) = true)) := by simp [hpv, hpe]
      have hcu' : ¬((u.length % 2 = 0) = ((!true) = true)) := by simp [hpe]
      have hcv' : ¬((v.length % 2 = 0) = ((!true) = true)) := by simp [hpv, hpe]
      rw [(hns u hu3 hu31 false).1 hcu, hsfxA u false false hcu, if_neg (by simp),
        hsfxA v false bF hcv] at hwF
      rw [(hns u hu3 hu31 true).2 hcu', hsfxB u true true hcu', if_pos rfl,
        hsfxB v true bT hcv', if_pos (hbT ((hns v hv3 hv31 true).2 hcv'))] at hwT
      have hET : lowerEndpoint (u,v) true = 4 + prefixEval u lowerJB + prefixEval v lowerJB := by
        have h := hep true _ _ hwT
        simpa [e1213] using h
      have hEFex : ∃ y : ℝ, 0 ≤ y ∧ y ≤ lowerJC ∧
          lowerEndpoint (u,v) false = 4 + prefixEval u lowerJA + prefixEval v y := by
        cases bF with
        | false =>
            refine ⟨lowerJA, hA0', hAC, ?_⟩
            have h := hep false _ _ hwF
            simpa [e3] using h
        | true =>
            refine ⟨lowerJC, hC0', le_refl _, ?_⟩
            have h := hep false _ _ hwF
            simpa [e3, e213] using h
      obtain ⟨y, hy0, hyC, hEFv⟩ := hEFex
      have hvpe : v.length % 2 = 0 := by omega
      have hmu := (pe_mono_le u lowerJA lowerJB hA0' hAB).1 hpe
      have hmv := (pe_mono_le v lowerJC lowerJB hC0' hCB).1 hvpe
      have hmy := (pe_mono_le v y lowerJC hy0 hyC).1 hvpe
      rw [hIA, hIB, hEFv, hET]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · -- both words of odd length
      have hpo : u.length % 2 = 1 := by omega
      have hpvo : v.length % 2 = 1 := by omega
      have hcu : ¬((u.length % 2 = 0) = ((!false) = true)) := by simp [hpo]
      have hcv : ¬((v.length % 2 = 0) = ((!false) = true)) := by simp [hpvo]
      have hcu' : ((u.length % 2 = 0) = ((!true) = true)) := by simp [hpo]
      have hcv' : ((v.length % 2 = 0) = ((!true) = true)) := by simp [hpvo]
      rw [(hns u hu3 hu31 false).2 hcu, hsfxB u false true hcu, if_pos rfl,
        hsfxB v false bF hcv, if_pos (hbF ((hns v hv3 hv31 false).2 hcv))] at hwF
      rw [(hns u hu3 hu31 true).1 hcu', hsfxA u true false hcu', if_neg (by simp),
        hsfxA v true bT hcv'] at hwT
      have hEF : lowerEndpoint (u,v) false = 4 + prefixEval u lowerJB + prefixEval v lowerJB := by
        have h := hep false _ _ hwF
        simpa [e1213] using h
      have hETex : ∃ y : ℝ, 0 ≤ y ∧ y ≤ lowerJC ∧
          lowerEndpoint (u,v) true = 4 + prefixEval u lowerJA + prefixEval v y := by
        cases bT with
        | false =>
            refine ⟨lowerJA, hA0', hAC, ?_⟩
            have h := hep true _ _ hwT
            simpa [e3] using h
        | true =>
            refine ⟨lowerJC, hC0', le_refl _, ?_⟩
            have h := hep true _ _ hwT
            simpa [e3, e213] using h
      obtain ⟨y, hy0, hyC, hETv⟩ := hETex
      have hmu := (pe_mono_le u lowerJA lowerJB hA0' hAB).2 hpo
      have hmv := (pe_mono_le v lowerJC lowerJB hC0' hCB).2 hpvo
      have hmy := (pe_mono_le v y lowerJC hy0 hyC).2 hpvo
      rw [hIA, hIB, hEF, hETv]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [hP]
  intro x hx
  simp only [lowerJInner, Set.mem_uIcc] at hx
  simp only [lowerCover, Set.mem_Icc]
  obtain ⟨m1, m2, m3, m4⟩ := main
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩
