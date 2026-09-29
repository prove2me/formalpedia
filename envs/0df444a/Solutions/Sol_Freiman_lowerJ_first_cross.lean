-- Prove2me | solution 1 for Freiman.lowerJ_first_cross
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T16:02:54.59885+00:00
-- url     : https://prove2.me/submissions/f9884686-ddb3-4eab-8f62-cef22402b4eb

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

open Freiman

namespace M7JF

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

lemma pe_pos (w : List ℕ+) : ∀ (x : ℝ), 0 < x → 0 < prefixEval w x := by
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

lemma cd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact Nat.one_pos
  | append_singleton w a ih =>
      have h : lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
        simp [lowerCD, List.foldl_append]
      rw [h]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos a.property ih) (Nat.le_add_left _ _)

lemma mat_cd (w : List ℕ+) :
    (lowerInitialWordMatrix w).c = ((lowerCD w).1 : ℝ) ∧
    (lowerInitialWordMatrix w).d = ((lowerCD w).2 : ℝ) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨by simp [lowerInitialWordMatrix, lowerCD], by simp [lowerInitialWordMatrix, lowerCD]⟩
  | append_singleton w a ih =>
      have hm : lowerInitialWordMatrix (w ++ [a]) =
          lowerInitialMatMul (lowerInitialWordMatrix w) ⟨0,1,1,((a:ℕ):ℝ)⟩ := by
        simp [lowerInitialWordMatrix, List.foldl_append]
      have hcd : lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
        simp [lowerCD, List.foldl_append]
      rw [hm, hcd]
      refine ⟨?_, ?_⟩
      · simp only [lowerInitialMatMul, ih.1, ih.2]; ring
      · simp only [lowerInitialMatMul, ih.1, ih.2]; push_cast; ring

lemma sign_eq (m n : ℕ) (h : m % 2 = n % 2) : ((-1:ℝ))^m = ((-1:ℝ))^n := by
  rcases Nat.even_or_odd m with hm | hm
  · have hn : Even n := by rw [Nat.even_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]
  · have hn : Odd n := by rw [Nat.odd_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]

end M7JF

open M7JF

theorem solution (hf : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) (hq : lowerScale (lowerNormalize p) < lowerJHK k (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)) : lowerJFirstCross p k := by
  classical
  -- difference formula
  have pe_diff : ∀ (w : List ℕ+) (x y : ℝ), 0 < x → 0 < y →
      prefixEval w x - prefixEval w y
        = (-1:ℝ)^w.length * (x - y)
            / (lowerInitialMatDen (lowerInitialWordMatrix w) x
               * lowerInitialMatDen (lowerInitialWordMatrix w) y) := by
    intro w x y hx hy
    obtain ⟨ex, dx, detx⟩ := hf w x hx
    obtain ⟨ey, dy, -⟩ := hf w y hy
    simp only [lowerInitialMatEval, lowerInitialMatDen] at ex ey dx dy ⊢
    rw [ex, ey, div_sub_div _ _ (ne_of_gt dx) (ne_of_gt dy)]
    congr 1
    linear_combination (x - y) * detx
  have hcdpos : ∀ w : List ℕ+, (0:ℝ) < ((lowerCD w).2 : ℝ) := by
    intro w; exact_mod_cast cd_pos w
  have hrat0 : ∀ w : List ℕ+, 0 ≤ lowerRatio w := by
    intro w; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hden : ∀ (w : List ℕ+) (x : ℝ), lowerInitialMatDen (lowerInitialWordMatrix w) x
      = ((lowerCD w).2 : ℝ) * (1 + lowerRatio w * x) := by
    intro w x
    have hd := (hcdpos w).ne'
    simp only [lowerInitialMatDen, (mat_cd w).1, (mat_cd w).2, lowerRatio]
    field_simp
    ring
  have htau : ∀ j : ℕ, lowerJTau j = lowerRatio (List.replicate j (3:ℕ+)) := by
    intro j
    induction j with
    | zero => simp [lowerJTau, finiteCF, lowerRatio, lowerCD]
    | succ j ih =>
        have hcd : lowerCD (List.replicate (j+1) (3:ℕ+))
            = ((lowerCD (List.replicate j (3:ℕ+))).2,
               (lowerCD (List.replicate j (3:ℕ+))).1 + 3 * (lowerCD (List.replicate j (3:ℕ+))).2) := by
          rw [List.replicate_succ']; simp [lowerCD, List.foldl_append]
        have hd := (hcdpos (List.replicate j (3:ℕ+))).ne'
        have hDpos : (0:ℝ) < ((lowerCD (List.replicate j (3:ℕ+))).2 : ℝ) := hcdpos _
        have hCnn : (0:ℝ) ≤ ((lowerCD (List.replicate j (3:ℕ+))).1 : ℝ) := Nat.cast_nonneg _
        have hstep : lowerJTau (j+1) = 1/(3 + lowerJTau j) := by
          simp [lowerJTau, List.replicate_succ, finiteCF]
        rw [hstep, ih]
        simp only [lowerRatio, hcd]
        push_cast
        rw [div_eq_div_iff (by positivity) (by positivity)]
        field_simp
        ring
  -- the three constants
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hlo : (17/10:ℝ) < Real.sqrt 3 := by nlinarith
  have hhi : Real.sqrt 3 < (18/10:ℝ) := by nlinarith
  have hAval : lowerJA = 1 / (2 + Real.sqrt 3) := by
    have h : lowerJA = prefixEval [3] lowerTau := rfl
    rw [h]; norm_num [prefixEval, lowerTau]; ring
  have hAd : (0:ℝ) < 2 + Real.sqrt 3 := by linarith
  have hA0 : (0:ℝ) < lowerJA := by rw [hAval]; positivity
  have hA1 : lowerJA < (28/100:ℝ) := by rw [hAval, div_lt_iff₀ hAd]; linarith
  have hA2 : (26/100:ℝ) < lowerJA := by rw [hAval, lt_div_iff₀ hAd]; linarith
  have hCval : lowerJC = 1 / (2 + 1/(1 + lowerJA)) := by
    have h1 : lowerJC = prefixEval [2,1,3] lowerTau := rfl
    have h2 : lowerJA = prefixEval [3] lowerTau := rfl
    rw [h1, h2]; norm_num [prefixEval]
  have h1A : (0:ℝ) < 1 + lowerJA := by linarith
  have hx1 : 1/(1 + lowerJA) < (794/1000:ℝ) := by rw [div_lt_iff₀ h1A]; linarith
  have hx2 : (781/1000:ℝ) < 1/(1 + lowerJA) := by rw [lt_div_iff₀ h1A]; linarith
  have hCd : (0:ℝ) < 2 + 1/(1 + lowerJA) := by linarith
  have hC1 : (357/1000:ℝ) < lowerJC := by rw [hCval, lt_div_iff₀ hCd]; linarith
  have hC2 : lowerJC < (36/100:ℝ) := by rw [hCval, div_lt_iff₀ hCd]; linarith
  have hC0 : (0:ℝ) < lowerJC := by linarith
  have hBval : lowerJB = 1 / (1 + lowerJC) := by
    have h1 : lowerJB = prefixEval [1,2,1,3] lowerTau := rfl
    have h2 : lowerJC = prefixEval [2,1,3] lowerTau := rfl
    rw [h1, h2]; norm_num [prefixEval]
  have h1C : (0:ℝ) < 1 + lowerJC := by linarith
  have hB1 : (73/100:ℝ) < lowerJB := by rw [hBval, lt_div_iff₀ h1C]; linarith
  have hB2 : lowerJB < (74/100:ℝ) := by rw [hBval, div_lt_iff₀ h1C]; linarith
  have hDval : lowerJD = 1 / (3 + 1/(3 + lowerJB)) := by
    have h1 : lowerJD = prefixEval [3,3] lowerJB := rfl
    rw [h1]; norm_num [prefixEval]
  have h3B : (0:ℝ) < 3 + lowerJB := by linarith
  have hy1 : 1/(3 + lowerJB) < (2681/10000:ℝ) := by rw [div_lt_iff₀ h3B]; linarith
  have hy2 : (2673/10000:ℝ) < 1/(3 + lowerJB) := by rw [lt_div_iff₀ h3B]; linarith
  have hDd : (0:ℝ) < 3 + 1/(3 + lowerJB) := by linarith
  have hD1 : (305/1000:ℝ) < lowerJD := by rw [hDval, lt_div_iff₀ hDd]; linarith
  have hD2 : lowerJD < (307/1000:ℝ) := by rw [hDval, div_lt_iff₀ hDd]; linarith
  have hD0 : (0:ℝ) < lowerJD := by linarith
  have hAD : lowerJA < lowerJD := by linarith
  have hDC : lowerJD < lowerJC := by linarith
  -- setup
  have hmix : ¬ lowerMixed p := hr.1
  have hpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    unfold lowerMixed at hmix
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [lowerNormalize, if_pos hh]; omega
    · simp only [lowerNormalize, if_neg hh]; omega
  set Z := lowerNormalize p with hZ
  set R := List.replicate k (3:ℕ+) with hRdef
  set IA := prefixEval R lowerJA with hIAdef
  set IC := prefixEval R lowerJC with hICdef
  set ID := prefixEval R lowerJD with hIDdef
  have hIAp : 0 < IA := pe_pos _ _ hA0
  have hICp : 0 < IC := pe_pos _ _ hC0
  have hIDp : 0 < ID := pe_pos _ _ hD0
  have ha1p : 0 < lowerInitialMatDen (lowerInitialWordMatrix Z.1) ID := (hf Z.1 ID hIDp).2.1
  have ha2p : 0 < lowerInitialMatDen (lowerInitialWordMatrix Z.1) IA := (hf Z.1 IA hIAp).2.1
  have hb1p : 0 < lowerInitialMatDen (lowerInitialWordMatrix Z.2) ID := (hf Z.2 ID hIDp).2.1
  have hb2p : 0 < lowerInitialMatDen (lowerInitialWordMatrix Z.2) IC := (hf Z.2 IC hICp).2.1
  have hn1p : 0 < lowerInitialMatDen (lowerInitialWordMatrix R) lowerJA := (hf R lowerJA hA0).2.1
  have hn2p : 0 < lowerInitialMatDen (lowerInitialWordMatrix R) lowerJC := (hf R lowerJC hC0).2.1
  have hn3p : 0 < lowerInitialMatDen (lowerInitialWordMatrix R) lowerJD := (hf R lowerJD hD0).2.1
  have P1 := pe_diff Z.1 ID IA hIDp hIAp
  have P2 := pe_diff Z.2 ID IC hIDp hICp
  have PN1 := pe_diff R lowerJD lowerJA hD0 hA0
  have PN2 := pe_diff R lowerJD lowerJC hD0 hC0
  have hlenR : R.length = k := by simp [hRdef]
  rw [hlenR] at PN1 PN2
  set a1 := lowerInitialMatDen (lowerInitialWordMatrix Z.1) ID with ha1
  set a2 := lowerInitialMatDen (lowerInitialWordMatrix Z.1) IA with ha2
  set b1 := lowerInitialMatDen (lowerInitialWordMatrix Z.2) ID with hb1
  set b2 := lowerInitialMatDen (lowerInitialWordMatrix Z.2) IC with hb2
  set n1 := lowerInitialMatDen (lowerInitialWordMatrix R) lowerJA with hn1
  set n2 := lowerInitialMatDen (lowerInitialWordMatrix R) lowerJC with hn2
  set n3 := lowerInitialMatDen (lowerInitialWordMatrix R) lowerJD with hn3
  have hsgn : ((-1:ℝ))^Z.2.length = ((-1:ℝ))^Z.1.length := sign_eq _ _ hpar.symm
  -- the two parameter ratios and denominators
  have hrZ1 := hden Z.1
  have hrZ2 := hden Z.2
  have hrR := hden R
  have hRtau : lowerRatio R = lowerJTau k := (htau k).symm
  have hd1p : (0:ℝ) < ((lowerCD Z.1).2 : ℝ) := hcdpos _
  have hd2p : (0:ℝ) < ((lowerCD Z.2).2 : ℝ) := hcdpos _
  have hdNp : (0:ℝ) < ((lowerCD R).2 : ℝ) := hcdpos _
  have hr0 : (0:ℝ) ≤ lowerRatio Z.1 := hrat0 _
  have hs0' : (0:ℝ) ≤ lowerRatio Z.2 := hrat0 _
  have ht0 : (0:ℝ) ≤ lowerJTau k := by rw [← hRtau]; exact hrat0 _
  -- the transfer of the scale bound
  have hHKval : lowerJHK k (lowerRatio Z.1) (lowerRatio Z.2)
      = ((lowerJD - lowerJA)*(1+lowerJTau k*lowerJC)*((1+lowerRatio Z.2*IC)*(1+lowerRatio Z.2*ID)))
        / ((lowerJC - lowerJD)*(1+lowerJTau k*lowerJA)*((1+lowerRatio Z.1*IA)*(1+lowerRatio Z.1*ID))) := by
    have h1 : lowerJIter k lowerJA = IA := rfl
    have h2 : lowerJIter k lowerJC = IC := rfl
    have h3 : lowerJIter k lowerJD = ID := rfl
    have hne1 : lowerJC - lowerJD ≠ 0 := by intro hcon; linarith [hDC]
    have hp2 : (0:ℝ) < 1 + lowerJTau k * lowerJA := by
      have := mul_nonneg ht0 (le_of_lt hA0); linarith
    have hp3 : (0:ℝ) < 1 + lowerRatio Z.1 * IA := by
      have := mul_nonneg hr0 (le_of_lt hIAp); linarith
    have hp4 : (0:ℝ) < 1 + lowerRatio Z.1 * ID := by
      have := mul_nonneg hr0 (le_of_lt hIDp); linarith
    simp only [lowerJHK, lowerJH, lowerJCoeff, h1, h2, h3]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  rw [show lowerScale Z = (((lowerCD Z.1).2:ℝ))^2/(((lowerCD Z.2).2:ℝ))^2 from rfl, hHKval,
    div_lt_div_iff₀ (by positivity) (by positivity)] at hq
  have TGT : (lowerJC - lowerJD)*n1*a1*a2 < (lowerJD - lowerJA)*n2*b1*b2 := by
    have e1 : a1 = ((lowerCD Z.1).2:ℝ)*(1+lowerRatio Z.1*ID) := by rw [ha1, hrZ1 ID]
    have e2 : a2 = ((lowerCD Z.1).2:ℝ)*(1+lowerRatio Z.1*IA) := by rw [ha2, hrZ1 IA]
    have e3 : b1 = ((lowerCD Z.2).2:ℝ)*(1+lowerRatio Z.2*ID) := by rw [hb1, hrZ2 ID]
    have e4 : b2 = ((lowerCD Z.2).2:ℝ)*(1+lowerRatio Z.2*IC) := by rw [hb2, hrZ2 IC]
    have e5 : n1 = ((lowerCD R).2:ℝ)*(1+lowerJTau k*lowerJA) := by
      rw [hn1, hrR lowerJA, hRtau]
    have e6 : n2 = ((lowerCD R).2:ℝ)*(1+lowerJTau k*lowerJC) := by
      rw [hn2, hrR lowerJC, hRtau]
    have heqL : (lowerJC - lowerJD)*n1*a1*a2
        = ((lowerCD R).2:ℝ) * ((((lowerCD Z.1).2:ℝ))^2 *
            ((lowerJC - lowerJD)*(1+lowerJTau k*lowerJA)*((1+lowerRatio Z.1*IA)*(1+lowerRatio Z.1*ID)))) := by
      rw [e1, e2, e5]; ring
    have heqR : (lowerJD - lowerJA)*n2*b1*b2
        = ((lowerCD R).2:ℝ) * (((lowerJD - lowerJA)*(1+lowerJTau k*lowerJC)*((1+lowerRatio Z.2*IC)*(1+lowerRatio Z.2*ID)))
            * (((lowerCD Z.2).2:ℝ))^2) := by
      rw [e3, e4, e6]; ring
    rw [heqL, heqR]
    exact mul_lt_mul_of_pos_left hq hdNp
  -- the sign identity
  have hsum : (prefixEval Z.1 ID - prefixEval Z.1 IA) + (prefixEval Z.2 ID - prefixEval Z.2 IC)
      = ((-1:ℝ)^Z.1.length * (-1:ℝ)^k) *
        ((lowerJD - lowerJA)/(n3*n1*a1*a2) + (lowerJD - lowerJC)/(n3*n2*b1*b2)) := by
    rw [P1, P2, PN1, PN2, hsgn]
    field_simp
  have hDen1 : (0:ℝ) < n3*n1*a1*a2 := mul_pos (mul_pos (mul_pos hn3p hn1p) ha1p) ha2p
  have hDen2 : (0:ℝ) < n3*n2*b1*b2 := mul_pos (mul_pos (mul_pos hn3p hn2p) hb1p) hb2p
  have hW : 0 < (lowerJD - lowerJA)/(n3*n1*a1*a2) + (lowerJD - lowerJC)/(n3*n2*b1*b2) := by
    rw [div_add_div _ _ (ne_of_gt hDen1) (ne_of_gt hDen2)]
    apply div_pos _ (mul_pos hDen1 hDen2)
    have hpos : 0 < n3 * ((lowerJD - lowerJA)*n2*b1*b2 - (lowerJC - lowerJD)*n1*a1*a2) :=
      mul_pos hn3p (by linarith)
    linarith [hpos]
  -- conclude
  have hIB2 : lowerJIter (k+2) lowerJB = ID := by
    have hsplit : List.replicate (k+2) (3:ℕ+) = R ++ List.replicate 2 (3:ℕ+) := by
      rw [hRdef, ← List.replicate_add]
    simp only [lowerJIter, hsplit, pe_append]
    rfl
  have hIAk : lowerJIter k lowerJA = IA := rfl
  have hICk : lowerJIter k lowerJC = IC := rfl
  by_cases hev : lowerJEven p k
  · have hE : ((-1:ℝ)^Z.1.length * (-1:ℝ)^k) = 1 := by
      rw [← pow_add]
      exact (Nat.even_iff.mpr hev).neg_one_pow
    rw [hE, one_mul] at hsum
    simp only [lowerJFirstCross, if_pos hev, lowerJInnerA, lowerJInnerB, lowerJActual,
      hIB2, hIAk, hICk, ← hZ]
    linarith
  · have hO : Odd (Z.1.length + k) := by
      rw [Nat.odd_iff]
      have : ¬ ((Z.1.length + k) % 2 = 0) := hev
      omega
    have hE : ((-1:ℝ)^Z.1.length * (-1:ℝ)^k) = -1 := by
      rw [← pow_add]; exact hO.neg_one_pow
    rw [hE] at hsum
    simp only [lowerJFirstCross, if_neg hev, lowerJInnerA, lowerJInnerB, lowerJActual,
      hIB2, hIAk, hICk, ← hZ]
    linarith
