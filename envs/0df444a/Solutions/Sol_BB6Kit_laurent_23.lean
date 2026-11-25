-- Prove2me | solution 1 for BB6Kit.laurent_23
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-25T15:45:46.515814+00:00
-- url     : https://prove2.me/submissions/838900bc-45d3-4786-b663-239b96fe6f34

import Mathlib

/-
  Elementary Pade proof of a polynomial lower bound for |u log 2 - v log 3|
  (|u log 2 - v log 3| > 2^-100 v^-75 for all positive u, v), and the bridge to the
  Laurent-type normalization of BB6Kit.laurent_23. Degree-16 Pade block; denominator
  lcm(1..8n+1) <= 2 (7/2)^(8n) from a binomial recurrence. No Baker theory, no zero estimates.
-/

-- ===== PadeShape =====
/-! Rational Bernstein certificates for the degree-16 Padé shape. -/
namespace CollatzPade

def shapeNumerator (x : ℝ) : ℝ :=
  32 * (x - 2)^5 * (x - 3)^8 * (4 - x)^3

private def gap (x : ℝ) : ℝ := 3 * x^8 - 16 * 6561 * shapeNumerator x

theorem padeShapeCell0 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap (2 + (1 / 4) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap (2 + (1 / 4) * t) =
      768 * t^0 * (1-t)^16 +
      13056 * t^1 * (1-t)^15 +
      104016 * t^2 * (1-t)^14 +
      515508 * t^3 * (1-t)^13 +
      (14231049 / 8) * t^4 * (1-t)^12 +
      (72091437 / 16) * t^5 * (1-t)^11 +
      (2199381573 / 256) * t^6 * (1-t)^10 +
      (12777971019 / 1024) * t^7 * (1-t)^9 +
      (908707543491 / 65536) * t^8 * (1-t)^8 +
      (96439882851 / 8192) * t^9 * (1-t)^7 +
      (124261317621 / 16384) * t^10 * (1-t)^6 +
      (29949991785 / 8192) * t^11 * (1-t)^5 +
      (42193207071 / 32768) * t^12 * (1-t)^4 +
      (5222116413 / 16384) * t^13 * (1-t)^3 +
      (3407068251 / 65536) * t^14 * (1-t)^2 +
      (5208653241 / 1048576) * t^15 * (1-t)^1 +
      (1764915561 / 8388608) * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell0_on (x : ℝ) (ha : 2 ≤ x)
    (hb : x ≤ (9 / 4)) : 0 ≤ gap x := by
  let t : ℝ := (x - 2) / (1 / 4)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : 2 + (1 / 4) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell0 t ht h1

theorem padeShapeCell1 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap ((9 / 4) + (1 / 8) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap ((9 / 4) + (1 / 8) * t) =
      (1764915561 / 8388608) * t^0 * (1-t)^16 +
      (5380840125 / 2097152) * t^1 * (1-t)^15 +
      (29193648453 / 2097152) * t^2 * (1-t)^14 +
      (368847511785 / 8388608) * t^3 * (1-t)^13 +
      (2993357710341 / 33554432) * t^4 * (1-t)^12 +
      (4179118938489 / 33554432) * t^5 * (1-t)^11 +
      (300671595567 / 2097152) * t^6 * (1-t)^10 +
      (27546986230533 / 134217728) * t^7 * (1-t)^9 +
      (403955417113815 / 1073741824) * t^8 * (1-t)^8 +
      (320784827368359 / 536870912) * t^9 * (1-t)^7 +
      (375036055322685 / 536870912) * t^10 * (1-t)^6 +
      (1260578058711051 / 2147483648) * t^11 * (1-t)^5 +
      (3028161411456081 / 8589934592) * t^12 * (1-t)^4 +
      (1274857861160163 / 8589934592) * t^13 * (1-t)^3 +
      (179418458439219 / 4294967296) * t^14 * (1-t)^2 +
      (243330252701511 / 34359738368) * t^15 * (1-t)^1 +
      (301299200323089 / 549755813888) * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell1_on (x : ℝ) (ha : (9 / 4) ≤ x)
    (hb : x ≤ (19 / 8)) : 0 ≤ gap x := by
  let t : ℝ := (x - (9 / 4)) / (1 / 8)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : (9 / 4) + (1 / 8) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell1 t ht h1

theorem padeShapeCell2 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap ((19 / 8) + (1 / 8) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap ((19 / 8) + (1 / 8) * t) =
      (301299200323089 / 549755813888) * t^0 * (1-t)^16 +
      (359268147944667 / 34359738368) * t^1 * (1-t)^15 +
      (793604024040273 / 8589934592) * t^2 * (1-t)^14 +
      (1078460825098419 / 2147483648) * t^3 * (1-t)^13 +
      (504971904802305 / 268435456) * t^4 * (1-t)^12 +
      (691645072867479 / 134217728) * t^5 * (1-t)^11 +
      (358592187577353 / 33554432) * t^6 * (1-t)^10 +
      (143679444575787 / 8388608) * t^7 * (1-t)^9 +
      (359944242461031 / 16777216) * t^8 * (1-t)^8 +
      (5527560415419 / 262144) * t^9 * (1-t)^7 +
      (4250878849371 / 262144) * t^10 * (1-t)^6 +
      (79135933689 / 8192) * t^11 * (1-t)^5 +
      (143268899145 / 32768) * t^12 * (1-t)^4 +
      (46529433 / 32) * t^13 * (1-t)^3 +
      (343266267 / 1024) * t^14 * (1-t)^2 +
      (3064563 / 64) * t^15 * (1-t)^1 +
      (817581 / 256) * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell2_on (x : ℝ) (ha : (19 / 8) ≤ x)
    (hb : x ≤ (5 / 2)) : 0 ≤ gap x := by
  let t : ℝ := (x - (19 / 8)) / (1 / 8)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : (19 / 8) + (1 / 8) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell2 t ht h1

theorem padeShapeCell3 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap ((5 / 2) + (1 / 2) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap ((5 / 2) + (1 / 2) * t) =
      (817581 / 256) * t^0 * (1-t)^16 +
      (511671 / 8) * t^1 * (1-t)^15 +
      (37083117 / 64) * t^2 * (1-t)^14 +
      (101313633 / 32) * t^3 * (1-t)^13 +
      (1503677625 / 128) * t^4 * (1-t)^12 +
      (1011050769 / 32) * t^5 * (1-t)^11 +
      (4104748461 / 64) * t^6 * (1-t)^10 +
      (3225020187 / 32) * t^7 * (1-t)^9 +
      (31829938851 / 256) * t^8 * (1-t)^8 +
      (1936775709 / 16) * t^9 * (1-t)^7 +
      (1483907229 / 16) * t^10 * (1-t)^6 +
      (221357367 / 4) * t^11 * (1-t)^5 +
      (201679065 / 8) * t^12 * (1-t)^4 +
      8476083 * t^13 * (1-t)^3 +
      1983609 * t^14 * (1-t)^2 +
      288684 * t^15 * (1-t)^1 +
      19683 * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell3_on (x : ℝ) (ha : (5 / 2) ≤ x)
    (hb : x ≤ 3) : 0 ≤ gap x := by
  let t : ℝ := (x - (5 / 2)) / (1 / 2)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : (5 / 2) + (1 / 2) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell3 t ht h1

theorem padeShapeCell4 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap (3 + (1 / 2) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap (3 + (1 / 2) * t) =
      19683 * t^0 * (1-t)^16 +
      341172 * t^1 * (1-t)^15 +
      2770929 * t^2 * (1-t)^14 +
      13997529 * t^3 * (1-t)^13 +
      (393796809 / 8) * t^4 * (1-t)^12 +
      (511127253 / 4) * t^5 * (1-t)^11 +
      (4052603205 / 16) * t^6 * (1-t)^10 +
      (6257020887 / 16) * t^7 * (1-t)^9 +
      (121671139395 / 256) * t^8 * (1-t)^8 +
      (14595936267 / 32) * t^9 * (1-t)^7 +
      (22035199629 / 64) * t^10 * (1-t)^6 +
      (6462451209 / 32) * t^11 * (1-t)^5 +
      (11515451289 / 128) * t^12 * (1-t)^4 +
      (937191945 / 32) * t^13 * (1-t)^3 +
      (418131741 / 64) * t^14 * (1-t)^2 +
      (14199045 / 16) * t^15 * (1-t)^1 +
      (14105757 / 256) * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell4_on (x : ℝ) (ha : 3 ≤ x)
    (hb : x ≤ (7 / 2)) : 0 ≤ gap x := by
  let t : ℝ := (x - 3) / (1 / 2)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : 3 + (1 / 2) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell4 t ht h1

theorem padeShapeCell5 (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ gap ((7 / 2) + (1 / 2) * t) := by
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr h1
  have he : gap ((7 / 2) + (1 / 2) * t) =
      (14105757 / 256) * t^0 * (1-t)^16 +
      (14012469 / 16) * t^1 * (1-t)^15 +
      (406937181 / 64) * t^2 * (1-t)^14 +
      (888678549 / 32) * t^3 * (1-t)^13 +
      (10351027977 / 128) * t^4 * (1-t)^12 +
      (5267685285 / 32) * t^5 * (1-t)^11 +
      (15391259733 / 64) * t^6 * (1-t)^10 +
      (8377010595 / 32) * t^7 * (1-t)^9 +
      (61270996035 / 256) * t^8 * (1-t)^8 +
      (936525285 / 4) * t^9 * (1-t)^7 +
      258397221 * t^10 * (1-t)^6 +
      248891184 * t^11 * (1-t)^5 +
      171784992 * t^12 * (1-t)^4 +
      77202432 * t^13 * (1-t)^3 +
      20729856 * t^14 * (1-t)^2 +
      2949120 * t^15 * (1-t)^1 +
      196608 * t^16 * (1-t)^0 := by
    unfold gap shapeNumerator
    ring
  rw [he]
  positivity

theorem padeShapeCell5_on (x : ℝ) (ha : (7 / 2) ≤ x)
    (hb : x ≤ 4) : 0 ≤ gap x := by
  let t : ℝ := (x - (7 / 2)) / (1 / 2)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have h1 : t ≤ 1 := by dsimp [t]; linarith
  have hx : (7 / 2) + (1 / 2) * t = x := by dsimp [t]; ring
  simpa only [hx] using padeShapeCell5 t ht h1

theorem shapeNumerator_nonneg (x : ℝ) (hx : 2 ≤ x) (hy : x ≤ 4) :
    0 ≤ shapeNumerator x := by
  unfold shapeNumerator
  have ha : 0 ≤ x - 2 := sub_nonneg.mpr hx
  have hb : 0 ≤ 4 - x := sub_nonneg.mpr hy
  positivity

theorem shapeNumerator_pos (x : ℝ) (hx : 2 < x) (hy : x < 4)
    (hz : x ≠ 3) : 0 < shapeNumerator x := by
  unfold shapeNumerator
  have ha : 0 < x - 2 := sub_pos.mpr hx
  have hb : 0 < 4 - x := sub_pos.mpr hy
  have hc : 0 ≤ (x - 3)^8 := by positivity
  have hd : (x - 3)^8 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have he : 0 < (x - 3)^8 := lt_of_le_of_ne hc (Ne.symm hd)
  positivity

theorem shape_bound (x : ℝ) (hx : 2 ≤ x) (hy : x ≤ 4) :
    (3 : ℝ)^8 * (shapeNumerator x / x^8) ≤ 3 / 16 := by
  have hg : 0 ≤ gap x := by
    by_cases h0 : x ≤ 9/4
    · exact padeShapeCell0_on x hx h0
    by_cases h1 : x ≤ 19/8
    · exact padeShapeCell1_on x (le_of_not_ge h0) h1
    by_cases h2 : x ≤ 5/2
    · exact padeShapeCell2_on x (le_of_not_ge h1) h2
    by_cases h3 : x ≤ 3
    · exact padeShapeCell3_on x (le_of_not_ge h2) h3
    by_cases h4 : x ≤ 7/2
    · exact padeShapeCell4_on x (le_of_not_ge h3) h4
    · exact padeShapeCell5_on x (le_of_not_ge h4) hy
  have hpow : 0 < x^8 := pow_pos (by linarith) _
  calc
    (3 : ℝ)^8 * (shapeNumerator x / x^8)
        = ((3 : ℝ)^8 * shapeNumerator x) / x^8 := by ring
    _ ≤ 3/16 := (div_le_iff₀ hpow).2 (by
      unfold gap at hg
      norm_num
      linarith only [hg])

end CollatzPade

open CollatzPade

#print axioms CollatzPade.shape_bound
#print axioms CollatzPade.shapeNumerator_pos

-- ===== PadeEscape =====
/-! Arithmetic end of the degree-16 Padé separation. -/
namespace CollatzPade

noncomputable def padeR : ℝ := 16 / 3
noncomputable def padeG : ℝ := 57610828800000

theorem pade_powers_escape (q : ℕ) :
    ∃ n : ℕ, (3 : ℝ)/2 * (q : ℝ) < padeR^n := by
  have hs : ∀ n : ℕ, (n : ℝ) + 1 ≤ padeR^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hn : 0 ≤ (n : ℝ) := by positivity
      rw [Nat.cast_succ, pow_succ]
      calc
        (n : ℝ) + 1 + 1 ≤ ((n : ℝ) + 1) * padeR := by
          unfold padeR
          linarith only [hn]
        _ ≤ padeR^n * padeR := mul_le_mul_of_nonneg_right ih
          (by norm_num [padeR])
  obtain ⟨n, hn⟩ := exists_nat_gt ((3 : ℝ)/2 * (q : ℝ))
  exact ⟨n, lt_of_lt_of_le hn (le_trans (by linarith) (hs n))⟩

theorem pade_no_adjacent_zero (A N : ℕ → ℤ) (L : ℝ)
    (hp : ∀ i, 0 < (A i : ℝ) * L + (N i : ℝ))
    (ha : ∀ i, ((0 < A i) ∧ A (i+1) < 0) ∨
      ((A i < 0) ∧ 0 < A (i+1))) (i : ℕ) :
    N i ≠ 0 ∨ N (i+1) ≠ 0 := by
  by_contra! hz
  have hp0 := hp i
  have hp1 := hp (i+1)
  rw [hz.1, Int.cast_zero, add_zero] at hp0
  rw [hz.2, Int.cast_zero, add_zero] at hp1
  rcases ha i with ⟨a,b⟩ | ⟨a,b⟩
  · have a' : 0 < (A i : ℝ) := by exact_mod_cast a
    have b' : (A (i+1) : ℝ) < 0 := by exact_mod_cast b
    by_cases hL : 0 < L
    · exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
        b'.le hL.le)) hp1
    · exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
        a'.le (le_of_not_gt hL))) hp0
  · have a' : (A i : ℝ) < 0 := by exact_mod_cast a
    have b' : 0 < (A (i+1) : ℝ) := by exact_mod_cast b
    by_cases hL : 0 < L
    · exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
        a'.le hL.le)) hp0
    · exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
        b'.le (le_of_not_gt hL))) hp1

theorem padeEscape (q : ℕ) (hq : 0 < q) (L : ℝ) (A N : ℕ → ℤ)
    (hp : ∀ i, 0 < (A i : ℝ) * L + (N i : ℝ))
    (he : ∀ i, (A i : ℝ) * L + (N i : ℝ) ≤
      (3 : ℝ)/4 * (q : ℝ) * ((3 : ℝ)/16)^i)
    (ha : ∀ i, ((0 < A i) ∧ A (i+1) < 0) ∨
      ((A i < 0) ∧ 0 < A (i+1)))
    (hA : ∀ i, |(A i : ℝ)| ≤ 18 * padeG^i) :
    (1 : ℝ) / (2^128 * (q : ℝ)^19) < |L| := by
  classical
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqN : (1 : ℕ) ≤ q := by omega
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hqN
  let n := Nat.find (pade_powers_escape q)
  have hn : (3 : ℝ)/2 * (q : ℝ) < padeR^n :=
    Nat.find_spec (pade_powers_escape q)
  have hn0 : n ≠ 0 := by
    intro hn'
    rw [hn', pow_zero] at hn
    linarith only [hq1, hn]
  let k := n - 1
  have hk : k+1 = n := by dsimp [k]; omega
  have hkmin : padeR^k ≤ (3 : ℝ)/2 * (q : ℝ) := by
    apply le_of_not_gt
    apply Nat.find_min (pade_powers_escape q)
    change k < n
    omega
  obtain ⟨j,hjn,hjj,hjN⟩ : ∃ j : ℕ, n ≤ j ∧ j ≤ n+1 ∧ N j ≠ 0 := by
    rcases pade_no_adjacent_zero A N L hp ha n with h | h
    · exact ⟨n, Nat.le_refl _, by omega, h⟩
    · exact ⟨n+1, by omega, Nat.le_refl _, h⟩
  have hr1 : 1 ≤ padeR := by norm_num [padeR]
  have hg1 : 1 ≤ padeG := by norm_num [padeG]
  have hjr : 0 < padeR^j := by
    exact pow_pos (by norm_num [padeR]) _
  have hrj : (3 : ℝ)/2 * (q : ℝ) < padeR^j :=
    lt_of_lt_of_le hn (pow_le_pow_right₀ hr1 hjn)
  have hinv : ((3 : ℝ)/16)^j = 1 / padeR^j := by
    rw [← one_div_pow]
    congr 1
    norm_num [padeR]
  have hh : (A j : ℝ) * L + (N j : ℝ) < 1/2 := by
    apply lt_of_le_of_lt (he j)
    rw [hinv, mul_one_div]
    apply (div_lt_iff₀ hjr).2
    linarith only [hrj]
  have hhabs : |(A j : ℝ) * L + (N j : ℝ)| < 1/2 := by
    rw [abs_of_pos (hp j)]
    exact hh
  have hNint : (1 : ℤ) ≤ |N j| := by
    have hh' := abs_pos.mpr hjN
    omega
  have hNreal : (1 : ℝ) ≤ |(N j : ℝ)| := by exact_mod_cast hNint
  have htri : |(N j : ℝ)| ≤ |(A j : ℝ) * L + (N j : ℝ)| +
      |(A j : ℝ)| * |L| := by
    calc
      |(N j : ℝ)| = |((A j : ℝ) * L + (N j : ℝ)) +
          -((A j : ℝ) * L)| := by
            rw [show (A j : ℝ) * L + (N j : ℝ) +
              -((A j : ℝ) * L) = (N j : ℝ) by ring]
      _ ≤ |(A j : ℝ) * L + (N j : ℝ)| +
          |-((A j : ℝ) * L)| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_mul]
  have hprod : 1/2 < 18 * padeG^j * |L| := by
    have hprod0 : 1/2 < |(A j : ℝ)| * |L| :=
      by linarith only [hNreal, htri, hhabs]
    exact lt_of_lt_of_le hprod0
      (mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _))
  have hG : padeG ≤ padeR^19 := by norm_num [padeG,padeR]
  have hG0 : 0 ≤ padeG := by norm_num [padeG]
  have hGk : padeG^k ≤ (((3 : ℝ)/2) * (q : ℝ))^19 := by
    calc
      padeG^k ≤ (padeR^19)^k := pow_le_pow_left₀ hG0 hG _
      _ = (padeR^k)^19 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 19 k]
      _ ≤ _ := pow_le_pow_left₀ (pow_nonneg
        (by norm_num [padeR]) k) hkmin _
  have hkj : j ≤ k+2 := by omega
  have hGj : padeG^j ≤ padeG^2 * (((3 : ℝ)/2) * (q : ℝ))^19 := by
    calc
      padeG^j ≤ padeG^(k+2) := pow_le_pow_right₀ hg1 hkj
      _ = padeG^2 * padeG^k := by rw [pow_add, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hGk (sq_nonneg _)
  have hC : (36 : ℝ) * padeG^2 * ((3 : ℝ)/2)^19 ≤ 2^128 := by
    norm_num [padeG]
  have hpre : 36 * padeG^j ≤ (2 : ℝ)^128 * (q : ℝ)^19 := by
    calc
      36 * padeG^j ≤ 36 *
          (padeG^2 * (((3 : ℝ)/2) * (q : ℝ))^19) :=
        mul_le_mul_of_nonneg_left hGj (by norm_num)
      _ = (36 * padeG^2 * ((3 : ℝ)/2)^19) * (q : ℝ)^19 := by
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  have hbig : (1 : ℝ) < (2^128 * (q : ℝ)^19) * |L| := by
    have hh' := mul_le_mul_of_nonneg_right hpre (abs_nonneg L)
    linarith only [hh', hprod]
  exact (div_lt_iff₀ (by positivity)).2 (by simpa [mul_comm] using hbig)

end CollatzPade

open CollatzPade
#print axioms CollatzPade.padeEscape

-- ===== PadeIntegrals =====
/-! Laurent term integration and the two degree-16 error bounds. -/
open Set MeasureTheory intervalIntegral

namespace CollatzPade

theorem pade_laurent_term (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (z : ℤ) :
    (∫ x in a..b, x^(z-1)) =
      if z = 0 then Real.log (b/a) else (b^z-a^z)/(z : ℝ) := by
  by_cases hz : z = 0
  · subst z
    simpa only [zero_sub, zpow_neg_one, if_pos rfl, if_true] using
      (integral_inv_of_pos ha hb)
  · have hk : z - 1 ≠ -1 := by omega
    have h0 : (0 : ℝ) ∉ uIcc a b := notMem_uIcc_of_lt ha hb
    have ih := integral_zpow (a := a) (b := b) (n := z - 1)
      (Or.inr ⟨hk,h0⟩)
    simpa only [if_neg hz, sub_add_cancel, Int.cast_sub, Int.cast_one]
      using ih

theorem pade_laurent_integrable (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (z : ℤ) (c : ℝ) :
    IntervalIntegrable (fun x : ℝ => c*x^(z-1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.mul
  apply continuousOn_id.zpow₀
  intro x hx
  left
  exact ne_of_gt (lt_of_lt_of_le (lt_min ha hb) hx.1)

theorem pade_laurent_sum {ι : Type*} (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, ∑ j ∈ s, c j * x^(e j-1)) =
      ∑ j ∈ s, c j * (if e j = 0 then Real.log (b/a)
        else (b^(e j)-a^(e j))/(e j : ℝ)) := by
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => pade_laurent_integrable a b ha hb (e i) (c i))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul,
    pade_laurent_term a b ha hb]

noncomputable def padeWeight (n : ℕ) (D x : ℝ) : ℝ :=
  D * (shapeNumerator x / x^8)^n

theorem pade_weight_nonneg (n : ℕ) (D x : ℝ) (hD : 0 ≤ D)
    (h2 : 2 ≤ x) (h4 : x ≤ 4) : 0 ≤ padeWeight n D x := by
  have hx : 0 ≤ x := by linarith
  unfold padeWeight
  exact mul_nonneg hD
    (pow_nonneg (div_nonneg (shapeNumerator_nonneg x h2 h4)
      (pow_nonneg hx _)) _)

theorem pade_weight_bound (n : ℕ) (D x : ℝ)
    (hD : D ≤ (3 : ℝ)^(8*n+1)) (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    padeWeight n D x ≤ 3 * ((3 : ℝ)/16)^n := by
  have hx : 0 ≤ x := by linarith
  have hq : 0 ≤ shapeNumerator x / x^8 :=
    div_nonneg (shapeNumerator_nonneg x h2 h4) (pow_nonneg hx _)
  unfold padeWeight
  calc
    D * (shapeNumerator x / x^8)^n ≤
        3^(8*n+1) * (shapeNumerator x / x^8)^n :=
      mul_le_mul_of_nonneg_right hD (pow_nonneg hq _)
    _ = 3 * ((3 : ℝ)^8 * (shapeNumerator x / x^8))^n := by
      rw [pow_succ, pow_mul, mul_pow]
      ring
    _ ≤ 3 * ((3 : ℝ)/16)^n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by norm_num) hq)
        (shape_bound x h2 h4) _) (by norm_num)

theorem pade_weight_cont (n : ℕ) (D a b : ℝ) (ha : 0 < a) :
    ContinuousOn (padeWeight n D) (Icc a b) := by
  unfold padeWeight
  apply continuousOn_const.mul
  apply ContinuousOn.pow
  apply ContinuousOn.div₀
  · unfold shapeNumerator
    fun_prop
  · fun_prop
  · intro x hx
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hx.1))

theorem pade_lobeL_cont (n : ℕ) (D : ℝ) :
    ContinuousOn (fun x : ℝ => ((3-x)/x)*padeWeight n D x)
      (Icc 2 3) := by
  apply ContinuousOn.mul _ (pade_weight_cont n D 2 3 (by norm_num))
  apply ContinuousOn.div₀
  · fun_prop
  · fun_prop
  · intro x hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hx.1)

theorem pade_lobeR_cont (n : ℕ) (D : ℝ) :
    ContinuousOn (fun x : ℝ => ((x-3)/x)*padeWeight n D x)
      (Icc 3 4) := by
  apply ContinuousOn.mul _ (pade_weight_cont n D 3 4 (by norm_num))
  apply ContinuousOn.div₀
  · fun_prop
  · fun_prop
  · intro x hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) hx.1)

theorem pade_left_positive (n : ℕ) (D : ℝ) (hD : 0 < D) :
    0 < ∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n D x := by
  apply intervalIntegral.integral_pos (by norm_num) (pade_lobeL_cont n D)
  · intro x hx
    have h2 := hx.1.le
    have h3 := hx.2
    have hp : 0 ≤ x := by linarith
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr h3) hp)
      (pade_weight_nonneg n D x hD.le h2 (by linarith))
  · refine ⟨(5:ℝ)/2, by norm_num, ?_⟩
    unfold padeWeight
    have hq := shapeNumerator_pos ((5:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num)
    positivity

theorem pade_right_positive (n : ℕ) (D : ℝ) (hD : 0 < D) :
    0 < ∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n D x := by
  apply intervalIntegral.integral_pos (by norm_num) (pade_lobeR_cont n D)
  · intro x hx
    have h3 := hx.1.le
    have hp : 0 ≤ x := by linarith
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr h3) hp)
      (pade_weight_nonneg n D x hD.le (by linarith) hx.2)
  · refine ⟨(7:ℝ)/2, by norm_num, ?_⟩
    unfold padeWeight
    have hq := shapeNumerator_pos ((7:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num)
    positivity

theorem pade_left_bound (n : ℕ) (D : ℝ)
    (hD0 : 0 ≤ D) (hD : D ≤ 3^(8*n+1)) :
    (∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n D x)
      ≤ (3:ℝ)/4 * ((3:ℝ)/16)^n := by
  let A : ℝ := 3/2 * ((3:ℝ)/16)^n
  have ca : ContinuousOn (fun x : ℝ => A * (3-x)) (Icc 2 3) :=
    by fun_prop
  have hi : IntervalIntegrable
      (fun x : ℝ => ((3-x)/x)*padeWeight n D x) volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] using pade_lobeL_cont n D
  have hia : IntervalIntegrable (fun x : ℝ => A*(3-x))
      volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] using ca
  have hle : (∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n D x)
      ≤ (∫ x in (2:ℝ)..3, A*(3-x)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hia
    intro x hx
    have h2 := hx.1
    have h3 := hx.2
    have h4 : x ≤ 4 := by linarith
    have hpos : 0 < x := by linarith
    have hn := sub_nonneg.mpr h3
    have hd : (3-x)/x ≤ (3-x)/2 := by
      apply (div_le_iff₀ hpos).2
      have hh := mul_le_mul_of_nonneg_left h2 hn
      nlinarith only [hh]
    calc
      ((3-x)/x)*padeWeight n D x ≤
          ((3-x)/2)*padeWeight n D x :=
        mul_le_mul_of_nonneg_right hd
          (pade_weight_nonneg n D x hD0 h2 h4)
      _ ≤ ((3-x)/2)*(3*((3:ℝ)/16)^n) :=
        mul_le_mul_of_nonneg_left (pade_weight_bound n D x hD h2 h4)
          (by positivity)
      _ = A*(3-x) := by dsimp [A]; ring
  have htri : (∫ x in (2:ℝ)..3, (3-x)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 3)
      (g := fun x : ℝ => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable (2:ℝ) 3), integral_id]
    norm_num
  rw [intervalIntegral.integral_const_mul, htri] at hle
  calc
    _ ≤ A*(1/2) := hle
    _ = _ := by dsimp [A]; ring

theorem pade_right_bound (n : ℕ) (D : ℝ)
    (hD0 : 0 ≤ D) (hD : D ≤ 3^(8*n+1)) :
    (∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n D x)
      ≤ (1:ℝ)/2 * ((3:ℝ)/16)^n := by
  let A : ℝ := ((3:ℝ)/16)^n
  have ca : ContinuousOn (fun x : ℝ => A * (x-3)) (Icc 3 4) :=
    by fun_prop
  have hi : IntervalIntegrable
      (fun x : ℝ => ((x-3)/x)*padeWeight n D x) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (3:ℝ) ≤ 4)] using pade_lobeR_cont n D
  have hia : IntervalIntegrable (fun x : ℝ => A*(x-3))
      volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (3:ℝ) ≤ 4)] using ca
  have hle : (∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n D x)
      ≤ (∫ x in (3:ℝ)..4, A*(x-3)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hia
    intro x hx
    have h3 := hx.1
    have h4 := hx.2
    have h2 : 2 ≤ x := by linarith
    have hpos : 0 < x := by linarith
    have hn := sub_nonneg.mpr h3
    have hd : (x-3)/x ≤ (x-3)/3 := by
      apply (div_le_iff₀ hpos).2
      have hh := mul_le_mul_of_nonneg_left h3 hn
      nlinarith only [hh]
    calc
      ((x-3)/x)*padeWeight n D x ≤
          ((x-3)/3)*padeWeight n D x :=
        mul_le_mul_of_nonneg_right hd
          (pade_weight_nonneg n D x hD0 h2 h4)
      _ ≤ ((x-3)/3)*(3*((3:ℝ)/16)^n) :=
        mul_le_mul_of_nonneg_left (pade_weight_bound n D x hD h2 h4)
          (by positivity)
      _ = A*(x-3) := by dsimp [A]; ring
  have htri : (∫ x in (3:ℝ)..4, (x-3)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => x)
      (g := fun _ : ℝ => 3)
      (continuous_id.intervalIntegrable (3:ℝ) 4)
      intervalIntegrable_const, integral_id]
    norm_num
  rw [intervalIntegral.integral_const_mul, htri] at hle
  calc
    _ ≤ A*(1/2) := hle
    _ = _ := by dsimp [A]; ring

end CollatzPade

open CollatzPade
#print axioms CollatzPade.pade_laurent_sum
#print axioms CollatzPade.pade_left_bound
#print axioms CollatzPade.pade_right_bound

-- ===== PadePolynomials =====
/-! Integer coefficient envelope of the degree-16 Padé block. -/
open Polynomial Finset

namespace CollatzPade

noncomputable def padeU : Polynomial ℤ := 2*(X-2)*(X-3)
noncomputable def padeV : Polynomial ℤ := (X-3)*(X-4)
noncomputable def padeQ : Polynomial ℤ := -(padeU^5*padeV^3)
noncomputable def padeP (n : ℕ) : Polynomial ℤ := (X-3)*padeQ^n
noncomputable def padeUp : Polynomial ℤ := C 2 * X^2 + C 10 * X + C 12
noncomputable def padeVp : Polynomial ℤ := X^2 + C 7 * X + C 12
noncomputable def padeQp : Polynomial ℤ := padeUp^5*padeVp^3
noncomputable def padePp (n : ℕ) : Polynomial ℤ := (X+C 3)*padeQp^n

theorem padeCoeffComp (p : Polynomial ℤ) (a : ℤ) (j : ℕ) :
    (p.comp (C a * X)).coeff j = a^j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial k c =>
    rw [monomial_comp, mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
      C_mul_X_pow_eq_monomial]
    simp only [coeff_monomial]
    split_ifs with h
    · subst j
      ring
    · ring

theorem padeU_scaled :
    padeU.comp (C 12 * X) = C 12 * (24 * X^2 - 10 * X + 1) := by
  simp only [padeU, mul_comp, ofNat_comp, sub_comp, X_comp,
    C_eq_intCast]
  norm_num
  ring

theorem padeV_scaled :
    padeV.comp (C 12 * X) = C 12 * (12 * X^2 - 7 * X + 1) := by
  simp only [padeV, mul_comp, ofNat_comp, sub_comp, X_comp,
    C_eq_intCast]
  norm_num
  ring

theorem padeCoeffMultiple (n j : ℕ) (hj : j ≤ 8*n) :
    ∃ w : ℤ, (padeP n).coeff j = 12^(8*n-j) * w := by
  let U : Polynomial ℤ := 24 * X^2 - 10 * X + 1
  let V : Polynomial ℤ := 12 * X^2 - 7 * X + 1
  have hQ : padeQ.comp (C 12 * X) = C ((12:ℤ)^8) * -(U^5*V^3) := by
    simp only [padeQ, neg_comp, mul_comp, pow_comp, padeU_scaled,
      padeV_scaled, C_eq_intCast]
    dsimp [U,V]
    norm_num
    ring
  let W : Polynomial ℤ := (C 12*X-3) * (-(U^5*V^3))^n
  have hf : (padeP n).comp (C 12 * X) = C ((12:ℤ)^(8*n))*W := by
    simp only [padeP, mul_comp, pow_comp, sub_comp, X_comp,
      ofNat_comp, hQ, mul_pow, map_pow]
    rw [pow_mul]
    dsimp [W]
    ring
  refine ⟨W.coeff j, ?_⟩
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff j) hf
  rw [padeCoeffComp, coeff_C_mul] at hc
  apply mul_left_cancel₀ (pow_ne_zero j (by norm_num : (12:ℤ)≠0))
  calc
    (12:ℤ)^j * (padeP n).coeff j = 12^(8*n) * W.coeff j := hc
    _ = 12^j * (12^(8*n-j) * W.coeff j) := by
      have hpow : (12:ℤ)^(8*n) = 12^j*12^(8*n-j) := by
        rw [← pow_add]
        congr 1 <;> omega
      rw [hpow]
      ring

theorem padeCompNeg (n : ℕ) :
    (padeP n).comp (-X) = C ((-1:ℤ)^(n+1))*padePp n := by
  have hU : padeU.comp (-X) = padeUp := by
    simp only [padeU, padeUp, mul_comp, ofNat_comp, sub_comp, X_comp,
      C_eq_intCast]
    norm_num
    ring
  have hV : padeV.comp (-X) = padeVp := by
    simp only [padeV, padeVp, mul_comp, ofNat_comp, sub_comp, X_comp,
      C_eq_intCast]
    norm_num
    ring
  have hn : C ((-1:ℤ)^(n+1)) = ((-1:Polynomial ℤ)^n)*(-1) := by
    rw [map_pow,pow_succ]
    simp
  rw [hn]
  simp only [padeP, padePp, padeQ, padeQp, mul_comp, pow_comp,
    neg_comp, sub_comp, X_comp, ofNat_comp, hU, hV, C_eq_intCast]
  rw [neg_pow]
  norm_num
  ring

theorem padeCoeffSignIdentity (n : ℕ) :
    (padeP n).coeff (8*n) = (-1:ℤ)^(n+1)*(padePp n).coeff (8*n) := by
  have hsc : C (-1) * (X : Polynomial ℤ) = -X := by
    simp
  have ha := padeCoeffComp (padeP n) (-1) (8*n)
  rw [hsc, padeCompNeg, coeff_C_mul] at ha
  have hb : (-1:ℤ)^(8*n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hb,one_mul] at ha
  exact ha.symm

theorem padeMulNonneg (p q : Polynomial ℤ)
    (hp : ∀ i, 0 ≤ p.coeff i) (hq : ∀ i, 0 ≤ q.coeff i) (n : ℕ) :
    0 ≤ (p*q).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun k hk => mul_nonneg (hp _) (hq _)

theorem padeMulCoeffLower (p q : Polynomial ℤ)
    (hp : ∀ i, 0 ≤ p.coeff i) (hq : ∀ i, 0 ≤ q.coeff i) (i j : ℕ) :
    p.coeff i*q.coeff j ≤ (p*q).coeff (i+j) := by
  have hm : (i,j) ∈ Finset.HasAntidiagonal.antidiagonal (i+j) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun k : ℕ×ℕ => p.coeff k.1*q.coeff k.2)
    (fun _ _ => mul_nonneg (hp _) (hq _)) hm

theorem padePowNonneg (p : Polynomial ℤ) (hp : ∀ i, 0 ≤ p.coeff i)
    (n : ℕ) : ∀ i, 0 ≤ (p^n).coeff i := by
  induction n with
  | zero =>
    intro i
    simp only [pow_zero,coeff_one]
    split_ifs <;> norm_num
  | succ n ih =>
    intro i
    rw [pow_succ]
    exact padeMulNonneg _ _ ih hp i

theorem padePowCoeffPos (p : Polynomial ℤ)
    (hp : ∀ i, 0 ≤ p.coeff i) (k : ℕ) (hpos : 0 < p.coeff k)
    (n : ℕ) : 0 < (p^n).coeff (k*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact lt_of_lt_of_le (mul_pos ih hpos)
      (padeMulCoeffLower _ _ (padePowNonneg p hp n) hp _ _)

theorem padeUp_nonneg (i : ℕ) : 0 ≤ padeUp.coeff i := by
  simp only [padeUp,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
  split_ifs <;> norm_num

theorem padeVp_nonneg (i : ℕ) : 0 ≤ padeVp.coeff i := by
  simp only [padeVp,coeff_add,coeff_X_pow,coeff_C_mul_X,coeff_C]
  split_ifs <;> norm_num

theorem padeQp_nonneg (i : ℕ) : 0 ≤ padeQp.coeff i :=
  padeMulNonneg _ _ (padePowNonneg _ padeUp_nonneg 5)
    (padePowNonneg _ padeVp_nonneg 3) i

theorem padeQp_pos : 0 < padeQp.coeff 8 := by
  have hU0 : 0 < padeUp.coeff 0 := by norm_num [padeUp,coeff_C_mul_X_pow]
  have hU2 : 0 < padeUp.coeff 2 := by
    simp only [padeUp,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    norm_num
  have hV0 : 0 < padeVp.coeff 0 := by norm_num [padeVp,coeff_X_pow]
  have hU4 : 0 < (padeUp^4).coeff 8 :=
    padePowCoeffPos _ padeUp_nonneg 2 hU2 4
  have hU5 : 0 < (padeUp^5).coeff 8 := by
    rw [show (5:ℕ)=4+1 by norm_num,pow_succ,← Nat.add_zero 8]
    exact lt_of_lt_of_le (mul_pos hU4 hU0)
      (padeMulCoeffLower _ _ (padePowNonneg _ padeUp_nonneg 4)
        padeUp_nonneg 8 0)
  have hV3 : 0 < (padeVp^3).coeff 0 :=
    padePowCoeffPos _ padeVp_nonneg 0 hV0 3
  exact lt_of_lt_of_le (mul_pos hU5 hV3)
    (padeMulCoeffLower _ _ (padePowNonneg _ padeUp_nonneg 5)
      (padePowNonneg _ padeVp_nonneg 3) 8 0)

theorem padeXadd_nonneg (i : ℕ) :
    0 ≤ ((X : Polynomial ℤ)+C 3).coeff i := by
  simp only [coeff_add,coeff_X,coeff_C]
  split_ifs <;> norm_num

theorem padePp_nonneg (n i : ℕ) : 0 ≤ (padePp n).coeff i :=
  padeMulNonneg _ _ padeXadd_nonneg
    (padePowNonneg _ padeQp_nonneg n) i

theorem padePp_pos (n : ℕ) : 0 < (padePp n).coeff (8*n) := by
  have h0 : 0 < ((X : Polynomial ℤ)+C 3).coeff 0 := by norm_num
  have h8 := padePowCoeffPos _ padeQp_nonneg 8 padeQp_pos n
  have hm := padeMulCoeffLower ((X : Polynomial ℤ)+C 3)
    (padeQp^n) padeXadd_nonneg (padePowNonneg _ padeQp_nonneg n) 0 (8*n)
  apply lt_of_lt_of_le (mul_pos h0 h8)
  simpa only [padePp,zero_add] using hm

theorem padeAbsCoeff (n : ℕ) :
    |(padeP n).coeff (8*n)| = (padePp n).coeff (8*n) := by
  rw [padeCoeffSignIdentity, abs_mul, abs_pow,
    abs_of_pos (padePp_pos n)]
  simp

theorem padeCoeffGrowth (n : ℕ) :
    |(padeP n).coeff (8*n)| ≤ 6 * ((20:ℤ)^5*14^3)^n := by
  rw [padeAbsCoeff]
  have hp : (0:ℤ) < 3^(8*n) := by positivity
  have hle : (padePp n).coeff (8*n) * 3^(8*n) ≤
      (padePp n).eval 3 := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    exact Finset.single_le_sum
      (f := fun j : ℕ => (padePp n).coeff j * (3:ℤ)^j)
      (s := (padePp n).support)
      (fun j _ => mul_nonneg (padePp_nonneg n j) (by positivity))
      (Polynomial.mem_support_iff.2 (ne_of_gt (padePp_pos n)))
  have hgoal : (padePp n).coeff (8*n) * 3^(8*n) ≤
      6 * ((20:ℤ)^5*14^3)^n * 3^(8*n) := by
    calc
      _ ≤ (padePp n).eval 3 := hle
      _ = 6 * ((60:ℤ)^5*42^3)^n := by
        norm_num [padePp,padeQp,padeUp,padeVp]
      _ = 6 * (((20:ℤ)^5*14^3)*3^8)^n := by norm_num
      _ = 6 * ((20:ℤ)^5*14^3)^n * 3^(8*n) := by
        simp only [mul_pow,pow_mul]
        ring
  exact le_of_mul_le_mul_right hgoal hp

end CollatzPade

open CollatzPade
#print axioms CollatzPade.padeCoeffMultiple
#print axioms CollatzPade.padeCoeffSignIdentity
#print axioms CollatzPade.padePp_pos

-- ===== PadeClearing =====
/-! Integral coefficient and endpoint denominator clearing. -/
open Polynomial Finset Set MeasureTheory intervalIntegral

namespace CollatzPade

noncomputable def padeDen (n : ℕ) : ℕ := (Finset.Icc 1 (8*n+1)).lcm id

noncomputable def padeA (n : ℕ) : ℤ := (padeDen n : ℤ)*(padeP n).coeff (8*n)

theorem padeDenPos (n : ℕ) : 0 < padeDen n := by
  apply Nat.pos_of_ne_zero
  simp [padeDen]

theorem padeDenDvd (n d : ℕ) (h1 : 0 < d) (h2 : d ≤ 8*n+1) :
    d ∣ padeDen n := by
  unfold padeDen
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨by omega,h2⟩)

theorem padePolyDegree (n : ℕ) : (padeP n).natDegree ≤ 16*n+1 := by
  have hsub (z : ℤ) : (X-(z:Polynomial ℤ)).natDegree ≤ 1 := by
    rw [← Polynomial.C_eq_intCast]
    exact Polynomial.natDegree_X_sub_C_le z
  have hU : padeU.natDegree ≤ 2 := by
    unfold padeU
    have hu : ((2:Polynomial ℤ)*(X-2)).natDegree ≤ 1 := by
      apply Polynomial.natDegree_mul_le_of_le (m := 0) (n := 1)
      · simp
      · simpa using hsub 2
    exact Polynomial.natDegree_mul_le_of_le hu (by simpa using hsub 3)
  have hV : padeV.natDegree ≤ 2 := by
    unfold padeV
    exact Polynomial.natDegree_mul_le_of_le (by simpa using hsub 3)
      (by simpa using hsub 4)
  have hQ : padeQ.natDegree ≤ 16 := by
    unfold padeQ
    rw [natDegree_neg]
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_pow_le_of_le 5 hU)
      (Polynomial.natDegree_pow_le_of_le 3 hV)
  unfold padeP
  have hh := Polynomial.natDegree_mul_le_of_le
    (p := (X-3 : Polynomial ℤ)) (q := padeQ^n) (m := 1)
    (by simpa using hsub 3) (Polynomial.natDegree_pow_le_of_le n hQ)
  omega

theorem padeCoeffAtEndpoint (n j a : ℕ) (ha : 0 < a) (hd : a ∣ 12) :
    ∃ z : ℤ, ((padeP n).coeff j : ℝ) *
      (a:ℝ)^((j:ℤ)-((8*n:ℕ):ℤ)) = (z:ℝ) := by
  by_cases hj : 8*n ≤ j
  · refine ⟨(padeP n).coeff j*(a:ℤ)^(j-8*n), ?_⟩
    rw [← Int.natCast_sub hj, zpow_natCast]
    push_cast <;> rfl
  · obtain ⟨s,hs⟩ := hd
    obtain ⟨w,hw⟩ := padeCoeffMultiple n j (by omega)
    have he : (j:ℤ)-((8*n:ℕ):ℤ) = -((8*n-j:ℕ):ℤ) := by
      rw [Int.natCast_sub (by omega : j ≤ 8*n)]
      ring
    refine ⟨(s:ℤ)^(8*n-j)*w, ?_⟩
    rw [he,zpow_neg,zpow_natCast,hw]
    push_cast
    have hh : (12:ℝ) = (a:ℝ)*(s:ℝ) := by exact_mod_cast hs
    rw [hh,mul_pow]
    have hn : (a:ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast ha)
    field_simp [hn] <;> ring

theorem padeClearedTerm (n j a b : ℕ) (hj : j ≤ 16*n+1)
    (hneq : j ≠ 8*n) (ha : 0 < a) (hb : 0 < b)
    (hda : a ∣ 12) (hdb : b ∣ 12) :
    ∃ z : ℤ, (padeDen n : ℝ) * ((padeP n).coeff j : ℝ) *
       (((b:ℝ)^((j:ℤ)-((8*n:ℕ):ℤ)) -
       (a:ℝ)^((j:ℤ)-((8*n:ℕ):ℤ))) /
       ((↑((j:ℤ)-((8*n:ℕ):ℤ)) : ℝ))) = (z:ℝ) := by
  let e : ℤ := (j:ℤ)-((8*n:ℕ):ℤ)
  have he : e ≠ 0 := by dsimp [e]; omega
  have hdiv : e ∣ (padeDen n : ℤ) := by
    by_cases hh : 8*n ≤ j
    · have hEq : e = ((j-8*n:ℕ):ℤ) := by
        exact (Int.natCast_sub hh).symm
      rw [hEq]
      exact_mod_cast padeDenDvd n (j-8*n) (by omega) (by omega)
    · have hEq : e = -((8*n-j:ℕ):ℤ) := by
        dsimp [e]
        rw [Int.natCast_sub (by omega : j ≤ 8*n)]
        push_cast
        ring
      rw [hEq,Int.neg_dvd]
      exact_mod_cast padeDenDvd n (8*n-j) (by omega) (by omega)
  obtain ⟨d,hd⟩ := hdiv
  obtain ⟨za,hza⟩ := padeCoeffAtEndpoint n j a ha hda
  obtain ⟨zb,hzb⟩ := padeCoeffAtEndpoint n j b hb hdb
  have hd' : (padeDen n : ℝ) = (e:ℝ)*(d:ℝ) := by exact_mod_cast hd
  have he' : (e:ℝ) ≠ 0 := by exact_mod_cast he
  refine ⟨d*(zb-za), ?_⟩
  change (padeDen n : ℝ) * ((padeP n).coeff j : ℝ) *
      (((b:ℝ)^e-(a:ℝ)^e)/(e:ℝ)) = _
  change ((padeP n).coeff j : ℝ)*(a:ℝ)^e = (za:ℝ) at hza
  change ((padeP n).coeff j : ℝ)*(b:ℝ)^e = (zb:ℝ) at hzb
  calc
    _ = (d:ℝ)*(((padeP n).coeff j : ℝ)*(b:ℝ)^e -
        ((padeP n).coeff j : ℝ)*(a:ℝ)^e) := by
      rw [hd']
      field_simp [he'] <;> ring
    _ = _ := by rw [hza,hzb]; push_cast; ring

theorem padeEvalP (n : ℕ) (x : ℝ) :
    (padeP n).eval₂ (Int.castRingHom ℝ) x =
      (x-3)*shapeNumerator x ^ n := by
  have hQ : padeQ.eval₂ (Int.castRingHom ℝ) x = shapeNumerator x := by
    simp only [padeQ,padeU,padeV,shapeNumerator,eval₂_mul,eval₂_pow,
      eval₂_neg,eval₂_sub,eval₂_X,eval₂_ofNat]
    ring
  simp only [padeP,eval₂_mul,eval₂_sub,eval₂_X,eval₂_ofNat,eval₂_pow,hQ]

theorem padeLaurentEval (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    (∑ j ∈ range (16*n+2),
      ((padeDen n : ℝ)*((padeP n).coeff j : ℝ)) *
        x^((j:ℤ)-((8*n:ℕ):ℤ)-1)) =
      ((x-3)/x) * padeWeight n (padeDen n : ℝ) x := by
  have hsum :
      (∑ j ∈ range (16*n+2), ((padeP n).coeff j : ℝ)*x^j) =
        (x-3)*shapeNumerator x^n := by
    have hh : (padeP n).natDegree < 16*n+2 :=
      (padePolyDegree n).trans_lt (by omega)
    rw [← padeEvalP n x, Polynomial.eval₂_eq_sum_range' _ hh x] <;> simp
  calc
    _ = (padeDen n : ℝ) *
        (∑ j ∈ range (16*n+2), ((padeP n).coeff j : ℝ)*x^j) /
          x^(8*n+1) := by
      rw [Finset.mul_sum,Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show (j:ℤ)-((8*n:ℕ):ℤ)-1 =
        (j:ℤ)-((8*n+1:ℕ):ℤ) by omega, zpow_sub₀ hx]
      simp only [zpow_natCast]
      ring
    _ = _ := by
      rw [hsum]
      unfold padeWeight
      rw [show x^(8*n+1)=(x^8)^n*x by rw [pow_succ,pow_mul],
        div_pow]
      field_simp [hx] <;> ring

theorem padeLobeInteger (n a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hda : a ∣ 12) (hdb : b ∣ 12) :
    ∃ c : ℤ, (∫ x in (a:ℝ)..(b:ℝ),
      ((x-3)/x)*padeWeight n (padeDen n : ℝ) x) =
      (padeA n : ℝ)*Real.log ((b:ℝ)/(a:ℝ)) + (c:ℝ) := by
  classical
  let S := range (16*n+2)
  let e : ℕ → ℤ := fun j => (j:ℤ)-((8*n:ℕ):ℤ)
  let C : ℕ → ℝ := fun j =>
    (padeDen n:ℝ)*((padeP n).coeff j:ℝ)
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hex (j : ℕ) (hj : j ∈ S) (hne : j ≠ 8*n) :
      ∃ c : ℤ, C j * (((b:ℝ)^(e j)-(a:ℝ)^(e j))/(e j:ℝ)) =
        (c:ℝ) := by
    unfold C e
    exact padeClearedTerm n j a b
      (by have h := Finset.mem_range.mp hj; omega) hne ha hb hda hdb
  let d : ℕ → ℤ := fun j =>
    if h : j ∈ S ∧ j ≠ 8*n then Classical.choose (hex j h.1 h.2)
    else 0
  refine ⟨∑ j ∈ S, d j, ?_⟩
  have hi : (∫ x in (a:ℝ)..(b:ℝ),
      ((x-3)/x)*padeWeight n (padeDen n : ℝ) x) =
      ∫ x in (a:ℝ)..(b:ℝ), ∑ j ∈ S, C j * x^(e j-1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hn : 0 < x := lt_of_lt_of_le (lt_min ha' hb') hx.1
    exact (padeLaurentEval n x (ne_of_gt hn)).symm
  rw [hi, pade_laurent_sum S e C _ _ ha' hb']
  have hm : 8*n ∈ S := Finset.mem_range.mpr (by omega)
  have hsplit :
      (∑ j ∈ S, C j * (if e j=0 then Real.log ((b:ℝ)/(a:ℝ))
        else ((b:ℝ)^(e j)-(a:ℝ)^(e j))/(e j:ℝ))) =
      ∑ j ∈ S, ((if j=8*n then (padeA n:ℝ) *
        Real.log ((b:ℝ)/(a:ℝ)) else 0)+(d j:ℝ)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases j0 : j=8*n
    · subst j
      simp [e,C,d,padeA]
    · have h0 : e j ≠ 0 := by dsimp [e]; omega
      have hc : j ∈ S ∧ j ≠ 8*n := ⟨hj,j0⟩
      simp only [if_neg h0,if_neg j0,zero_add,d,dif_pos hc]
      exact Classical.choose_spec (hex j hj j0)
  rw [hsplit,Finset.sum_add_distrib]
  simp [hm]

end CollatzPade

open CollatzPade
#print axioms CollatzPade.padeLobeInteger

-- ===== PadeCoreAssembly =====
/-! Assembly of the all-height separation, with its explicit LCM input. -/
open Set MeasureTheory intervalIntegral
namespace CollatzPade

noncomputable def padeLeft (n : ℕ) : ℝ :=
  ∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n (padeDen n:ℝ) x

noncomputable def padeRight (n : ℕ) : ℝ :=
  ∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n (padeDen n:ℝ) x

theorem padeLeftLog (n : ℕ) :
    ∃ B : ℤ, -padeLeft n = (padeA n:ℝ)*Real.log (3/2)+(B:ℝ) := by
  have h := padeLobeInteger n 2 3 (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨c,hc⟩ := h
  refine ⟨c,?_⟩
  convert hc using 1 <;> simp only [Nat.cast_ofNat]
  unfold padeLeft
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

theorem padeRightLog (n : ℕ) :
    ∃ C : ℤ, padeRight n = (padeA n:ℝ)*Real.log (4/3)+(C:ℝ) := by
  simpa only [padeRight,Nat.cast_ofNat] using
    padeLobeInteger n 3 4 (by decide) (by decide) (by decide) (by decide)

theorem padeA_alt (n : ℕ) :
    (0 < padeA n ∧ padeA (n+1)<0) ∨
    (padeA n<0 ∧ 0 < padeA (n+1)) := by
  have hsgn (k : ℕ) : (-1:ℤ)^k = 1 ∨ (-1:ℤ)^k = -1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      rcases ih with h | h
      · right; norm_num [h]
      · left; norm_num [h]
  have he (k:ℕ) : padeA k = (-1:ℤ)^(k+1)*
      ((padeDen k:ℤ)*(padePp k).coeff (8*k)) := by
    rw [padeA,padeCoeffSignIdentity]
    ring
  have hpos (k:ℕ) : 0 < (padeDen k : ℤ)*(padePp k).coeff (8*k) :=
    mul_pos (by exact_mod_cast padeDenPos k) (padePp_pos k)
  rw [he n,he (n+1),show n+1+1=(n+1)+1 by rfl,
    show (-1:ℤ)^(n+1+1) = (-1:ℤ)^(n+1)*(-1) by rw [pow_succ]]
  rcases hsgn (n+1) with h|h
  · left
    constructor
    · simpa [h] using hpos n
    · simpa [h] using neg_neg_of_pos (hpos (n+1))
  · right
    constructor
    · simpa [h] using neg_neg_of_pos (hpos n)
    · simpa [h] using hpos (n+1)

theorem padeA_growth (Dgood : ∀ n, padeDen n ≤ 3^(8*n+1))
    (n : ℕ) : |(padeA n:ℝ)| ≤ 18*padeG^n := by
  have hn : 0 ≤ (padeDen n:ℝ) := by positivity
  have he : (padeDen n:ℝ) ≤ (3:ℝ)^(8*n+1) := by
    exact_mod_cast Dgood n
  have hc : |((padeP n).coeff (8*n):ℝ)| ≤
      6 * ((20:ℝ)^5*14^3)^n := by
    exact_mod_cast padeCoeffGrowth n
  unfold padeA
  push_cast
  rw [abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ (3:ℝ)^(8*n+1) * (6*((20:ℝ)^5*14^3)^n) :=
      mul_le_mul he hc (abs_nonneg _) (by positivity)
    _ = 18 * (((3:ℝ)^8)^n * ((20:ℝ)^5*14^3)^n) := by
      rw [pow_succ (3:ℝ) (8*n), pow_mul (3:ℝ) 8 n]
      ring
    _ = 18*padeG^n := by
      rw [← mul_pow]
      have hh : (3:ℝ)^8 * ((20:ℝ)^5*14^3) = padeG := by
        norm_num [padeG]
      rw [hh]

theorem pade_log32_lb : (1:ℝ)/3 ≤ Real.log (3/2) := by
  calc
    _ = 1-((3:ℝ)/2)⁻¹ := by norm_num
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)

theorem pade_log43_lb : (1:ℝ)/4 ≤ Real.log (4/3) := by
  calc
    _ = 1-((4:ℝ)/3)⁻¹ := by norm_num
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)

theorem log23_sep_of_lcmBound
    (Dgood : ∀ n, padeDen n ≤ 3^(8*n+1))
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    (1 : ℝ) / (2^128 * (v : ℝ)^19) <
      |(u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3| := by
  let L := (u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3
  change (1:ℝ)/(2^128*(v:ℝ)^19) < |L|
  have hvn : 1 ≤ v := by omega
  have hvR : 1 ≤ (v:ℝ) := by exact_mod_cast hvn
  have hv0 : 0 < (v:ℝ) := by exact_mod_cast hv
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h32 : Real.log ((3:ℝ)/2) = Real.log 3-Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have h43 : Real.log ((4:ℝ)/3) = 2*Real.log 2-Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have hsmall : (1:ℝ)/(2^128*(v:ℝ)^19) < 1/4 := by
    apply (div_lt_iff₀ (by positivity)).2
    have h : (1:ℝ) ≤ (v:ℝ)^19 := one_le_pow₀ hvR
    have h' := mul_le_mul_of_nonneg_left h
      (by norm_num : (0:ℝ) ≤ (1/4)*2^128)
    nlinarith only [h']
  by_cases huv : u ≤ v
  · have hcast : (u:ℝ) ≤ v := by exact_mod_cast huv
    have hlog : (1:ℝ)/3 ≤ Real.log 3-Real.log 2 := by
      simpa only [h32] using pade_log32_lb
    have hh1 := mul_le_mul_of_nonneg_right hcast hl2.le
    have hh2 := mul_le_mul_of_nonneg_left hlog hv0.le
    have hL : (1:ℝ)/4 ≤ -L := by
      dsimp [L]
      nlinarith only [hh1,hh2,hvR]
    exact hsmall.trans_le (hL.trans (neg_le_abs _))
  by_cases h2 : 2*v ≤ u
  · have hx : (2:ℝ)*(v:ℝ) ≤ u := by exact_mod_cast h2
    have hlog : (1:ℝ)/4 ≤ 2*Real.log 2-Real.log 3 := by
      simpa only [h43] using pade_log43_lb
    have hh1 := mul_le_mul_of_nonneg_right hx hl2.le
    have hh2 := mul_le_mul_of_nonneg_left hlog hv0.le
    have hL : (1:ℝ)/4 ≤ L := by
      dsimp [L]
      nlinarith only [hh1,hh2,hvR]
    exact hsmall.trans_le (hL.trans (le_abs_self _))
  let a : ℤ := (2:ℤ)*(v:ℤ)-(u:ℤ)
  let b : ℤ := (u:ℤ)-(v:ℤ)
  have ha : 0 < (a:ℝ) := by
    have h : u < 2*v := by omega
    have h' : (u:ℝ) < (2:ℝ)*(v:ℝ) := by exact_mod_cast h
    dsimp [a]; push_cast; linarith
  have hb : 0 < (b:ℝ) := by
    have h : v < u := by omega
    have h' : (v:ℝ)<(u:ℝ) := by exact_mod_cast h
    dsimp [b]; push_cast; linarith
  have hab : (a:ℝ)+(b:ℝ)=(v:ℝ) := by
    dsimp [a,b]; push_cast; ring
  choose B hB using padeLeftLog
  choose C hC using padeRightLog
  let N : ℕ → ℤ := fun n => -a*B n+b*C n
  have hEq (n : ℕ) :
      (padeA n:ℝ)*L+(N n:ℝ) =
        (a:ℝ)*padeLeft n + (b:ℝ)*padeRight n := by
    have hlog : -(a:ℝ)*Real.log (3/2) +
        (b:ℝ)*Real.log (4/3) = L := by
      rw [h32,h43]
      dsimp [a,b,L]
      push_cast
      ring
    have hleft : padeLeft n =
        -((padeA n:ℝ)*Real.log (3/2)+(B n:ℝ)) := by
      linarith only [hB n]
    rw [hleft,hC n,←hlog]
    dsimp [N]
    push_cast
    ring
  apply padeEscape v hv L padeA N _ _ padeA_alt (padeA_growth Dgood)
  · intro n
    rw [hEq]
    have hD0 : (0:ℝ)<padeDen n := by exact_mod_cast padeDenPos n
    exact add_pos (mul_pos ha (pade_left_positive n _ hD0))
      (mul_pos hb (pade_right_positive n _ hD0))
  · intro n
    rw [hEq]
    have hD0 : (0:ℝ)≤padeDen n := by positivity
    have hD : (padeDen n:ℝ) ≤ (3:ℝ)^(8*n+1) :=
      by exact_mod_cast Dgood n
    have h1 := mul_le_mul_of_nonneg_left
      (pade_left_bound n _ hD0 hD) ha.le
    have h2a := mul_le_mul_of_nonneg_left
      (pade_right_bound n _ hD0 hD) hb.le
    change (a:ℝ)*padeLeft n ≤ (a:ℝ)*(3/4*((3:ℝ)/16)^n) at h1
    change (b:ℝ)*padeRight n ≤ (b:ℝ)*(1/2*((3:ℝ)/16)^n) at h2a
    have hh : (0:ℝ) ≤ (b:ℝ)*((3:ℝ)/16)^n := by positivity
    calc
      _ ≤ (a:ℝ)*(3/4*((3:ℝ)/16)^n)+(b:ℝ)*(1/2*((3:ℝ)/16)^n) :=
        add_le_add h1 h2a
      _ ≤ ((3:ℝ)/4)*((a:ℝ)+(b:ℝ))*((3:ℝ)/16)^n := by
        nlinarith only [hh]
      _ = ((3:ℝ)/4)*(v:ℝ)*((3:ℝ)/16)^n := by rw [hab]

end CollatzPade

open CollatzPade
#print axioms CollatzPade.log23_sep_of_lcmBound

-- ===== PadeLcm =====
open scoped BigOperators

set_option maxRecDepth 4096

namespace CollatzPade

def padeMultinomial (k : ℕ) : ℕ :=
  (6*k).choose (3*k) * (3*k).choose k

-- [compiled-unknown]
private lemma pade_multinomial_pos (k : ℕ) :
    0 < padeMultinomial k := by
  unfold padeMultinomial
  exact Nat.mul_pos (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega))

-- [compiled-unknown]
private lemma pade_multinomial_factorial (k : ℕ) :
    padeMultinomial k * (3*k).factorial * (2*k).factorial *
      k.factorial = (6*k).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial
    (n := 6*k) (k := 3*k) (by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial
    (n := 3*k) (k := k) (by omega)
  rw [show 6*k-3*k = 3*k by omega] at h1
  rw [show 3*k-k = 2*k by omega] at h2
  calc
    padeMultinomial k * (3*k).factorial * (2*k).factorial *
        k.factorial =
        (6*k).choose (3*k) * (3*k).factorial *
          ((3*k).choose k * k.factorial * (2*k).factorial) := by
      unfold padeMultinomial
      ring
    _ = (6*k).choose (3*k) * (3*k).factorial *
        (3*k).factorial := by rw [h2]
    _ = (6*k).factorial := h1

-- [compiled-unknown]
private lemma pade_weighted_choose (k : ℕ) :
    (3*k).choose k * 4^k ≤ 27^k := by
  have hs :
      (1:ℕ)^k * 2^(3*k-k) * (3*k).choose k ≤
        ∑ i ∈ Finset.range (3*k+1),
          (1:ℕ)^i * 2^(3*k-i) * (3*k).choose i :=
    Finset.single_le_sum
      (f := fun i => (1:ℕ)^i * 2^(3*k-i) * (3*k).choose i)
      (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < 3*k+1))
  have hadd : ((1:ℕ) + 2)^(3*k) =
      ∑ i ∈ Finset.range (3*k+1), (1:ℕ)^i * 2^(3*k-i) * (3*k).choose i := by
    have h := add_pow (1:ℕ) 2 (3*k)
    simpa only [Nat.cast_id] using h
  rw [← hadd] at hs
  rw [show 3*k-k = 2*k by omega] at hs
  simp only [one_pow, one_mul] at hs
  change 2^(2*k) * (3*k).choose k ≤ 3^(3*k) at hs
  rw [pow_mul, pow_mul] at hs
  change 4^k * (3*k).choose k ≤ 27^k at hs
  simpa only [mul_comm] using hs

-- [compiled-unknown]
private lemma pade_multinomial_bound (k : ℕ) :
    padeMultinomial k ≤ 432^k := by
  have h1 := Nat.choose_le_two_pow (6*k) (3*k)
  rw [pow_mul] at h1
  change (6*k).choose (3*k) ≤ 64^k at h1
  have h2 := pade_weighted_choose k
  have h : padeMultinomial k * 4^k ≤ 432^k * 4^k := by
    calc
      padeMultinomial k * 4^k =
          (6*k).choose (3*k) * ((3*k).choose k * 4^k) := by
        unfold padeMultinomial
        ring
      _ ≤ 64^k * 27^k := Nat.mul_le_mul h1 h2
      _ = 432^k * 4^k := by
        rw [← mul_pow, ← mul_pow]
        norm_num
  exact Nat.le_of_mul_le_mul_right h (by positivity : 0 < (4:ℕ)^k)

-- [compiled-unknown]
private lemma pade_six_floor_parts (k d : ℕ) :
    (3*k)/d = ((6*k)/d)/2 ∧
    (2*k)/d = ((6*k)/d)/3 ∧
    k/d = ((6*k)/d)/6 := by
  refine ⟨?_, ?_, ?_⟩
  · symm
    calc
      (6*k)/d/2 = (2*(3*k))/(2*d) := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 2]
        congr 1 <;> omega
      _ = (3*k)/d := Nat.mul_div_mul_left _ _ (by decide)
  · symm
    calc
      (6*k)/d/3 = (3*(2*k))/(3*d) := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 3]
        congr 1 <;> omega
      _ = (2*k)/d := Nat.mul_div_mul_left _ _ (by decide)
  · symm
    calc
      (6*k)/d/6 = (6*k)/(6*d) := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 6]
      _ = k/d := Nat.mul_div_mul_left _ _ (by decide)

-- [compiled-unknown]
private lemma pade_six_floor_le (k d : ℕ) :
    (3*k)/d + (2*k)/d + k/d ≤ (6*k)/d := by
  obtain ⟨h2, h3, h6⟩ := pade_six_floor_parts k d
  rw [h2, h3, h6]
  omega

-- [compiled-unknown]
private lemma pade_six_floor_gap (k d : ℕ) (hd : 0 < d)
    (hkd : k < d) (hd6 : d ≤ 6*k) :
    1 ≤ (6*k)/d - ((3*k)/d + (2*k)/d + k/d) := by
  obtain ⟨h2, h3, h6⟩ := pade_six_floor_parts k d
  have hq1 : 1 ≤ (6*k)/d :=
    (Nat.le_div_iff_mul_le hd).2 (by simpa using hd6)
  have hq6 : (6*k)/d < 6 :=
    (Nat.div_lt_iff_lt_mul hd).2 (by omega)
  rw [h2, h3, h6]
  omega

-- [compiled-unknown]
private theorem pade_lcm_six_dvd_of_factorial
    (k B : ℕ) (hB : 0 < B)
    (hfac : B * (3*k).factorial * (2*k).factorial * k.factorial =
      (6*k).factorial) :
    Nat.lcmUpto (6*k) ∣ B * Nat.lcmUpto k := by
  by_cases hk : k = 0
  · subst k
    simp [Nat.lcmUpto]
  apply (Nat.factorization_prime_le_iff_dvd
    (Nat.lcmUpto_ne_zero _)
    (Nat.mul_ne_zero hB.ne' (Nat.lcmUpto_ne_zero _))).mp
  intro p hp
  rw [Nat.factorization_lcmUpto _ hp,
    Nat.factorization_mul hB.ne' (Nat.lcmUpto_ne_zero _),
    Finsupp.add_apply, Nat.factorization_lcmUpto _ hp]
  let b := Nat.log p (6*k) + 1
  let t := Nat.log p k + 1
  let δ : ℕ → ℕ := fun i =>
    (6*k)/p^i - ((3*k)/p^i + (2*k)/p^i + k/p^i)
  have ht : t ≤ b := by
    dsimp [t, b]
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hf (z : ℕ) (hz : z ≤ 6*k) :
      z.factorial.factorization p =
        ∑ i ∈ Finset.Ico 1 b, z/p^i := by
    apply Nat.factorization_factorial hp
    exact (Nat.log_mono_right hz).trans_lt (Nat.lt_succ_self _)
  have hF := congrArg (fun z : ℕ => z.factorization p) hfac
  have hB1 : B * (3*k).factorial ≠ 0 :=
    Nat.mul_ne_zero hB.ne' (Nat.factorial_ne_zero _)
  have hB2 : B * (3*k).factorial * (2*k).factorial ≠ 0 :=
    Nat.mul_ne_zero hB1 (Nat.factorial_ne_zero _)
  rw [Nat.factorization_mul hB2 (Nat.factorial_ne_zero _),
    Nat.factorization_mul hB1 (Nat.factorial_ne_zero _),
    Nat.factorization_mul hB.ne' (Nat.factorial_ne_zero _)] at hF
  simp only [Finsupp.add_apply] at hF
  rw [hf (3*k) (by omega), hf (2*k) (by omega),
    hf k (by omega), hf (6*k) le_rfl] at hF
  have hd (i : ℕ) :
      (6*k)/p^i =
        (3*k)/p^i + (2*k)/p^i + k/p^i + δ i := by
    have := pade_six_floor_le k (p^i)
    dsimp [δ]
    omega
  have hsum :
      (∑ i ∈ Finset.Ico 1 b, (6*k)/p^i) =
        ∑ i ∈ Finset.Ico 1 b,
          ((3*k)/p^i + (2*k)/p^i + k/p^i + δ i) :=
    Finset.sum_congr rfl (fun i _ => hd i)
  simp only [Finset.sum_add_distrib] at hsum
  have hδ : (∑ i ∈ Finset.Ico 1 b, δ i) = B.factorization p := by
    omega
  have hsubset : Finset.Ico t b ⊆ Finset.Ico 1 b :=
    Finset.Ico_subset_Ico (by dsimp [t]; omega) le_rfl
  have hcount : b-t ≤ ∑ i ∈ Finset.Ico 1 b, δ i := by
    calc
      b-t = ∑ i ∈ Finset.Ico t b, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ Finset.Ico t b, δ i := by
        apply Finset.sum_le_sum
        intro i hi
        have hti := (Finset.mem_Ico.mp hi).1
        have hib := (Finset.mem_Ico.mp hi).2
        have hki : k < p^i := Nat.lt_pow_of_log_lt hp.one_lt (by
          dsimp [t] at hti
          omega)
        have hi6 : p^i ≤ 6*k := Nat.pow_le_of_le_log (by omega) (by
          dsimp [b] at hib
          omega)
        exact pade_six_floor_gap k (p^i) (pow_pos hp.pos _) hki hi6
      _ ≤ ∑ i ∈ Finset.Ico 1 b, δ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro i _ _
          exact Nat.zero_le _)
  rw [hδ] at hcount
  dsimp [t, b] at ht hcount
  omega

-- [compiled-unknown]
private theorem pade_lcm_six_dvd (k : ℕ) :
    Nat.lcmUpto (6*k) ∣ padeMultinomial k * Nat.lcmUpto k :=
  pade_lcm_six_dvd_of_factorial k (padeMultinomial k)
    (pade_multinomial_pos k) (pade_multinomial_factorial k)

-- [compiled-unknown]
private lemma pade_lcmUpto_mono {m n : ℕ} (h : m ≤ n) :
    Nat.lcmUpto m ≤ Nat.lcmUpto n := by
  apply Nat.le_of_dvd (Nat.lcmUpto_pos n)
  change (Finset.Icc 1 m).lcm id ∣ (Finset.Icc 1 n).lcm id
  apply Finset.lcm_mono
  intro i hi
  rcases Finset.mem_Icc.mp hi with ⟨h1, hm⟩
  exact Finset.mem_Icc.mpr ⟨h1, hm.trans h⟩

def padeLcmSeq : ℕ → ℕ
  | 0 => 1
  | n+1 => Nat.lcm (padeLcmSeq n) (n+1)

-- [compiled-unknown]
private lemma padeLcmSeq_eq (n : ℕ) :
    padeLcmSeq n = Nat.lcmUpto n := by
  induction n with
  | zero => simp [padeLcmSeq, Nat.lcmUpto]
  | succ n ih =>
      have hset : Finset.Icc 1 (n+1) =
          insert (n+1) (Finset.Icc 1 n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      change Nat.lcm (padeLcmSeq n) (n+1) =
        (Finset.Icc 1 (n+1)).lcm id
      rw [ih, hset, Finset.lcm_insert, lcm_eq_nat_lcm]
      change Nat.lcm (Nat.lcmUpto n) (n+1) =
        Nat.lcm (n+1) (Nat.lcmUpto n)
      exact Nat.lcm_comm _ _

def padeSmallScan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | fuel+1, i, d, a, b =>
      decide (a*d ≤ b) &&
        padeSmallScan fuel (i+1) (Nat.lcm d (i+1)) (2*a) (7*b)

-- [compiled-unknown]
private lemma padeSmallScan_sound (A B fuel i : ℕ)
    (h : padeSmallScan fuel i (padeLcmSeq i) (A*2^i) (B*7^i) = true) :
    ∀ j < fuel, A*2^(i+j) * padeLcmSeq (i+j) ≤ B*7^(i+j) := by
  induction fuel generalizing i with
  | zero =>
      intro j hj
      omega
  | succ fuel ih =>
      have hh :
          A*2^i * padeLcmSeq i ≤ B*7^i ∧
          padeSmallScan fuel (i+1)
            (Nat.lcm (padeLcmSeq i) (i+1))
            (2*(A*2^i)) (7*(B*7^i)) = true := by
        simpa only [padeSmallScan, Bool.and_eq_true, decide_eq_true_eq] using h
      intro j hj
      cases j with
      | zero => simpa only [Nat.add_zero] using hh.1
      | succ j =>
          have ha : A*2^(i+1) = 2*(A*2^i) := by
            rw [pow_succ']
            ring
          have hb : B*7^(i+1) = 7*(B*7^i) := by
            rw [pow_succ']
            ring
          have ht :
              padeSmallScan fuel (i+1)
                (padeLcmSeq (i+1)) (A*2^(i+1)) (B*7^(i+1)) = true := by
            rw [padeLcmSeq, ha, hb]
            exact hh.2
          have hr := ih (i+1) ht j (by omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr

-- [compiled-unknown]
private lemma padeSmallScan_checked :
    padeSmallScan 192 1 1 14 28 = true := by
  decide +kernel

-- [compiled-unknown]
private lemma pade_lcm_small_nat (m : ℕ)
    (hm0 : 1 ≤ m) (hm : m ≤ 192) :
    7*2^m * Nat.lcmUpto m ≤ 4*7^m := by
  have hs :
      padeSmallScan 192 1 (padeLcmSeq 1) (7*2^1) (4*7^1) = true := by
    simpa [padeLcmSeq] using padeSmallScan_checked
  have hr := padeSmallScan_sound 7 4 192 1 hs (m-1) (by omega)
  have he : 1+(m-1) = m := by omega
  simpa only [he, padeLcmSeq_eq] using hr

-- [compiled-unknown]
private lemma pade_lcm_small (m : ℕ)
    (hm0 : 1 ≤ m) (hm : m ≤ 192) :
    (Nat.lcmUpto m : ℝ) ≤ ((4:ℝ)/7)*((7:ℝ)/2)^m := by
  have h : (7:ℝ)*2^m * (Nat.lcmUpto m : ℝ) ≤ 4*7^m := by
    exact_mod_cast pade_lcm_small_nat m hm0 hm
  have hd : (Nat.lcmUpto m : ℝ) ≤ 4*7^m/(7*2^m) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 7*2^m)).2
    simpa only [mul_comm] using h
  calc
    (Nat.lcmUpto m : ℝ) ≤ 4*7^m/(7*2^m) := hd
    _ = ((4:ℝ)/7)*((7:ℝ)/2)^m := by
      rw [div_pow]
      field_simp <;> ring

-- [compiled-unknown]
private lemma pade_rounding_growth (k : ℕ) (hk : 33 ≤ k) :
    (432:ℝ)^k ≤ ((7:ℝ)/2)^(5*k-5) := by
  have hs : ∀ j : ℕ,
      (432:ℝ)^(33+j) ≤ ((7:ℝ)/2)^(160+5*j) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
        calc
          (432:ℝ)^(33+(j+1)) = (432:ℝ)^(33+j)*432 := by
            rw [show 33+(j+1) = (33+j)+1 by omega, pow_succ]
          _ ≤ ((7:ℝ)/2)^(160+5*j) * ((7:ℝ)/2)^5 :=
            mul_le_mul ih (by norm_num) (by norm_num) (by positivity)
          _ = ((7:ℝ)/2)^(160+5*(j+1)) := by
            rw [← pow_add]
            congr 1
  have h1 : 33+(k-33) = k := by omega
  have h2 : 160+5*(k-33) = 5*k-5 := by omega
  simpa only [h1, h2] using hs (k-33)

-- [compiled-unknown]
theorem pade_lcmUpto_bound (m : ℕ) (hm0 : 1 ≤ m) :
    (Nat.lcmUpto m : ℝ) ≤ ((4:ℝ)/7)*((7:ℝ)/2)^m := by
  revert hm0
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm0
      by_cases hm : m ≤ 192
      · exact pade_lcm_small m hm0 hm
      · let k := (m+5)/6
        have hk33 : 33 ≤ k := by dsimp [k]; omega
        have hkm : k < m := by dsimp [k]; omega
        have hm6 : m ≤ 6*k := by dsimp [k]; omega
        have hshift : 6*k-5 ≤ m := by dsimp [k]; omega
        have hi := ih k hkm (by omega : 1 ≤ k)
        have h6 :
            Nat.lcmUpto (6*k) ≤ padeMultinomial k * Nat.lcmUpto k :=
          Nat.le_of_dvd
            (Nat.mul_pos (pade_multinomial_pos k) (Nat.lcmUpto_pos k))
            (pade_lcm_six_dvd k)
        calc
          (Nat.lcmUpto m : ℝ) ≤ (Nat.lcmUpto (6*k) : ℝ) := by
            exact_mod_cast pade_lcmUpto_mono hm6
          _ ≤ (padeMultinomial k : ℝ) * (Nat.lcmUpto k : ℝ) := by
            exact_mod_cast h6
          _ ≤ (432:ℝ)^k * (((4:ℝ)/7)*((7:ℝ)/2)^k) :=
            mul_le_mul (by exact_mod_cast pade_multinomial_bound k)
              hi (by positivity) (by positivity)
          _ ≤ ((7:ℝ)/2)^(5*k-5) *
              (((4:ℝ)/7)*((7:ℝ)/2)^k) :=
            mul_le_mul_of_nonneg_right (pade_rounding_growth k hk33)
              (by positivity)
          _ = ((4:ℝ)/7)*((7:ℝ)/2)^(6*k-5) := by
            have he : (5*k-5)+k = 6*k-5 := by omega
            rw [← mul_assoc, mul_comm (((7:ℝ)/2)^(5*k-5)) ((4:ℝ)/7),
              mul_assoc, ← pow_add, he]
          _ ≤ ((4:ℝ)/7)*((7:ℝ)/2)^m :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) hshift) (by norm_num)

-- [compiled-unknown]
theorem pade_modified_shape_scale :
    ((7:ℝ)/2)^8 * (((3:ℝ)/16)/(3:ℝ)^8) =
      (5764801:ℝ)/8957952 := by
  norm_num

-- [compiled-unknown]
theorem pade_modified_coefficient_scale :
    ((7:ℝ)/2)^8 * (20:ℝ)^5 * (14:ℝ)^3 =
      (197732674300000:ℝ) := by
  norm_num

-- [compiled-unknown]
theorem pade_modified_decay :
    (197732674300000:ℝ) * ((5764801:ℝ)/8957952)^75 < 1 := by
  norm_num

-- [compiled-unknown]
theorem pade_modified_prefactor :
    (24:ℝ) * (197732674300000:ℝ)^2 < (2:ℝ)^100 := by
  norm_num

-- [compiled-unknown]
theorem pade_modified_powers_escape (q : ℕ) :
    ∃ n : ℕ, (q:ℝ) < ((8957952:ℝ)/5764801)^n := by
  exact pow_unbounded_of_one_lt (q:ℝ) (by norm_num)

-- [compiled-unknown]
theorem pade_lcm_bound_modified (n : ℕ) :
    (((Finset.Icc 1 (8*n+1)).lcm id : ℕ) : ℝ) ≤
      2 * ((7:ℝ)/2)^(8*n) := by
  have h := pade_lcmUpto_bound (8*n+1) (by omega)
  change (Nat.lcmUpto (8*n+1) : ℝ) ≤
    2 * ((7:ℝ)/2)^(8*n)
  calc
    (Nat.lcmUpto (8*n+1) : ℝ) ≤
        ((4:ℝ)/7)*((7:ℝ)/2)^(8*n+1) := h
    _ = 2 * ((7:ℝ)/2)^(8*n) := by
      rw [pow_succ]
      ring

end CollatzPade

-- ===== PadeCore =====
/-! Degree-16 Padé separation with the compiled LCM growth bound. -/
open Set MeasureTheory intervalIntegral
namespace CollatzPade

noncomputable def padeRho75 : ℝ := (5764801:ℝ)/8957952
noncomputable def padeR75 : ℝ := (8957952:ℝ)/5764801
noncomputable def padeG75 : ℝ := 197732674300000

theorem pade_weight_bound75 (n : ℕ) (D x : ℝ)
    (hD : D ≤ 2 * ((7:ℝ)/2)^(8*n)) (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    padeWeight n D x ≤ 2 * padeRho75^n := by
  let z : ℝ := shapeNumerator x / x^8
  have hx : 0 ≤ x := by linarith
  have hz : 0 ≤ z :=
    div_nonneg (shapeNumerator_nonneg x h2 h4) (pow_nonneg hx _)
  have hshape : (3:ℝ)^8 * z ≤ (3:ℝ)/16 := shape_bound x h2 h4
  have hz' : z ≤ ((3:ℝ)/16)/(3:ℝ)^8 := by
    apply (le_div_iff₀ (by positivity)).2
    simpa only [mul_comm] using hshape
  have hbase : ((7:ℝ)/2)^8 * z ≤ padeRho75 := by
    change _ ≤ (5764801:ℝ)/8957952
    rw [← pade_modified_shape_scale]
    exact mul_le_mul_of_nonneg_left hz' (by positivity)
  change D*z^n ≤ 2*padeRho75^n
  calc
    _ ≤ (2*((7:ℝ)/2)^(8*n))*z^n :=
      mul_le_mul_of_nonneg_right hD (pow_nonneg hz _)
    _ = 2 * ((((7:ℝ)/2)^8 * z)^n) := by
      rw [pow_mul ((7:ℝ)/2) 8 n, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbase _) (by norm_num)

theorem pade_left_bound75 (n : ℕ) (D : ℝ)
    (hD0 : 0 ≤ D) (hD : D ≤ 2 * ((7:ℝ)/2)^(8*n)) :
    (∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n D x)
      ≤ (1:ℝ)/2 * padeRho75^n := by
  let A : ℝ := padeRho75^n
  have ca : ContinuousOn (fun x : ℝ => A * (3-x)) (Icc 2 3) :=
    by fun_prop
  have hi : IntervalIntegrable
      (fun x : ℝ => ((3-x)/x)*padeWeight n D x) volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] using pade_lobeL_cont n D
  have hia : IntervalIntegrable (fun x : ℝ => A*(3-x))
      volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] using ca
  have hle : (∫ x in (2:ℝ)..3, ((3-x)/x)*padeWeight n D x)
      ≤ (∫ x in (2:ℝ)..3, A*(3-x)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hia
    intro x hx
    have h2 := hx.1
    have h3 := hx.2
    have h4 : x ≤ 4 := by linarith
    have hpos : 0 < x := by linarith
    have hn := sub_nonneg.mpr h3
    have hd : (3-x)/x ≤ (3-x)/2 := by
      apply (div_le_iff₀ hpos).2
      have hh := mul_le_mul_of_nonneg_left h2 hn
      nlinarith only [hh]
    calc
      ((3-x)/x)*padeWeight n D x ≤
          ((3-x)/2)*padeWeight n D x :=
        mul_le_mul_of_nonneg_right hd
          (pade_weight_nonneg n D x hD0 h2 h4)
      _ ≤ ((3-x)/2)*(2*padeRho75^n) :=
        mul_le_mul_of_nonneg_left (pade_weight_bound75 n D x hD h2 h4)
          (by positivity)
      _ = A*(3-x) := by dsimp [A]; ring
  have htri : (∫ x in (2:ℝ)..3, (3-x)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 3)
      (g := fun x : ℝ => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable (2:ℝ) 3), integral_id]
    norm_num
  rw [intervalIntegral.integral_const_mul, htri] at hle
  calc
    _ ≤ A*(1/2) := hle
    _ = _ := by dsimp [A]; ring

theorem pade_right_bound75 (n : ℕ) (D : ℝ)
    (hD0 : 0 ≤ D) (hD : D ≤ 2 * ((7:ℝ)/2)^(8*n)) :
    (∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n D x)
      ≤ (1:ℝ)/3 * padeRho75^n := by
  let A : ℝ := (2:ℝ)/3 * padeRho75^n
  have ca : ContinuousOn (fun x : ℝ => A * (x-3)) (Icc 3 4) :=
    by fun_prop
  have hi : IntervalIntegrable
      (fun x : ℝ => ((x-3)/x)*padeWeight n D x) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (3:ℝ) ≤ 4)] using pade_lobeR_cont n D
  have hia : IntervalIntegrable (fun x : ℝ => A*(x-3))
      volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (3:ℝ) ≤ 4)] using ca
  have hle : (∫ x in (3:ℝ)..4, ((x-3)/x)*padeWeight n D x)
      ≤ (∫ x in (3:ℝ)..4, A*(x-3)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hia
    intro x hx
    have h3 := hx.1
    have h4 := hx.2
    have h2 : 2 ≤ x := by linarith
    have hpos : 0 < x := by linarith
    have hn := sub_nonneg.mpr h3
    have hd : (x-3)/x ≤ (x-3)/3 := by
      apply (div_le_iff₀ hpos).2
      have hh := mul_le_mul_of_nonneg_left h3 hn
      nlinarith only [hh]
    calc
      ((x-3)/x)*padeWeight n D x ≤
          ((x-3)/3)*padeWeight n D x :=
        mul_le_mul_of_nonneg_right hd
          (pade_weight_nonneg n D x hD0 h2 h4)
      _ ≤ ((x-3)/3)*(2*padeRho75^n) :=
        mul_le_mul_of_nonneg_left (pade_weight_bound75 n D x hD h2 h4)
          (by positivity)
      _ = A*(x-3) := by dsimp [A]; ring
  have htri : (∫ x in (3:ℝ)..4, (x-3)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => x)
      (g := fun _ : ℝ => 3)
      (continuous_id.intervalIntegrable (3:ℝ) 4)
      intervalIntegrable_const, integral_id]
    norm_num
  rw [intervalIntegral.integral_const_mul, htri] at hle
  calc
    _ ≤ A*(1/2) := hle
    _ = _ := by dsimp [A]; ring


theorem padeEscape75 (q : ℕ) (hq : 0 < q) (L : ℝ) (A N : ℕ → ℤ)
    (hp : ∀ i, 0 < (A i : ℝ) * L + (N i : ℝ))
    (he : ∀ i, (A i : ℝ) * L + (N i : ℝ) ≤
      (1 : ℝ)/2 * (q : ℝ) * padeRho75^i)
    (ha : ∀ i, ((0 < A i) ∧ A (i+1) < 0) ∨
      ((A i < 0) ∧ 0 < A (i+1)))
    (hA : ∀ i, |(A i : ℝ)| ≤ 12 * padeG75^i) :
    (1 : ℝ) / (2^100 * (q : ℝ)^75) < |L| := by
  classical
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqN : (1 : ℕ) ≤ q := by omega
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hqN
  let n := Nat.find (pade_modified_powers_escape q)
  have hn : (q : ℝ) < padeR75^n :=
    Nat.find_spec (pade_modified_powers_escape q)
  have hn0 : n ≠ 0 := by
    intro hn'
    rw [hn', pow_zero] at hn
    linarith only [hq1, hn]
  let k := n - 1
  have hk : k+1 = n := by dsimp [k]; omega
  have hkmin : padeR75^k ≤ (q : ℝ) := by
    apply le_of_not_gt
    apply Nat.find_min (pade_modified_powers_escape q)
    change k < n
    omega
  obtain ⟨j,hjn,hjj,hjN⟩ : ∃ j : ℕ, n ≤ j ∧ j ≤ n+1 ∧ N j ≠ 0 := by
    rcases pade_no_adjacent_zero A N L hp ha n with h | h
    · exact ⟨n, Nat.le_refl _, by omega, h⟩
    · exact ⟨n+1, by omega, Nat.le_refl _, h⟩
  have hr1 : 1 ≤ padeR75 := by norm_num [padeR75]
  have hg1 : 1 ≤ padeG75 := by norm_num [padeG75]
  have hjr : 0 < padeR75^j := by
    exact pow_pos (by norm_num [padeR75]) _
  have hrj : (q : ℝ) < padeR75^j :=
    lt_of_lt_of_le hn (pow_le_pow_right₀ hr1 hjn)
  have hinv : padeRho75^j = 1 / padeR75^j := by
    rw [← one_div_pow]
    congr 1
    norm_num [padeR75,padeRho75]
  have hh : (A j : ℝ) * L + (N j : ℝ) < 1/2 := by
    apply lt_of_le_of_lt (he j)
    rw [hinv, mul_one_div]
    apply (div_lt_iff₀ hjr).2
    linarith only [hrj]
  have hhabs : |(A j : ℝ) * L + (N j : ℝ)| < 1/2 := by
    rw [abs_of_pos (hp j)]
    exact hh
  have hNint : (1 : ℤ) ≤ |N j| := by
    have hh' := abs_pos.mpr hjN
    omega
  have hNreal : (1 : ℝ) ≤ |(N j : ℝ)| := by exact_mod_cast hNint
  have htri : |(N j : ℝ)| ≤ |(A j : ℝ) * L + (N j : ℝ)| +
      |(A j : ℝ)| * |L| := by
    calc
      |(N j : ℝ)| = |((A j : ℝ) * L + (N j : ℝ)) +
          -((A j : ℝ) * L)| := by
            rw [show (A j : ℝ) * L + (N j : ℝ) +
              -((A j : ℝ) * L) = (N j : ℝ) by ring]
      _ ≤ |(A j : ℝ) * L + (N j : ℝ)| +
          |-((A j : ℝ) * L)| := abs_add_le _ _
      _ = _ := by rw [abs_neg,abs_mul]
  have hprod : 1/2 < 12 * padeG75^j * |L| := by
    have hprod0 : 1/2 < |(A j : ℝ)| * |L| :=
      by linarith only [hNreal, htri, hhabs]
    exact lt_of_lt_of_le hprod0
      (mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _))
  have hG : padeG75 ≤ padeR75^75 := by norm_num [padeG75,padeR75]
  have hG0 : 0 ≤ padeG75 := by norm_num [padeG75]
  have hGk : padeG75^k ≤ (q : ℝ)^75 := by
    calc
      padeG75^k ≤ (padeR75^75)^k := pow_le_pow_left₀ hG0 hG _
      _ = (padeR75^k)^75 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 75 k]
      _ ≤ _ := pow_le_pow_left₀ (pow_nonneg
        (by norm_num [padeR75]) k) hkmin _
  have hkj : j ≤ k+2 := by omega
  have hGj : padeG75^j ≤ padeG75^2 * (q : ℝ)^75 := by
    calc
      padeG75^j ≤ padeG75^(k+2) := pow_le_pow_right₀ hg1 hkj
      _ = padeG75^2 * padeG75^k := by rw [pow_add, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hGk (sq_nonneg _)
  have hC : (24 : ℝ) * padeG75^2 ≤ 2^100 :=
    pade_modified_prefactor.le
  have hpre : 24 * padeG75^j ≤ (2 : ℝ)^100 * (q : ℝ)^75 := by
    calc
      24 * padeG75^j ≤ 24 * (padeG75^2 * (q : ℝ)^75) :=
        mul_le_mul_of_nonneg_left hGj (by norm_num)
      _ = (24 * padeG75^2) * (q : ℝ)^75 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  have hbig : (1 : ℝ) < (2^100 * (q : ℝ)^75) * |L| := by
    have hh' := mul_le_mul_of_nonneg_right hpre (abs_nonneg L)
    linarith only [hh', hprod]
  exact (div_lt_iff₀ (by positivity)).2 (by simpa [mul_comm] using hbig)


theorem padeA_growth75 (n : ℕ) : |(padeA n:ℝ)| ≤ 12*padeG75^n := by
  have hn : 0 ≤ (padeDen n:ℝ) := by positivity
  have he : (padeDen n:ℝ) ≤ 2 * ((7:ℝ)/2)^(8*n) :=
    pade_lcm_bound_modified n
  have hc : |((padeP n).coeff (8*n):ℝ)| ≤
      6 * ((20:ℝ)^5*14^3)^n := by
    exact_mod_cast padeCoeffGrowth n
  unfold padeA
  push_cast
  rw [abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ (2*((7:ℝ)/2)^(8*n)) * (6*((20:ℝ)^5*14^3)^n) :=
      mul_le_mul he hc (abs_nonneg _) (by positivity)
    _ = 12 * ((((7:ℝ)/2)^8)^n * ((20:ℝ)^5*14^3)^n) := by
      rw [pow_mul ((7:ℝ)/2) 8 n]
      ring
    _ = 12*padeG75^n := by
      rw [← mul_pow]
      have h : ((7:ℝ)/2)^8 * ((20:ℝ)^5*14^3) = padeG75 := by
        rw [← mul_assoc]
        exact pade_modified_coefficient_scale
      rw [h]

theorem hsep75
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    (1 : ℝ) / (2^100 * (v : ℝ)^75) <
      |(u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3| := by
  let L := (u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3
  change (1:ℝ)/(2^100*(v:ℝ)^75) < |L|
  have hvn : 1 ≤ v := by omega
  have hvR : 1 ≤ (v:ℝ) := by exact_mod_cast hvn
  have hv0 : 0 < (v:ℝ) := by exact_mod_cast hv
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h32 : Real.log ((3:ℝ)/2) = Real.log 3-Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have h43 : Real.log ((4:ℝ)/3) = 2*Real.log 2-Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have hsmall : (1:ℝ)/(2^100*(v:ℝ)^75) < 1/4 := by
    apply (div_lt_iff₀ (by positivity)).2
    have h : (1:ℝ) ≤ (v:ℝ)^75 := one_le_pow₀ hvR
    have h' := mul_le_mul_of_nonneg_left h
      (by norm_num : (0:ℝ) ≤ (1/4)*2^100)
    nlinarith only [h']
  by_cases huv : u ≤ v
  · have hcast : (u:ℝ) ≤ v := by exact_mod_cast huv
    have hlog : (1:ℝ)/3 ≤ Real.log 3-Real.log 2 := by
      simpa only [h32] using pade_log32_lb
    have hh1 := mul_le_mul_of_nonneg_right hcast hl2.le
    have hh2 := mul_le_mul_of_nonneg_left hlog hv0.le
    have hL : (1:ℝ)/4 ≤ -L := by
      dsimp [L]
      nlinarith only [hh1,hh2,hvR]
    exact hsmall.trans_le (hL.trans (neg_le_abs _))
  by_cases h2 : 2*v ≤ u
  · have hx : (2:ℝ)*(v:ℝ) ≤ u := by exact_mod_cast h2
    have hlog : (1:ℝ)/4 ≤ 2*Real.log 2-Real.log 3 := by
      simpa only [h43] using pade_log43_lb
    have hh1 := mul_le_mul_of_nonneg_right hx hl2.le
    have hh2 := mul_le_mul_of_nonneg_left hlog hv0.le
    have hL : (1:ℝ)/4 ≤ L := by
      dsimp [L]
      nlinarith only [hh1,hh2,hvR]
    exact hsmall.trans_le (hL.trans (le_abs_self _))
  let a : ℤ := (2:ℤ)*(v:ℤ)-(u:ℤ)
  let b : ℤ := (u:ℤ)-(v:ℤ)
  have ha : 0 < (a:ℝ) := by
    have h : u < 2*v := by omega
    have h' : (u:ℝ) < (2:ℝ)*(v:ℝ) := by exact_mod_cast h
    dsimp [a]; push_cast; linarith
  have hb : 0 < (b:ℝ) := by
    have h : v < u := by omega
    have h' : (v:ℝ)<(u:ℝ) := by exact_mod_cast h
    dsimp [b]; push_cast; linarith
  have hab : (a:ℝ)+(b:ℝ)=(v:ℝ) := by
    dsimp [a,b]; push_cast; ring
  choose B hB using padeLeftLog
  choose C hC using padeRightLog
  let N : ℕ → ℤ := fun n => -a*B n+b*C n
  have hEq (n : ℕ) :
      (padeA n:ℝ)*L+(N n:ℝ) =
        (a:ℝ)*padeLeft n + (b:ℝ)*padeRight n := by
    have hlog : -(a:ℝ)*Real.log (3/2) +
        (b:ℝ)*Real.log (4/3) = L := by
      rw [h32,h43]
      dsimp [a,b,L]
      push_cast
      ring
    have hleft : padeLeft n =
        -((padeA n:ℝ)*Real.log (3/2)+(B n:ℝ)) := by
      linarith only [hB n]
    rw [hleft,hC n,←hlog]
    dsimp [N]
    push_cast
    ring
  apply padeEscape75 v hv L padeA N _ _ padeA_alt padeA_growth75
  · intro n
    rw [hEq]
    have hD0 : (0:ℝ)<padeDen n := by exact_mod_cast padeDenPos n
    exact add_pos (mul_pos ha (pade_left_positive n _ hD0))
      (mul_pos hb (pade_right_positive n _ hD0))
  · intro n
    rw [hEq]
    have hD0 : (0:ℝ)≤padeDen n := by positivity
    have hD : (padeDen n:ℝ) ≤ 2 * ((7:ℝ)/2)^(8*n) :=
      pade_lcm_bound_modified n
    have h1 := mul_le_mul_of_nonneg_left
      (pade_left_bound75 n _ hD0 hD) ha.le
    have h2a := mul_le_mul_of_nonneg_left
      (pade_right_bound75 n _ hD0 hD) hb.le
    change (a:ℝ)*padeLeft n ≤ (a:ℝ)*(1/2*padeRho75^n) at h1
    change (b:ℝ)*padeRight n ≤ (b:ℝ)*(1/3*padeRho75^n) at h2a
    have hh : (0:ℝ) ≤ (b:ℝ)*padeRho75^n :=
      mul_nonneg hb.le (pow_nonneg (by norm_num [padeRho75]) _)
    calc
      _ ≤ (a:ℝ)*(1/2*padeRho75^n)+(b:ℝ)*(1/3*padeRho75^n) :=
        add_le_add h1 h2a
      _ ≤ ((1:ℝ)/2)*((a:ℝ)+(b:ℝ))*padeRho75^n := by
        nlinarith only [hh]
      _ = ((1:ℝ)/2)*(v:ℝ)*padeRho75^n := by rw [hab]


end CollatzPade

open CollatzPade
#print axioms CollatzPade.hsep75

-- ===== Bridge =====
namespace BB6Kit

theorem laurent_23_of_sep
    (hsep : ∀ u v : ℕ, 0 < u → 0 < v →
      (1 : ℝ) / (2 ^ 100 * (v : ℝ) ^ 75) <
        |(u : ℝ) * Real.log 2 - (v : ℝ) * Real.log 3|)
    (b1 b2 : ℕ) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    -(25.2 * Real.log 3 * (max (Real.log ((b1 : ℝ) / Real.log 3 + b2) + 0.38) 10) ^ 2) ≤
      Real.log |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2| := by
  let H : ℝ := max (Real.log ((b1 : ℝ) / Real.log 3 + b2) + 0.38) 10
  have hb1r : (0 : ℝ) < (b1 : ℝ) := by
    exact_mod_cast hb1
  have hb2r : (0 : ℝ) < (b2 : ℝ) := by
    exact_mod_cast hb2
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hHten : (10 : ℝ) ≤ H := by
    dsimp [H]
    exact le_max_right _ _
  have hHarg :
      Real.log ((b1 : ℝ) / Real.log 3 + b2) + 0.38 ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have harg :
      (b2 : ℝ) ≤ (b1 : ℝ) / Real.log 3 + (b2 : ℝ) := by
    have hdiv : 0 ≤ (b1 : ℝ) / Real.log 3 :=
      le_of_lt (div_pos hb1r (by linarith))
    linarith
  have hlogb2 : Real.log (b2 : ℝ) ≤ H := by
    have hmono := Real.log_le_log hb2r harg
    linarith
  have hlogden :
      Real.log ((1 : ℝ) / ((2 : ℝ) ^ 100 * (b2 : ℝ) ^ 75)) =
        - ((100 : ℝ) * Real.log 2 + 75 * Real.log (b2 : ℝ)) := by
    rw [Real.log_div (by norm_num) (by positivity),
      Real.log_one, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] <;> ring
  have habs :
      |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2| =
        |(b1 : ℝ) * Real.log 2 - (b2 : ℝ) * Real.log 3| :=
    abs_sub_comm _ _
  have hlogform :
      - ((100 : ℝ) * Real.log 2 + 75 * Real.log (b2 : ℝ)) <
        Real.log |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2| := by
    have h := Real.log_lt_log
      (show (0 : ℝ) < (1 : ℝ) / ((2 : ℝ) ^ 100 * (b2 : ℝ) ^ 75) by
        positivity)
      (hsep b1 b2 hb1 hb2)
    rw [hlogden] at h
    rw [habs]
    exact h
  have hquad : (100 : ℝ) + 75 * H ≤ 11 * H ^ 2 := by
    nlinarith [sq_nonneg (H - 10)]
  have hcoef : (11 : ℝ) ≤ 25.2 * Real.log 3 := by
    nlinarith
  have hcoefsqr :
      (11 : ℝ) * H ^ 2 ≤ (25.2 * Real.log 3) * H ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg H)
  have hbound :
      (100 : ℝ) * Real.log 2 + 75 * Real.log (b2 : ℝ) ≤
        25.2 * Real.log 3 * H ^ 2 := by
    calc
      (100 : ℝ) * Real.log 2 + 75 * Real.log (b2 : ℝ)
          ≤ 100 + 75 * H := by linarith
      _ ≤ 11 * H ^ 2 := hquad
      _ ≤ 25.2 * Real.log 3 * H ^ 2 := hcoefsqr
  change -(25.2 * Real.log 3 * H ^ 2) ≤
    Real.log |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2|
  linarith

end BB6Kit


theorem solution (b1 b2 : ℕ) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    -(25.2 * Real.log 3 * (max (Real.log ((b1 : ℝ) / Real.log 3 + b2) + 0.38) 10) ^ 2) ≤
      Real.log |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2| :=
  BB6Kit.laurent_23_of_sep CollatzPade.hsep75 b1 b2 hb1 hb2
