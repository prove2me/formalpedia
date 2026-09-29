-- Prove2me | solution 1 for Freiman.lower_h5_exception_event
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T21:13:03.062314+00:00
-- url     : https://prove2.me/submissions/60a8421a-b8d0-4a15-992e-9debe8fc5c1e

import Mathlib
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry

/-! Disproof of 12adca3d `Freiman.lower_h5_exception_event`.

The hypotheses never pin the RIGHT context word `c.context.words.2` (only
`lowerH5CatalogValid`, which is not assumed, forces it to be `[3,1]`), so nothing forces the
predecessor to satisfy `lowerR`, which `LowerH5PriorityEvent.branch` demands.

Counterexample (n = 1, m = 0, t = 1133/250):
* `h 0 = ([3,1,3,1,2],[3,1,2,1,2])`, a member of `lowerFixedRoots`; it normalises to
  `([3,1,2,1,2],[3,1,3,1,2])`, so it is not mixed, has ¬L, ¬R, ¬A3, A9 and ¬A16.
* `h 1 = lowerChild (h 0) ([2],[]) = ([3,1,2,1,2,2],[3,1,3,1,2])`; the label `([2],[])` is
  offered (A9 branch) and its priority clause is vacuous because ¬R.
* `c` has kind `b2h9not`, context `(([2],[2]),(false,false))`, words `([2],[])`, reflect,
  old cuts `[H7,H9,H18]`, the context box as rectangle; its relaxed goodness is `some`.
Every real inequality (widths for normalisation / shortening, cover endpoints, goodness,
parameter box, the H7/H9/H18 certificate cuts and A9) is discharged by rational interval
arithmetic.  The conclusion would need `lowerR (h 0)`, which is false. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Freiman

/-! ## Interval arithmetic for `prefixEval` -/

/-- rational prefix evaluation -/
def dp12PeQ : List ℕ+ → ℚ → ℚ
  | [], x => x
  | a :: w, x => 1 / (((a : ℕ) : ℚ) + dp12PeQ w x)

lemma dp12_peQ_cast (w : List ℕ+) (x : ℚ) : ((dp12PeQ w x : ℚ) : ℝ) = prefixEval w (x : ℝ) := by
  induction w with
  | nil => simp [dp12PeQ, prefixEval]
  | cons a w ih => simp [dp12PeQ, prefixEval, ih]

lemma dp12_pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => simpa [prefixEval] using hx
  | cons a w ih =>
    simp only [prefixEval]
    have : (0:ℝ) ≤ ((a : ℕ) : ℝ) := by positivity
    positivity

lemma dp12_pe_mono (w : List ℕ+) (x z y : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    (prefixEval w x ≤ prefixEval w z ∧ prefixEval w z ≤ prefixEval w y) ∨
    (prefixEval w y ≤ prefixEval w z ∧ prefixEval w z ≤ prefixEval w x) := by
  induction w with
  | nil => left; simp [prefixEval]; exact ⟨hxz, hzy⟩
  | cons a w ih =>
    simp only [prefixEval]
    have ha : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
    have h0x := dp12_pe_nonneg w x hx
    have h0z := dp12_pe_nonneg w z (le_trans hx hxz)
    have h0y := dp12_pe_nonneg w y (le_trans hx (le_trans hxz hzy))
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      constructor
      · exact one_div_le_one_div_of_le (by linarith) (by linarith)
      · exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · left
      constructor
      · exact one_div_le_one_div_of_le (by linarith) (by linarith)
      · exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- interval bounds of prefixEval at a real in [lo,hi] -/
def dp12Lo (w : List ℕ+) (lo hi : ℚ) : ℚ := min (dp12PeQ w lo) (dp12PeQ w hi)
def dp12Hi (w : List ℕ+) (lo hi : ℚ) : ℚ := max (dp12PeQ w lo) (dp12PeQ w hi)

lemma dp12_pe_bounds (w : List ℕ+) (lo hi : ℚ) (z : ℝ) (h0 : 0 ≤ lo) (h1 : (lo : ℝ) ≤ z)
    (h2 : z ≤ (hi : ℝ)) :
    ((dp12Lo w lo hi : ℚ) : ℝ) ≤ prefixEval w z ∧ prefixEval w z ≤ ((dp12Hi w lo hi : ℚ) : ℝ) := by
  have h0' : (0:ℝ) ≤ (lo : ℝ) := by exact_mod_cast h0
  simp only [dp12Lo, dp12Hi, Rat.cast_min, Rat.cast_max, dp12_peQ_cast]
  rcases dp12_pe_mono w lo z hi h0' h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
  · exact ⟨min_le_of_left_le a, le_max_of_le_right b⟩
  · exact ⟨min_le_of_right_le a, le_max_of_le_left b⟩

/-- constants -/
def dp12TauL : ℚ := 7320508075688772 / 10^16
def dp12TauU : ℚ := 7320508075688773 / 10^16
def dp12AlL : ℚ := 2637626158259733 / 10^16
def dp12AlU : ℚ := 2637626158259734 / 10^16
def dp12BeL : ℚ := 7912878474779200 / 10^16
def dp12BeU : ℚ := 7912878474779201 / 10^16

lemma dp12_tau_bounds : ((dp12TauL : ℚ) : ℝ) ≤ lowerTau ∧ lowerTau ≤ ((dp12TauU : ℚ) : ℝ) := by
  unfold lowerTau dp12TauL dp12TauU
  constructor
  · have : ((7320508075688772 / 10^16 : ℚ) : ℝ) + 1 ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by positivity) (by norm_num)]; norm_num
    push_cast at this ⊢; linarith
  · have : Real.sqrt 3 ≤ ((7320508075688773 / 10^16 : ℚ) : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by positivity)]; norm_num
    push_cast at this ⊢; linarith

lemma dp12_alpha_bounds : ((dp12AlL : ℚ) : ℝ) ≤ lowerAlpha ∧ lowerAlpha ≤ ((dp12AlU : ℚ) : ℝ) := by
  unfold lowerAlpha dp12AlL dp12AlU
  constructor
  · have : 6 * ((2637626158259733 / 10^16 : ℚ) : ℝ) + 3 ≤ Real.sqrt 21 := by
      rw [Real.le_sqrt (by positivity) (by norm_num)]; norm_num
    push_cast at this ⊢; linarith
  · have : Real.sqrt 21 ≤ 6 * ((2637626158259734 / 10^16 : ℚ) : ℝ) + 3 := by
      rw [Real.sqrt_le_left (by positivity)]; norm_num
    push_cast at this ⊢; linarith

lemma dp12_beta_bounds : ((dp12BeL : ℚ) : ℝ) ≤ lowerBeta ∧ lowerBeta ≤ ((dp12BeU : ℚ) : ℝ) := by
  unfold lowerBeta dp12BeL dp12BeU
  constructor
  · have : 2 * ((7912878474779200 / 10^16 : ℚ) : ℝ) + 3 ≤ Real.sqrt 21 := by
      rw [Real.le_sqrt (by positivity) (by norm_num)]; norm_num
    push_cast at this ⊢; linarith
  · have : Real.sqrt 21 ≤ 2 * ((7912878474779201 / 10^16 : ℚ) : ℝ) + 3 := by
      rw [Real.sqrt_le_left (by positivity)]; norm_num
    push_cast at this ⊢; linarith

/-- width bounds -/
def dp12WLo (w : List ℕ+) : ℚ :=
  max (dp12Lo w dp12BeL dp12BeU - dp12Hi w dp12AlL dp12AlU)
      (dp12Lo w dp12AlL dp12AlU - dp12Hi w dp12BeL dp12BeU)
def dp12WHi (w : List ℕ+) : ℚ :=
  max (dp12Hi w dp12BeL dp12BeU - dp12Lo w dp12AlL dp12AlU)
      (dp12Hi w dp12AlL dp12AlU - dp12Lo w dp12BeL dp12BeU)

lemma dp12_width_bounds (w : List ℕ+) :
    ((dp12WLo w : ℚ) : ℝ) ≤ lowerWidth w ∧ lowerWidth w ≤ ((dp12WHi w : ℚ) : ℝ) := by
  obtain ⟨a1, a2⟩ := dp12_alpha_bounds
  obtain ⟨b1, b2⟩ := dp12_beta_bounds
  obtain ⟨pa1, pa2⟩ := dp12_pe_bounds w dp12AlL dp12AlU lowerAlpha (by norm_num [dp12AlL]) a1 a2
  obtain ⟨pb1, pb2⟩ := dp12_pe_bounds w dp12BeL dp12BeU lowerBeta (by norm_num [dp12BeL]) b1 b2
  unfold lowerWidth dp12WLo dp12WHi
  push_cast
  constructor
  · apply max_le
    · exact le_trans (by linarith) (le_abs_self _)
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_le]
    constructor
    · have := le_max_right ((dp12Hi w dp12BeL dp12BeU : ℝ) - (dp12Lo w dp12AlL dp12AlU : ℝ))
        ((dp12Hi w dp12AlL dp12AlU : ℝ) - (dp12Lo w dp12BeL dp12BeU : ℝ))
      linarith
    · have := le_max_left ((dp12Hi w dp12BeL dp12BeU : ℝ) - (dp12Lo w dp12AlL dp12AlU : ℝ))
        ((dp12Hi w dp12AlL dp12AlU : ℝ) - (dp12Lo w dp12BeL dp12BeU : ℝ))
      linarith

lemma dp12_wle (u v : List ℕ+) (h : dp12WHi u ≤ dp12WLo v) : lowerWidth u ≤ lowerWidth v := by
  have h' : ((dp12WHi u : ℚ) : ℝ) ≤ ((dp12WLo v : ℚ) : ℝ) := by exact_mod_cast h
  linarith [(dp12_width_bounds u).2, (dp12_width_bounds v).1]

lemma dp12_wnle (u v : List ℕ+) (h : dp12WHi v < dp12WLo u) : ¬ lowerWidth u ≤ lowerWidth v := by
  have h' : ((dp12WHi v : ℚ) : ℝ) < ((dp12WLo u : ℚ) : ℝ) := by exact_mod_cast h
  intro hc; linarith [(dp12_width_bounds u).1, (dp12_width_bounds v).2]

lemma dp12_wle75 (u v : List ℕ+) (h : dp12WHi u ≤ 7/5 * dp12WLo v) :
    lowerWidth u ≤ (7/5 : ℝ) * lowerWidth v := by
  have h' : ((dp12WHi u : ℚ) : ℝ) ≤ ((7/5 * dp12WLo v : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith [(dp12_width_bounds u).2, (dp12_width_bounds v).1]

lemma dp12_wnle75 (u v : List ℕ+) (h : 7/5 * dp12WHi v < dp12WLo u) :
    ¬ lowerWidth u ≤ (7/5 : ℝ) * lowerWidth v := by
  have h' : ((7/5 * dp12WHi v : ℚ) : ℝ) < ((dp12WLo u : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  intro hc; linarith [(dp12_width_bounds u).1, (dp12_width_bounds v).2]

/-! width facts -/
lemma dp12_N1 : ¬ lowerWidth [3,1,2,1,2] ≤ lowerWidth [3,1,3,1,2] :=
  dp12_wnle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N2 : ¬ lowerWidth [3,1,3,1,2] ≤ lowerWidth [3,1,2,1,2,2] :=
  dp12_wnle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N3 : ¬ lowerWidth [3,1,3,1,2,1] ≤ lowerWidth [3,1,2,1,2,2] :=
  dp12_wnle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N4 : ¬ lowerWidth [3,1,3,1,2] ≤ lowerWidth [3,1,2,1,2,1] :=
  dp12_wnle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N5 : lowerWidth [3,1,3,1,2,1] ≤ lowerWidth [3,1,2,1,2,1] :=
  dp12_wle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N6 : lowerWidth [3,1,2,1,2,2] ≤ lowerWidth [3,1,3,1,2,1] :=
  dp12_wle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_N7 : ¬ lowerWidth [3,1,2,1,2,2] ≤ lowerWidth [3,1,3,1,2,2] :=
  dp12_wnle _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S1 : ¬ lowerWidth [3,1,2,1,2,1,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,3,1,2,1,3] :=
  dp12_wnle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S2 : ¬ lowerWidth [3,1,2,1,2,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,3,1,2,3] :=
  dp12_wnle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S3 : ¬ lowerWidth [3,1,3,1,2,1,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,2,1,2,2,3] :=
  dp12_wnle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S4 : lowerWidth [3,1,3,1,2,1,1,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,2,1,2,2,1,3] :=
  dp12_wle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S5 : ¬ lowerWidth [3,1,2,1,2,2,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,3,1,2,2,3] :=
  dp12_wnle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])
lemma dp12_S6 : ¬ lowerWidth [3,1,2,1,2,2,1,3] ≤ (7/5 : ℝ) * lowerWidth [3,1,3,1,2,2,1,3] :=
  dp12_wnle75 _ _ (by norm_num [dp12WHi, dp12WLo, dp12Hi, dp12Lo, dp12PeQ, dp12AlL, dp12AlU, dp12BeL, dp12BeU])

lemma dp12_ends_iff (w s : List ℕ+) : lowerEnds w s ↔ s.isSuffixOf w = true := by
  unfold lowerEnds; rw [List.isSuffixOf_iff_suffix]

lemma dp12_ends (w s : List ℕ+) (h : s.isSuffixOf w = false) : ¬ lowerEnds w s := by
  rw [dp12_ends_iff]; simp [h]

lemma dp12_nshort (w : List ℕ+) (u : Bool) (h3 : ([3] : List ℕ+).isSuffixOf w = false)
    (h31 : ([3,1] : List ℕ+).isSuffixOf w = false) : lowerNaturalShort w u = false := by
  have a := dp12_ends w [3] h3
  have b := dp12_ends w [3,1] h31
  unfold lowerNaturalShort
  split_ifs <;> simp [a, b]

lemma dp12_ns0 (u : Bool) : lowerNaturalShort [3,1,2,1,2] u = false := dp12_nshort _ u rfl rfl
lemma dp12_ns1 (u : Bool) : lowerNaturalShort [3,1,3,1,2] u = false := dp12_nshort _ u rfl rfl
lemma dp12_ns2 (u : Bool) : lowerNaturalShort [3,1,2,1,2,2] u = false := dp12_nshort _ u rfl rfl
lemma dp12_ns3 (u : Bool) : lowerNaturalShort [3,1,3,1,2,1] u = false := dp12_nshort _ u rfl rfl
lemma dp12_ns4 (u : Bool) : lowerNaturalShort [3,1,2,1,2,1] u = false := dp12_nshort _ u rfl rfl
lemma dp12_ns5 (u : Bool) : lowerNaturalShort [3,1,3,1,2,2] u = false := dp12_nshort _ u rfl rfl
lemma dp12_norm0 : lowerNormalize ([3,1,3,1,2],[3,1,2,1,2]) = ([3,1,2,1,2],[3,1,3,1,2]) := by
  unfold lowerNormalize; rw [if_neg dp12_N1]
lemma dp12_norm1 : lowerNormalize ([3,1,2,1,2,2],[3,1,3,1,2]) = ([3,1,3,1,2],[3,1,2,1,2,2]) := by
  unfold lowerNormalize; rw [if_neg dp12_N2]
lemma dp12_norm1e : lowerNormalize ([3,1,2,1,2,2],[3,1,3,1,2,1]) = ([3,1,3,1,2,1],[3,1,2,1,2,2]) := by
  unfold lowerNormalize; rw [if_neg dp12_N3]
lemma dp12_normae : lowerNormalize ([3,1,2,1,2,1],[3,1,3,1,2,1]) = ([3,1,2,1,2,1],[3,1,3,1,2,1]) := by
  unfold lowerNormalize; rw [if_pos dp12_N5]
lemma dp12_normb : lowerNormalize ([3,1,3,1,2,1],[3,1,2,1,2,2]) = ([3,1,3,1,2,1],[3,1,2,1,2,2]) := by
  unfold lowerNormalize; rw [if_pos dp12_N6]
lemma dp12_normc : lowerNormalize ([3,1,3,1,2,2],[3,1,2,1,2,2]) = ([3,1,2,1,2,2],[3,1,3,1,2,2]) := by
  unfold lowerNormalize; rw [if_neg dp12_N7]
lemma dp12_E_le (w1 w2 : List ℕ+) (x : ℚ)
    (h : 4 + dp12Hi w1 dp12TauL dp12TauU + dp12Hi w2 dp12TauL dp12TauU ≤ x) :
    4 + prefixEval w1 lowerTau + prefixEval w2 lowerTau ≤ (x : ℝ) := by
  obtain ⟨t1, t2⟩ := dp12_tau_bounds
  have h0 : (0:ℚ) ≤ dp12TauL := by norm_num [dp12TauL]
  have a := (dp12_pe_bounds w1 dp12TauL dp12TauU lowerTau h0 t1 t2).2
  have b := (dp12_pe_bounds w2 dp12TauL dp12TauU lowerTau h0 t1 t2).2
  have h' : ((4 + dp12Hi w1 dp12TauL dp12TauU + dp12Hi w2 dp12TauL dp12TauU : ℚ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

lemma dp12_le_E (w1 w2 : List ℕ+) (x : ℚ)
    (h : x ≤ 4 + dp12Lo w1 dp12TauL dp12TauU + dp12Lo w2 dp12TauL dp12TauU) :
    (x : ℝ) ≤ 4 + prefixEval w1 lowerTau + prefixEval w2 lowerTau := by
  obtain ⟨t1, t2⟩ := dp12_tau_bounds
  have h0 : (0:ℚ) ≤ dp12TauL := by norm_num [dp12TauL]
  have a := (dp12_pe_bounds w1 dp12TauL dp12TauU lowerTau h0 t1 t2).1
  have b := (dp12_pe_bounds w2 dp12TauL dp12TauU lowerTau h0 t1 t2).1
  have h' : (x : ℝ) ≤ ((4 + dp12Lo w1 dp12TauL dp12TauU + dp12Lo w2 dp12TauL dp12TauU : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

lemma dp12_mem_cover (p : LowerPair) (a1 a2 b1 b2 : List ℕ+) (x : ℚ)
    (ha : lowerEndpointWords p false = (a1, a2)) (hb : lowerEndpointWords p true = (b1, b2))
    (h1 : 4 + dp12Hi a1 dp12TauL dp12TauU + dp12Hi a2 dp12TauL dp12TauU ≤ x)
    (h2 : x ≤ 4 + dp12Lo b1 dp12TauL dp12TauU + dp12Lo b2 dp12TauL dp12TauU) :
    (x : ℝ) ∈ lowerCover p := by
  unfold lowerCover lowerEndpoint
  rw [ha, hb]
  exact ⟨dp12_E_le a1 a2 x h1, dp12_le_E b1 b2 x h2⟩

/-! endpoint words -/
lemma dp12_EW0f : lowerEndpointWords ([3,1,3,1,2],[3,1,2,1,2]) false =
    ([3,1,3,1,2,1,3],[3,1,2,1,2,1,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N1, dp12_S1]
lemma dp12_EW0t : lowerEndpointWords ([3,1,3,1,2],[3,1,2,1,2]) true =
    ([3,1,3,1,2,3],[3,1,2,1,2,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N1, dp12_S2]
lemma dp12_EW1f : lowerEndpointWords ([3,1,2,1,2,2],[3,1,3,1,2]) false =
    ([3,1,2,1,2,2,3],[3,1,3,1,2,1,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N2, dp12_N3, dp12_S3]
lemma dp12_EW1t : lowerEndpointWords ([3,1,2,1,2,2],[3,1,3,1,2]) true =
    ([3,1,2,1,2,2,1,3],[3,1,3,1,2,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N2]
lemma dp12_EWaf : lowerEndpointWords ([3,1,2,1,2,1],[3,1,3,1,2]) false =
    ([3,1,2,1,2,1,3],[3,1,3,1,2,1,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N4, dp12_N5, dp12_S1]
lemma dp12_EWat : lowerEndpointWords ([3,1,2,1,2,1],[3,1,3,1,2]) true =
    ([3,1,2,1,2,1,1,3],[3,1,3,1,2,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N4]
lemma dp12_EWbf : lowerEndpointWords ([3,1,3,1,2,1],[3,1,2,1,2,2]) false =
    ([3,1,3,1,2,1,3],[3,1,2,1,2,2,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N6, dp12_S3]
lemma dp12_EWbt : lowerEndpointWords ([3,1,3,1,2,1],[3,1,2,1,2,2]) true =
    ([3,1,3,1,2,1,1,3],[3,1,2,1,2,2,1,2,1,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N6, dp12_S4]
lemma dp12_EWcf : lowerEndpointWords ([3,1,3,1,2,2],[3,1,2,1,2,2]) false =
    ([3,1,3,1,2,2,3],[3,1,2,1,2,2,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N7, dp12_S5]
lemma dp12_EWct : lowerEndpointWords ([3,1,3,1,2,2],[3,1,2,1,2,2]) true =
    ([3,1,3,1,2,2,1,3],[3,1,2,1,2,2,1,3]) := by
  simp [lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerEndpointSuffix, dp12_ns0, dp12_ns1, dp12_ns2, dp12_ns3, dp12_ns4, dp12_ns5, dp12_norm0, dp12_norm1, dp12_norm1e, dp12_normae, dp12_normb, dp12_normc, dp12_N7, dp12_S6]

/-! cover memberships -/
lemma dp12_t_C0 : (((1133/250 : ℚ)) : ℝ) ∈ lowerCover ([3,1,3,1,2],[3,1,2,1,2]) :=
  dp12_mem_cover _ _ _ _ _ _ dp12_EW0f dp12_EW0t
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
lemma dp12_t_C1 : (((1133/250 : ℚ)) : ℝ) ∈ lowerCover ([3,1,2,1,2,2],[3,1,3,1,2]) :=
  dp12_mem_cover _ _ _ _ _ _ dp12_EW1f dp12_EW1t
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
lemma dp12_t_Ca : (((1133/250 : ℚ)) : ℝ) ∈ lowerCover ([3,1,2,1,2,1],[3,1,3,1,2]) :=
  dp12_mem_cover _ _ _ _ _ _ dp12_EWaf dp12_EWat
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
lemma dp12_x_Cb : (((1133021/250000 : ℚ)) : ℝ) ∈ lowerCover ([3,1,3,1,2,1],[3,1,2,1,2,2]) :=
  dp12_mem_cover _ _ _ _ _ _ dp12_EWbf dp12_EWbt
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
lemma dp12_x_Cc : (((1133021/250000 : ℚ)) : ℝ) ∈ lowerCover ([3,1,3,1,2,2],[3,1,2,1,2,2]) :=
  dp12_mem_cover _ _ _ _ _ _ dp12_EWcf dp12_EWct
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])
    (by norm_num [dp12Hi, dp12Lo, dp12PeQ, dp12TauL, dp12TauU])

/-! ## Certificate thresholds -/
lemma dp12_thr_lo (c x0 x1 y0 y1 r s cl x0u x1u y0l y1l : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hcl : 0 ≤ cl) (hc : cl ≤ c) (hy0l : 0 ≤ y0l) (hy0 : y0l ≤ y0) (hy1l : 0 ≤ y1l) (hy1 : y1l ≤ y1)
    (hx0 : 0 ≤ x0) (hx0u : x0 ≤ x0u) (hx1 : 0 ≤ x1) (hx1u : x1 ≤ x1u) :
    cl * (1 + s * y0l) * (1 + s * y1l) / ((1 + r * x0u) * (1 + r * x1u)) ≤
      c * (1 + s * y0) * (1 + s * y1) / ((1 + r * x0) * (1 + r * x1)) := by
  have a1 : 0 ≤ s * y0l := mul_nonneg hs hy0l
  have a2 : 0 ≤ s * y1l := mul_nonneg hs hy1l
  have b1 : 0 ≤ r * x0 := mul_nonneg hr hx0
  have b2 : 0 ≤ r * x1 := mul_nonneg hr hx1
  have e1 : s * y0l ≤ s * y0 := mul_le_mul_of_nonneg_left hy0 hs
  have e2 : s * y1l ≤ s * y1 := mul_le_mul_of_nonneg_left hy1 hs
  have f1 : r * x0 ≤ r * x0u := mul_le_mul_of_nonneg_left hx0u hr
  have f2 : r * x1 ≤ r * x1u := mul_le_mul_of_nonneg_left hx1u hr
  apply div_le_div₀
  · have : 0 ≤ c := le_trans hcl hc
    have : 0 ≤ 1 + s * y0 := by linarith
    have : 0 ≤ 1 + s * y1 := by linarith
    positivity
  · apply mul_le_mul (mul_le_mul hc (by linarith) (by linarith) (by linarith)) (by linarith) (by linarith)
    have : 0 ≤ 1 + s * y0 := by linarith
    have : 0 ≤ c := le_trans hcl hc
    positivity
  · have : 0 < 1 + r * x0 := by linarith
    have : 0 < 1 + r * x1 := by linarith
    positivity
  · apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

lemma dp12_thr_hi (c x0 x1 y0 y1 r s cu x0l x1l y0u y1u : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc0 : 0 ≤ c) (hc : c ≤ cu) (hy0 : 0 ≤ y0) (hy0u : y0 ≤ y0u) (hy1 : 0 ≤ y1) (hy1u : y1 ≤ y1u)
    (hx0l : 0 ≤ x0l) (hx0 : x0l ≤ x0) (hx1l : 0 ≤ x1l) (hx1 : x1l ≤ x1) :
    c * (1 + s * y0) * (1 + s * y1) / ((1 + r * x0) * (1 + r * x1)) ≤
      cu * (1 + s * y0u) * (1 + s * y1u) / ((1 + r * x0l) * (1 + r * x1l)) :=
  dp12_thr_lo cu x0l x1l y0u y1u r s c x0 x1 y0 y1 hr hs hc0 hc hy0 hy0u hy1 hy1u hx0l hx0 hx1l hx1

def dp12CU (z : CertField) : ℚ :=
  z.a + certDirectedTerm z.b certSqrt3Upper certSqrt3Lower +
    certDirectedTerm z.c certSqrt7Upper certSqrt7Lower +
    certDirectedTerm z.d certSqrt21Upper certSqrt21Lower

lemma dp12_dir (q lo hi : ℚ) (x : ℝ) (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ (hi : ℝ)) :
    ((certDirectedTerm q lo hi : ℚ) : ℝ) ≤ q * x ∧ (q : ℝ) * x ≤ ((certDirectedTerm q hi lo : ℚ) : ℝ) := by
  unfold certDirectedTerm
  split_ifs with hq
  · have hq' : (0:ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 hq', mul_le_mul_of_nonneg_left h2 hq'⟩
  · have hq' : (q:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hq))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 hq', mul_le_mul_of_nonpos_left h1 hq'⟩

lemma dp12_sqrt_bounds (n : ℕ) (lo hi : ℚ) (h0 : 0 ≤ lo) (hlo : lo ^ 2 ≤ n) (hhi : (n : ℚ) ≤ hi ^ 2)
    (hh : 0 ≤ hi) : (lo : ℝ) ≤ Real.sqrt n ∧ Real.sqrt n ≤ (hi : ℝ) := by
  constructor
  · rw [Real.le_sqrt (by exact_mod_cast h0) (by positivity)]; exact_mod_cast hlo
  · rw [Real.sqrt_le_left (by exact_mod_cast hh)]; exact_mod_cast hhi

lemma dp12_cf_bounds (z : CertField) :
    ((certFieldLower z : ℚ) : ℝ) ≤ certFieldVal z ∧ certFieldVal z ≤ ((dp12CU z : ℚ) : ℝ) := by
  have s3 := dp12_sqrt_bounds 3 certSqrt3Lower certSqrt3Upper (by norm_num [certSqrt3Lower])
    (by norm_num [certSqrt3Lower]) (by norm_num [certSqrt3Upper]) (by norm_num [certSqrt3Upper])
  have s7 := dp12_sqrt_bounds 7 certSqrt7Lower certSqrt7Upper (by norm_num [certSqrt7Lower])
    (by norm_num [certSqrt7Lower]) (by norm_num [certSqrt7Upper]) (by norm_num [certSqrt7Upper])
  have s21 := dp12_sqrt_bounds 21 certSqrt21Lower certSqrt21Upper (by norm_num [certSqrt21Lower])
    (by norm_num [certSqrt21Lower]) (by norm_num [certSqrt21Upper]) (by norm_num [certSqrt21Upper])
  push_cast at s3 s7 s21
  have d3 := dp12_dir z.b _ _ _ s3.1 s3.2
  have d7 := dp12_dir z.c _ _ _ s7.1 s7.2
  have d21 := dp12_dir z.d _ _ _ s21.1 s21.2
  unfold certFieldLower dp12CU certFieldVal
  push_cast
  constructor <;> linarith [d3.1, d3.2, d7.1, d7.2, d21.1, d21.2]

def dp12TL (t : CertThreshold) (r s : ℚ) : ℚ :=
  certFieldLower t.c * (1 + s * certFieldLower t.y0) * (1 + s * certFieldLower t.y1) /
    ((1 + r * dp12CU t.x0) * (1 + r * dp12CU t.x1))
def dp12TU (t : CertThreshold) (r s : ℚ) : ℚ :=
  dp12CU t.c * (1 + s * dp12CU t.y0) * (1 + s * dp12CU t.y1) /
    ((1 + r * certFieldLower t.x0) * (1 + r * certFieldLower t.x1))
def dp12TOk (t : CertThreshold) : Prop :=
  0 ≤ certFieldLower t.c ∧ 0 ≤ certFieldLower t.x0 ∧ 0 ≤ certFieldLower t.x1 ∧
    0 ≤ certFieldLower t.y0 ∧ 0 ≤ certFieldLower t.y1

lemma dp12_thr_bounds (t : CertThreshold) (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hok : dp12TOk t) :
    ((dp12TL t r s : ℚ) : ℝ) ≤ certThresholdVal t r s ∧ certThresholdVal t r s ≤ ((dp12TU t r s : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  have hr' : (0:ℝ) ≤ r := by exact_mod_cast hr
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast hs
  have c := dp12_cf_bounds t.c
  have x0 := dp12_cf_bounds t.x0
  have x1 := dp12_cf_bounds t.x1
  have y0 := dp12_cf_bounds t.y0
  have y1 := dp12_cf_bounds t.y1
  have h1' : (0:ℝ) ≤ (certFieldLower t.c : ℝ) := by exact_mod_cast h1
  have h2' : (0:ℝ) ≤ (certFieldLower t.x0 : ℝ) := by exact_mod_cast h2
  have h3' : (0:ℝ) ≤ (certFieldLower t.x1 : ℝ) := by exact_mod_cast h3
  have h4' : (0:ℝ) ≤ (certFieldLower t.y0 : ℝ) := by exact_mod_cast h4
  have h5' : (0:ℝ) ≤ (certFieldLower t.y1 : ℝ) := by exact_mod_cast h5
  unfold certThresholdVal certThresholdNum certThresholdDen dp12TL dp12TU
  push_cast
  constructor
  · exact dp12_thr_lo _ _ _ _ _ _ _ _ _ _ _ _ hr' hs' h1' c.1 h4' y0.1 h5' y1.1
      (le_trans h2' x0.1) x0.2 (le_trans h3' x1.1) x1.2
  · exact dp12_thr_hi _ _ _ _ _ _ _ _ _ _ _ _ hr' hs' (le_trans h1' c.1) c.2
      (le_trans h4' y0.1) y0.2 (le_trans h5' y1.1) y1.2 h2' x0.1 h3' x1.1


/-! ## Concrete facts about the counterexample -/

def dp12h0 : LowerPair := ([3,1,3,1,2],[3,1,2,1,2])
def dp12h1 : LowerPair := ([3,1,2,1,2,2],[3,1,3,1,2])
def dp12H : ℕ → LowerPair
  | 0 => dp12h0
  | _ => dp12h1

lemma dp12_r1 : lowerRatio [3,1,2,1,2] = ((15/41 : ℚ) : ℝ) := by
  simp [lowerRatio, lowerCD]
lemma dp12_r2 : lowerRatio [3,1,3,1,2] = ((19/53 : ℚ) : ℝ) := by
  simp [lowerRatio, lowerCD]
lemma dp12_r3 : lowerRatio [3,1,2,1,2,2] = ((41/97 : ℚ) : ℝ) := by
  simp [lowerRatio, lowerCD]
lemma dp12_sc : lowerScale ([3,1,2,1,2],[3,1,3,1,2]) = ((1681/2809 : ℚ) : ℝ) := by
  simp [lowerScale, lowerCD]; norm_num

lemma dp12_notR : ¬ lowerR dp12h0 := by
  unfold lowerR dp12h0; rw [dp12_norm0]; exact dp12_ends _ _ rfl

lemma dp12_A9 : lowerA dp12h0 9 := by
  show lowerScale (lowerNormalize dp12h0) ≤
    lowerThreshold dp12h0 ((3 - Real.sqrt 3) / 2) 36 63 63 66
  unfold lowerThreshold dp12h0
  have e36 : lowerTheta 36 = prefixEval [] (lowerTau / 2) := rfl
  have e63 : lowerTheta 63 = prefixEval [2,3] lowerTau := rfl
  have e66 : lowerTheta 66 = prefixEval [1,1,3] lowerTau := rfl
  simp only [dp12_norm0, dp12_r1, dp12_r2, dp12_sc, e36, e63, e66, prefixEval]
  obtain ⟨t1, t2⟩ := dp12_tau_bounds
  have h0 : (0:ℚ) ≤ dp12TauL := by norm_num [dp12TauL]
  have b63 := dp12_pe_bounds [2,3] dp12TauL dp12TauU lowerTau h0 t1 t2
  have b66 := dp12_pe_bounds [1,1,3] dp12TauL dp12TauU lowerTau h0 t1 t2
  have hc : ((2 - dp12TauU) / 2 : ℝ) ≤ (3 - Real.sqrt 3) / 2 := by
    unfold lowerTau at t2; linarith
  have tl0 : (0:ℝ) ≤ lowerTau := le_trans (by norm_num [dp12TauL]) t1
  have key := dp12_thr_lo ((3 - Real.sqrt 3) / 2) (lowerTau / 2) (prefixEval [2,3] lowerTau)
    (prefixEval [2,3] lowerTau) (prefixEval [1,1,3] lowerTau) ((15/41 : ℚ) : ℝ) ((19/53 : ℚ) : ℝ)
    ((2 - dp12TauU) / 2) ((dp12TauU : ℝ) / 2) ((dp12Hi [2,3] dp12TauL dp12TauU : ℚ) : ℝ)
    ((dp12Lo [2,3] dp12TauL dp12TauU : ℚ) : ℝ) ((dp12Lo [1,1,3] dp12TauL dp12TauU : ℚ) : ℝ)
    (by norm_num) (by norm_num) (by norm_num [dp12TauU]) hc
    (by exact_mod_cast (show (0:ℚ) ≤ dp12Lo [2,3] dp12TauL dp12TauU by
      norm_num [dp12Lo, dp12PeQ, dp12TauL, dp12TauU])) b63.1
    (by exact_mod_cast (show (0:ℚ) ≤ dp12Lo [1,1,3] dp12TauL dp12TauU by
      norm_num [dp12Lo, dp12PeQ, dp12TauL, dp12TauU])) b66.1
    (by linarith) (by linarith) (dp12_pe_nonneg _ _ tl0) b63.2
  simp only [prefixEval] at key
  have num : ((1681/2809 : ℚ) : ℝ) ≤ (2 - dp12TauU) / 2 *
      (1 + ((19/53 : ℚ) : ℝ) * ((dp12Lo [2,3] dp12TauL dp12TauU : ℚ) : ℝ)) *
      (1 + ((19/53 : ℚ) : ℝ) * ((dp12Lo [1,1,3] dp12TauL dp12TauU : ℚ) : ℝ)) /
      ((1 + ((15/41 : ℚ) : ℝ) * ((dp12TauU : ℝ) / 2)) *
        (1 + ((15/41 : ℚ) : ℝ) * ((dp12Hi [2,3] dp12TauL dp12TauU : ℚ) : ℝ))) := by
    have : ((1681/2809 : ℚ)) ≤ (2 - dp12TauU) / 2 *
      (1 + (19/53 : ℚ) * dp12Lo [2,3] dp12TauL dp12TauU) *
      (1 + (19/53 : ℚ) * dp12Lo [1,1,3] dp12TauL dp12TauU) /
      ((1 + (15/41 : ℚ) * (dp12TauU / 2)) *
        (1 + (15/41 : ℚ) * dp12Hi [2,3] dp12TauL dp12TauU)) := by
      norm_num [dp12Lo, dp12Hi, dp12PeQ, dp12TauL, dp12TauU]
    exact_mod_cast this
  calc ((1681/2809 : ℚ) : ℝ) ≤ _ := num
    _ ≤ _ := key
    _ = _ := by ring

lemma dp12_offered : lowerOffered dp12h0 ([2],[]) := by
  left
  have hm : ¬ lowerMixed dp12h0 := by simp [lowerMixed, dp12h0]
  rw [if_neg hm]
  have hA9 := dp12_A9
  unfold lowerEqualList
  split_ifs <;> simp_all

lemma dp12_priority (t : ℝ) : lowerPriority t dp12h0 ([2],[]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp at h
  · exact absurd h.2.2.2.2.1 dp12_notR

lemma dp12_child0 : lowerChild dp12h0 ([2],[]) = dp12h1 := by
  simp [lowerChild, dp12h0, dp12h1, dp12_norm0]
lemma dp12_child0a : lowerChild dp12h0 ([1],[]) = ([3,1,2,1,2,1],[3,1,3,1,2]) := by
  simp [lowerChild, dp12h0, dp12_norm0]
lemma dp12_child1a : lowerChild dp12h1 ([1],[]) = ([3,1,3,1,2,1],[3,1,2,1,2,2]) := by
  simp [lowerChild, dp12h1, dp12_norm1]
lemma dp12_child1b : lowerChild dp12h1 ([2],[]) = ([3,1,3,1,2,2],[3,1,2,1,2,2]) := by
  simp [lowerChild, dp12h1, dp12_norm1]

lemma dp12_state0 : lowerState (((1133/250 : ℚ)) : ℝ) dp12h0 := by
  refine ⟨⟨⟨([3,1,3],[3,1,2]), by decide, [1,2], [1,2], by decide, by decide, by decide⟩, by decide⟩,
    ⟨_, dp12_child0a ▸ dp12_t_Ca, dp12_child0 ▸ dp12_t_C1⟩, dp12_t_C0, ?_⟩
  unfold lowerParameterBox dp12h0
  rw [dp12_r1, dp12_r2]
  norm_num

lemma dp12_state1 : lowerState (((1133/250 : ℚ)) : ℝ) dp12h1 := by
  refine ⟨⟨⟨([3,1,2],[3,1,3]), by decide, [1,2,2], [1,2], by decide, by decide, by decide⟩, by decide⟩,
    ⟨_, dp12_child1a ▸ dp12_x_Cb, dp12_child1b ▸ dp12_x_Cc⟩, dp12_t_C1, ?_⟩
  unfold lowerParameterBox dp12h1
  rw [dp12_r3, dp12_r2]
  norm_num

lemma dp12_history : lowerHistory (((1133/250 : ℚ)) : ℝ) dp12H 1 := by
  refine ⟨Or.inl (by decide), ?_, ?_⟩
  · intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact dp12_state0
    · exact dp12_state1
  · intro j hj
    have : j = 0 := by omega
    subst this
    exact ⟨([2],[]), dp12_offered, dp12_priority _, dp12_child0.symm⟩

def dp12Case : LowerH5Case where
  id := 0
  name := "counterexample"
  kind := .b2h9not
  context := ⟨([2],[2]),(false,false)⟩
  words := ([2],[])
  reflect := true
  rectangle := ⟨(lowerH5ContextBox [2]).1,(lowerH5ContextBox [2]).2,
    (lowerH5ContextBox [2]).1,(lowerH5ContextBox [2]).2⟩
  oldCuts := lowerH5ExpectedCuts .b2h9not
  automatic := 0

lemma dp12_shape : lowerH5CaseShape dp12Case := by
  refine ⟨rfl, rfl, by decide, rfl, rfl, ?_⟩
  decide +kernel

lemma dp12_exc : lowerH5Exceptional dp12Case := ⟨rfl, by decide⟩

lemma dp12_cuts : lowerHistoryAtBase ([3,1,2,1,2],[3,1,3,1,2]) dp12Case.oldCuts := by
  have ok7 : dp12TOk lowerHistoryH7.threshold := by unfold dp12TOk; decide +kernel
  have ok9 : dp12TOk lowerHistoryH9.threshold := by unfold dp12TOk; decide +kernel
  have ok18 : dp12TOk lowerH5H18.threshold := by unfold dp12TOk; decide +kernel
  have c7 : dp12TU lowerHistoryH7.threshold (15/41) (19/53) ≤ 1681/2809 := by decide +kernel
  have c9 : 1681/2809 ≤ dp12TL lowerHistoryH9.threshold (15/41) (19/53) := by decide +kernel
  have c18 : 1681/2809 ≤ dp12TL lowerH5H18.threshold (15/41) (19/53) := by decide +kernel
  have b7 := dp12_thr_bounds _ (15/41) (19/53) (by norm_num) (by norm_num) ok7
  have b9 := dp12_thr_bounds _ (15/41) (19/53) (by norm_num) (by norm_num) ok9
  have b18 := dp12_thr_bounds _ (15/41) (19/53) (by norm_num) (by norm_num) ok18
  have c7' : ((dp12TU lowerHistoryH7.threshold (15/41) (19/53) : ℚ) : ℝ) ≤ ((1681/2809 : ℚ) : ℝ) := by
    exact_mod_cast c7
  have c9' : ((1681/2809 : ℚ) : ℝ) ≤ ((dp12TL lowerHistoryH9.threshold (15/41) (19/53) : ℚ) : ℝ) := by
    exact_mod_cast c9
  have c18' : ((1681/2809 : ℚ) : ℝ) ≤ ((dp12TL lowerH5H18.threshold (15/41) (19/53) : ℚ) : ℝ) := by
    exact_mod_cast c18
  have l7 : lowerHistoryH7.lower = true := by decide +kernel
  have s7 : lowerHistoryH7.strict = false := by decide +kernel
  have l9 : lowerHistoryH9.lower = false := by decide +kernel
  have s9 : lowerHistoryH9.strict = false := by decide +kernel
  have l18 : lowerH5H18.lower = false := by decide +kernel
  have s18 : lowerH5H18.strict = false := by decide +kernel
  unfold lowerHistoryAtBase lowerHistoryConditions
  rw [dp12_r1, dp12_r2, dp12_sc]
  intro b hb
  simp only [dp12Case, lowerH5ExpectedCuts, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · unfold certBoundHolds; rw [if_pos l7, if_neg (by simp [s7])]
    push_cast at b7 c7' ⊢
    linarith [b7.2]
  · unfold certBoundHolds; rw [if_neg (by simp [l9]), if_neg (by simp [s9])]
    push_cast at b9 c9' ⊢
    linarith [b9.1]
  · unfold certBoundHolds; rw [if_neg (by simp [l18]), if_neg (by simp [s18])]
    push_cast at b18 c18' ⊢
    linarith [b18.1]

lemma dp12_immediate : lowerH5Immediate dp12H 1 dp12Case := by
  refine ⟨0, rfl, ?_⟩
  show lowerHistoryContextFits (lowerNormalize dp12h0) dp12Case.context ∧
    dp12h1 = lowerHistoryAppend (lowerNormalize dp12h0) dp12Case.words ∧
    lowerNormalize dp12h1 = lowerHistoryOrient dp12h1 dp12Case.reflect ∧
    lowerHistoryAtBase (lowerNormalize dp12h0) dp12Case.oldCuts
  have n0 : lowerNormalize dp12h0 = ([3,1,2,1,2],[3,1,3,1,2]) := dp12_norm0
  have n1 : lowerNormalize dp12h1 = ([3,1,3,1,2],[3,1,2,1,2,2]) := dp12_norm1
  rw [n0, n1]
  refine ⟨?_, rfl, rfl, dp12_cuts⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, rfl⟩ <;>
    simp (config := {decide := true}) [dp12Case, dp12_ends_iff]

/-! ## The disproof -/

open Freiman in
theorem solution : ¬ (∀ (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (c : LowerH5Case) (hshape : lowerH5CaseShape c) (hc : lowerH5Immediate h n c)
    (he : lowerH5Exceptional c), ∃ m : ℕ, LowerH5PriorityEvent t h n m) := by
  intro H
  obtain ⟨m, hm⟩ := H _ dp12H 1 dp12_history dp12Case dp12_shape dp12_immediate dp12_exc
  have hm0 : m = 0 := by have := hm.next; omega
  subst hm0
  exact dp12_notR hm.branch.2.2.2.2.1
