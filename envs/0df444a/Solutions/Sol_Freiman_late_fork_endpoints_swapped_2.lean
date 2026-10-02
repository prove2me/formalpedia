-- Prove2me | solution 2 for Freiman.late_fork_endpoints_swapped
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:07:39.265199+00:00
-- url     : https://prove2.me/submissions/d97db8d8-d9bf-4ced-ad55-1d11875c3a14

import Mathlib
import Definitions.Def_Freiman_lateGeometry

set_option autoImplicit false

open Freiman in
theorem d340_pe_append (w : List ℕ+) (a : ℕ+) (x : ℝ) :
    prefixEval (w ++ [a]) x = prefixEval w (1 / (((a:ℕ):ℝ) + x)) := by
  induction w with
  | nil => simp [prefixEval]
  | cons b w ih => simp [prefixEval, ih]

open Freiman in
theorem d340_cd_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

open Freiman in
theorem d340_cd_bound (w : List ℕ+) : 0 < (lowerCD w).2 ∧ (lowerCD w).1 ≤ (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => simp [lowerCD]
  | append_singleton w a ih =>
    rw [d340_cd_append]
    have ha : 1 ≤ (a:ℕ) := a.pos
    constructor <;> nlinarith [ih.1, ih.2]

open Freiman in
theorem d340_pe_diff (w : List ℕ+) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    |prefixEval w x - prefixEval w y| *
      ((((lowerCD w).2 : ℝ) + x * (lowerCD w).1) * (((lowerCD w).2 : ℝ) + y * (lowerCD w).1))
      = |x - y| := by
  induction w using List.reverseRecOn with
  | nil => intro x y _ _; simp [prefixEval, lowerCD]
  | append_singleton w a ih =>
    intro x y hx hy
    rw [d340_pe_append, d340_pe_append, d340_cd_append]
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hb := d340_cd_bound w
    have hQ : (0:ℝ) < ((lowerCD w).2 : ℝ) := by exact_mod_cast hb.1
    have hQ' : (0:ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
    set Q : ℝ := ((lowerCD w).2 : ℝ) with hQdef
    set Q' : ℝ := ((lowerCD w).1 : ℝ) with hQ'def
    set A : ℝ := ((a:ℕ):ℝ) with hA
    have hax : 0 < A + x := by linarith
    have hay : 0 < A + y := by linarith
    have hx' : 0 ≤ 1 / (A + x) := by positivity
    have hy' : 0 ≤ 1 / (A + y) := by positivity
    have h := ih _ _ hx' hy'
    push_cast
    have e1 : Q' + A * Q + x * Q = (A + x) * (Q + 1 / (A + x) * Q') := by
      field_simp; ring
    have e2 : Q' + A * Q + y * Q = (A + y) * (Q + 1 / (A + y) * Q') := by
      field_simp; ring
    have e3 : 1 / (A + x) - 1 / (A + y) = (y - x) / ((A + x) * (A + y)) := by
      field_simp; ring
    rw [e1, e2]
    rw [e3, abs_div, abs_of_pos (by positivity : (0:ℝ) < (A + x) * (A + y)), abs_sub_comm y x] at h
    have hne : (A + x) * (A + y) ≠ 0 := by positivity
    calc |prefixEval w (1 / (A + x)) - prefixEval w (1 / (A + y))| *
          ((A + x) * (Q + 1 / (A + x) * Q') * ((A + y) * (Q + 1 / (A + y) * Q')))
        = (|prefixEval w (1 / (A + x)) - prefixEval w (1 / (A + y))| *
          ((Q + 1 / (A + x) * Q') * (Q + 1 / (A + y) * Q'))) * ((A + x) * (A + y)) := by ring
      _ = |x - y| := by rw [h]; field_simp

open Freiman in
theorem d340_sqrt21 : (3:ℝ) < Real.sqrt 21 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

open Freiman in
theorem d340_width (w : List ℕ+) :
    lowerWidth w * ((((lowerCD w).2 : ℝ) + lowerBeta * (lowerCD w).1) *
      (((lowerCD w).2 : ℝ) + lowerAlpha * (lowerCD w).1)) = lowerBeta - lowerAlpha := by
  have h3 := d340_sqrt21
  have hb : 0 ≤ lowerBeta := by unfold lowerBeta; linarith
  have ha : 0 ≤ lowerAlpha := by unfold lowerAlpha; linarith
  have hab : lowerAlpha ≤ lowerBeta := by unfold lowerAlpha lowerBeta; linarith
  unfold lowerWidth
  rw [d340_pe_diff w _ _ hb ha, abs_of_nonneg (by linarith)]

open Freiman in
theorem d340_tie (X Y : List ℕ+) (h : lowerWidth X = lowerWidth Y) :
    2 * ((lowerCD X).2 : ℤ) + (lowerCD X).1 = 2 * (lowerCD Y).2 + (lowerCD Y).1 ∧
    (((lowerCD X).2 : ℤ) - 2 * (lowerCD X).1 = (lowerCD Y).2 - 2 * (lowerCD Y).1 ∨
     ((lowerCD X).2 : ℤ) - 2 * (lowerCD X).1 = -(((lowerCD Y).2 : ℤ) - 2 * (lowerCD Y).1)) := by
  have h3 := d340_sqrt21
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hX := d340_width X
  have hY := d340_width Y
  have hbX := d340_cd_bound X
  have hbY := d340_cd_bound Y
  set a : ℕ := (lowerCD X).1
  set b : ℕ := (lowerCD X).2
  set c : ℕ := (lowerCD Y).1
  set d : ℕ := (lowerCD Y).2
  have hαpos : 0 < lowerAlpha := by unfold lowerAlpha; linarith
  have hβ : lowerBeta = 3 * lowerAlpha := by unfold lowerBeta lowerAlpha; ring
  have hα2 : 3 * lowerAlpha ^ 2 = 1 - 3 * lowerAlpha := by
    unfold lowerAlpha; nlinarith [hs]
  have hWpos : lowerWidth X ≠ 0 := by
    intro h0; rw [h0, zero_mul, hβ] at hX; linarith
  rw [h] at hX
  have hP : ((b:ℝ) + lowerBeta * a) * ((b:ℝ) + lowerAlpha * a) =
      ((d:ℝ) + lowerBeta * c) * ((d:ℝ) + lowerAlpha * c) := by
    have := hX.trans hY.symm
    rw [h] at hWpos
    exact mul_left_cancel₀ hWpos this
  rw [hβ] at hP
  -- expand: (b + 3αa)(b + αa) = b² + a² + α(4ab - 3a²)
  set m : ℤ := (b:ℤ)^2 + (a:ℤ)^2 - (d:ℤ)^2 - (c:ℤ)^2 with hm
  set n : ℤ := 4*(a:ℤ)*b - 3*(a:ℤ)^2 - 4*(c:ℤ)*d + 3*(c:ℤ)^2 with hn
  have hmn : (m:ℝ) + lowerAlpha * (n:ℝ) = 0 := by
    rw [hm, hn]; push_cast
    have e1 : ((b:ℝ) + 3 * lowerAlpha * a) * ((b:ℝ) + lowerAlpha * a) =
        (b:ℝ)^2 + (a:ℝ)^2 + lowerAlpha * (4*a*b - 3*a^2) := by
      have : ((b:ℝ) + 3 * lowerAlpha * a) * ((b:ℝ) + lowerAlpha * a) =
        (b:ℝ)^2 + 4 * lowerAlpha * a * b + (3 * lowerAlpha^2) * a^2 := by ring
      rw [this, hα2]; ring
    have e2 : ((d:ℝ) + 3 * lowerAlpha * c) * ((d:ℝ) + lowerAlpha * c) =
        (d:ℝ)^2 + (c:ℝ)^2 + lowerAlpha * (4*c*d - 3*c^2) := by
      have : ((d:ℝ) + 3 * lowerAlpha * c) * ((d:ℝ) + lowerAlpha * c) =
        (d:ℝ)^2 + 4 * lowerAlpha * c * d + (3 * lowerAlpha^2) * c^2 := by ring
      rw [this, hα2]; ring
    rw [e1, e2] at hP
    linarith
  have hirr : Irrational (Real.sqrt 21) := by
    have h21 : ¬ IsSquare (21:ℕ) := by
      rintro ⟨r, hr⟩
      have hr5 : r ≤ 5 := by nlinarith
      interval_cases r <;> omega
    have := (irrational_sqrt_natCast_iff (n := 21)).mpr h21
    simpa using this
  have hn0 : n = 0 := by
    by_contra hne
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hne
    apply (irrational_iff_ne_rational _).mp hirr (3 * n - 6 * m) n hne
    have hα : lowerAlpha = -(m:ℝ) / n := by field_simp; linarith
    have : Real.sqrt 21 = 6 * lowerAlpha + 3 := by unfold lowerAlpha; ring
    rw [this, hα]; push_cast; field_simp; ring
  have hm0 : m = 0 := by
    rw [hn0] at hmn; push_cast at hmn; exact_mod_cast (by linarith : (m:ℝ) = 0)
  have E1 : (2 * (b:ℤ) + a) ^ 2 = (2 * (d:ℤ) + c) ^ 2 := by
    have := hm0; have := hn0; rw [hm] at *; rw [hn] at *; nlinarith
  have E2 : ((b:ℤ) - 2 * a) ^ 2 = ((d:ℤ) - 2 * c) ^ 2 := by
    have := hm0; have := hn0; rw [hm] at *; rw [hn] at *; nlinarith
  refine ⟨?_, sq_eq_sq_iff_eq_or_eq_neg.mp E2⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp E1 with h1 | h1
  · exact h1
  · omega

open Freiman in
theorem d340_eqw_swap (p : LowerPair) (u : Bool) (h : lowerWidth p.1 ≠ lowerWidth p.2) :
    lowerEqualWords (p.2, p.1) u = (lowerEqualWords p u).swap := by
  have hN : lowerNormalize (p.2, p.1) = lowerNormalize p := by
    unfold lowerNormalize
    rcases lt_or_gt_of_ne h with h' | h'
    · simp [not_le.mpr h', h'.le]
    · simp [not_le.mpr h', h'.le]
  unfold lowerEqualWords
  simp only [hN]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [not_le.mpr h', h'.le]
  · simp [not_le.mpr h', h'.le]

open Freiman in
theorem d340_ew_swap (p : LowerPair) (u : Bool)
    (h0 : lowerWidth p.1 ≠ lowerWidth p.2)
    (h1 : lowerWidth (p.1 ++ [1]) ≠ lowerWidth p.2)
    (h2 : lowerWidth p.1 ≠ lowerWidth (p.2 ++ [1])) :
    lowerEndpointWords (p.2, p.1) u = (lowerEndpointWords p u).swap := by
  unfold lowerEndpointWords
  by_cases hpar : p.1.length % 2 = p.2.length % 2
  · simp only [hpar, if_true]
    exact d340_eqw_swap p u h0
  · have hpar' : ¬ p.2.length % 2 = p.1.length % 2 := fun h => hpar h.symm
    simp only [hpar, hpar', if_false]
    rcases lt_or_gt_of_ne h0 with h' | h'
    · simp only [not_le.mpr h', h'.le, if_true, if_false]
      split_ifs with hu
      · have := d340_eqw_swap (p.1, p.2 ++ [1]) u h2
        simpa using this
      · simp [lowerNaturalWords]
    · simp only [not_le.mpr h', h'.le, if_true, if_false]
      split_ifs with hu
      · have := d340_eqw_swap (p.1 ++ [1], p.2) u h1
        simpa using this
      · simp [lowerNaturalWords]

open Freiman in
theorem d340_endpoint_swap (p : LowerPair) (u : Bool)
    (h0 : lowerWidth p.1 ≠ lowerWidth p.2)
    (h1 : lowerWidth (p.1 ++ [1]) ≠ lowerWidth p.2)
    (h2 : lowerWidth p.1 ≠ lowerWidth (p.2 ++ [1])) :
    lowerEndpoint (p.2, p.1) u = lowerEndpoint p u := by
  unfold lowerEndpoint
  rw [d340_ew_swap p u h0 h1 h2]
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

def d340_F (s : List ℕ+) (z : ℕ × ℕ) : ℕ × ℕ :=
  s.foldl (fun z (a : ℕ+) => (z.2, z.1 + (a:ℕ) * z.2)) z

open Freiman in
theorem d340_cd_split (w s : List ℕ+) : lowerCD (w ++ s) = d340_F s (lowerCD w) := by
  induction s using List.reverseRecOn with
  | nil => simp [d340_F]
  | append_singleton s a ih =>
    rw [← List.append_assoc, d340_cd_append, ih]
    simp [d340_F, List.foldl_append]

open Freiman in
theorem d340_notie (w₁ w₂ s t : List ℕ+)
    (H : ∀ a b c d X1 X2 Y1 Y2 : ℕ, 0 < b → a ≤ b → 0 < d → c ≤ d →
      d340_F s (a, b) = (X1, X2) → d340_F t (c, d) = (Y1, Y2) →
      2 * (X2:ℤ) + X1 = 2 * Y2 + Y1 →
      ((X2:ℤ) - 2 * X1 = Y2 - 2 * Y1 ∨ (X2:ℤ) - 2 * X1 = -((Y2:ℤ) - 2 * Y1)) → False) :
    lowerWidth (w₁ ++ s) ≠ lowerWidth (w₂ ++ t) := by
  intro h
  obtain ⟨e1, e2⟩ := d340_tie _ _ h
  rw [d340_cd_split, d340_cd_split] at e1 e2
  obtain ⟨hb1, hb2⟩ := d340_cd_bound w₁
  obtain ⟨hd1, hd2⟩ := d340_cd_bound w₂
  exact H _ _ _ _ _ _ _ _ hb1 hb2 hd1 hd2 rfl rfl e1 e2

open Freiman in
theorem d340_labels : ∀ l ∈ lowerLateCandidates,
    (l.1.reverse, l.2 ++ [1]) ∈ lateEndpointData.toList.map LateEndpoint.words →
    l = ([2,1,3],[1,2,2]) ∨ l = ([1,1,3],[1,1,1,1]) ∨ l = ([2,3],[1,1,1,1]) ∨
    l = ([3,3],[1,1,1,1]) ∨ l = ([3,3],[1,1,1,2]) ∨ l = ([1,1,3],[1,2,1]) := by
  decide +kernel

open Freiman in
theorem d340_ep_mem (i : ℕ) (hi : lateIndex i lateCatalog.endpoints.size) :
    (lateEndpoint lateCatalog i).words ∈ lateEndpointData.toList.map LateEndpoint.words := by
  obtain ⟨h1, h2⟩ := hi
  have hlt : i - 1 < lateCatalog.endpoints.size := by omega
  unfold lateEndpoint
  rw [Array.getElem?_eq_getElem hlt]
  simp only [Option.getD_some]
  apply List.mem_map_of_mem
  exact Array.getElem_mem_toList hlt

open Freiman in
theorem d340_child (p : LowerPair) (l : LowerLabel) :
    lowerChild p l = ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) := rfl

open Freiman in
theorem d340_notie' (w₁ w₂ s t : List ℕ+)
    (H : ∀ a b c d : ℤ, 0 ≤ a → 0 < b → a ≤ b → 0 ≤ c → 0 < d → c ≤ d →
      2 * ((d340_F s (a.toNat, b.toNat)).2 : ℤ) + (d340_F s (a.toNat, b.toNat)).1 =
        2 * ((d340_F t (c.toNat, d.toNat)).2 : ℤ) + (d340_F t (c.toNat, d.toNat)).1 →
      (((d340_F s (a.toNat, b.toNat)).2 : ℤ) - 2 * (d340_F s (a.toNat, b.toNat)).1 =
          ((d340_F t (c.toNat, d.toNat)).2 : ℤ) - 2 * (d340_F t (c.toNat, d.toNat)).1 ∨
        ((d340_F s (a.toNat, b.toNat)).2 : ℤ) - 2 * (d340_F s (a.toNat, b.toNat)).1 =
          -(((d340_F t (c.toNat, d.toNat)).2 : ℤ) - 2 * (d340_F t (c.toNat, d.toNat)).1)) → False) :
    lowerWidth (w₁ ++ s) ≠ lowerWidth (w₂ ++ t) := by
  apply d340_notie
  intro a b c d X1 X2 Y1 Y2 hb hab hd hcd hX hY e1 e2
  have := H a b c d (by positivity) (by exact_mod_cast hb) (by exact_mod_cast hab) (by positivity)
    (by exact_mod_cast hd) (by exact_mod_cast hcd)
  simp only [Int.toNat_natCast, hX, hY] at this
  exact this e1 e2

open Freiman in
theorem d340_cases (q0 q2 : List ℕ+) (l : LowerLabel) (d : ℕ+)
    (hsix : l = ([2,1,3],[1,2,2]) ∨ l = ([1,1,3],[1,1,1,1]) ∨ l = ([2,3],[1,1,1,1]) ∨
      l = ([3,3],[1,1,1,1]) ∨ l = ([3,3],[1,1,1,2]) ∨ l = ([1,1,3],[1,2,1]))
    (hd : d = 1 ∨ d = 2) :
    lowerWidth (q0 ++ [3, 1] ++ l.1.reverse) ≠ lowerWidth (q2 ++ (l.2 ++ [d])) ∧
    lowerWidth (q0 ++ [3, 1] ++ l.1.reverse ++ [1]) ≠ lowerWidth (q2 ++ (l.2 ++ [d])) ∧
    lowerWidth (q0 ++ [3, 1] ++ l.1.reverse) ≠ lowerWidth (q2 ++ (l.2 ++ [d]) ++ [1]) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  rcases hsix with h | h | h | h | h | h <;> subst h <;> rcases hd with rfl | rfl <;>
  simp only [List.reverse_cons, List.reverse_nil, List.append_assoc, List.cons_append,
    List.nil_append] <;>
  apply d340_notie' <;>
  intro a b c d ha hb hab hc hd hcd e1 e2 <;>
  simp only [d340_F, List.foldl_cons, List.foldl_nil, PNat.val_ofNat] at e1 e2 <;>
  push_cast [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb.le, Int.toNat_of_nonneg hc,
    Int.toNat_of_nonneg hd.le] at e1 e2 <;>
  rcases e2 with e2 | e2 <;> linarith

open Freiman in
theorem solution (p : LowerPair) (path : LatePath) (hm : lateMatches p path.right3) (hv : latePathValid lateCatalog path) (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) (n : LateNormalization) (hmem : n ∈ path.normalizations) (d : ℕ+) (hd : d ∈ ([1, 2] : List ℕ+)) (upper : Bool) (hw : n.wide = true) : lowerEndpoint (lowerChild (lowerChild p n.label) ([d], [])) upper = lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d)) upper := by
  obtain ⟨_, _, _, _, _, hcand, _, _, hnorm, _, hchk, hcv, _⟩ := hv
  have hlab : n.label ∈ lowerLateCandidates := by
    apply hcand
    have : n.label ∈ path.normalizations.map LateNormalization.label := List.mem_map_of_mem hmem
    rw [hnorm] at this
    exact List.mem_of_mem_tail (List.dropLast_subset _ this)
  have hfw : ∀ e : ℕ+, lateForkWords n e = (n.label.1.reverse, n.label.2 ++ [e]) := by
    intro e; simp [lateForkWords, lateWords, lowerHistorySet, lowerHistoryPick, hw]
  have hend : (n.label.1.reverse, n.label.2 ++ [1]) ∈
      lateEndpointData.toList.map LateEndpoint.words := by
    have hs : (lateForkWords n 1, true, lateForkWords n 2, false, true) ∈ lateExpectedSpecs path := by
      unfold lateExpectedSpecs
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨n, hmem, by simp⟩
    rw [← hchk] at hs
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp hs
    have hv' := hcv c hc
    have := d340_ep_mem c.a hv'.1
    unfold lateCheckSpec at hce
    simp only [Prod.mk.injEq] at hce
    rw [hce.1, hfw] at this
    exact this
  have hsix := d340_labels n.label hlab hend
  have hnn := hn n hmem
  unfold lateNormalizationHolds at hnn
  simp only [hw, if_true] at hnn
  obtain ⟨q0, hq0⟩ : ∃ q0, (lowerNormalize p).1 = q0 ++ [3,1] := by
    obtain ⟨_, hL, _⟩ := hm
    obtain ⟨q0, h⟩ := hL
    exact ⟨q0, h.symm⟩
  have hL : lowerChild (lowerChild p n.label) ([d], []) =
      ((lowerNormalize p).2 ++ (n.label.2 ++ [d]), (lowerNormalize p).1 ++ n.label.1.reverse) := by
    rw [d340_child (lowerChild p n.label), hnn, d340_child]
    simp
  have hR : lowerHistoryAppend (lowerNormalize p) (lateForkWords n d) =
      ((lowerNormalize p).1 ++ n.label.1.reverse, (lowerNormalize p).2 ++ (n.label.2 ++ [d])) := by
    rw [hfw]; rfl
  rw [hL, hR, hq0]
  generalize (lowerNormalize p).2 = q2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  obtain ⟨c1, c2, c3⟩ := d340_cases q0 q2 n.label d hsix hd
  exact d340_endpoint_swap (q0 ++ [3, 1] ++ n.label.1.reverse, q2 ++ (n.label.2 ++ [d])) upper
    c1 c2 c3
