-- Prove2me | solution 1 for ComputableDistributionsWaveMission.test_modules
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T17:28:11.081117+00:00
-- url     : https://prove2.me/submissions/74e24bf7-ce48-4cd5-83df-fed5944ef8f1

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_MissionTargets
import Mathlib

set_option autoImplicit true

/-! Compactly supported smooth tests on rational coordinates.

Every represented real is read through its real value (the supremum of its
lower endpoints). This turns equivalence, order, the `Small` estimate, limits
and bracket derivatives into statements about real numbers. Tests are then
built from real data: a test module in every dimension from pointwise sums and
scalings, and product bumps from Mathlib's `ContDiffBump`. -/

open ComputableAnalysis (RealCompute QInterval QPoint RationalBox)
open Filter Topology
open scoped ContDiff

namespace TMSol

noncomputable def val (x : RealCompute) : ℝ :=
  sSup (Set.range fun n => ((x.compute n).lo : ℝ))

theorem lo_le_hi {x : RealCompute} (hx : x.Valid) (n m : ℕ) :
    (x.compute n).lo ≤ (x.compute m).hi := by
  have h1 := hx.2.1 n (max n m) (le_max_left _ _)
  have h2 := hx.2.1 m (max n m) (le_max_right _ _)
  exact le_trans h1.1 (le_trans h1.2.1 h2.2.2)

theorem lo_le_val {x : RealCompute} (hx : x.Valid) (n : ℕ) : ((x.compute n).lo : ℝ) ≤ val x :=
  le_csSup ⟨((x.compute 0).hi : ℝ), by rintro _ ⟨m, rfl⟩; dsimp only; exact_mod_cast lo_le_hi hx m 0⟩ ⟨n, rfl⟩

theorem val_le_hi {x : RealCompute} (hx : x.Valid) (n : ℕ) : val x ≤ ((x.compute n).hi : ℝ) :=
  csSup_le ⟨_, ⟨0, rfl⟩⟩ (by rintro _ ⟨m, rfl⟩; dsimp only; exact_mod_cast lo_le_hi hx m n)

theorem width_small {x : RealCompute} (hx : x.Valid) (q : ℚ) (hq : 0 < q) :
    ∃ N, ∀ n, N ≤ n → ((x.compute n).hi : ℝ) - (x.compute n).lo ≤ q := by
  obtain ⟨N, hN⟩ := hx.2.2 ⟨q, hq⟩
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [QInterval.width] at this
  exact_mod_cast (by linarith : (x.compute n).hi - (x.compute n).lo ≤ q)

theorem eq_of_forall_rat {a b : ℝ} (h : ∀ q : ℚ, 0 < q → |a - b| ≤ q) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn hpos
  have := h q (by exact_mod_cast hq0)
  linarith

theorem le_of_forall_rat {a b : ℝ} (h : ∀ q : ℚ, 0 < q → a ≤ b + q) : a ≤ b := by
  by_contra hne
  push Not at hne
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (sub_pos.mpr hne)
  have := h q (by exact_mod_cast hq0)
  linarith

theorem val_unique {x : RealCompute} (hx : x.Valid) {y : ℝ}
    (h : ∀ n, ((x.compute n).lo : ℝ) ≤ y ∧ y ≤ (x.compute n).hi) : val x = y := by
  apply eq_of_forall_rat
  intro q hq
  obtain ⟨N, hN⟩ := width_small hx q hq
  have hw := hN N le_rfl
  have := lo_le_val hx N
  have := val_le_hi hx N
  have := h N
  rw [abs_le]; constructor <;> linarith

theorem equiv_iff {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y ↔ val x = val y := by
  constructor
  · intro h
    apply eq_of_forall_rat
    intro q hq
    obtain ⟨N1, h1⟩ := width_small hx (q / 2) (by positivity)
    obtain ⟨N2, h2⟩ := width_small hy (q / 2) (by positivity)
    have ho := (RealCompute.compareAt_overlap_iff x y (max N1 N2) (max N1 N2)).1 (h (max N1 N2))
    obtain ⟨o1, o2⟩ := ho
    have o1' : (((x.compute (max N1 N2)).lo : ℚ) : ℝ) ≤ (y.compute (max N1 N2)).hi := by exact_mod_cast o1
    have o2' : (((y.compute (max N1 N2)).lo : ℚ) : ℝ) ≤ (x.compute (max N1 N2)).hi := by exact_mod_cast o2
    have w1 := h1 (max N1 N2) (le_max_left N1 N2)
    have w2 := h2 (max N1 N2) (le_max_right N1 N2)
    have := lo_le_val hx (max N1 N2); have := val_le_hi hx (max N1 N2)
    have := lo_le_val hy (max N1 N2); have := val_le_hi hy (max N1 N2)
    push_cast at w1 w2
    rw [abs_le]; constructor <;> linarith
  · intro h n
    apply (RealCompute.compareAt_overlap_iff x y n n).2
    constructor
    · have := lo_le_val hx n; have := val_le_hi hy n
      exact_mod_cast (by linarith : ((x.compute n).lo : ℝ) ≤ (y.compute n).hi)
    · have := lo_le_val hy n; have := val_le_hi hx n
      exact_mod_cast (by linarith : ((y.compute n).lo : ℝ) ≤ (x.compute n).hi)

theorem le_iff {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    x.Le y ↔ val x ≤ val y := by
  constructor
  · intro h
    apply le_of_forall_rat
    intro q hq
    obtain ⟨N, hN⟩ := width_small hy q hq
    have h1 : val x ≤ (y.compute N).hi :=
      csSup_le ⟨_, ⟨0, rfl⟩⟩ (by rintro _ ⟨m, rfl⟩; dsimp only; exact_mod_cast h m N)
    have := hN N le_rfl
    have := lo_le_val hy N
    linarith
  · intro h n m
    have := lo_le_val hx n; have := val_le_hi hy m
    exact_mod_cast (by linarith : ((x.compute n).lo : ℝ) ≤ (y.compute m).hi)

theorem ofRat_valid' (q : ℚ) : (RealCompute.ofRat q).Valid := RealCompute.ofRat_valid q

theorem val_ofRat (q : ℚ) : val (RealCompute.ofRat q) = q :=
  val_unique (ofRat_valid' q) (fun n => by simp)

theorem add_valid' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.add x y).Valid := RealCompute.add_valid hx hy

theorem sub_valid' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.sub x y).Valid := RealCompute.sub_valid hx hy

theorem mul_valid' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    (RealCompute.mul x y).Valid := RealCompute.mul_valid hx hy

theorem val_add {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.add x y) = val x + val y := by
  apply val_unique (add_valid' hx hy)
  intro n
  simp only [RealCompute.add, RealCompute.addCompute]
  push_cast
  have := lo_le_val hx n; have := val_le_hi hx n
  have := lo_le_val hy n; have := val_le_hi hy n
  constructor <;> linarith

theorem val_sub {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.sub x y) = val x - val y := by
  apply val_unique (sub_valid' hx hy)
  intro n
  simp only [RealCompute.sub, RealCompute.subCompute]
  push_cast
  have := lo_le_val hx n; have := val_le_hi hx n
  have := lo_le_val hy n; have := val_le_hi hy n
  constructor <;> linarith

theorem val_scaleRat (r : ℚ) {x : RealCompute} (hx : x.Valid) :
    val (RealCompute.scaleRat r x) = r * val x := by
  apply val_unique (RealCompute.scaleRat_valid hx)
  intro n
  have h1 := lo_le_val hx n; have h2 := val_le_hi hx n
  simp only [RealCompute.scaleRat, RealCompute.scaleRatCompute]
  by_cases hr : 0 ≤ r
  · simp only [hr, if_true]
    have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 hr', mul_le_mul_of_nonneg_left h2 hr'⟩
  · simp only [hr, if_false]
    have hr' : (r : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hr))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 hr', mul_le_mul_of_nonpos_left h1 hr'⟩

theorem minRat_le (a b : ℚ) : ComputableAnalysis.minRat a b ≤ a ∧ ComputableAnalysis.minRat a b ≤ b := by
  unfold ComputableAnalysis.minRat; split_ifs with h <;> constructor <;> linarith

theorem le_maxRat (a b : ℚ) : a ≤ ComputableAnalysis.maxRat2 a b ∧ b ≤ ComputableAnalysis.maxRat2 a b := by
  unfold ComputableAnalysis.maxRat2; split_ifs with h <;> constructor <;> linarith

theorem min4_le (a b c d : ℚ) : ComputableAnalysis.min4 a b c d ≤ a ∧ ComputableAnalysis.min4 a b c d ≤ b ∧
    ComputableAnalysis.min4 a b c d ≤ c ∧ ComputableAnalysis.min4 a b c d ≤ d := by
  unfold ComputableAnalysis.min4
  have h1 := minRat_le a b; have h2 := minRat_le c d
  have h3 := minRat_le (ComputableAnalysis.minRat a b) (ComputableAnalysis.minRat c d)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem le_max4 (a b c d : ℚ) : a ≤ ComputableAnalysis.max4 a b c d ∧ b ≤ ComputableAnalysis.max4 a b c d ∧
    c ≤ ComputableAnalysis.max4 a b c d ∧ d ≤ ComputableAnalysis.max4 a b c d := by
  unfold ComputableAnalysis.max4
  have h1 := le_maxRat a b; have h2 := le_maxRat c d
  have h3 := le_maxRat (ComputableAnalysis.maxRat2 a b) (ComputableAnalysis.maxRat2 c d)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mul_lower {a1 a2 b1 b2 a b m : ℝ} (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (hb1 : b1 ≤ b) (hb2 : b ≤ b2)
    (h11 : m ≤ a1 * b1) (h12 : m ≤ a1 * b2) (h21 : m ≤ a2 * b1) (h22 : m ≤ a2 * b2) : m ≤ a * b := by
  have key : ∀ c, m ≤ c * b1 → m ≤ c * b2 → m ≤ c * b := by
    intro c hc1 hc2
    rcases le_total 0 c with hc | hc
    · exact le_trans hc1 (mul_le_mul_of_nonneg_left hb1 hc)
    · exact le_trans hc2 (mul_le_mul_of_nonpos_left hb2 hc)
  rcases le_total 0 b with hb | hb
  · exact le_trans (key a1 h11 h12) (mul_le_mul_of_nonneg_right ha1 hb)
  · exact le_trans (key a2 h21 h22) (mul_le_mul_of_nonpos_right ha2 hb)

theorem mul_upper {a1 a2 b1 b2 a b M : ℝ} (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (hb1 : b1 ≤ b) (hb2 : b ≤ b2)
    (h11 : a1 * b1 ≤ M) (h12 : a1 * b2 ≤ M) (h21 : a2 * b1 ≤ M) (h22 : a2 * b2 ≤ M) : a * b ≤ M := by
  have h := mul_lower (b := -b) (m := -M) ha1 ha2 (neg_le_neg hb2) (neg_le_neg hb1)
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem val_mul {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.mul x y) = val x * val y := by
  apply val_unique (mul_valid' hx hy)
  intro n
  simp only [RealCompute.mul, RealCompute.mulCompute, ComputableAnalysis.QBox.mulRealInterval]
  have h1 := lo_le_val hx n; have h2 := val_le_hi hx n
  have h3 := lo_le_val hy n; have h4 := val_le_hi hy n
  obtain ⟨m1, m2, m3, m4⟩ := min4_le ((x.compute n).lo * (y.compute n).lo) ((x.compute n).lo * (y.compute n).hi)
    ((x.compute n).hi * (y.compute n).lo) ((x.compute n).hi * (y.compute n).hi)
  obtain ⟨M1, M2, M3, M4⟩ := le_max4 ((x.compute n).lo * (y.compute n).lo) ((x.compute n).lo * (y.compute n).hi)
    ((x.compute n).hi * (y.compute n).lo) ((x.compute n).hi * (y.compute n).hi)
  have m1' := (Rat.cast_le (K := ℝ)).2 m1; have m2' := (Rat.cast_le (K := ℝ)).2 m2
  have m3' := (Rat.cast_le (K := ℝ)).2 m3; have m4' := (Rat.cast_le (K := ℝ)).2 m4
  have M1' := (Rat.cast_le (K := ℝ)).2 M1; have M2' := (Rat.cast_le (K := ℝ)).2 M2
  have M3' := (Rat.cast_le (K := ℝ)).2 M3; have M4' := (Rat.cast_le (K := ℝ)).2 M4
  push_cast at m1' m2' m3' m4' M1' M2' M3' M4'
  exact ⟨mul_lower h1 h2 h3 h4 m1' m2' m3' m4', mul_upper h1 h2 h3 h4 M1' M2' M3' M4'⟩

theorem small_iff {a b : RealCompute} (ha : a.Valid) (hb : b.Valid) (B : ℚ) :
    ComputableAnalysis.RealApproximationOrder.Small
      (ComputableAnalysis.RealApproximationOrder.sub
        (ComputableAnalysis.RealApproximationOrder.parameter a ha)
        (ComputableAnalysis.RealApproximationOrder.parameter b hb)) B ↔ |val a - val b| ≤ B := by
  have hs : (RealCompute.sub a b).Valid := sub_valid' ha hb
  show (RealCompute.ofRat (-B)).Le (RealCompute.sub a b) ∧
    (RealCompute.sub a b).Le (RealCompute.ofRat B) ↔ _
  rw [le_iff (ofRat_valid' _) hs, le_iff hs (ofRat_valid' _), val_ofRat, val_ofRat, val_sub ha hb,
    abs_le]
  push_cast
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)

theorem inInterval_iff {y : RealCompute} (hy : y.Valid) (I : QInterval) :
    ComputableAnalysis.RawLimit.InInterval y I ↔ (I.lo : ℝ) ≤ val y ∧ val y ≤ I.hi := by
  unfold ComputableAnalysis.RawLimit.InInterval
  rw [le_iff (ofRat_valid' _) hy, le_iff hy (ofRat_valid' _), val_ofRat, val_ofRat]

theorem tendsTo_iff {u : ℕ → RealCompute} {x : RealCompute} (hu : ∀ n, (u n).Valid) (hx : x.Valid) :
    ComputableAnalysis.RawLimit.TendsTo u x ↔ Tendsto (fun n => val (u n)) atTop (𝓝 (val x)) := by
  constructor
  · rintro ⟨-, -, h⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    obtain ⟨m, hm⟩ := width_small hx q hq0'
    obtain ⟨N, hN⟩ := h m ⟨q, hq0'⟩
    refine ⟨N, fun n hn => ?_⟩
    have hi := (inInterval_iff (hu n) _).1 (hN n hn)
    simp only [QInterval.expand] at hi
    push_cast at hi
    have := hm m le_rfl
    have := lo_le_val hx m; have := val_le_hi hx m
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  · intro h
    refine ⟨hx, hu, fun m eps => ?_⟩
    have he : (0 : ℝ) < eps.val := by exact_mod_cast eps.property
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h _ he
    refine ⟨N, fun n hn => ?_⟩
    rw [inInterval_iff (hu n)]
    have := hN n hn
    rw [Real.dist_eq, abs_lt] at this
    have := lo_le_val hx m; have := val_le_hi hx m
    simp only [QInterval.expand]
    push_cast
    constructor <;> linarith

/-! A represented real with a prescribed real value. -/

noncomputable def ofReal (r : ℝ) : RealCompute where
  compute n := ⟨(⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n, ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n⟩

theorem ofReal_lo_lt_hi (r : ℝ) (n : ℕ) : ((ofReal r).compute n).lo < ((ofReal r).compute n).hi := by
  show (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n < ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n
  exact div_lt_div_of_pos_right (lt_add_one _) (by positivity)

theorem ofReal_valid (r : ℝ) : (ofReal r).Valid := by
  refine ⟨fun n => ?_, fun n m hnm => ?_, fun eps => ?_⟩
  · exact sub_nonneg.mpr (le_of_lt (ofReal_lo_lt_hi r n))
  · show (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ (⌊r * 2 ^ m⌋ : ℚ) / 2 ^ m ∧
      (⌊r * 2 ^ m⌋ : ℚ) / 2 ^ m ≤ ((⌊r * 2 ^ m⌋ : ℚ) + 1) / 2 ^ m ∧
      ((⌊r * 2 ^ m⌋ : ℚ) + 1) / 2 ^ m ≤ ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    set a := ⌊r * 2 ^ n⌋
    set b := ⌊r * 2 ^ (n + k)⌋
    have ha1 : (a : ℝ) ≤ r * 2 ^ n := Int.floor_le _
    have ha2 : r * 2 ^ n < a + 1 := Int.lt_floor_add_one _
    have hb1 : (b : ℝ) ≤ r * 2 ^ (n + k) := Int.floor_le _
    have hb2 : r * 2 ^ (n + k) < b + 1 := Int.lt_floor_add_one _
    have hk : (0 : ℝ) < 2 ^ k := by positivity
    have e : (2 : ℝ) ^ (n + k) = 2 ^ n * 2 ^ k := pow_add _ _ _
    have c1 : a * 2 ^ k ≤ b := by
      apply Int.le_floor.mpr
      push_cast
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right ha1 hk.le
    have c2 : b < (a + 1) * 2 ^ k := by
      apply Int.floor_lt.mpr
      push_cast
      rw [e, ← mul_assoc]
      exact mul_lt_mul_of_pos_right ha2 hk
    have c2' : b + 1 ≤ (a + 1) * 2 ^ k := c2
    have q1 : (a : ℚ) * 2 ^ k ≤ b := by exact_mod_cast c1
    have q2 : (b : ℚ) + 1 ≤ ((a : ℚ) + 1) * 2 ^ k := by exact_mod_cast c2'
    have eq : (2 : ℚ) ^ (n + k) = 2 ^ n * 2 ^ k := pow_add _ _ _
    have hn : (0 : ℚ) < 2 ^ n := by positivity
    have hk' : (0 : ℚ) < 2 ^ k := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [div_le_div_iff₀ hn (by positivity), eq]
      nlinarith
    · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [div_le_div_iff₀ (by positivity) hn, eq]
      nlinarith
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one eps.property (by norm_num : (1 / 2 : ℚ) < 1)
    refine ⟨N, fun n hn => ?_⟩
    show ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ eps.val
    rw [← sub_div, add_sub_cancel_left]
    have : (1 / 2 : ℚ) ^ n ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [one_div_pow, one_div_pow] at this
    have hN' : (1 : ℚ) / 2 ^ N < eps.val := by rw [← one_div_pow]; exact hN
    linarith

theorem val_ofReal (r : ℝ) : val (ofReal r) = r := by
  apply val_unique (ofReal_valid r)
  intro n
  show (((⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n : ℚ) : ℝ) ≤ r ∧ r ≤ ((((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n : ℚ) : ℝ)
  push_cast
  have h1 : (⌊r * 2 ^ n⌋ : ℝ) ≤ r * 2 ^ n := Int.floor_le _
  have h2 : r * 2 ^ n < ⌊r * 2 ^ n⌋ + 1 := Int.lt_floor_add_one _
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · rw [div_le_iff₀ hn]; exact h1
  · rw [le_div_iff₀ hn]; exact h2.le

/-! Derivatives along admissible brackets, read through real values. -/

def RDeriv (g : ℚ → ℝ) (q : ℚ) (d : ℝ) : Prop :=
  ∀ A : RealCompute, A.Valid → val A = q → (∀ n, (A.compute n).lo < (A.compute n).hi) →
    Tendsto (fun n => (g (A.compute n).hi - g (A.compute n).lo) /
      (((A.compute n).hi : ℝ) - (A.compute n).lo)) atTop (𝓝 d)

theorem val_secant {f : ℚ → RealCompute} (hf : ∀ r, (f r).Valid) (a b : ℚ) :
    val (ComputableAnalysis.BracketDerivative.secant f a b) = (val (f b) - val (f a)) / ((b : ℝ) - a) := by
  unfold ComputableAnalysis.BracketDerivative.secant
  change val (RealCompute.scaleRat (1 / (b - a)) (RealCompute.sub (f b) (f a))) = _
  rw [val_scaleRat _ (sub_valid' (hf b) (hf a)), val_sub (hf b) (hf a)]
  push_cast
  ring

theorem admissible_iff {q : ℚ} {A : RealCompute} :
    ComputableAnalysis.BracketDerivative.Admissible (fun _ => True) (RealCompute.ofRat q) A ↔
      A.Valid ∧ val A = q ∧ ∀ n, (A.compute n).lo < (A.compute n).hi := by
  constructor
  · rintro ⟨-, hA, he, hn⟩
    exact ⟨hA, by rw [(equiv_iff hA (ofRat_valid' q)).1 he, val_ofRat], fun n => (hn n).1⟩
  · rintro ⟨hA, he, hn⟩
    exact ⟨ofRat_valid' q, hA, (equiv_iff hA (ofRat_valid' q)).2 (by rw [he, val_ofRat]),
      fun n => ⟨hn n, fun _ _ _ => trivial⟩⟩

theorem hasDeriv_iff {f : ℚ → RealCompute} (hf : ∀ r, (f r).Valid) {q : ℚ} {d : RealCompute}
    (hd : d.Valid) :
    ComputableAnalysis.BracketDerivative.HasDerivativeAt (fun _ => True) f (RealCompute.ofRat q) d ↔
      RDeriv (fun r => val (f r)) q (val d) := by
  have key : ∀ A, ComputableAnalysis.BracketDerivative.Admissible (fun _ => True) (RealCompute.ofRat q) A →
      (ComputableAnalysis.RawLimit.HasParametrizedLimit
        (ComputableAnalysis.BracketDerivative.secants f A) d ↔
      Tendsto (fun n => (val (f (A.compute n).hi) - val (f (A.compute n).lo)) /
        (((A.compute n).hi : ℝ) - (A.compute n).lo)) atTop (𝓝 (val d))) := by
    intro A hA
    rw [ComputableAnalysis.RawLimit.parametrizedLimit_iff,
      tendsTo_iff (ComputableAnalysis.BracketDerivative.secants_valid (fun r _ => hf r) hA) hd]
    unfold ComputableAnalysis.BracketDerivative.secants
    simp only [val_secant hf]
  constructor
  · intro h A hA hv hn
    have hadm := admissible_iff.2 ⟨hA, hv, hn⟩
    exact (key A hadm).1 (h.2.2.2.2 A hadm)
  · intro h
    refine ⟨ofRat_valid' q, hd, fun r _ => hf r, ⟨ofReal q, admissible_iff.2
      ⟨ofReal_valid q, val_ofReal q, ofReal_lo_lt_hi q⟩⟩, fun A hA => ?_⟩
    obtain ⟨h1, h2, h3⟩ := admissible_iff.1 hA
    exact (key A hA).2 (h A h1 h2 h3)

/-! Test functions from real-valued derivative data. -/

open ComputableDistributions (TestFunction MultiIndex incrementIndex replaceCoordinate)

structure RData (n : ℕ) where
  G : MultiIndex n → QPoint n → ℝ
  box : RationalBox n
  vanish : ∀ α x, ¬ box.Contains x → G α x = 0
  L : MultiIndex n → ℚ
  L_nonneg : ∀ α, 0 ≤ L α
  lip : ∀ α (x y : QPoint n) (δ : ℚ), 0 ≤ δ → (∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) →
    |G α x - G α y| ≤ L α * δ
  deriv : ∀ α i (x : QPoint n),
    RDeriv (fun r => G α (replaceCoordinate x i r)) (x i) (G (incrementIndex α i) x)

noncomputable def RData.toTest {n : ℕ} (D : RData n) : TestFunction n where
  derivative α x := ofReal (D.G α x)
  derivative_valid α x := ofReal_valid _
  support := D.box
  derivative_vanishes_off_support α x hx := by
    rw [equiv_iff (ofReal_valid _) (ofRat_valid' 0), val_ofReal, val_ofRat, D.vanish α x hx]
    simp
  derivativeLipschitz := D.L
  derivativeLipschitz_nonneg := D.L_nonneg
  derivative_control α x y δ hδ hc := by
    rw [small_iff, val_ofReal, val_ofReal]
    push_cast
    exact D.lip α x y δ hδ hc
  partialDerivative α i x := by
    rw [hasDeriv_iff (fun r => ofReal_valid _) (ofReal_valid _)]
    simp only [val_ofReal]
    exact D.deriv α i x

@[simp] theorem RData.val_toTest {n : ℕ} (D : RData n) (α : MultiIndex n) (x : QPoint n) :
    val (D.toTest.derivative α x) = D.G α x := val_ofReal _

noncomputable def shadow {n : ℕ} (φ : TestFunction n) : RData n where
  G α x := val (φ.derivative α x)
  box := φ.support
  vanish α x hx := by
    rw [(equiv_iff (φ.derivative_valid α x) (ofRat_valid' 0)).1
      (φ.derivative_vanishes_off_support α x hx), val_ofRat]
    simp
  L := φ.derivativeLipschitz
  L_nonneg := φ.derivativeLipschitz_nonneg
  lip α x y δ hδ hc := by
    have := (small_iff _ _ _).1 (φ.derivative_control α x y δ hδ hc)
    push_cast at this
    exact this
  deriv α i x := (hasDeriv_iff (fun r => φ.derivative_valid _ _) (φ.derivative_valid _ _)).1
    (φ.partialDerivative α i x)

@[simp] theorem shadow_G {n : ℕ} (φ : TestFunction n) (α : MultiIndex n) (x : QPoint n) :
    (shadow φ).G α x = val (φ.derivative α x) := rfl

def zeroData (n : ℕ) : RData n where
  G _ _ := 0
  box := ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl⟩
  vanish _ _ _ := rfl
  L _ := 0
  L_nonneg _ := le_rfl
  lip _ _ _ _ _ _ := by simp
  deriv _ _ _ := by
    intro A _ _ _
    simp only [sub_self, zero_div]
    exact tendsto_const_nhds

@[simp] theorem zeroData_G (n : ℕ) (α : MultiIndex n) (x : QPoint n) : (zeroData n).G α x = 0 := rfl

def addData {n : ℕ} (D E : RData n) : RData n where
  G α x := D.G α x + E.G α x
  box := ⟨fun i => min (D.box.lower i) (E.box.lower i), fun i => max (D.box.upper i) (E.box.upper i),
    fun i => le_trans (min_le_left _ _) (le_trans (D.box.ordered i) (le_max_left _ _))⟩
  vanish α x hx := by
    have h1 : ¬ D.box.Contains x := fun h => hx fun i =>
      ⟨le_trans (min_le_left _ _) (h i).1, le_trans (h i).2 (le_max_left _ _)⟩
    have h2 : ¬ E.box.Contains x := fun h => hx fun i =>
      ⟨le_trans (min_le_right _ _) (h i).1, le_trans (h i).2 (le_max_right _ _)⟩
    simp [D.vanish α x h1, E.vanish α x h2]
  L α := D.L α + E.L α
  L_nonneg α := add_nonneg (D.L_nonneg α) (E.L_nonneg α)
  lip α x y δ hδ hc := by
    have h1 := D.lip α x y δ hδ hc
    have h2 := E.lip α x y δ hδ hc
    calc |D.G α x + E.G α x - (D.G α y + E.G α y)|
        = |(D.G α x - D.G α y) + (E.G α x - E.G α y)| := by ring_nf
      _ ≤ |D.G α x - D.G α y| + |E.G α x - E.G α y| := abs_add_le _ _
      _ ≤ _ := by push_cast; linarith
  deriv α i x := by
    intro A h1 h2 h3
    refine ((D.deriv α i x A h1 h2 h3).add (E.deriv α i x A h1 h2 h3)).congr (fun k => ?_)
    ring

@[simp] theorem addData_G {n : ℕ} (D E : RData n) (α : MultiIndex n) (x : QPoint n) :
    (addData D E).G α x = D.G α x + E.G α x := rfl

noncomputable def scaleData {n : ℕ} (c : ℝ) (D : RData n) : RData n where
  G α x := c * D.G α x
  box := D.box
  vanish α x hx := by simp [D.vanish α x hx]
  L α := (⌈|c|⌉₊ : ℚ) * D.L α
  L_nonneg α := mul_nonneg (Nat.cast_nonneg _) (D.L_nonneg α)
  lip α x y δ hδ hc := by
    have h1 := D.lip α x y δ hδ hc
    have hc' : |c| ≤ (⌈|c|⌉₊ : ℝ) := Nat.le_ceil _
    rw [← mul_sub, abs_mul]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul hc' h1 (abs_nonneg _) (Nat.cast_nonneg _)
  deriv α i x := by
    intro A h1 h2 h3
    refine ((D.deriv α i x A h1 h2 h3).const_mul c).congr (fun k => ?_)
    ring

@[simp] theorem scaleData_G {n : ℕ} (c : ℝ) (D : RData n) (α : MultiIndex n) (x : QPoint n) :
    (scaleData c D).G α x = c * D.G α x := rfl

theorem equivalent_iff {n : ℕ} (φ ψ : TestFunction n) :
    φ.Equivalent ψ ↔ ∀ α x, val (φ.derivative α x) = val (ψ.derivative α x) :=
  forall_congr' fun α => forall_congr' fun x =>
    equiv_iff (φ.derivative_valid α x) (ψ.derivative_valid α x)

/-- The test module in dimension `n`: pointwise sums and real scalings. -/
noncomputable def space (n : ℕ) : ComputableDistributions.TestFunctionSpace n where
  zero := (zeroData n).toTest
  add φ ψ := (addData (shadow φ) (shadow ψ)).toTest
  scale r _ φ := (scaleData (val r) (shadow φ)).toTest
  zero_derivative α x := by
    rw [equiv_iff ((RData.toTest _).derivative_valid α x) (ofRat_valid' 0)]
    simp [val_ofRat]
  add_derivative φ ψ α x := by
    rw [equiv_iff ((RData.toTest _).derivative_valid α x) (add_valid' (φ.derivative_valid α x) (ψ.derivative_valid α x)),
      val_add (φ.derivative_valid α x) (ψ.derivative_valid α x)]
    simp
  scale_derivative r hr φ α x := by
    rw [equiv_iff ((RData.toTest _).derivative_valid α x) (mul_valid' hr (φ.derivative_valid α x)),
      val_mul hr (φ.derivative_valid α x)]
    simp
  add_zero φ := by rw [equivalent_iff]; intro α x; simp
  zero_add φ := by rw [equivalent_iff]; intro α x; simp
  add_comm φ ψ := by rw [equivalent_iff]; intro α x; simp [add_comm]
  add_assoc φ ψ χ := by rw [equivalent_iff]; intro α x; simp [add_assoc]
  scale_one φ := by rw [equivalent_iff]; intro α x; simp [val_ofRat]
  scale_zero φ := by rw [equivalent_iff]; intro α x; simp [val_ofRat]
  scale_add_scalar r hr s hs φ := by
    rw [equivalent_iff]; intro α x; simp [val_add hr hs, add_mul]
  scale_mul_scalar r hr s hs φ := by
    rw [equivalent_iff]; intro α x; simp [val_mul hr hs, mul_assoc]
  scale_add_test r hr φ ψ := by
    rw [equivalent_iff]; intro α x; simp [mul_add]
  add_congr φ φ' ψ ψ' h1 h2 := by
    rw [equivalent_iff] at h1 h2 ⊢; intro α x; simp [h1 α x, h2 α x]
  scale_test_congr r hr φ ψ h := by
    rw [equivalent_iff] at h ⊢; intro α x; simp [h α x]
  scale_scalar_congr r s hr hs φ h := by
    rw [equivalent_iff]; intro α x; simp [(equiv_iff hr hs).1 h]

/-! Secants of a differentiable real function along shrinking brackets. -/

theorem rderiv_of_hasDerivAt {h : ℝ → ℝ} {q : ℚ} {d : ℝ} (hd : HasDerivAt h d (q : ℝ)) :
    RDeriv (fun r => h r) q d := by
  intro A hA hv hlt
  set a : ℕ → ℝ := fun n => ((A.compute n).lo : ℝ) with ha_def
  set b : ℕ → ℝ := fun n => ((A.compute n).hi : ℝ) with hb_def
  have ha : ∀ n, a n ≤ q := fun n => hv ▸ lo_le_val hA n
  have hb : ∀ n, (q : ℝ) ≤ b n := fun n => hv ▸ val_le_hi hA n
  have hab : ∀ n, a n < b n := fun n => by simp only [a, b]; exact_mod_cast hlt n
  have hwidth : Tendsto (fun n => b n - a n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r, hr0, hr⟩ := exists_rat_btwn hε
    obtain ⟨N, hN⟩ := width_small hA r (by exact_mod_cast hr0)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (sub_pos.2 (hab n))]
    exact lt_of_le_of_lt (hN n hn) hr
  have hta : Tendsto a atTop (𝓝 (q : ℝ)) := by
    have h1 : Tendsto (fun n => (q : ℝ) - (b n - a n)) atTop (𝓝 q) := by
      simpa using (tendsto_const_nhds (x := (q : ℝ))).sub hwidth
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun n => by linarith [hb n]) ha
  have htb : Tendsto b atTop (𝓝 (q : ℝ)) := by
    have h1 : Tendsto (fun n => (q : ℝ) + (b n - a n)) atTop (𝓝 q) := by
      simpa using (tendsto_const_nhds (x := (q : ℝ))).add hwidth
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 hb
      (fun n => by linarith [ha n])
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev := hd.isLittleO.def (half_pos hε)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (hta.eventually hev)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (htb.eventually hev)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := hN1 n (le_of_max_le_left hn)
  have e2 := hN2 n (le_of_max_le_right hn)
  simp only [smul_eq_mul, Real.norm_eq_abs] at e1 e2
  have hpos : 0 < b n - a n := sub_pos.2 (hab n)
  have key : (h (b n) - h (a n)) / (b n - a n) - d =
      ((h (b n) - h q - (b n - q) * d) - (h (a n) - h q - (a n - q) * d)) / (b n - a n) := by
    field_simp
    ring
  show |(h (b n) - h (a n)) / (b n - a n) - d| < ε
  rw [key, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  have t1 := abs_sub (h (b n) - h q - (b n - q) * d) (h (a n) - h q - (a n - q) * d)
  rw [abs_of_nonneg (sub_nonneg.2 (hb n))] at e2
  rw [abs_of_nonpos (sub_nonpos.2 (ha n))] at e1
  nlinarith

/-! A one-dimensional plateau bump and its derivatives. -/

noncomputable def bump (a b : ℚ) (ha : 0 < a) (hab : a < b) : ℝ → ℝ :=
  ⇑(⟨a, b, by exact_mod_cast ha, by exact_mod_cast hab⟩ : ContDiffBump (0 : ℝ))

noncomputable def bD (a b : ℚ) (ha : 0 < a) (hab : a < b) (k : ℕ) : ℝ → ℝ :=
  deriv^[k] (bump a b ha hab)

theorem bD_contDiff (a b : ℚ) (ha : 0 < a) (hab : a < b) (k : ℕ) :
    ContDiff ℝ ∞ (bD a b ha hab k) :=
  ContDiff.iterate_deriv k (ContDiffBump.contDiff _)

theorem bD_hasDerivAt (a b : ℚ) (ha : 0 < a) (hab : a < b) (k : ℕ) (t : ℝ) :
    HasDerivAt (bD a b ha hab k) (bD a b ha hab (k + 1) t) t := by
  have hd : Differentiable ℝ (bD a b ha hab k) :=
    (bD_contDiff a b ha hab k).differentiable (by simp)
  have : bD a b ha hab (k + 1) = deriv (bD a b ha hab k) := by
    simp only [bD]; rw [Function.iterate_succ_apply']
  rw [this]
  exact (hd t).hasDerivAt

theorem bD_tsupport (a b : ℚ) (ha : 0 < a) (hab : a < b) (k : ℕ) :
    tsupport (bD a b ha hab k) ⊆ Metric.closedBall 0 b := by
  induction k with
  | zero =>
    simp only [bD, Function.iterate_zero, id, bump]
    rw [ContDiffBump.tsupport_eq]
  | succ k ih =>
    have : bD a b ha hab (k + 1) = deriv (bD a b ha hab k) := by
      simp only [bD]; rw [Function.iterate_succ_apply']
    rw [this]
    exact (tsupport_deriv_subset).trans ih

theorem bD_zero_of (a b : ℚ) (ha : 0 < a) (hab : a < b) (k : ℕ) {t : ℝ} (ht : b < |t|) :
    bD a b ha hab k t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport (bD a b ha hab k) := subset_tsupport _ hne
  have h2 := bD_tsupport a b ha hab k h1
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
  linarith

theorem bD_one (a b : ℚ) (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : |t| ≤ a) :
    bD a b ha hab 0 t = 1 := by
  simp only [bD, Function.iterate_zero, id, bump]
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact ht

/-! The product test in `n` coordinates. -/

noncomputable def bG (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n) :
    (Fin n → ℝ) → ℝ :=
  fun y => ∏ i, bD a b ha hab (α i) (y i)

theorem bG_contDiff (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n) :
    ContDiff ℝ 1 (bG n a b ha hab α) :=
  contDiff_prod (fun i _ => ((bD_contDiff a b ha hab (α i)).of_le (by simp)).comp
    (contDiff_apply ℝ ℝ i))

theorem bG_compact (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n) :
    HasCompactSupport (bG n a b ha hab α) := by
  apply HasCompactSupport.intro (isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℝ) (b : ℝ)))
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bD_zero_of a b ha hab (α i) hi)

theorem bG_lip (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n) :
    ∃ C : ℕ, ∀ y z : Fin n → ℝ, |bG n a b ha hab α y - bG n a b ha hab α z| ≤ C * dist y z := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (bG_compact n a b ha hab α)
    (bG_contDiff n a b ha hab α) (by norm_num)
  refine ⟨⌈(C : ℝ)⌉₊, fun y z => ?_⟩
  have h1 := hC.dist_le_mul y z
  rw [Real.dist_eq] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (Nat.le_ceil _) dist_nonneg)

theorem update_cast {n : ℕ} (x : QPoint n) (i : Fin n) (r : ℚ) :
    (fun j => ((replaceCoordinate x i r j : ℚ) : ℝ)) = Function.update (fun j => (x j : ℝ)) i (r : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [replaceCoordinate]
  · simp [replaceCoordinate, h]

theorem bG_partial (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n) (i : Fin n)
    (y : Fin n → ℝ) :
    HasDerivAt (fun t => bG n a b ha hab α (Function.update y i t))
      (bG n a b ha hab (incrementIndex α i) y) (y i) := by
  set P := ∏ j ∈ Finset.univ \ {i}, bD a b ha hab (α j) (y j)
  have h1 : (fun t => bG n a b ha hab α (Function.update y i t)) =
      fun t => bD a b ha hab (α i) t * P := by
    funext t
    have : bG n a b ha hab α (Function.update y i t) =
        ∏ j, Function.update (fun j => bD a b ha hab (α j) (y j)) i (bD a b ha hab (α i) t) j := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have h2 : bG n a b ha hab (incrementIndex α i) y = bD a b ha hab (α i + 1) (y i) * P := by
    have : bG n a b ha hab (incrementIndex α i) y =
        ∏ j, Function.update (fun j => bD a b ha hab (α j) (y j)) i
          (bD a b ha hab (α i + 1) (y i)) j := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j = i
      · subst h; simp [incrementIndex]
      · simp [h, incrementIndex]
    rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [h1, h2]
  exact (bD_hasDerivAt a b ha hab (α i) (y i)).mul_const P

/-- The product of one-dimensional bumps equal to one on `[-a, a]` and
supported in `[-b, b]`, as test data in `n` coordinates. -/
noncomputable def bumpData (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) : RData n where
  G α x := bG n a b ha hab α (fun j => (x j : ℝ))
  box := ⟨fun _ => -b, fun _ => b, fun _ => by linarith⟩
  vanish α x hx := by
    simp only [RationalBox.Contains, not_forall, not_and_or, not_le] at hx
    obtain ⟨i, hi⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply bD_zero_of
    rcases hi with hi | hi
    · have : (x i : ℝ) < -b := by exact_mod_cast hi
      rw [abs_of_neg (by linarith [(by exact_mod_cast (lt_trans ha hab) : (0 : ℝ) < b)])]
      linarith
    · have : (b : ℝ) < x i := by exact_mod_cast hi
      rw [abs_of_pos (by linarith [(by exact_mod_cast (lt_trans ha hab) : (0 : ℝ) < b)])]
      exact this
  L α := ((Classical.choose (bG_lip n a b ha hab α) : ℕ) : ℚ)
  L_nonneg α := Nat.cast_nonneg _
  lip α x y δ hδ hc := by
    have h1 := Classical.choose_spec (bG_lip n a b ha hab α) (fun j => (x j : ℝ)) (fun j => (y j : ℝ))
    have h2 : dist (fun j => (x j : ℝ)) (fun j => (y j : ℝ)) ≤ δ := by
      rw [dist_pi_le_iff (by exact_mod_cast hδ)]
      intro j
      rw [Real.dist_eq, abs_le]
      have := hc j
      constructor
      · have : (y j : ℝ) ≤ x j + δ := by exact_mod_cast (hc j).2
        linarith
      · have : (x j : ℝ) ≤ y j + δ := by exact_mod_cast (hc j).1
        linarith
    push_cast
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  deriv α i x := by
    have h := rderiv_of_hasDerivAt (bG_partial n a b ha hab α i (fun j => (x j : ℝ)))
    intro A h1 h2 h3
    have := h A h1 h2 h3
    simp only [update_cast]
    exact this

@[simp] theorem bumpData_G (n : ℕ) (a b : ℚ) (ha : 0 < a) (hab : a < b) (α : MultiIndex n)
    (x : QPoint n) : (bumpData n a b ha hab).G α x = ∏ i, bD a b ha hab (α i) (x i) := rfl

theorem main : ComputableDistributions.TestModulesExist := by
  refine ⟨⟨space⟩, fun n r hr => ?_, fun R hR => ?_⟩
  · have h1 : 0 < r / 2 := by positivity
    have h2 : r / 2 < r := by linarith
    refine ⟨(bumpData n (r / 2) r h1 h2).toTest, fun i => ⟨le_rfl, le_rfl⟩, ?_⟩
    rw [ComputableDistributions.TestFunction.atOrigin, ComputableDistributions.TestFunction.value,
      equiv_iff ((RData.toTest _).derivative_valid _ _) (ofRat_valid' 1), RData.val_toTest,
      bumpData_G, val_ofRat]
    push_cast
    apply Finset.prod_eq_one
    intro i _
    apply bD_one
    simp [ComputableAnalysis.origin]
    positivity
  · refine ⟨(bumpData 1 R (R + 1) hR (by linarith)).toTest, fun x h1 h2 => ?_⟩
    rw [ComputableDistributions.TestFunction.value,
      equiv_iff ((RData.toTest _).derivative_valid _ _) (ofRat_valid' 1), RData.val_toTest,
      bumpData_G, val_ofRat]
    push_cast
    apply Finset.prod_eq_one
    intro i _
    apply bD_one
    show |((x : ℚ) : ℝ)| ≤ (R : ℝ)
    have e1 : ((-R : ℚ) : ℝ) ≤ x := by exact_mod_cast h1
    have e2 : (x : ℝ) ≤ R := by exact_mod_cast h2
    push_cast at e1
    rw [abs_le]
    exact ⟨e1, e2⟩

end TMSol

theorem solution : ComputableDistributions.TestModulesExist := TMSol.main
