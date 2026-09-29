-- Prove2me | solution 1 for CannonFloydParry.exists_conj_supp_subset_Icc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:57:52.622859+00:00
-- url     : https://prove2.me/submissions/6fddbc8d-772e-4887-88c7-a184bbc04513

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

open Set

/-- piecewise affine map, identity outside `[t0, t3]`, slopes powers of two inside -/
noncomputable def pw (t0 t1 t2 t3 : ℝ) (n1 n2 n3 : ℤ) (c1 c2 c3 : ℝ) (x : ℝ) : ℝ :=
  if x ≤ t0 then x else if x ≤ t1 then (2:ℝ) ^ n1 * x + c1 else
    if x ≤ t2 then (2:ℝ) ^ n2 * x + c2 else if x ≤ t3 then (2:ℝ) ^ n3 * x + c3 else x

structure PwData where
  t0 : ℝ
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ
  n1 : ℤ
  n2 : ℤ
  n3 : ℤ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  h01 : t0 ≤ t1
  h12 : t1 ≤ t2
  h23 : t2 ≤ t3
  e0 : t0 = (2:ℝ) ^ n1 * t0 + c1
  e1 : (2:ℝ) ^ n1 * t1 + c1 = (2:ℝ) ^ n2 * t1 + c2
  e2 : (2:ℝ) ^ n2 * t2 + c2 = (2:ℝ) ^ n3 * t2 + c3
  e3 : (2:ℝ) ^ n3 * t3 + c3 = t3

namespace PwData

variable (D : PwData)

noncomputable def f : ℝ → ℝ := pw D.t0 D.t1 D.t2 D.t3 D.n1 D.n2 D.n3 D.c1 D.c2 D.c3

lemma aff_strictMono (n : ℤ) (c : ℝ) : StrictMono (fun x : ℝ => (2:ℝ) ^ n * x + c) := by
  intro x y h
  have : (0:ℝ) < 2 ^ n := zpow_pos (by norm_num) n
  simp only
  nlinarith

lemma strictMono_f : StrictMono D.f := by
  have g3 : StrictMono (fun x => if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    strictMono_glue ((aff_strictMono D.n3 D.c3).strictMonoOn _) (strictMono_id.strictMonoOn _)
      (by simpa using D.e3)
  have g2 : StrictMono (fun x => if x ≤ D.t2 then (2:ℝ) ^ D.n2 * x + D.c2 else
      if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    strictMono_glue ((aff_strictMono D.n2 D.c2).strictMonoOn _) (g3.strictMonoOn _)
      (by simp only [D.h23, if_true]; exact D.e2)
  have g1 : StrictMono (fun x => if x ≤ D.t1 then (2:ℝ) ^ D.n1 * x + D.c1 else
      if x ≤ D.t2 then (2:ℝ) ^ D.n2 * x + D.c2 else
      if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    strictMono_glue ((aff_strictMono D.n1 D.c1).strictMonoOn _) (g2.strictMonoOn _)
      (by simp only [D.h12, if_true]; exact D.e1)
  have g0 := strictMono_glue (f := id) (c := D.t0) (strictMono_id.strictMonoOn _)
      (g1.strictMonoOn _) (by simp only [D.h01, if_true, id]; exact D.e0)
  exact g0

lemma f_eq_of_le {x : ℝ} (hx : x ≤ D.t0) : D.f x = x := by
  simp [f, pw, hx]

lemma f_eq_of_ge {x : ℝ} (hx : D.t3 ≤ x) : D.f x = x := by
  have h01 := D.h01; have h12 := D.h12; have h23 := D.h23
  unfold f pw
  split_ifs with c0 c1 c2 c3
  · rfl
  · have ex : x = D.t1 := le_antisymm c1 (by linarith)
    have e2' : D.t2 = D.t1 := by linarith
    have e3' : D.t3 = D.t1 := by linarith
    have := D.e1; have := D.e2; have := D.e3
    rw [e2'] at *; rw [e3'] at *; rw [ex]; linarith
  · have ex : x = D.t2 := le_antisymm c2 (by linarith)
    have e3' : D.t3 = D.t2 := by linarith
    have := D.e2; have := D.e3
    rw [e3'] at *; rw [ex]; linarith
  · have ex : x = D.t3 := le_antisymm c3 hx
    rw [ex]; exact D.e3
  · rfl

lemma continuous_f : Continuous D.f := by
  have ca : ∀ (n : ℤ) (c : ℝ), Continuous (fun x : ℝ => (2:ℝ) ^ n * x + c) := by
    intro n c; fun_prop
  have g3 : Continuous (fun x => if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    Continuous.if_le (ca _ _) continuous_id continuous_id continuous_const
      (fun x hx => by rw [hx]; exact D.e3)
  have g2 : Continuous (fun x => if x ≤ D.t2 then (2:ℝ) ^ D.n2 * x + D.c2 else
      if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    Continuous.if_le (ca _ _) g3 continuous_id continuous_const
      (fun x hx => by rw [hx]; simp only [D.h23, if_true]; exact D.e2)
  have g1 : Continuous (fun x => if x ≤ D.t1 then (2:ℝ) ^ D.n1 * x + D.c1 else
      if x ≤ D.t2 then (2:ℝ) ^ D.n2 * x + D.c2 else
      if x ≤ D.t3 then (2:ℝ) ^ D.n3 * x + D.c3 else x) :=
    Continuous.if_le (ca _ _) g2 continuous_id continuous_const
      (fun x hx => by rw [hx]; simp only [D.h12, if_true]; exact D.e1)
  exact Continuous.if_le continuous_id g1 continuous_id continuous_const
      (fun x hx => by rw [hx]; simp only [D.h01, if_true]; exact D.e0)

lemma surjective_f : Function.Surjective D.f := by
  apply D.continuous_f.surjective
  · apply Filter.tendsto_id.congr'
    filter_upwards [Filter.eventually_ge_atTop D.t3] with x hx
    exact (D.f_eq_of_ge hx).symm
  · apply Filter.tendsto_id.congr'
    filter_upwards [Filter.eventually_le_atBot D.t0] with x hx
    exact (D.f_eq_of_le hx).symm

noncomputable def iso : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective D.f D.strictMono_f D.surjective_f

@[simp] lemma iso_apply (x : ℝ) : D.iso x = D.f x := rfl

lemma piece1 {z : ℝ} (h0 : D.t0 ≤ z) (h1 : z ≤ D.t1) : D.f z = (2:ℝ) ^ D.n1 * z + D.c1 := by
  unfold f pw
  by_cases hz0 : z ≤ D.t0
  · have : z = D.t0 := le_antisymm hz0 h0
    rw [if_pos hz0, this]; exact D.e0
  · rw [if_neg hz0, if_pos h1]

lemma piece2 {z : ℝ} (h1 : D.t1 ≤ z) (h2 : z ≤ D.t2) : D.f z = (2:ℝ) ^ D.n2 * z + D.c2 := by
  have h01 := D.h01
  unfold f pw
  by_cases hz0 : z ≤ D.t0
  · have e1 : z = D.t0 := le_antisymm hz0 (by linarith)
    have e2 : D.t1 = D.t0 := by linarith
    have := D.e0; have := D.e1
    rw [if_pos hz0, e1]; rw [e2] at *; linarith
  · rw [if_neg hz0]
    by_cases hz1 : z ≤ D.t1
    · have : z = D.t1 := le_antisymm hz1 h1
      rw [if_pos hz1, this]; exact D.e1
    · rw [if_neg hz1, if_pos h2]

lemma piece3 {z : ℝ} (h2 : D.t2 ≤ z) (h3 : z ≤ D.t3) : D.f z = (2:ℝ) ^ D.n3 * z + D.c3 := by
  have h01 := D.h01; have h12 := D.h12
  unfold f pw
  by_cases hz0 : z ≤ D.t0
  · have e1 : z = D.t0 := le_antisymm hz0 (by linarith)
    have e2 : D.t1 = D.t0 := by linarith
    have e3 : D.t2 = D.t0 := by linarith
    have := D.e0; have := D.e1; have := D.e2
    rw [if_pos hz0, e1]; rw [e2, e3] at *; linarith
  · rw [if_neg hz0]
    by_cases hz1 : z ≤ D.t1
    · have e1 : z = D.t1 := le_antisymm hz1 (by linarith)
      have e2 : D.t2 = D.t1 := by linarith
      have := D.e1; have := D.e2
      rw [if_pos hz1, e1]; rw [e2] at *; linarith
    · rw [if_neg hz1]
      by_cases hz2 : z ≤ D.t2
      · have : z = D.t2 := le_antisymm hz2 h2
        rw [if_pos hz2, this]; exact D.e2
      · rw [if_neg hz2, if_pos h3]

/-- on each closed piece the map is affine -/
lemma affine_piece {x y : ℝ} (hxy : x < y)
    (hB : ∀ t ∈ ({D.t0, D.t1, D.t2, D.t3} : Set ℝ), t ∉ Ioo x y) :
    ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Icc x y, D.f z = (2:ℝ) ^ n * z + c := by
  have k0 := hB D.t0 (by simp); have k1 := hB D.t1 (by simp)
  have k2 := hB D.t2 (by simp); have k3 := hB D.t3 (by simp)
  simp only [mem_Ioo, not_and_or, not_lt] at k0 k1 k2 k3
  by_cases y0 : y ≤ D.t0
  · refine ⟨0, 0, fun z hz => ?_⟩
    rw [D.f_eq_of_le (le_trans hz.2 y0)]; simp
  have x0 : D.t0 ≤ x := by rcases k0 with h | h <;> [exact h; exact absurd h y0]
  by_cases y1 : y ≤ D.t1
  · exact ⟨D.n1, D.c1, fun z hz => D.piece1 (le_trans x0 hz.1) (le_trans hz.2 y1)⟩
  have x1 : D.t1 ≤ x := by rcases k1 with h | h <;> [exact h; exact absurd h y1]
  by_cases y2 : y ≤ D.t2
  · exact ⟨D.n2, D.c2, fun z hz => D.piece2 (le_trans x1 hz.1) (le_trans hz.2 y2)⟩
  have x2 : D.t2 ≤ x := by rcases k2 with h | h <;> [exact h; exact absurd h y2]
  by_cases y3 : y ≤ D.t3
  · exact ⟨D.n3, D.c3, fun z hz => D.piece3 (le_trans x2 hz.1) (le_trans hz.2 y3)⟩
  have x3 : D.t3 ≤ x := by rcases k3 with h | h <;> [exact h; exact absurd h y3]
  refine ⟨0, 0, fun z hz => ?_⟩
  rw [D.f_eq_of_ge (le_trans x3 hz.1)]; simp

/-- the induced order isomorphism of the unit interval -/
noncomputable def ui (h0 : 0 ≤ D.t0) (h1 : D.t3 ≤ 1) : UI ≃o UI :=
  restrict D.iso (fun x hx => D.f_eq_of_le (le_trans hx h0))
    (fun x hx => D.f_eq_of_ge (le_trans h1 hx))

lemma ui_coe (h0 : 0 ≤ D.t0) (h1 : D.t3 ≤ 1) (z : UI) : ((D.ui h0 h1 z : UI) : ℝ) = D.f z := rfl

lemma ui_pow_coe (h0 : 0 ≤ D.t0) (h1 : D.t3 ≤ 1) (n : ℕ) (z : UI) :
    (((D.ui h0 h1) ^ n) z : ℝ) = D.f^[n] z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RelIso.mul_apply, ih, Function.iterate_succ_apply, ui_coe]

lemma isThompson_ui (h0 : 0 ≤ D.t0) (h1 : D.t3 ≤ 1)
    (hd0 : IsDyadic D.t0) (hd1 : IsDyadic D.t1) (hd2 : IsDyadic D.t2) (hd3 : IsDyadic D.t3) :
    IsThompson (D.ui h0 h1) := by
  classical
  refine ⟨{D.t0, D.t1, D.t2, D.t3}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> assumption
  · intro x y hxy hB
    obtain ⟨n, c, hnc⟩ := D.affine_piece hxy (by
      intro t ht htm
      have : t ∈ Ioo (x : ℝ) (y : ℝ) ∩ (({D.t0, D.t1, D.t2, D.t3} : Finset ℝ) : Set ℝ) := by
        refine ⟨htm, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact ht
      rw [hB] at this; exact this)
    exact ⟨n, c, fun z hz => by rw [ui_coe]; exact hnc z hz⟩

end PwData

/-- right-moving bump on `[u, v]` -/
noncomputable def bumpR (u v l : ℝ) (hl : 0 ≤ l) (huv : u + 3 * l ≤ v) : PwData where
  t0 := u
  t1 := u + l
  t2 := v - 2 * l
  t3 := v
  n1 := 1
  n2 := 0
  n3 := -1
  c1 := -u
  c2 := l
  c3 := v / 2
  h01 := by linarith
  h12 := by linarith
  h23 := by linarith
  e0 := by simp; ring
  e1 := by simp; ring
  e2 := by simp; ring
  e3 := by simp; ring

/-- left-moving bump on `[m, w]` -/
noncomputable def bumpL (m w l : ℝ) (hl : 0 ≤ l) (hmw : m + 3 * l ≤ w) : PwData where
  t0 := m
  t1 := m + 2 * l
  t2 := w - l
  t3 := w
  n1 := -1
  n2 := 0
  n3 := 1
  c1 := m / 2
  c2 := -l
  c3 := -w
  h01 := by linarith
  h12 := by linarith
  h23 := by linarith
  e0 := by simp; ring
  e1 := by simp; ring
  e2 := by simp; ring
  e3 := by simp; ring

lemma bumpR_iter (u v l : ℝ) (hl : 0 < l) (huv : u + 3 * l ≤ v) (n : ℕ) :
    ∀ x, u + l ≤ x → x ≤ v →
      u + l ≤ (bumpR u v l hl.le huv).f^[n] x ∧ (bumpR u v l hl.le huv).f^[n] x ≤ v ∧
      v - (bumpR u v l hl.le huv).f^[n] x ≤ max (v - x - n * l) (2 * l) := by
  set D := bumpR u v l hl.le huv
  have step : ∀ x, u + l ≤ x → x ≤ v →
      u + l ≤ D.f x ∧ D.f x ≤ v ∧ v - D.f x ≤ max (v - x - l) (2 * l) := by
    intro x hx1 hx2
    by_cases hc : x ≤ v - 2 * l
    · have : D.f x = x + l := by rw [D.piece2 (z := x) hx1 hc]; simp [D, bumpR]
      rw [this]
      refine ⟨by linarith, by linarith, le_max_of_le_left (by linarith)⟩
    · push Not at hc
      have : D.f x = x / 2 + v / 2 := by
        rw [D.piece3 (z := x) hc.le hx2]; simp [D, bumpR]; ring
      rw [this]
      refine ⟨by linarith, by linarith, le_max_of_le_right (by linarith)⟩
  induction n with
  | zero =>
    intro x hx1 hx2
    simp only [Function.iterate_zero, id, Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨hx1, hx2, le_max_left _ _⟩
  | succ n ih =>
    intro x hx1 hx2
    obtain ⟨s1, s2, s3⟩ := step x hx1 hx2
    obtain ⟨i1, i2, i3⟩ := ih (D.f x) s1 s2
    rw [Function.iterate_succ_apply]
    refine ⟨i1, i2, ?_⟩
    refine le_trans i3 (max_le ?_ (le_max_right _ _))
    have hn : (0:ℝ) ≤ n * l := by positivity
    push_cast
    rcases le_max_iff.1 s3 with h | h
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)

lemma bumpL_iter (m w l : ℝ) (hl : 0 < l) (hmw : m + 3 * l ≤ w) (n : ℕ) :
    ∀ x, m ≤ x → x ≤ w - l →
      m ≤ (bumpL m w l hl.le hmw).f^[n] x ∧ (bumpL m w l hl.le hmw).f^[n] x ≤ w - l ∧
      (bumpL m w l hl.le hmw).f^[n] x - m ≤ max (x - m - n * l) (2 * l) := by
  set D := bumpL m w l hl.le hmw
  have step : ∀ x, m ≤ x → x ≤ w - l →
      m ≤ D.f x ∧ D.f x ≤ w - l ∧ D.f x - m ≤ max (x - m - l) (2 * l) := by
    intro x hx1 hx2
    by_cases hc : m + 2 * l ≤ x
    · have : D.f x = x - l := by rw [D.piece2 (z := x) hc hx2]; simp [D, bumpL]; ring
      rw [this]
      refine ⟨by linarith, by linarith, le_max_of_le_left (by linarith)⟩
    · push Not at hc
      have : D.f x = x / 2 + m / 2 := by
        rw [D.piece1 (z := x) hx1 hc.le]; simp [D, bumpL]; ring
      rw [this]
      refine ⟨by linarith, by linarith, le_max_of_le_right (by linarith)⟩
  induction n with
  | zero =>
    intro x hx1 hx2
    simp only [Function.iterate_zero, id, Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨hx1, hx2, le_max_left _ _⟩
  | succ n ih =>
    intro x hx1 hx2
    obtain ⟨s1, s2, s3⟩ := step x hx1 hx2
    obtain ⟨i1, i2, i3⟩ := ih (D.f x) s1 s2
    rw [Function.iterate_succ_apply]
    refine ⟨i1, i2, ?_⟩
    refine le_trans i3 (max_le ?_ (le_max_right _ _))
    have hn : (0:ℝ) ≤ n * l := by positivity
    push_cast
    rcases le_max_iff.1 s3 with h | h
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)

lemma dy_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma dy_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma dy_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]; exact dy_add hx (dy_neg hy)

lemma dy_half {x : ℝ} (hx : IsDyadic x) : IsDyadic (x / 2) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨m, k + 1, by rw [pow_succ]; field_simp⟩

lemma dy_two_mul {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 * x) := by
  rw [two_mul]; exact dy_add hx hx

lemma dy_one : IsDyadic 1 := ⟨1, 0, by simp⟩

lemma dy_pow (M : ℕ) : IsDyadic ((1/2 : ℝ) ^ M) := ⟨1, M, by simp⟩

theorem _root_.solution {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hda : IsDyadic a) (hdb : IsDyadic b)
    {w : UI ≃o UI} (hw : w ∈ F) (hw0 : TrivialNearZero w) (hw1 : TrivialNearOne w) :
    ∃ φ : UI ≃o UI, φ ∈ F ∧ TrivialNearZero φ ∧ TrivialNearOne φ ∧
      ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧
        ∀ z : UI, (φ (w (φ.symm z)) : ℝ) ≠ (z : ℝ) → (z : ℝ) ∈ Set.Icc c d := by
  obtain ⟨ε0, hε0, hw0'⟩ := hw0
  obtain ⟨ε1, hε1, hw1'⟩ := hw1
  set m := (a + b) / 2 with hmdef
  have hma : a < m := by linarith
  have hmb : m < b := by linarith
  have hm0 : 0 < m := by linarith
  have hm1 : m < 1 := by linarith
  have hdm : IsDyadic m := dy_half (dy_add hda hdb)
  set e0 := min (ε0 / 2) (m / 2) with he0
  set e1 := min (ε1 / 2) ((1 - m) / 2) with he1
  have he0p : 0 < e0 := lt_min (by linarith) (by linarith)
  have he1p : 0 < e1 := lt_min (by linarith) (by linarith)
  have he0a : e0 ≤ ε0 / 2 := min_le_left _ _
  have he0b : e0 ≤ m / 2 := min_le_right _ _
  have he1a : e1 ≤ ε1 / 2 := min_le_left _ _
  have he1b : e1 ≤ (1 - m) / 2 := min_le_right _ _
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
    (lt_min (lt_min (half_pos he0p) (half_pos he1p))
      (lt_min (lt_min (by linarith : (0:ℝ) < m / 4) (by linarith : (0:ℝ) < (1 - m) / 4))
        (lt_min (by linarith : (0:ℝ) < (m - a) / 2) (by linarith : (0:ℝ) < (b - m) / 2))))
    (by norm_num : (1/2 : ℝ) < 1)
  set l := (1/2 : ℝ) ^ M with hldef
  have hl : 0 < l := by positivity
  have l1 : l < e0 / 2 := lt_of_lt_of_le hM (le_trans (min_le_left _ _) (min_le_left _ _))
  have l2 : l < e1 / 2 := lt_of_lt_of_le hM (le_trans (min_le_left _ _) (min_le_right _ _))
  have l3 : l < m / 4 := lt_of_lt_of_le hM
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have l4 : l < (1 - m) / 4 := lt_of_lt_of_le hM
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have l5 : l < (m - a) / 2 := lt_of_lt_of_le hM
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have l6 : l < (b - m) / 2 := lt_of_lt_of_le hM
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hdl : IsDyadic l := dy_pow M
  have hR : l + 3 * l ≤ m := by linarith
  have hL : m + 3 * l ≤ 1 - l := by linarith
  set DR := bumpR l m l hl.le hR with hDR
  set DL := bumpL m (1 - l) l hl.le hL with hDL
  have h0R : 0 ≤ DR.t0 := hl.le
  have h1R : DR.t3 ≤ 1 := hm1.le
  have h0L : 0 ≤ DL.t0 := hm0.le
  have h1L : DL.t3 ≤ 1 := by show 1 - l ≤ 1; linarith
  set gR := DR.ui h0R h1R with hgR
  set gL := DL.ui h0L h1L with hgL
  set N := 2 ^ M with hN
  have hNl : (N : ℝ) * l = 1 := by
    rw [hN, hldef]; push_cast; rw [← mul_pow]; norm_num
  have hthR : IsThompson gR := DR.isThompson_ui h0R h1R hdl (dy_add hdl hdl)
    (dy_sub hdm (dy_two_mul hdl)) hdm
  have hthL : IsThompson gL := DL.isThompson_ui h0L h1L hdm (dy_add hdm (dy_two_mul hdl))
    (dy_sub (dy_sub dy_one hdl) hdl) (dy_sub dy_one hdl)
  set φ := gR ^ N * gL ^ N with hφ
  have hφcoe : ∀ z : UI, (φ z : ℝ) = DR.f^[N] (DL.f^[N] z) := by
    intro z
    rw [hφ, RelIso.mul_apply, PwData.ui_pow_coe, PwData.ui_pow_coe]
  have monoR : StrictMono DR.f^[N] := DR.strictMono_f.iterate N
  have monoL : StrictMono DL.f^[N] := DL.strictMono_f.iterate N
  have fixR_le : ∀ x, x ≤ l → DR.f^[N] x = x := fun x hx =>
    Function.iterate_fixed (DR.f_eq_of_le hx) N
  have fixR_ge : ∀ x, m ≤ x → DR.f^[N] x = x := fun x hx =>
    Function.iterate_fixed (DR.f_eq_of_ge hx) N
  have fixL_le : ∀ x, x ≤ m → DL.f^[N] x = x := fun x hx =>
    Function.iterate_fixed (DL.f_eq_of_le hx) N
  have fixL_ge : ∀ x, 1 - l ≤ x → DL.f^[N] x = x := fun x hx =>
    Function.iterate_fixed (DL.f_eq_of_ge hx) N
  -- the two endpoints
  obtain ⟨c1, c2, c3⟩ := bumpR_iter l m l hl hR N e0 (by linarith) (by linarith)
  obtain ⟨d1, d2, d3⟩ := bumpL_iter m (1 - l) l hl hL N (1 - e1) (by linarith) (by linarith)
  rw [hNl] at c3 d3
  have hc : m - 2 * l ≤ DR.f^[N] e0 := by
    have := le_max_iff.1 c3
    rcases this with h | h
    · nlinarith
    · linarith
  have hd : DL.f^[N] (1 - e1) ≤ m + 2 * l := by
    have := le_max_iff.1 d3
    rcases this with h | h
    · nlinarith
    · linarith
  refine ⟨φ, ?_, ?_, ?_, DR.f^[N] e0, DL.f^[N] (1 - e1), ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_F_of_isThompson hthR) _)
      (Subgroup.pow_mem _ (mem_F_of_isThompson hthL) _)
  · refine ⟨l, hl, fun z hz => ?_⟩
    rw [hφcoe, fixL_le _ (by linarith), fixR_le _ hz.le]
  · refine ⟨l, hl, fun z hz => ?_⟩
    rw [hφcoe, fixL_ge _ (by linarith), fixR_ge _ (by linarith [z.2.2])]
  · linarith
  · have h1 : DR.f^[N] e0 < DR.f^[N] m := monoR (by linarith)
    rw [fixR_ge m le_rfl] at h1
    linarith
  · linarith
  · intro z hz
    set y := φ.symm z with hy
    have hyz : φ y = z := by rw [hy]; exact φ.apply_symm_apply z
    have hy0 : e0 ≤ (y : ℝ) := by
      by_contra hlt
      push Not at hlt
      have := hw0' y (by linarith)
      apply hz
      have h2 : w y = y := Subtype.ext this
      rw [h2, hyz]
    have hy1 : (y : ℝ) ≤ 1 - e1 := by
      by_contra hlt
      push Not at hlt
      have := hw1' y (by linarith)
      apply hz
      have h2 : w y = y := Subtype.ext this
      rw [h2, hyz]
    have hzeq : (z : ℝ) = DR.f^[N] (DL.f^[N] y) := by rw [← hyz, hφcoe]
    constructor
    · rw [hzeq]
      calc DR.f^[N] e0 = DR.f^[N] (DL.f^[N] e0) := by rw [fixL_le e0 (by linarith)]
        _ ≤ DR.f^[N] (DL.f^[N] y) := monoR.monotone (monoL.monotone hy0)
    · rw [hzeq]
      calc DR.f^[N] (DL.f^[N] y) ≤ DR.f^[N] (DL.f^[N] (1 - e1)) :=
            monoR.monotone (monoL.monotone hy1)
        _ = DL.f^[N] (1 - e1) := fixR_ge _ d1

end CannonFloydParry
