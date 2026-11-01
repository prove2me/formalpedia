-- Prove2me | solution 1 for FCP.Kakeya.kakeya_two_dim
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T20:26:40.417059+00:00
-- url     : https://prove2.me/submissions/f262a144-a572-489d-854f-e43b975546a2

import Mathlib
import Definitions.Def_FCP_Kakeya

set_option autoImplicit false
set_option linter.all false

namespace Kak2

open Real

/-- the grid cell (of side `δ`) containing the point `(x, y)` -/
noncomputable def cell (δ x y : ℝ) : ℤ × ℤ := (⌊x / δ⌋, ⌊y / δ⌋)

lemma floor_close {δ x y : ℝ} (hδ : 0 < δ) (h : ⌊x / δ⌋ = ⌊y / δ⌋) : |x - y| < δ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  have h2 : x / δ - y / δ = (x - y) / δ := by ring
  rw [h2, abs_div, abs_of_pos hδ, div_lt_one hδ] at h1
  exact h1

lemma floor_diff_lt {δ x y : ℝ} (hδ : 0 < δ) :
    ((⌊x / δ⌋ - ⌊y / δ⌋ : ℤ) : ℝ) < (x - y) / δ + 1 := by
  have h1 := Int.floor_le (x / δ)
  have h2 := Int.lt_floor_add_one (y / δ)
  have h3 : (x - y) / δ = x / δ - y / δ := by ring
  push_cast
  rw [h3]
  linarith

lemma cos_gt_half {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : 1 / 2 < cos θ := by
  have hp : (1:ℝ) < π / 3 := by have := Real.pi_gt_three; linarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three]) (lt_of_le_of_lt h1 hp)
  rw [Real.cos_pi_div_three] at this
  exact this

/-- two points of one segment in the same column lie in rows at most 2 apart -/
lemma row_bound {δ a0 a1 θ t1 t2 : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hc : (cell δ (a0 + t1 * cos θ) (a1 + t1 * sin θ)).1 = (cell δ (a0 + t2 * cos θ) (a1 + t2 * sin θ)).1) :
    (cell δ (a0 + t1 * cos θ) (a1 + t1 * sin θ)).2 - (cell δ (a0 + t2 * cos θ) (a1 + t2 * sin θ)).2 ≤ 2 := by
  simp only [cell] at hc ⊢
  have hx := floor_close hδ hc
  have hcos := cos_gt_half h0 h1
  have hsin0 : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three])
  have hsin1 : sin θ ≤ 1 := Real.sin_le_one θ
  have e1 : a0 + t1 * cos θ - (a0 + t2 * cos θ) = (t1 - t2) * cos θ := by ring
  rw [e1, abs_mul, abs_of_pos (by linarith : (0:ℝ) < cos θ)] at hx
  have hu : |t1 - t2| < 2 * δ := by nlinarith [abs_nonneg (t1 - t2)]
  have hy := floor_diff_lt (x := a1 + t1 * sin θ) (y := a1 + t2 * sin θ) hδ
  have e2 : a1 + t1 * sin θ - (a1 + t2 * sin θ) = (t1 - t2) * sin θ := by ring
  rw [e2] at hy
  have h3 : (t1 - t2) * sin θ ≤ |t1 - t2| := by
    calc (t1 - t2) * sin θ ≤ |t1 - t2| * sin θ := by
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hsin0
      _ ≤ |t1 - t2| * 1 := by exact mul_le_mul_of_nonneg_left hsin1 (abs_nonneg _)
      _ = |t1 - t2| := mul_one _
  have h4 : (t1 - t2) * sin θ / δ < 2 := by
    rw [div_lt_iff₀ hδ]; linarith
  have h5 : ((⌊(a1 + t1 * sin θ) / δ⌋ - ⌊(a1 + t2 * sin θ) / δ⌋ : ℤ) : ℝ) < 3 := by linarith
  have h6 : (⌊(a1 + t1 * sin θ) / δ⌋ - ⌊(a1 + t2 * sin θ) / δ⌋ : ℤ) < 3 := by exact_mod_cast h5
  omega

/-- column spread of two points of one segment -/
lemma col_bound {δ a0 a1 θ t1 t2 : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (((cell δ (a0 + t1 * cos θ) (a1 + t1 * sin θ)).1 - (cell δ (a0 + t2 * cos θ) (a1 + t2 * sin θ)).1 : ℤ) : ℝ)
      < |t1 - t2| / δ + 1 := by
  simp only [cell]
  have hy := floor_diff_lt (x := a0 + t1 * cos θ) (y := a0 + t2 * cos θ) hδ
  have e2 : a0 + t1 * cos θ - (a0 + t2 * cos θ) = (t1 - t2) * cos θ := by ring
  rw [e2] at hy
  have hcos := cos_gt_half h0 h1
  have hcos1 : cos θ ≤ 1 := Real.cos_le_one θ
  have h3 : (t1 - t2) * cos θ ≤ |t1 - t2| := by
    calc (t1 - t2) * cos θ ≤ |t1 - t2| * cos θ := by
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |t1 - t2| * 1 := by exact mul_le_mul_of_nonneg_left hcos1 (abs_nonneg _)
      _ = |t1 - t2| := mul_one _
  have h4 : (t1 - t2) * cos θ / δ ≤ |t1 - t2| / δ := div_le_div_of_nonneg_right h3 hδ.le
  linarith

/-- two segments meeting the same two cells: parameter gap times |sin(angle)| is < 4δ -/
lemma pair_param {δ a0 a1 θ b0 b1 θ' t1 t2 s1 s2 : ℝ} (hδ : 0 < δ)
    (h1 : cell δ (a0 + t1 * cos θ) (a1 + t1 * sin θ) = cell δ (b0 + s1 * cos θ') (b1 + s1 * sin θ'))
    (h2 : cell δ (a0 + t2 * cos θ) (a1 + t2 * sin θ) = cell δ (b0 + s2 * cos θ') (b1 + s2 * sin θ')) :
    |t1 - t2| * |sin (θ' - θ)| < 4 * δ := by
  simp only [cell, Prod.mk.injEq] at h1 h2
  have x1 := floor_close hδ h1.1
  have y1 := floor_close hδ h1.2
  have x2 := floor_close hδ h2.1
  have y2 := floor_close hδ h2.2
  set wx := (a0 + t1 * cos θ - (b0 + s1 * cos θ')) - (a0 + t2 * cos θ - (b0 + s2 * cos θ')) with hwx
  set wy := (a1 + t1 * sin θ - (b1 + s1 * sin θ')) - (a1 + t2 * sin θ - (b1 + s2 * sin θ')) with hwy
  have hx : |wx| < 2 * δ := by
    calc |wx| ≤ |a0 + t1 * cos θ - (b0 + s1 * cos θ')| + |a0 + t2 * cos θ - (b0 + s2 * cos θ')| :=
          abs_sub _ _
      _ < δ + δ := add_lt_add x1 x2
      _ = 2 * δ := by ring
  have hy : |wy| < 2 * δ := by
    calc |wy| ≤ |a1 + t1 * sin θ - (b1 + s1 * sin θ')| + |a1 + t2 * sin θ - (b1 + s2 * sin θ')| :=
          abs_sub _ _
      _ < δ + δ := add_lt_add y1 y2
      _ = 2 * δ := by ring
  have key : (t1 - t2) * sin (θ' - θ) = wx * sin θ' - wy * cos θ' := by
    rw [Real.sin_sub, hwx, hwy]; ring
  rw [← abs_mul, key]
  calc |wx * sin θ' - wy * cos θ'| ≤ |wx * sin θ'| + |wy * cos θ'| := abs_sub _ _
    _ = |wx| * |sin θ'| + |wy| * |cos θ'| := by rw [abs_mul, abs_mul]
    _ ≤ |wx| * 1 + |wy| * 1 := by
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
    _ < 2 * δ + 2 * δ := by linarith
    _ = 4 * δ := by ring

/-- counting grid cells with bounded column spread and row spread ≤ 2 in each column -/
lemma card_grid (S : Finset (ℤ × ℤ)) (X : ℝ) (hX : 0 ≤ X)
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ((p.1 - q.1 : ℤ) : ℝ) ≤ X)
    (hrow : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p.2 - q.2 ≤ 2) :
    (S.card : ℝ) ≤ (2 * X + 1) * 5 := by
  rcases S.eq_empty_or_nonempty with h | ⟨p0, hp0⟩
  · simp [h]; positivity
  have hfib : ∀ b ∈ S.image Prod.fst, (S.filter (fun a => a.1 = b)).card ≤ 5 := by
    intro b _
    rcases (S.filter (fun a => a.1 = b)).eq_empty_or_nonempty with h | ⟨r, hr⟩
    · simp [h]
    rw [Finset.mem_filter] at hr
    have hsub : ∀ a ∈ S.filter (fun a => a.1 = b), a.2 ∈ Finset.Icc (r.2 - 2) (r.2 + 2) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_Icc]
      have e : a.1 = r.1 := by rw [ha.2, hr.2]
      constructor
      · have := hrow r hr.1 a ha.1 e.symm; omega
      · have := hrow a ha.1 r hr.1 e; omega
    have hinj : Set.InjOn Prod.snd (↑(S.filter (fun a => a.1 = b)) : Set (ℤ × ℤ)) := by
      intro a ha c hc hac
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hc
      exact Prod.ext (by rw [ha.2, hc.2]) hac
    have := Finset.card_le_card_of_injOn Prod.snd hsub hinj
    rw [Int.card_Icc] at this
    omega
  have h1 := Finset.card_le_mul_card_image S 5 hfib
  have hsub : S.image Prod.fst ⊆ Finset.Icc (p0.1 - ⌊X⌋) (p0.1 + ⌊X⌋) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    rw [Finset.mem_Icc]
    have ha := hcol p hp p0 hp0
    have hb := hcol p0 hp0 p hp
    have ha' : p.1 - p0.1 ≤ ⌊X⌋ := Int.le_floor.mpr ha
    have hb' : p0.1 - p.1 ≤ ⌊X⌋ := Int.le_floor.mpr hb
    constructor <;> omega
  have h2 := Finset.card_le_card hsub
  rw [Int.card_Icc] at h2
  have hfl : (0:ℤ) ≤ ⌊X⌋ := Int.floor_nonneg.mpr hX
  have h3 : (S.card : ℤ) ≤ 5 * (2 * ⌊X⌋ + 1) := by
    have : ((S.image Prod.fst).card : ℤ) ≤ 2 * ⌊X⌋ + 1 := by
      have e : (p0.1 + ⌊X⌋ + 1 - (p0.1 - ⌊X⌋)) = 2 * ⌊X⌋ + 1 := by ring
      rw [e] at h2
      have : ((2 * ⌊X⌋ + 1).toNat : ℤ) = 2 * ⌊X⌋ + 1 := Int.toNat_of_nonneg (by omega)
      omega
    have h1' : (S.card : ℤ) ≤ 5 * ((S.image Prod.fst).card : ℤ) := by exact_mod_cast h1
    linarith
  have h4 : (S.card : ℝ) ≤ 5 * (2 * (⌊X⌋ : ℝ) + 1) := by exact_mod_cast h3
  have h5 : (⌊X⌋ : ℝ) ≤ X := Int.floor_le X
  linarith

attribute [local instance 10] Classical.propDecidable

/-- the unit segment from `(a0,a1)` in direction `θ` meets the cell `q` -/
def meets (δ a0 a1 θ : ℝ) (q : ℤ × ℤ) : Prop :=
  ∃ t ∈ Set.Icc (0:ℝ) 1, cell δ (a0 + t * cos θ) (a1 + t * sin θ) = q

lemma single_count (Q : Finset (ℤ × ℤ)) {δ a0 a1 θ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ((Q.filter (meets δ a0 a1 θ)).card : ℝ) ≤ 5 * (2 / δ + 3) := by
  have := card_grid (Q.filter (meets δ a0 a1 θ)) (1 / δ + 1) (by positivity) ?_ ?_
  · calc _ ≤ (2 * (1 / δ + 1) + 1) * 5 := this
      _ = 5 * (2 / δ + 3) := by ring
  · intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    obtain ⟨t1, ht1, rfl⟩ := hp.2
    obtain ⟨t2, ht2, rfl⟩ := hq.2
    have hc := col_bound (a0 := a0) (a1 := a1) (t1 := t1) (t2 := t2) hδ h0 h1
    have ht : |t1 - t2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
    have : |t1 - t2| / δ ≤ 1 / δ := div_le_div_of_nonneg_right ht hδ.le
    linarith
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    obtain ⟨t1, ht1, rfl⟩ := hp.2
    obtain ⟨t2, ht2, rfl⟩ := hq.2
    exact row_bound hδ h0 h1 hpq

lemma pair_count (Q : Finset (ℤ × ℤ)) {δ a0 a1 θ b0 b1 θ' : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hs : 0 < |sin (θ' - θ)|) :
    ((Q.filter (fun q => meets δ a0 a1 θ q ∧ meets δ b0 b1 θ' q)).card : ℝ)
      ≤ 5 * (8 / |sin (θ' - θ)| + 3) := by
  have := card_grid (Q.filter (fun q => meets δ a0 a1 θ q ∧ meets δ b0 b1 θ' q))
    (4 / |sin (θ' - θ)| + 1) (by positivity) ?_ ?_
  · calc _ ≤ (2 * (4 / |sin (θ' - θ)| + 1) + 1) * 5 := this
      _ = 5 * (8 / |sin (θ' - θ)| + 3) := by ring
  · intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    obtain ⟨⟨t1, ht1, rfl⟩, ⟨s1, hs1, e1⟩⟩ := hp.2
    obtain ⟨⟨t2, ht2, rfl⟩, ⟨s2, hs2, e2⟩⟩ := hq.2
    have hc := col_bound (a0 := a0) (a1 := a1) (t1 := t1) (t2 := t2) hδ h0 h1
    have hpp := pair_param (a0 := a0) (a1 := a1) (θ := θ) hδ e1.symm e2.symm
    have : |t1 - t2| / δ < 4 / |sin (θ' - θ)| := by
      rw [div_lt_div_iff₀ hδ hs]; linarith
    linarith
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    obtain ⟨⟨t1, ht1, rfl⟩, -⟩ := hp.2
    obtain ⟨⟨t2, ht2, rfl⟩, -⟩ := hq.2
    exact row_bound hδ h0 h1 hpq

lemma sin_abs_ge {x : ℝ} (hx : |x| ≤ 1) : |x| / 2 ≤ |sin x| := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y / 2 ≤ sin y := by
    intro y hy0 hy1
    have h := Real.mul_le_sin hy0 (by linarith)
    have : y / 2 ≤ 2 / π * y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    have := key x h hx
    linarith [le_abs_self (sin x)]
  · rw [abs_of_nonpos h] at hx ⊢
    have := key (-x) (by linarith) hx
    rw [Real.sin_neg] at this
    linarith [neg_le_abs (sin x)]

lemma inv_dist_sum (K m : ℕ) (hm : m ≤ K) :
    ∑ m' ∈ (Finset.range (K + 1)).filter (fun m' => m' ≠ m), 1 / |(m:ℝ) - m'|
      ≤ 2 * (1 + Real.log K) := by
  let g : ℕ → ℕ := fun m' => if m' ≤ m then m - m' else m' - m
  have hdist : ∀ m' : ℕ, |(m:ℝ) - m'| = (g m' : ℝ) := by
    intro m'
    simp only [g]
    split_ifs with h
    · rw [Nat.cast_sub h]
      exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))
    · replace h := not_le.mp h
      rw [Nat.cast_sub h.le, abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h.le))
  set s := (Finset.range (K + 1)).filter (fun m' => m' ≠ m) with hs
  have hmaps : ∀ m' ∈ s, g m' ∈ Finset.Icc 1 K := by
    intro m' hm'
    rw [hs, Finset.mem_filter, Finset.mem_range] at hm'
    rw [Finset.mem_Icc]
    simp only [g]
    split_ifs with h <;> omega
  rw [Finset.sum_congr rfl (fun m' _ => by rw [hdist m'])]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.Icc 1 K,
      ∑ i ∈ s.filter (fun i => g i = j), 1 / (g i : ℝ) ≤ 2 * (1 / (j:ℝ)) := by
    intro j hj
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hsub : s.filter (fun i => g i = j) ⊆ {m - j, m + j} := by
      intro i hi
      rw [Finset.mem_filter] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have := hi.2
      simp only [g] at this
      split_ifs at this with h <;> omega
    have h2 : (s.filter (fun i => g i = j)).card ≤ 2 :=
      (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
    exact_mod_cast h2
  calc ∑ j ∈ Finset.Icc 1 K, ∑ i ∈ s.filter (fun i => g i = j), 1 / (g i : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 K, 2 * (1 / (j:ℝ)) := Finset.sum_le_sum hfib
    _ = 2 * ((harmonic K : ℚ) : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 2 * (1 + Real.log K) := by linarith [harmonic_le_one_add_log K]

lemma double_count {ι : Type*} (D : Finset ι) (Q : Finset (ℤ × ℤ)) (P : ι → ℤ × ℤ → Prop) :
    (∑ m ∈ D, ((Q.filter (P m)).card : ℝ)) ^ 2 ≤
      (Q.card : ℝ) * ∑ m ∈ D, ∑ m' ∈ D, ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) := by
  have hL : ∑ m ∈ D, ((Q.filter (P m)).card : ℝ)
      = ∑ q ∈ Q, ∑ m ∈ D, (if P m q then (1:ℝ) else 0) := by
    calc ∑ m ∈ D, ((Q.filter (P m)).card : ℝ)
        = ∑ m ∈ D, ∑ q ∈ Q, (if P m q then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_); rw [Finset.sum_boole]
      _ = ∑ q ∈ Q, ∑ m ∈ D, (if P m q then (1:ℝ) else 0) := Finset.sum_comm
  have hR : ∑ q ∈ Q, (∑ m ∈ D, (if P m q then (1:ℝ) else 0)) ^ 2
      = ∑ m ∈ D, ∑ m' ∈ D, ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) := by
    have e : ∀ q, (∑ m ∈ D, (if P m q then (1:ℝ) else 0)) ^ 2
        = ∑ m ∈ D, ∑ m' ∈ D, (if P m q ∧ P m' q then (1:ℝ) else 0) := by
      intro q
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
      by_cases h1 : P m q <;> by_cases h2 : P m' q <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun q _ => e q), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [Finset.sum_boole]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Q (fun _ => (1:ℝ))
    (fun q => ∑ m ∈ D, (if P m q then (1:ℝ) else 0))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hL, ← hR]
  exact hcs

/-- far pairs of directions: few common cells -/
lemma far_pair (Q : Finset (ℤ × ℤ)) (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (hKδ : (K : ℝ) * δ ≤ 1)
    {m m' : ℕ} (hm : m ≤ K) (hm' : m' ≤ K) (hfar : m' + 2 ≤ m ∨ m + 2 ≤ m')
    {θ θ' a0 a1 b0 b1 : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1)
    (hsep : (|(m:ℝ) - m'| - 1) * δ ≤ |θ - θ'|) :
    ((Q.filter (fun q => meets δ a0 a1 θ q ∧ meets δ b0 b1 θ' q)).card : ℝ)
      ≤ 175 / δ * (1 / |(m:ℝ) - m'|) := by
  set dm := |(m:ℝ) - m'| with hdm
  have hdm2 : 2 ≤ dm := by
    rw [hdm]
    rcases hfar with h | h
    · have : ((m' : ℝ) + 2 ≤ m) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : ((m : ℝ) + 2 ≤ m') := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have hdmK : dm ≤ K := by
    rw [hdm, abs_sub_le_iff]
    have a : (m:ℝ) ≤ K := by exact_mod_cast hm
    have b : (m':ℝ) ≤ K := by exact_mod_cast hm'
    have c : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have d : (0:ℝ) ≤ m' := Nat.cast_nonneg m'
    constructor <;> linarith
  have hdmδ : dm * δ ≤ 1 := by nlinarith
  have hpos : 0 < dm * δ := by positivity
  have hφ1 : |θ' - θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hφ2 : dm * δ / 2 ≤ |θ' - θ| := by
    rw [abs_sub_comm]; nlinarith
  have hsin := sin_abs_ge hφ1
  have hs4 : dm * δ / 4 ≤ |sin (θ' - θ)| := by linarith
  have hs : 0 < |sin (θ' - θ)| := by linarith
  have hc := pair_count Q (a0 := a0) (a1 := a1) (b0 := b0) (b1 := b1) hδ h0 h1 hs
  have e1 : 8 / |sin (θ' - θ)| ≤ 32 / (dm * δ) := by
    rw [div_le_div_iff₀ hs hpos]; linarith
  have e2 : (3:ℝ) ≤ 3 / (dm * δ) := by
    rw [le_div_iff₀ hpos]; linarith
  have e3 : 175 / δ * (1 / dm) = 5 * (32 / (dm * δ) + 3 / (dm * δ)) := by
    field_simp; ring
  rw [e3]
  linarith

/-- the combinatorial Córdoba estimate at one scale -/
lemma scale_lemma (D : Finset ℕ) (K : ℕ) (hD : D ⊆ Finset.range (K + 1)) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hKδ : (K : ℝ) * δ ≤ 1) (θ a0 a1 : ℕ → ℝ) (hθ : ∀ m ∈ D, 0 ≤ θ m ∧ θ m ≤ 1)
    (hsep : ∀ m ∈ D, ∀ m' ∈ D, (|(m:ℝ) - m'| - 1) * δ ≤ |θ m - θ m'|)
    (Q : Finset (ℤ × ℤ)) (w : ℝ) (hw0 : 0 ≤ w)
    (hw : ∀ m ∈ D, w ≤ 2 * δ * ((Q.filter (meets δ (a0 m) (a1 m) (θ m))).card : ℝ)) :
    (D.card : ℝ) * w ^ 2 ≤ 1700 * Q.card * δ * (1 + Real.log K) := by
  set P : ℕ → ℤ × ℤ → Prop := fun m q => meets δ (a0 m) (a1 m) (θ m) q with hP
  set L := 1 + Real.log K with hL
  have hlog : 0 ≤ Real.log K := Real.log_natCast_nonneg K
  have hmK : ∀ m ∈ D, m ≤ K := fun m hm => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hD hm))
  have hrow : ∀ m ∈ D, ∑ m' ∈ D, ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) ≤ 425 * L / δ := by
    intro m hm
    rw [← Finset.sum_filter_add_sum_filter_not D (fun m' => m' + 2 ≤ m ∨ m + 2 ≤ m')]
    have hfar : ∑ m' ∈ D.filter (fun m' => m' + 2 ≤ m ∨ m + 2 ≤ m'),
        ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) ≤ 175 / δ * (2 * L) := by
      calc ∑ m' ∈ D.filter (fun m' => m' + 2 ≤ m ∨ m + 2 ≤ m'),
            ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ)
          ≤ ∑ m' ∈ D.filter (fun m' => m' + 2 ≤ m ∨ m + 2 ≤ m'), 175 / δ * (1 / |(m:ℝ) - m'|) := by
            apply Finset.sum_le_sum
            intro m' hm'
            rw [Finset.mem_filter] at hm'
            exact far_pair Q K hδ hKδ (hmK m hm) (hmK m' hm'.1) hm'.2 (hθ m hm).1 (hθ m hm).2
              (hθ m' hm'.1).1 (hθ m' hm'.1).2 (hsep m hm m' hm'.1)
        _ = 175 / δ * ∑ m' ∈ D.filter (fun m' => m' + 2 ≤ m ∨ m + 2 ≤ m'), 1 / |(m:ℝ) - m'| := by
            rw [Finset.mul_sum]
        _ ≤ 175 / δ * ∑ m' ∈ (Finset.range (K + 1)).filter (fun m' => m' ≠ m), 1 / |(m:ℝ) - m'| := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m' hm'
              rw [Finset.mem_filter] at hm' ⊢
              exact ⟨hD hm'.1, by omega⟩
            · intro _ _ _; positivity
        _ ≤ 175 / δ * (2 * L) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact inv_dist_sum K m (hmK m hm)
    have hnear : ∑ m' ∈ D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m')),
        ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) ≤ 3 * (25 / δ) := by
      have hone : ∀ m' ∈ D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m')),
          ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) ≤ 25 / δ := by
        intro m' _
        have h1 : (Q.filter (fun q => P m q ∧ P m' q)).card ≤ (Q.filter (P m)).card :=
          Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩)
        have h2 := single_count Q (a0 := a0 m) (a1 := a1 m) hδ (hθ m hm).1 (hθ m hm).2
        have h3 : 5 * (2 / δ + 3) ≤ 25 / δ := by
          rw [show (25:ℝ) / δ = 5 * (2 / δ + 3 / δ) by ring]
          have : (3:ℝ) ≤ 3 / δ := by rw [le_div_iff₀ hδ]; linarith
          linarith
        have h1' : ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ) ≤ (Q.filter (P m)).card := by
          exact_mod_cast h1
        exact le_trans h1' (le_trans h2 h3)
      have hcard : (D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m'))).card ≤ 3 := by
        have hsub : D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m')) ⊆ Finset.Icc (m - 1) (m + 1) := by
          intro m' hm'
          rw [Finset.mem_filter] at hm'
          rw [Finset.mem_Icc]
          omega
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        omega
      calc _ ≤ ∑ m' ∈ D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m')), 25 / δ := Finset.sum_le_sum hone
        _ = (D.filter (fun m' => ¬ (m' + 2 ≤ m ∨ m + 2 ≤ m'))).card * (25 / δ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (25 / δ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
    have hfin : 175 / δ * (2 * L) + 3 * (25 / δ) ≤ 425 * L / δ := by
      have : 175 / δ * (2 * L) + 3 * (25 / δ) = (350 * L + 75) / δ := by field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hδ.le
      linarith
    linarith
  have hT : ∑ m ∈ D, ∑ m' ∈ D, ((Q.filter (fun q => P m q ∧ P m' q)).card : ℝ)
      ≤ D.card * (425 * L / δ) := by
    calc _ ≤ ∑ m ∈ D, 425 * L / δ := Finset.sum_le_sum hrow
      _ = D.card * (425 * L / δ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlow : (D.card : ℝ) * (w / (2 * δ)) ≤ ∑ m ∈ D, ((Q.filter (P m)).card : ℝ) := by
    calc (D.card : ℝ) * (w / (2 * δ)) = ∑ m ∈ D, w / (2 * δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ D, ((Q.filter (P m)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [div_le_iff₀ (by positivity)]
          have := hw m hm
          linarith
  have hcs := double_count D Q P
  have hlow0 : 0 ≤ (D.card : ℝ) * (w / (2 * δ)) := by positivity
  have h : ((D.card : ℝ) * (w / (2 * δ))) ^ 2 ≤ Q.card * (D.card * (425 * L / δ)) := by
    calc ((D.card : ℝ) * (w / (2 * δ))) ^ 2 ≤ (∑ m ∈ D, ((Q.filter (P m)).card : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hlow0 hlow 2
      _ ≤ _ := hcs
      _ ≤ Q.card * (D.card * (425 * L / δ)) := mul_le_mul_of_nonneg_left hT (by positivity)
  rcases Nat.eq_zero_or_pos D.card with hc | hc
  · rw [hc]; simp only [Nat.cast_zero, zero_mul]; positivity
  have hc' : (0:ℝ) < D.card := by exact_mod_cast hc
  have e1 : ((D.card : ℝ) * w ^ 2) * D.card = ((D.card : ℝ) * (w / (2 * δ))) ^ 2 * (4 * δ ^ 2) := by
    field_simp; ring
  have e2 : (1700 * Q.card * δ * L) * (D.card : ℝ) = (Q.card * (D.card * (425 * L / δ))) * (4 * δ ^ 2) := by
    field_simp; ring
  have h4 : ((D.card : ℝ) * w ^ 2) * D.card ≤ (1700 * Q.card * δ * L) * D.card := by
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right h (by positivity)
  exact le_of_mul_le_mul_right h4 hc'

lemma exists_level {d : ℝ} (h0 : 0 < d) (h1 : d ≤ 1) :
    ∃ k : ℕ, (1/2:ℝ) ^ (k + 1) < d ∧ d ≤ (1/2:ℝ) ^ k := by
  have hex : ∃ n : ℕ, (1/2:ℝ) ^ n < d := exists_pow_lt_of_lt_one h0 (by norm_num)
  have hN : (1/2:ℝ) ^ (Nat.find hex) < d := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h; rw [h, pow_zero] at hN; linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]; exact hN
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    exact not_lt.mp this

lemma coord_le_dist (p q : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |p.ofLp i - q.ofLp i| ≤ dist p q := by
  rw [EuclideanSpace.dist_eq]
  apply Real.abs_le_sqrt
  have := Finset.single_le_sum (f := fun j => dist (p.ofLp j) (q.ofLp j) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)
  simpa [Real.dist_eq, sq_abs] using this

/-- the 3 × 3 block of cells around `c` -/
noncomputable def nbr (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-1:ℤ) 1 ×ˢ Finset.Icc (-1:ℤ) 1).image (fun e => (c.1 + e.1, c.2 + e.2))

lemma nbr_card (c : ℤ × ℤ) : (nbr c).card ≤ 9 := by
  unfold nbr
  exact (Finset.card_image_le).trans (by rw [Finset.card_product, Int.card_Icc]; decide)

lemma floor_near {δ x y : ℝ} (hδ : 0 < δ) (h : |y - x| ≤ δ) :
    ⌊y / δ⌋ - ⌊x / δ⌋ ∈ Finset.Icc (-1:ℤ) 1 := by
  rw [Finset.mem_Icc]
  have h1 := floor_diff_lt (x := y) (y := x) hδ
  have h2 := floor_diff_lt (x := x) (y := y) hδ
  rw [abs_le] at h
  have a1 : (y - x) / δ ≤ 1 := by rw [div_le_one hδ]; linarith
  have a2 : (x - y) / δ ≤ 1 := by rw [div_le_one hδ]; linarith
  have b1 : ((⌊y / δ⌋ - ⌊x / δ⌋ : ℤ) : ℝ) < 2 := by linarith
  have b2 : ((⌊x / δ⌋ - ⌊y / δ⌋ : ℤ) : ℝ) < 2 := by linarith
  have c1 : (⌊y / δ⌋ - ⌊x / δ⌋ : ℤ) < 2 := by exact_mod_cast b1
  have c2 : (⌊x / δ⌋ - ⌊y / δ⌋ : ℤ) < 2 := by exact_mod_cast b2
  constructor <;> omega

lemma cell_mem_nbr {δ x0 x1 y0 y1 : ℝ} (hδ : 0 < δ) (h0 : |y0 - x0| ≤ δ) (h1 : |y1 - x1| ≤ δ) :
    cell δ y0 y1 ∈ nbr (cell δ x0 x1) := by
  unfold nbr cell
  rw [Finset.mem_image]
  refine ⟨(⌊y0 / δ⌋ - ⌊x0 / δ⌋, ⌊y1 / δ⌋ - ⌊x1 / δ⌋),
    Finset.mem_product.mpr ⟨floor_near hδ h0, floor_near hδ h1⟩, ?_⟩
  simp

lemma cos_add_sin_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : 1 ≤ cos θ + sin θ := by
  have hc := cos_gt_half h0 h1
  have hs0 : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three])
  have hc1 := Real.cos_le_one θ
  have hs1 := Real.sin_le_one θ
  have := Real.cos_sq_add_sin_sq θ
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ cos θ) (by linarith : 0 ≤ 1 - cos θ),
    mul_nonneg hs0 (by linarith : 0 ≤ 1 - sin θ)]

lemma vol_param_cell {δ a0 a1 θ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℤ × ℤ) :
    MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ cell δ (a0 + t * cos θ) (a1 + t * sin θ) = q}
      ≤ ENNReal.ofReal (2 * δ) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le ?_)
  intro t ht t' ht'
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have e := ht.2.trans ht'.2.symm
  simp only [cell, Prod.mk.injEq] at e
  have hx := floor_close hδ e.1
  have hy := floor_close hδ e.2
  have ex : a0 + t * cos θ - (a0 + t' * cos θ) = (t - t') * cos θ := by ring
  have ey : a1 + t * sin θ - (a1 + t' * sin θ) = (t - t') * sin θ := by ring
  rw [ex, abs_mul] at hx
  rw [ey, abs_mul] at hy
  have hcs := cos_add_sin_ge h0 h1
  have hc0 : 0 ≤ cos θ := by linarith [cos_gt_half h0 h1]
  have hs0 : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three])
  rw [abs_of_nonneg hc0] at hx
  rw [abs_of_nonneg hs0] at hy
  have : |t - t'| ≤ |t - t'| * cos θ + |t - t'| * sin θ := by
    nlinarith [abs_nonneg (t - t')]
  linarith

lemma vol_floor_set {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ ⌊θ / δ⌋₊ = m} ≤ ENNReal.ofReal δ := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le ?_)
  intro θ hθ θ' hθ'
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have a := Nat.floor_le (div_nonneg hθ.1.1 hδ.le)
  have b := Nat.lt_floor_add_one (θ / δ)
  have c := Nat.floor_le (div_nonneg hθ'.1.1 hδ.le)
  have d := Nat.lt_floor_add_one (θ' / δ)
  rw [hθ.2] at a b
  rw [hθ'.2] at c d
  have : |θ / δ - θ' / δ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have e : θ / δ - θ' / δ = (θ - θ') / δ := by ring
  rw [e, abs_div, abs_of_pos hδ, div_le_one hδ] at this
  exact this

lemma sep_of_floor {δ θ θ' : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ θ) (h0' : 0 ≤ θ') :
    (|((⌊θ / δ⌋₊ : ℕ) : ℝ) - (⌊θ' / δ⌋₊ : ℕ)| - 1) * δ ≤ |θ - θ'| := by
  have a := Nat.floor_le (div_nonneg h0 hδ.le)
  have b := Nat.lt_floor_add_one (θ / δ)
  have c := Nat.floor_le (div_nonneg h0' hδ.le)
  have d := Nat.lt_floor_add_one (θ' / δ)
  have h : |((⌊θ / δ⌋₊ : ℕ) : ℝ) - (⌊θ' / δ⌋₊ : ℕ)| ≤ |θ / δ - θ' / δ| + 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self (θ / δ - θ' / δ), neg_le_abs (θ / δ - θ' / δ)]
  have e : θ / δ - θ' / δ = (θ - θ') / δ := by ring
  rw [e, abs_div, abs_of_pos hδ] at h
  have : (|((⌊θ / δ⌋₊ : ℕ) : ℝ) - (⌊θ' / δ⌋₊ : ℕ)| - 1) ≤ |θ - θ'| / δ := by linarith
  rwa [le_div_iff₀ hδ] at this

lemma pick_level {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (μ : ℕ → ENNReal) (h : 1 ≤ ∑' k, μ k) :
    ∃ k, ENNReal.ofReal ((1 - ρ) / 4 * ρ ^ k) ≤ μ k := by
  by_contra hne
  simp only [not_exists, not_le] at hne
  have hnn : ∀ k : ℕ, 0 ≤ (1 - ρ) / 4 * ρ ^ k :=
    fun k => mul_nonneg (div_nonneg (by linarith) (by norm_num)) (pow_nonneg h0 k)
  have hs : Summable (fun k : ℕ => (1 - ρ) / 4 * ρ ^ k) :=
    (summable_geometric_of_lt_one h0 h1).mul_left _
  have hne1 : (1:ℝ) - ρ ≠ 0 := (sub_pos.mpr h1).ne'
  have hsum : ∑' k : ℕ, (1 - ρ) / 4 * ρ ^ k = 1 / 4 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]; field_simp
  have hle : ∑' k, μ k ≤ ∑' k : ℕ, ENNReal.ofReal ((1 - ρ) / 4 * ρ ^ k) :=
    ENNReal.tsum_le_tsum (fun k => (hne k).le)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs, hsum] at hle
  have h2 : (1:ENNReal) ≤ ENNReal.ofReal (1 / 4) := h.trans hle
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2

lemma growth {γ r c : ℝ} (hγ : 0 < γ) (hr : γ < r) (hc : 0 < c) :
    ∃ c0 > 0, ∀ k : ℕ, c0 * γ ^ k * (1 + k) < c * r ^ k := by
  set R := r / γ with hR
  have hR1 : 1 < R := by rw [hR, lt_div_iff₀ hγ]; linarith
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hR1
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  have hB' : ∀ k : ℕ, (k:ℝ) ≤ B * R ^ k := by
    intro k
    have := hB (Set.mem_range_self k)
    simp only [pow_one] at this
    rwa [div_le_iff₀ (pow_pos (by linarith) k)] at this
  have hB0 : 0 ≤ B := by
    have := hB' 0; simpa using this
  refine ⟨c / (2 * (1 + B)), div_pos hc (by linarith), fun k => ?_⟩
  have hRk : 1 ≤ R ^ k := one_le_pow₀ hR1.le
  have h1 : (1 + (k:ℝ)) ≤ (1 + B) * R ^ k := by
    rw [add_mul, one_mul]; linarith [hB' k]
  have hγk : 0 < γ ^ k := pow_pos hγ k
  have e : γ ^ k * R ^ k = r ^ k := by
    rw [← mul_pow, hR]; congr 1; field_simp
  calc c / (2 * (1 + B)) * γ ^ k * (1 + k) ≤ c / (2 * (1 + B)) * γ ^ k * ((1 + B) * R ^ k) := by
        apply mul_le_mul_of_nonneg_left h1
        exact mul_nonneg (div_nonneg hc.le (by linarith)) hγk.le
    _ = c / 2 * (γ ^ k * R ^ k) := by field_simp
    _ = c / 2 * r ^ k := by rw [e]
    _ < c * r ^ k := by have := mul_pos hc (pow_pos (hγ.trans hr) k); linarith

noncomputable def dir (θ : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![cos θ, sin θ]

lemma dir_ofLp0 (θ : ℝ) : (dir θ).ofLp 0 = cos θ := by simp [dir]
lemma dir_ofLp1 (θ : ℝ) : (dir θ).ofLp 1 = sin θ := by simp [dir]

lemma norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, dir_ofLp0, dir_ofLp1]
  simp [Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]

lemma seg_point (a : EuclideanSpace ℝ (Fin 2)) (θ t : ℝ) :
    (AffineMap.lineMap a (a + dir θ) t).ofLp 0 = a.ofLp 0 + t * cos θ ∧
    (AffineMap.lineMap a (a + dir θ) t).ofLp 1 = a.ofLp 1 + t * sin θ := by
  rw [AffineMap.lineMap_apply_module]
  (constructor <;> simp [dir]) <;> ring

lemma rpow_pow_half (s : ℝ) (k : ℕ) : ((1/2:ℝ) ^ (k + 1)) ^ s = ((1/2:ℝ) ^ s) ^ (k + 1) := by
  rw [← Real.rpow_natCast ((1/2:ℝ) ^ s), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ← Real.rpow_natCast (1/2:ℝ), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1; ring

lemma level_finite (s : ℝ) (hs0 : 0 ≤ s) (T : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (c0 : ℝ)
    (hlt : ∑' n, ⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s < ENNReal.ofReal c0) (k : ℕ) :
    ∃ F : Finset ℕ, (∀ n, n ∈ F ↔ ((T n).Nonempty ∧ ENNReal.ofReal ((1/2:ℝ)^(k+1)) < Metric.ediam (T n) ∧
        Metric.ediam (T n) ≤ ENNReal.ofReal ((1/2:ℝ)^k))) ∧
      (F.card : ℝ) * ((1/2:ℝ)^s)^(k+1) < c0 := by
  have hne : ∑' n, (⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s) ≠ ⊤ := ne_top_of_lt hlt
  have hσ : 0 < ((1/2:ℝ)^s)^(k+1) := pow_pos (Real.rpow_pos_of_pos (by norm_num) s) _
  have hε : ENNReal.ofReal (((1/2:ℝ)^s)^(k+1)) ≠ 0 := (ENNReal.ofReal_pos.mpr hσ).ne'
  have hfin := ENNReal.finite_const_le_of_tsum_ne_top hne hε
  have key : ∀ n, ((T n).Nonempty ∧ ENNReal.ofReal ((1/2:ℝ)^(k+1)) < Metric.ediam (T n) ∧
        Metric.ediam (T n) ≤ ENNReal.ofReal ((1/2:ℝ)^k)) →
      ENNReal.ofReal (((1/2:ℝ)^s)^(k+1)) ≤ ⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s := by
    rintro n ⟨hn, hlo, -⟩
    rw [iSup_pos hn, ← rpow_pow_half, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0]
    exact ENNReal.rpow_le_rpow hlo.le hs0
  have hfin2 : {n | (T n).Nonempty ∧ ENNReal.ofReal ((1/2:ℝ)^(k+1)) < Metric.ediam (T n) ∧
        Metric.ediam (T n) ≤ ENNReal.ofReal ((1/2:ℝ)^k)}.Finite := hfin.subset (fun n hn => key n hn)
  refine ⟨hfin2.toFinset, fun n => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq], ?_⟩
  have hsum : ∑ n ∈ hfin2.toFinset, ENNReal.ofReal (((1/2:ℝ)^s)^(k+1)) < ENNReal.ofReal c0 := by
    calc ∑ n ∈ hfin2.toFinset, ENNReal.ofReal (((1/2:ℝ)^s)^(k+1))
        ≤ ∑ n ∈ hfin2.toFinset, ⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s :=
          Finset.sum_le_sum (fun n hn => key n ((Set.Finite.mem_toFinset hfin2).mp hn))
      _ ≤ ∑' n, ⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s := ENNReal.sum_le_tsum _
      _ < ENNReal.ofReal c0 := hlt
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hsum
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hsum

lemma final_ineq {w Dc δ Qc Fc σ c1 : ℝ} {k : ℕ} (hw : 0 < w) (hD : w ≤ Dc * δ)
    (hs : Dc * w ^ 2 ≤ 1700 * Qc * δ * (1 + k)) (hQ0 : 0 ≤ Qc) (hQ : Qc ≤ 9 * Fc) (hF0 : 0 ≤ Fc)
    (hF : Fc * σ ^ (k + 1) < c1 / 61200) (hδ : δ = (1/2:ℝ)^k) (hσ : 1/4 < σ) :
    w ^ 3 < c1 * (1 / (4 * σ)) ^ k * (1 + k) := by
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hσ0 : 0 < σ := by linarith
  have hσk : 0 < σ ^ k := pow_pos hσ0 k
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hδ2 : δ ^ 2 = (1/4:ℝ)^k := by rw [hδ, ← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : w ^ 3 ≤ 15300 * Fc * (1/4:ℝ)^k * (1 + k) := by
    have a1 : w ^ 3 ≤ (Dc * δ) * w ^ 2 := by
      have : w ^ 3 = w * w ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hD (by positivity)
    have a3 : δ * (Dc * w ^ 2) ≤ δ * (1700 * Qc * δ * (1 + k)) := mul_le_mul_of_nonneg_left hs hδ0.le
    have hpos : 0 ≤ δ ^ 2 * (1 + k) := by positivity
    have a4 := mul_le_mul_of_nonneg_right hQ hpos
    have e : (Dc * δ) * w ^ 2 = δ * (Dc * w ^ 2) := by ring
    have e' : δ * (1700 * Qc * δ * (1 + k)) = 1700 * (Qc * (δ ^ 2 * (1 + k))) := by ring
    have e'' : 15300 * Fc * (1/4:ℝ)^k * (1 + k) = 1700 * (9 * Fc * (δ ^ 2 * (1 + k))) := by
      rw [hδ2]; ring
    rw [e''] ; nlinarith
  have h2 : 15300 * (Fc * σ ^ k) < c1 := by
    have e : Fc * σ ^ (k + 1) = (Fc * σ ^ k) * σ := by ring
    rw [e] at hF
    have : (Fc * σ ^ k) * (1/4) ≤ (Fc * σ ^ k) * σ := mul_le_mul_of_nonneg_left hσ.le (by positivity)
    linarith
  have e3 : (1 / (4 * σ)) ^ k * σ ^ k = (1/4:ℝ) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hX : 0 < (1/4:ℝ)^k * (1 + k) := by positivity
  have h3 : 15300 * Fc * (1/4:ℝ)^k * (1 + k) * σ ^ k < c1 * (1 / (4 * σ)) ^ k * (1 + k) * σ ^ k := by
    have l : 15300 * Fc * (1/4:ℝ)^k * (1 + k) * σ ^ k = (15300 * (Fc * σ ^ k)) * ((1/4:ℝ)^k * (1 + k)) := by
      ring
    have r : c1 * (1 / (4 * σ)) ^ k * (1 + k) * σ ^ k = c1 * ((1/4:ℝ)^k * (1 + k)) := by
      rw [← e3]; ring
    rw [l, r]
    exact mul_lt_mul_of_pos_right h2 hX
  have h4 := lt_of_mul_lt_mul_right h3 hσk.le
  linarith

lemma log_two_pow_le (k : ℕ) : Real.log ((2 ^ k : ℕ) : ℝ) ≤ k := by
  push_cast
  rw [Real.log_pow]
  have := Real.log_two_lt_d9
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- every countable cover of a planar Kakeya set by sets of diameter ≤ 1 has `s`-sum ≥ c0 -/
theorem hausdorff_pos (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s < 2) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ S : Set (EuclideanSpace ℝ (Fin 2)), FCP.Kakeya.IsKakeya S →
      ∀ T : ℕ → Set (EuclideanSpace ℝ (Fin 2)), S ⊆ ⋃ n, T n → (∀ n, Metric.ediam (T n) ≤ 1) →
        ENNReal.ofReal c0 ≤ ∑' n, ⨆ (_ : (T n).Nonempty), Metric.ediam (T n) ^ s := by
  set σ : ℝ := (1/2:ℝ) ^ s with hσdef
  have hσ4 : 1/4 < σ := by
    have := Real.rpow_lt_rpow_of_exponent_gt (x := (1/2:ℝ)) (by norm_num) (by norm_num) hs2
    rw [show ((1/2:ℝ) ^ (2:ℝ)) = 1/4 by rw [Real.rpow_two]; norm_num] at this
    exact this
  set γ : ℝ := 1 / (4 * σ) with hγdef
  have hγ0 : 0 < γ := div_pos one_pos (by linarith)
  have hγ1 : γ < 1 := by rw [hγdef, div_lt_one (by linarith)]; linarith
  set ρ : ℝ := 1 - (1 - γ) / 6 with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hρ3 : γ < ρ ^ 3 := by
    have h := one_add_mul_le_pow (a := -((1 - γ) / 6)) (by linarith) 3
    have e : (1 + -((1 - γ) / 6)) = ρ := by rw [hρdef]; ring
    rw [e] at h; push_cast at h; linarith
  set c : ℝ := ((1 - ρ) / 4) ^ 3 with hcdef
  have hc : 0 < c := pow_pos (div_pos (by linarith) (by norm_num)) 3
  obtain ⟨c1, hc1, hgrow⟩ := growth hγ0 hρ3 hc
  refine ⟨c1 / 61200, div_pos hc1 (by norm_num), ?_⟩
  intro S hS T hcov hdiam
  by_contra hlt
  rw [not_le] at hlt
  have hF := fun k => level_finite s hs0 T (c1 / 61200) hlt k
  choose F hFmem hFcard using hF
  have hx : ∀ n, ∃ x : EuclideanSpace ℝ (Fin 2), (T n).Nonempty → x ∈ T n := fun n => by
    by_cases h : (T n).Nonempty
    · exact ⟨h.some, fun _ => h.some_mem⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose x hxmem using hx
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → Finset (ℤ × ℤ), ∀ k, Q k =
      (F k).biUnion (fun n => nbr (cell ((1/2:ℝ)^k) ((x n).ofLp 0) ((x n).ofLp 1))) := ⟨_, fun _ => rfl⟩
  have hQcard : ∀ k, ((Q k).card : ℝ) ≤ 9 * (F k).card := by
    intro k
    rw [hQ]
    have h1 := Finset.card_biUnion_le (s := F k)
      (t := fun n => nbr (cell ((1/2:ℝ)^k) ((x n).ofLp 0) ((x n).ofLp 1)))
    have h2 : ∑ n ∈ F k, (nbr (cell ((1/2:ℝ)^k) ((x n).ofLp 0) ((x n).ofLp 1))).card ≤ ∑ n ∈ F k, 9 :=
      Finset.sum_le_sum (fun n _ => nbr_card _)
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 := h1.trans h2
    have h4 : (((F k).biUnion (fun n => nbr (cell ((1/2:ℝ)^k) ((x n).ofLp 0) ((x n).ofLp 1)))).card : ℝ)
        ≤ (F k).card * 9 := by exact_mod_cast h3
    linarith
  have hQcell : ∀ k n, n ∈ F k → ∀ y ∈ T n, cell ((1/2:ℝ)^k) (y.ofLp 0) (y.ofLp 1) ∈ Q k := by
    intro k n hn y hy
    have hP := (hFmem k n).mp hn
    have hδpos : (0:ℝ) < (1/2:ℝ)^k := by positivity
    have hd : dist y (x n) ≤ (1/2:ℝ)^k := by
      have h1 : edist y (x n) ≤ Metric.ediam (T n) := Metric.edist_le_ediam_of_mem hy (hxmem n hP.1)
      have h2 := h1.trans hP.2.2
      rw [edist_dist] at h2
      exact (ENNReal.ofReal_le_ofReal_iff hδpos.le).mp h2
    rw [hQ, Finset.mem_biUnion]
    exact ⟨n, hn, cell_mem_nbr hδpos ((coord_le_dist y (x n) 0).trans hd)
      ((coord_le_dist y (x n) 1).trans hd)⟩
  have ha : ∀ θ : ℝ, ∃ a : EuclideanSpace ℝ (Fin 2), affineSegment ℝ a (a + dir θ) ⊆ S :=
    fun θ => hS (dir θ) (norm_dir θ)
  choose a ha using ha
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℕ → Set ℝ, ∀ θ k, A θ k = {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
      cell ((1/2:ℝ)^k) ((a θ).ofLp 0 + t * cos θ) ((a θ).ofLp 1 + t * sin θ) ∈ Q k} :=
    ⟨_, fun _ _ => rfl⟩
  have hsegsum : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → 1 ≤ ∑' k, MeasureTheory.volume (A θ k) := by
    intro θ h0 h1
    have hcos := cos_gt_half h0 h1
    set Z : Set ℝ := ⋃ n, {t : ℝ | Metric.ediam (T n) = 0 ∧
      AffineMap.lineMap (a θ) (a θ + dir θ) t ∈ T n} with hZ
    have hZ0 : MeasureTheory.volume Z = 0 := by
      apply MeasureTheory.measure_iUnion_null
      intro n
      apply Set.Subsingleton.measure_zero
      intro t ht t' ht'
      have h := Metric.edist_le_ediam_of_mem ht.2 ht'.2
      rw [ht.1, nonpos_iff_eq_zero, edist_eq_zero] at h
      have e0 := congrArg (fun p => p.ofLp 0) h
      simp only at e0
      rw [(seg_point (a θ) θ t).1, (seg_point (a θ) θ t').1] at e0
      have : (t - t') * cos θ = 0 := by rw [sub_mul]; linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    have hsub : Set.Icc (0:ℝ) 1 ⊆ (⋃ k, A θ k) ∪ Z := by
      intro t ht
      have hp : AffineMap.lineMap (a θ) (a θ + dir θ) t ∈ S :=
        ha θ (by unfold affineSegment; exact ⟨t, ht, rfl⟩)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hp)
      by_cases hd0 : Metric.ediam (T n) = 0
      · right; rw [hZ]; exact Set.mem_iUnion.mpr ⟨n, hd0, hn⟩
      · left
        have hne : (T n).Nonempty := ⟨_, hn⟩
        have hdtop : Metric.ediam (T n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hdiam n)
        have hdpos : 0 < (Metric.ediam (T n)).toReal := ENNReal.toReal_pos hd0 hdtop
        have hd1 : (Metric.ediam (T n)).toReal ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top (hdiam n); simpa using this
        obtain ⟨k, hk1, hk2⟩ := exists_level hdpos hd1
        have hmemF : n ∈ F k := by
          rw [hFmem]
          refine ⟨hne, ?_, ?_⟩
          · rw [← ENNReal.ofReal_toReal hdtop]; exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mpr hk1
          · rw [← ENNReal.ofReal_toReal hdtop]; exact ENNReal.ofReal_le_ofReal hk2
        have hc := hQcell k n hmemF _ hn
        rw [(seg_point (a θ) θ t).1, (seg_point (a θ) θ t).2] at hc
        exact Set.mem_iUnion.mpr ⟨k, by rw [hA]; exact ⟨ht, hc⟩⟩
    calc (1 : ENNReal) = MeasureTheory.volume (Set.Icc (0:ℝ) 1) := by simp [Real.volume_Icc]
      _ ≤ MeasureTheory.volume ((⋃ k, A θ k) ∪ Z) := MeasureTheory.measure_mono hsub
      _ ≤ MeasureTheory.volume (⋃ k, A θ k) + MeasureTheory.volume Z := MeasureTheory.measure_union_le _ _
      _ ≤ ∑' k, MeasureTheory.volume (A θ k) := by
          rw [hZ0, add_zero]; exact MeasureTheory.measure_iUnion_le _
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ℕ → Set ℝ, ∀ k, Ω k = {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧
      ENNReal.ofReal ((1 - ρ) / 4 * ρ ^ k) ≤ MeasureTheory.volume (A θ k)} := ⟨_, fun _ => rfl⟩
  have hΩcov : Set.Icc (0:ℝ) 1 ⊆ ⋃ k, Ω k := by
    intro θ hθ
    obtain ⟨k, hk⟩ := pick_level hρ0.le hρ1 _ (hsegsum θ hθ.1 hθ.2)
    exact Set.mem_iUnion.mpr ⟨k, by rw [hΩ]; exact ⟨hθ, hk⟩⟩
  have hΩsum : 1 ≤ ∑' k, MeasureTheory.volume (Ω k) := by
    calc (1 : ENNReal) = MeasureTheory.volume (Set.Icc (0:ℝ) 1) := by simp [Real.volume_Icc]
      _ ≤ MeasureTheory.volume (⋃ k, Ω k) := MeasureTheory.measure_mono hΩcov
      _ ≤ _ := MeasureTheory.measure_iUnion_le _
  obtain ⟨k, hk⟩ := pick_level hρ0.le hρ1 _ hΩsum
  set w : ℝ := (1 - ρ) / 4 * ρ ^ k with hw
  set δ : ℝ := (1/2:ℝ) ^ k with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hKδ : ((2 ^ k : ℕ) : ℝ) * δ = 1 := by rw [hδ]; push_cast; rw [← mul_pow]; norm_num
  have hθex : ∀ m : ℕ, ∃ θ : ℝ, (∃ θ' ∈ Ω k, ⌊θ' / δ⌋₊ = m) → (θ ∈ Ω k ∧ ⌊θ / δ⌋₊ = m) := by
    intro m
    by_cases h : ∃ θ' ∈ Ω k, ⌊θ' / δ⌋₊ = m
    · obtain ⟨θ', h1, h2⟩ := h; exact ⟨θ', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose θm hθm using hθex
  set D := (Finset.range (2 ^ k + 1)).filter (fun m => ∃ θ' ∈ Ω k, ⌊θ' / δ⌋₊ = m) with hD
  have hDsub : D ⊆ Finset.range (2 ^ k + 1) := Finset.filter_subset _ _
  have hDθ : ∀ m ∈ D, θm m ∈ Ω k ∧ ⌊θm m / δ⌋₊ = m :=
    fun m hm => hθm m (Finset.mem_filter.mp hm).2
  have hΩD : Ω k ⊆ ⋃ m ∈ D, {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ ⌊θ / δ⌋₊ = m} := by
    intro θ hθ
    have hθ' := hθ
    rw [hΩ] at hθ'
    have hle : ⌊θ / δ⌋₊ < 2 ^ k + 1 := by
      rw [Nat.floor_lt (div_nonneg hθ'.1.1 hδ0.le)]
      have : θ / δ ≤ ((2 ^ k : ℕ) : ℝ) := by rw [div_le_iff₀ hδ0]; linarith [hθ'.1.2]
      push_cast at this ⊢; linarith
    rw [Set.mem_iUnion₂]
    exact ⟨⌊θ / δ⌋₊, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hle, θ, hθ, rfl⟩, hθ'.1, rfl⟩
  have hwD : w ≤ D.card * δ := by
    have h1 : ENNReal.ofReal w ≤ ∑ m ∈ D, ENNReal.ofReal δ := by
      calc ENNReal.ofReal w ≤ MeasureTheory.volume (Ω k) := hk
        _ ≤ MeasureTheory.volume (⋃ m ∈ D, {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ ⌊θ / δ⌋₊ = m}) :=
            MeasureTheory.measure_mono hΩD
        _ ≤ ∑ m ∈ D, MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ ⌊θ / δ⌋₊ = m} :=
            MeasureTheory.measure_biUnion_finset_le _ _
        _ ≤ ∑ m ∈ D, ENNReal.ofReal δ := Finset.sum_le_sum (fun m _ => vol_floor_set hδ0 m)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hwm : ∀ m ∈ D, w ≤ 2 * δ *
      (((Q k).filter (meets δ ((a (θm m)).ofLp 0) ((a (θm m)).ofLp 1) (θm m))).card : ℝ) := by
    intro m hm
    have hΩm := (hDθ m hm).1
    rw [hΩ] at hΩm
    obtain ⟨⟨h0, h1⟩, hvol⟩ := hΩm
    set C := (Q k).filter (meets δ ((a (θm m)).ofLp 0) ((a (θm m)).ofLp 1) (θm m)) with hC
    have hsub : A (θm m) k ⊆ ⋃ q ∈ C, {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
        cell δ ((a (θm m)).ofLp 0 + t * cos (θm m)) ((a (θm m)).ofLp 1 + t * sin (θm m)) = q} := by
      intro t ht
      rw [hA] at ht
      rw [Set.mem_iUnion₂]
      exact ⟨_, Finset.mem_filter.mpr ⟨ht.2, t, ht.1, rfl⟩, ht.1, rfl⟩
    have h2 : ENNReal.ofReal w ≤ ∑ q ∈ C, ENNReal.ofReal (2 * δ) := by
      calc ENNReal.ofReal w ≤ MeasureTheory.volume (A (θm m) k) := hvol
        _ ≤ _ := MeasureTheory.measure_mono hsub
        _ ≤ _ := MeasureTheory.measure_biUnion_finset_le _ _
        _ ≤ ∑ q ∈ C, ENNReal.ofReal (2 * δ) :=
            Finset.sum_le_sum (fun q _ => vol_param_cell hδ0 h0 h1 q)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h2
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    linarith
  have hθm01 : ∀ m ∈ D, 0 ≤ θm m ∧ θm m ≤ 1 := by
    intro m hm
    have := (hDθ m hm).1
    rw [hΩ] at this
    exact this.1
  have hsep : ∀ m ∈ D, ∀ m' ∈ D, (|(m:ℝ) - m'| - 1) * δ ≤ |θm m - θm m'| := by
    intro m hm m' hm'
    have h := sep_of_floor hδ0 (hθm01 m hm).1 (hθm01 m' hm').1
    rw [(hDθ m hm).2, (hDθ m' hm').2] at h
    exact h
  have hw0 : 0 ≤ w := mul_nonneg (div_nonneg (by linarith) (by norm_num)) (pow_nonneg hρ0.le k)
  have hwpos : 0 < w := mul_pos (div_pos (by linarith) (by norm_num)) (pow_pos hρ0 k)
  have hscale := scale_lemma D (2 ^ k) hDsub δ hδ0 hδ1 hKδ.le θm (fun m => (a (θm m)).ofLp 0)
    (fun m => (a (θm m)).ofLp 1) hθm01 hsep (Q k) w hw0 hwm
  have hs' : (D.card : ℝ) * w ^ 2 ≤ 1700 * (Q k).card * δ * (1 + k) :=
    hscale.trans (mul_le_mul_of_nonneg_left (by linarith [log_two_pow_le k]) (by positivity))
  have hfinal : w ^ 3 < c1 * γ ^ k * (1 + k) :=
    final_ineq hwpos hwD hs' (Nat.cast_nonneg _) (hQcard k) (Nat.cast_nonneg _) (hFcard k) hδ hσ4
  have hg := hgrow k
  have e : w ^ 3 = c * (ρ ^ 3) ^ k := by rw [hw, hcdef]; ring
  linarith

end Kak2

open FCP.Kakeya in
theorem solution : KakeyaSetConjectureDim 2 := by
  intro S hS
  apply le_antisymm
  · calc dimH S ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (Set.subset_univ _)
      _ = _ := by rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr2 : (r : ℝ) < 2 := by
      have h1 : r < 2 := by exact_mod_cast hr
      exact_mod_cast h1
    obtain ⟨c0, hc0, hbound⟩ := Kak2.hausdorff_pos (r : ℝ) r.2 hr2
    apply le_dimH_of_hausdorffMeasure_ne_zero
    apply ne_of_gt
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    calc (0 : ENNReal) < ENNReal.ofReal c0 := ENNReal.ofReal_pos.mpr hc0
      _ ≤ _ := by
        refine le_iSup₂_of_le (1 : ENNReal) one_pos ?_
        refine le_iInf₂ (fun T hT => le_iInf (fun hdT => ?_))
        exact hbound S hS T hT hdT
