-- Prove2me | solution 1 for DeepONetUniversal.interpolation_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:29:37.816414+00:00
-- url     : https://prove2.me/submissions/c9fd3dd3-7e3f-4514-9ec8-3ae1c45941cd

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic
import Theorems.Thm_DeepONetUniversal_arzela_ascoli

open MeasureTheory Filter Topology DeepONetUniversal

private lemma sensor_mem_Icc {a b : ℝ} (hab : a < b) {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    sensor a b m j ∈ Set.Icc a b := by
  unfold sensor
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hba : 0 < b - a := sub_pos.mpr hab
  have hj_le : (j : ℝ) ≤ m := Nat.cast_le.mpr hj
  constructor
  · have : 0 ≤ (j : ℝ) * (b - a) / m := by positivity
    linarith
  · have h1 : (j : ℝ) * (b - a) / m ≤ m * (b - a) / m := by
      gcongr
    rw [mul_div_cancel_left₀ _ hm_pos.ne'] at h1
    linarith

private lemma sensor_succ_sub (a b : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    sensor a b m (j + 1) - sensor a b m j = (b - a) / m := by
  unfold sensor
  push_cast
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

private lemma interp_index_bounds {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    let j := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
    j + 1 ≤ m ∧ sensor a b m j ≤ x ∧ x ≤ sensor a b m (j + 1) := by
  intro j
  have hba : 0 < b - a := sub_pos.mpr hab
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hj_le_pred : j ≤ m - 1 := min_le_right _ _
  have hj_succ : j + 1 ≤ m := by omega
  set t : ℝ := (x - a) * m / (b - a)
  have ht_nonneg : 0 ≤ t := by
    apply div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hm_pos.le) hba.le
  have ht_le_m : t ≤ m := by
    rw [div_le_iff₀ hba]
    have : x - a ≤ b - a := sub_le_sub_right hx.2 a
    nlinarith
  have hlo : sensor a b m j ≤ x := by
    unfold sensor
    have hj_le_floor : (j : ℝ) ≤ ⌊t⌋₊ := Nat.cast_le.mpr (min_le_left _ _)
    have hfloor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht_nonneg
    have hjt : (j : ℝ) ≤ t := hj_le_floor.trans hfloor_le
    have h1 : (j : ℝ) * (b - a) / m ≤ t * (b - a) / m := by gcongr
    have h2 : t * (b - a) / m = x - a := by
      dsimp [t]
      field_simp [hba.ne', hm_pos.ne']
    rw [h2] at h1
    linarith
  have hhi : x ≤ sensor a b m (j + 1) := by
    by_cases hfl : ⌊t⌋₊ ≤ m - 1
    · have hj_eq : j = ⌊t⌋₊ := min_eq_left hfl
      rw [hj_eq]
      unfold sensor
      have ht_lt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h1 : t * (b - a) / m < ((⌊t⌋₊ : ℝ) + 1) * (b - a) / m := by gcongr
      have h2 : t * (b - a) / m = x - a := by
        dsimp [t]
        field_simp [hba.ne', hm_pos.ne']
      rw [h2] at h1
      push_cast
      linarith
    · have hj_eq : j = m - 1 := by
        change min ⌊t⌋₊ (m - 1) = m - 1
        exact min_eq_right (by omega)
      have hj1 : j + 1 = m := by omega
      rw [hj1]
      unfold sensor
      rw [mul_div_cancel_left₀ _ hm_pos.ne']
      linarith [hx.2]
  exact ⟨hj_succ, hlo, hhi⟩

private lemma abs_sub_interp_le {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (u : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    let j := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
    |u x - interp a b m u x| ≤
      max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| := by
  intro j
  obtain ⟨_, hlo, hhi⟩ := interp_index_bounds hab hm hx
  have hstep : sensor a b m (j + 1) - sensor a b m j = (b - a) / m := sensor_succ_sub a b hm j
  have hstep_pos : 0 < sensor a b m (j + 1) - sensor a b m j := by
    rw [hstep]
    exact div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hm)
  set lam : ℝ := (x - sensor a b m j) / (sensor a b m (j + 1) - sensor a b m j)
  have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hlo) hstep_pos.le
  have hlam1 : lam ≤ 1 := (div_le_one hstep_pos).mpr (sub_le_sub_right hhi _)
  have heq : u x - interp a b m u x =
      (1 - lam) * (u x - u (sensor a b m j)) + lam * (u x - u (sensor a b m (j + 1))) := by
    change u x - (u (sensor a b m j) + (u (sensor a b m (j + 1)) - u (sensor a b m j)) /
      (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j)) =
      (1 - lam) * (u x - u (sensor a b m j)) + lam * (u x - u (sensor a b m (j + 1)))
    dsimp only [lam]
    have hne : sensor a b m (j + 1) - sensor a b m j ≠ 0 := hstep_pos.ne'
    field_simp [hne]
    ring
  rw [heq]
  have hM0 : |u x - u (sensor a b m j)| ≤
      max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| := le_max_left _ _
  have hM1 : |u x - u (sensor a b m (j + 1))| ≤
      max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| := le_max_right _ _
  calc |(1 - lam) * (u x - u (sensor a b m j)) + lam * (u x - u (sensor a b m (j + 1)))|
      ≤ |(1 - lam) * (u x - u (sensor a b m j))| + |lam * (u x - u (sensor a b m (j + 1)))| :=
        abs_add_le _ _
    _ = (1 - lam) * |u x - u (sensor a b m j)| + lam * |u x - u (sensor a b m (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlam1), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| +
        lam * max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| := by
        gcongr
    _ = max |u x - u (sensor a b m j)| |u x - u (sensor a b m (j + 1))| := by ring

theorem solution {a b : ℝ} (hab : a < b) (V : Set C(Set.Icc a b, ℝ))
    (hV : IsCompact V) :
    ∃ κ : ℕ → ℝ,
      (∀ m : ℕ, 0 < m → ∀ u ∈ V, ∀ x ∈ Set.Icc a b, |evalAt u x - interp a b m (evalAt u) x| ≤ κ m) ∧
        Tendsto κ atTop (𝓝 0) := by
  by_cases hVne : V.Nonempty
  · have hcl : IsCompact (closure V) := by
      rwa [hV.isClosed.closure_eq]
    obtain ⟨⟨M, hM⟩, heq⟩ := (arzela_ascoli (Set.Icc a b) isCompact_Icc V).mp hcl
    let S (m : ℕ) : Set ℝ :=
      {r | ∃ u ∈ V, ∃ x ∈ Set.Icc a b, r = |evalAt u x - interp a b m (evalAt u) x|}
    let κ : ℕ → ℝ := fun m => if m = 0 then 0 else sSup (S m)
    have hS_ne : ∀ m : ℕ, (S m).Nonempty := by
      intro m
      obtain ⟨u₀, hu₀⟩ := hVne
      exact ⟨|evalAt u₀ a - interp a b m (evalAt u₀) a|, u₀, hu₀, a, Set.left_mem_Icc.mpr hab.le, rfl⟩
    have hS_bdd : ∀ m : ℕ, 0 < m → BddAbove (S m) := by
      intro m hm
      refine ⟨2 * M, ?_⟩
      rintro r ⟨u, huV, x, hx, rfl⟩
      obtain ⟨hj_succ, _, _⟩ := interp_index_bounds hab hm hx
      set j := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
      have hx0 : sensor a b m j ∈ Set.Icc a b := sensor_mem_Icc hab hm (by omega)
      have hx1 : sensor a b m (j + 1) ∈ Set.Icc a b := sensor_mem_Icc hab hm hj_succ
      have hu_bd : ∀ z (hz : z ∈ Set.Icc a b), |evalAt u z| ≤ M := by
        intro z hz
        simp only [evalAt, dif_pos hz]
        exact hM u ⟨u, huV, rfl⟩ ⟨z, hz⟩
      have hle := abs_sub_interp_le hab hm (evalAt u) hx
      have h1 : |evalAt u x - evalAt u (sensor a b m j)| ≤ 2 * M := by
        calc |evalAt u x - evalAt u (sensor a b m j)|
            ≤ |evalAt u x| + |evalAt u (sensor a b m j)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hu_bd x hx) (hu_bd _ hx0)
          _ = 2 * M := by ring
      have h2 : |evalAt u x - evalAt u (sensor a b m (j + 1))| ≤ 2 * M := by
        calc |evalAt u x - evalAt u (sensor a b m (j + 1))|
            ≤ |evalAt u x| + |evalAt u (sensor a b m (j + 1))| := abs_sub _ _
          _ ≤ M + M := add_le_add (hu_bd x hx) (hu_bd _ hx1)
          _ = 2 * M := by ring
      exact hle.trans (max_le h1 h2)
    refine ⟨κ, ?_, ?_⟩
    · intro m hm u huV x hx
      simp only [κ, if_neg hm.ne']
      exact le_csSup (hS_bdd m hm) ⟨u, huV, x, hx, rfl⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := heq (ε / 2) (half_pos hε)
      obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
      refine ⟨max N 1, fun m hm => ?_⟩
      have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hm)
      have hm_gt : (b - a) / δ < m := hN.trans_le (Nat.cast_le.mpr ((le_max_left N 1).trans hm))
      have hstep_lt : (b - a) / m < δ := by
        have hm_rpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
        rw [div_lt_iff₀ hm_rpos]
        rw [div_lt_iff₀ hδpos] at hm_gt
        linarith
      have hκ_nonneg : 0 ≤ κ m := by
        simp only [κ, if_neg hm_pos.ne']
        obtain ⟨u₀, hu₀⟩ := hVne
        exact (abs_nonneg _).trans
          (le_csSup (hS_bdd m hm_pos) ⟨u₀, hu₀, a, Set.left_mem_Icc.mpr hab.le, rfl⟩)
      have hκ_le : κ m ≤ ε / 2 := by
        simp only [κ, if_neg hm_pos.ne']
        refine csSup_le (hS_ne m) ?_
        rintro r ⟨u, huV, x, hx, rfl⟩
        obtain ⟨hj_succ, hlo, hhi⟩ := interp_index_bounds hab hm_pos hx
        set j := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
        have hx0 : sensor a b m j ∈ Set.Icc a b := sensor_mem_Icc hab hm_pos (by omega)
        have hx1 : sensor a b m (j + 1) ∈ Set.Icc a b := sensor_mem_Icc hab hm_pos hj_succ
        have hstep := sensor_succ_sub a b hm_pos j
        have hd0 : dist (⟨x, hx⟩ : Set.Icc a b) ⟨sensor a b m j, hx0⟩ < δ := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
          calc x - sensor a b m j ≤ sensor a b m (j + 1) - sensor a b m j := sub_le_sub_right hhi _
            _ = (b - a) / m := hstep
            _ < δ := hstep_lt
        have hd1 : dist (⟨x, hx⟩ : Set.Icc a b) ⟨sensor a b m (j + 1), hx1⟩ < δ := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hhi)]
          calc sensor a b m (j + 1) - x ≤ sensor a b m (j + 1) - sensor a b m j :=
                sub_le_sub_left hlo _
            _ = (b - a) / m := hstep
            _ < δ := hstep_lt
        have h1 : |evalAt u x - evalAt u (sensor a b m j)| < ε / 2 := by
          rw [evalAt, dif_pos hx, evalAt, dif_pos hx0]
          exact hδ u ⟨u, huV, rfl⟩ ⟨x, hx⟩ ⟨_, hx0⟩ hd0
        have h2 : |evalAt u x - evalAt u (sensor a b m (j + 1))| < ε / 2 := by
          rw [evalAt, dif_pos hx, evalAt, dif_pos hx1]
          exact hδ u ⟨u, huV, rfl⟩ ⟨x, hx⟩ ⟨_, hx1⟩ hd1
        exact (abs_sub_interp_le hab hm_pos (evalAt u) hx).trans (max_le h1.le h2.le)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hκ_nonneg]
      linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hVne
    refine ⟨fun _ => 0, ?_, tendsto_const_nhds⟩
    intro m _ u huV
    rw [hVne] at huV
    exact huV.elim
