-- Prove2me | solution 1 for CompOT.Sinkhorn.remark_4_12_distance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:38:03.377394+00:00
-- url     : https://prove2.me/submissions/aa08b980-e922-4508-b8e6-f259b619a58e

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

set_option autoImplicit false
open CompOT.Sinkhorn

theorem hil_eq {n : ℕ} (hn : 0 < n) (u u' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) :
    hilbertMetric u u' = varNorm (fun i => Real.log (u i) - Real.log (u' i)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f : Fin n → ℝ := fun i => Real.log (u i) - Real.log (u' i) with hf
  obtain ⟨i0, hi0⟩ := Finite.exists_max f
  obtain ⟨j0, hj0⟩ := Finite.exists_min f
  set r : Fin n → ℝ := fun i => u i / u' i with hr
  have hrpos : ∀ i, 0 < r i := fun i => div_pos (hu i) (hu' i)
  have hlogr : ∀ i, Real.log (r i) = f i := fun i => by
    simp only [hr, hf]; rw [Real.log_div (hu i).ne' (hu' i).ne']
  have hrle : ∀ i j, f i ≤ f j → r i ≤ r j := by
    intro i j h
    rw [← hlogr, ← hlogr] at h
    exact (Real.log_le_log_iff (hrpos i) (hrpos j)).1 h
  set g : Fin n → Fin n → ℝ := fun i j => u i * u' j / (u j * u' i) with hg
  have hgr : ∀ i j, g i j = r i / r j := by
    intro i j
    simp only [hg, hr]
    have := (hu i).ne'; have := (hu' i).ne'; have := (hu j).ne'; have := (hu' j).ne'
    field_simp
  have hsup : (⨆ i, ⨆ j, g i j) = g i0 j0 := by
    apply le_antisymm
    · refine ciSup_le (fun i => ciSup_le (fun j => ?_))
      rw [hgr, hgr]
      have h1 := hrle _ _ (hi0 i)
      have h2 := hrle _ _ (hj0 j)
      have := hrpos i; have := hrpos j; have := hrpos i0; have := hrpos j0
      rw [div_le_div_iff₀ (hrpos j) (hrpos j0)]
      nlinarith [mul_le_mul h1 h2 (hrpos j0).le (hrpos i0).le]
    · exact le_trans (le_ciSup (f := fun j => g i0 j) (Set.finite_range _).bddAbove j0)
        (le_ciSup (f := fun i => ⨆ j, g i j) (Set.finite_range _).bddAbove i0)
  have hmax : (⨆ i, f i) = f i0 :=
    le_antisymm (ciSup_le hi0) (le_ciSup (Set.finite_range f).bddAbove i0)
  have hmin : (⨅ i, f i) = f j0 :=
    le_antisymm (ciInf_le (Set.finite_range f).bddBelow j0) (le_ciInf hj0)
  unfold hilbertMetric varNorm
  rw [hsup, hmax, hmin]
  simp only [hg]
  rw [Real.log_div (mul_pos (hu i0) (hu' j0)).ne' (mul_pos (hu j0) (hu' i0)).ne',
    Real.log_mul (hu i0).ne' (hu' j0).ne', Real.log_mul (hu j0).ne' (hu' i0).ne']
  simp only [hf]
  ring

lemma varNorm_eq {n : ℕ} (f : Fin n → ℝ) (i0 j0 : Fin n) (hi : ∀ i, f i ≤ f i0)
    (hj : ∀ j, f j0 ≤ f j) : varNorm f = f i0 - f j0 := by
  have : Nonempty (Fin n) := ⟨i0⟩
  unfold varNorm
  rw [le_antisymm (ciSup_le hi) (le_ciSup (Set.finite_range f).bddAbove i0),
    le_antisymm (ciInf_le (Set.finite_range f).bddBelow j0) (le_ciInf hj)]

lemma sub_le_varNorm {n : ℕ} (f : Fin n → ℝ) (i j : Fin n) : f i - f j ≤ varNorm f := by
  have : Nonempty (Fin n) := ⟨i⟩
  unfold varNorm
  have h1 := le_ciSup (Set.finite_range f).bddAbove i
  have h2 := ciInf_le (Set.finite_range f).bddBelow j
  linarith

lemma varNorm_exists {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ i0 j0, varNorm f = f i0 - f j0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max f
  obtain ⟨j0, hj0⟩ := Finite.exists_min f
  exact ⟨i0, j0, varNorm_eq f i0 j0 hi0 hj0⟩

lemma varNorm_neg {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : varNorm (fun i => - f i) = varNorm f := by
  obtain ⟨i0, j0, h⟩ := varNorm_exists hn (fun i => - f i)
  obtain ⟨i1, j1, h1⟩ := varNorm_exists hn f
  apply le_antisymm
  · rw [h]; have := sub_le_varNorm f j0 i0; linarith
  · rw [h1]
    have := sub_le_varNorm (fun i => - f i) j1 i1; linarith

lemma varNorm_nonneg {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : 0 ≤ varNorm f := by
  have := sub_le_varNorm f ⟨0, hn⟩ ⟨0, hn⟩; linarith

theorem solution {n : ℕ} (hn : 0 < n) (u u' u'' : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i) (hu'' : ∀ i, 0 < u'' i) :
    0 ≤ hilbertMetric u u' ∧
    hilbertMetric u u' = hilbertMetric u' u ∧
    hilbertMetric u u'' ≤ hilbertMetric u u' + hilbertMetric u' u'' ∧
    (hilbertMetric u u' = 0 ↔ ∃ r : ℝ, 0 < r ∧ u = r • u') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hil_eq hn u u' hu hu']; exact varNorm_nonneg hn _
  · rw [hil_eq hn u u' hu hu', hil_eq hn u' u hu' hu, ← varNorm_neg hn]
    congr 1; funext i; ring
  · rw [hil_eq hn u u'' hu hu'', hil_eq hn u u' hu hu', hil_eq hn u' u'' hu' hu'']
    obtain ⟨i0, j0, h⟩ := varNorm_exists hn (fun i => Real.log (u i) - Real.log (u'' i))
    rw [h]
    have h1 := sub_le_varNorm (fun i => Real.log (u i) - Real.log (u' i)) i0 j0
    have h2 := sub_le_varNorm (fun i => Real.log (u' i) - Real.log (u'' i)) i0 j0
    try simp only at h1 h2 ⊢
    linarith
  · rw [hil_eq hn u u' hu hu']
    constructor
    · intro h
      have hc : ∀ i j, Real.log (u i) - Real.log (u' i) = Real.log (u j) - Real.log (u' j) := by
        intro i j
        have h1 := sub_le_varNorm (fun i => Real.log (u i) - Real.log (u' i)) i j
        have h2 := sub_le_varNorm (fun i => Real.log (u i) - Real.log (u' i)) j i
        try simp only at h1 h2
        linarith
      refine ⟨u ⟨0, hn⟩ / u' ⟨0, hn⟩, div_pos (hu _) (hu' _), ?_⟩
      funext i
      have := hc i ⟨0, hn⟩
      have h3 : Real.log (u i / u' i) = Real.log (u ⟨0, hn⟩ / u' ⟨0, hn⟩) := by
        rw [Real.log_div (hu i).ne' (hu' i).ne', Real.log_div (hu _).ne' (hu' _).ne']
        exact this
      have h4 := Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos (hu i) (hu' i)))
        (Set.mem_Ioi.2 (div_pos (hu _) (hu' _))) h3
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← h4]
      field_simp [(hu' i).ne']
    · rintro ⟨r, hr, rfl⟩
      rw [varNorm_eq (fun i => Real.log ((r • u') i) - Real.log (u' i)) ⟨0, hn⟩ ⟨0, hn⟩]
      · ring
      · intro i; simp only [Pi.smul_apply, smul_eq_mul]
        rw [Real.log_mul hr.ne' (hu' i).ne', Real.log_mul hr.ne' (hu' _).ne']
        linarith
      · intro i; simp only [Pi.smul_apply, smul_eq_mul]
        rw [Real.log_mul hr.ne' (hu' i).ne', Real.log_mul hr.ne' (hu' _).ne']
        linarith
