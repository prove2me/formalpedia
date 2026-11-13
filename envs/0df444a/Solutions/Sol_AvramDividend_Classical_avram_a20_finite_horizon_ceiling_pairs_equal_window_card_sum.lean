-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_horizon_ceiling_pairs_equal_window_card_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:00:38.49135+00:00
-- url     : https://prove2.me/submissions/de5fc8d2-6c2c-4537-b2f3-74aafaa7cac0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_real_mesh_ceiling_cell_iff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k)
    (hF : ∀ u ∈ F, 0 < u ∧ u ≤ T) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i)).card *
      (F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i)).card := by
  intro s t
  obtain ⟨hst, htT, hs, ht⟩ :=
    avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hCeilPast (i : Fin k) (u : ℝ≥0) :
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val ↔
        u ≤ s i := by
    have hsmul : (s i : ℝ) * (k : ℝ) = (i.val : ℝ) * (T : ℝ) := by
      rw [hs i]; field_simp
    rw [Nat.ceil_le]
    have hreal :
        (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ (i.val : ℝ) ↔
          (u : ℝ) ≤ (s i : ℝ) := by
      rw [div_le_iff₀ hTr, ← hsmul]
      exact mul_le_mul_iff_of_pos_right hkr
    exact hreal.trans (by exact_mod_cast (Iff.rfl : u ≤ s i ↔ u ≤ s i))
  have hCeilCell (i : Fin k) (u : ℝ≥0) :
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1 ↔
        s i < u ∧ u ≤ t i := by
    have h := avram_p4_f_assembly_real_mesh_ceiling_cell_iff
      (u : ℝ) (T : ℝ) hTr k i.val hk
    rw [← hs i, ← ht i] at h
    constructor
    · intro hu
      obtain ⟨ha, hb⟩ := h.mp hu
      exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
    · rintro ⟨ha, hb⟩
      apply h.mpr
      exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  have hPast (i : Fin k) :
      F.filter (fun u : ℝ≥0 =>
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val) =
      F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i) := by
    ext u; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hc⟩
      exact ⟨hu, (hF u hu).1, (hCeilPast i u).mp hc⟩
    · rintro ⟨hu, _, hle⟩
      exact ⟨hu, (hCeilPast i u).mpr hle⟩
  have hCell (i : Fin k) :
      F.filter (fun v : ℝ≥0 =>
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1) =
      F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i) := by
    ext v; simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => hCeilCell i v)
  calc
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
      ∑ i : Fin k,
        (F.filter (fun u : ℝ≥0 =>
          Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
        (F.filter (fun v : ℝ≥0 =>
          Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card :=
      avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum F T hT k hk hF
    _ = ∑ i : Fin k,
        (F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s i)).card *
        (F.filter (fun v : ℝ≥0 => s i < v ∧ v ≤ t i)).card := by
      apply Finset.sum_congr rfl
      intro i hi; rw [hPast i, hCell i]
