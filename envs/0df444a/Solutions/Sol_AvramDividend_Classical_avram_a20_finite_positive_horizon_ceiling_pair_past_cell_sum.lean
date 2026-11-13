-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_positive_horizon_ceiling_pair_past_cell_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:57:05.714121+00:00
-- url     : https://prove2.me/submissions/305481a2-ebbb-425e-bfa3-811d2728ef1b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_grid_cross_pair_card_identity
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
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun u : ℝ≥0 =>
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
      (F.filter (fun v : ℝ≥0 =>
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card := by
  classical
  let g : ℝ≥0 → Fin (k + 1) := fun u =>
    ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hg (u : ℝ≥0) (hu : u ∈ F) :
      (g u).val = Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    change min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k =
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
    exact Nat.min_eq_left
      (avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
        u T hT (hF u hu).1 (hF u hu).2 k hk).2
  have hPast (i : Fin k) :
      F.filter (fun u : ℝ≥0 => g u < i.succ) =
      F.filter (fun u : ℝ≥0 =>
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val) := by
    ext u; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hlt⟩
      refine ⟨hu, ?_⟩
      change (g u).val < (i.succ).val at hlt
      simpa [hg u hu, Nat.lt_succ_iff] using hlt
    · rintro ⟨hu, hle⟩
      refine ⟨hu, ?_⟩
      change (g u).val < (i.succ).val
      simpa [hg u hu, Nat.lt_succ_iff] using hle
  have hCell (i : Fin k) :
      F.filter (fun v : ℝ≥0 => g v = i.succ) =
      F.filter (fun v : ℝ≥0 =>
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1) := by
    ext v; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, heq⟩
      refine ⟨hv, ?_⟩
      have hval := congrArg Fin.val heq
      simpa [hg v hv] using hval
    · rintro ⟨hv, heq⟩
      refine ⟨hv, ?_⟩
      apply Fin.ext
      simpa [hg v hv] using heq
  have hEq :
      (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => g p.1 < g p.2) =
      (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ))) := by
    apply Finset.filter_congr
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    change (g p.1).val < (g p.2).val ↔ _
    rw [hg p.1 hp1, hg p.2 hp2]
  have hAll :
      (∑ i : Fin (k + 1),
        (F.filter (fun u : ℝ≥0 => g u < i)).card *
        (F.filter (fun v : ℝ≥0 => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card := by
    simpa only [hEq] using
      (avram_p4_f_assembly_finite_grid_cross_pair_card_identity F (k + 1) g)
  rw [Fin.sum_univ_succ] at hAll; simp only [Fin.not_lt_zero, Finset.filter_false, Finset.card_empty,
    zero_mul, zero_add] at hAll
  simp_rw [hPast, hCell] at hAll
  exact hAll.symm
