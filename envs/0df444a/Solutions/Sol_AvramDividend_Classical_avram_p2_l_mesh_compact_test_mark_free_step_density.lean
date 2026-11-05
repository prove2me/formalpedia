-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_mark_free_step_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:50:00.199829+00:00
-- url     : https://prove2.me/submissions/53930104-4436-4d48-8fa2-6124cf31974b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_support_cutoff_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_negative_test_global_right_tail
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_fine_partition_with_margins
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_global_step_error_from_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped BigOperators

/-- Continuous compact negative-mark tests admit globally uniform finite Ioc
step approximations avoiding any prescribed finite original jump-mark set. -/
theorem solution (S : Finset ℝ) (f : ℝ → ℝ) (ρ η : ℝ)
    (hη : 0 < η) (hfcomp : HasCompactSupport f)
    (hfcont : Continuous f)
    (hf : ∀ z : ℝ, -ρ < z → f z = 0) :
    ∃ n : ℕ, ∃ a b c : Fin n → ℝ,
      (∀ i, b i ≤ -ρ) ∧
      (∀ i, a i ∉ S ∧ b i ∉ S) ∧
      (∀ z : ℝ, |f z - (∑ i : Fin n,
        if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η) := by
  classical
  have hfcut : f (-ρ) = 0 :=
    avram_p2_l_mesh_continuous_negative_support_cutoff_zero f ρ hfcont hf
  obtain ⟨R, hR, hright⟩ :=
    avram_p2_l_mesh_continuous_negative_test_global_right_tail
      f ρ η hη (hfcont.continuousAt) hfcut hf
  obtain ⟨L0, hzero⟩ :=
    avram_p2_l_mesh_compact_test_left_tail_zero f hfcomp
  obtain ⟨δ, hδ, hmod⟩ :=
    avram_p2_l_mesh_compact_test_uniform_modulus f hfcomp hfcont η hη
  let B : ℝ := (R - ρ) / 2
  have hRB : R < B := by dsimp [B]; linarith
  have hB : B < -ρ := by dsimp [B]; linarith
  let C : ℝ := min L0 B
  let A : ℝ := C - 2
  let L : ℝ := C - 1
  have hAB : A < B := by
    have hCB : C ≤ B := min_le_right L0 B
    dsimp [A]
    linarith
  have hAL : A < L := by dsimp [A, L]; linarith
  have hLL0 : L < L0 := by
    have hCL0 : C ≤ L0 := min_le_left L0 B
    dsimp [L]
    linarith
  obtain ⟨n, p, hp, havoid, hwidth, hpfirst, hplastR, hplastB⟩ :=
    avram_p2_l_mesh_mark_free_fine_partition_with_margins
      S A B L R δ hAB hAL hRB hδ
  have hleft : ∀ z : ℝ, z ≤ p 0 → f z = 0 := by
    intro z hz
    apply hzero
    linarith
  have hright' : ∀ z : ℝ,
      p (Fin.last n) < z → |f z| ≤ η := by
    intro z hz
    exact hright z (lt_trans hplastR hz)
  have hbound := avram_p2_l_mesh_global_step_error_from_partition
    f p δ η hη hp hwidth hmod hleft hright'
  refine ⟨n, (fun i : Fin n => p i.castSucc),
    (fun i : Fin n => p i.succ),
    (fun i : Fin n => f (p i.castSucc)), ?_, ?_, ?_⟩
  · intro i
    have hle : p i.succ ≤ p (Fin.last n) :=
      hp.monotone (Fin.le_last i.succ)
    exact le_of_lt (lt_of_le_of_lt hle (lt_trans hplastB hB))
  · intro i
    exact ⟨havoid i.castSucc, havoid i.succ⟩
  · intro z
    exact hbound z
