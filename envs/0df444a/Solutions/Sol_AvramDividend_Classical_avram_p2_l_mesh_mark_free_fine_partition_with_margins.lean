-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_mark_free_fine_partition_with_margins
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:22:46.427024+00:00
-- url     : https://prove2.me/submissions/92757a1e-7b97-420b-9d18-20d11d427fb2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_archimedean_positive_fine_cell
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_near_uniform_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A sufficiently fine finite near-uniform mesh avoids a finite mark set,
has a first cut in the zero tail, and has a final cut inside the right margin. -/
theorem solution (S : Finset ℝ) (A B L R δ : ℝ)
    (hAB : A < B) (hAL : A < L) (hRB : R < B) (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ p : Fin (n + 1) → ℝ,
      StrictMono p ∧
      (∀ i : Fin (n + 1), p i ∉ S) ∧
      (∀ i : Fin n, p i.succ - p i.castSucc < δ) ∧
      p 0 < L ∧ R < p (Fin.last n) ∧ p (Fin.last n) < B := by
  let ε : ℝ := min (δ / 2) (min ((L - A) / 2) ((B - R) / 3))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) (lt_min (by linarith) (by linarith))
  obtain ⟨n, hh, hsmall⟩ :=
    avram_p2_l_mesh_archimedean_positive_fine_cell A B ε hAB hε
  let h : ℝ := (B - A) / ((n : ℝ) + 1)
  let r : ℝ := h / 4
  have hh' : 0 < h := hh
  have hr : 0 < r := by dsimp [r]; positivity
  have hsep : 2 * r ≤ h := by dsimp [r]; linarith
  obtain ⟨p, hpmono, hpnear, hpwidth⟩ :=
    avram_p2_l_mesh_mark_free_near_uniform_partition S n A h r hh' hr hsep
  have hδsmall : h < δ / 2 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hAsmall : h < (L - A) / 2 :=
    lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_left _ _))
  have hBsmall : h < (B - R) / 3 :=
    lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  have hcell : h + 2 * r < δ := by dsimp [r]; linarith
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  have htotal : ((n : ℝ) + 1) * h = B - A := by
    dsimp [h]
    field_simp
  have hlast : A + (n : ℝ) * h = B - h := by nlinarith
  have hfirst : |p 0 - A| < r := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] using (hpnear 0).1
  have hfinal : |p (Fin.last n) - (B - h)| < r := by
    simpa only [Fin.val_last, hlast] using (hpnear (Fin.last n)).1
  have hleft : p 0 < L := by
    have hlt := (abs_lt.mp hfirst).2
    dsimp [r] at hlt
    linarith
  have hright : R < p (Fin.last n) := by
    have hgt := (abs_lt.mp hfinal).1
    dsimp [r] at hgt
    linarith
  have hupper : p (Fin.last n) < B := by
    have hlt := (abs_lt.mp hfinal).2
    dsimp [r] at hlt
    linarith
  refine ⟨n, p, hpmono, ?_, ?_, hleft, hright, hupper⟩
  · intro i
    exact (hpnear i).2
  · intro i
    exact lt_trans (hpwidth i) hcell
