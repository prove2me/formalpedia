-- Prove2me | solution 1 for DbarRegularity.integral_ball_norm_rpow_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:37:44.674284+00:00
-- url     : https://prove2.me/submissions/7a96a60a-aa05-474d-a7d9-9b2e844e78c4

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- `∫_{|x| < r} |x|^{1-d} dx = d |B(0,1)| r` on `ℝ^d`, `d ≥ 1`. -/
theorem integral_ball_norm_rpow_one_sub {d : ℕ} (hd : 0 < d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (1 - d : ℝ)) (ball 0 r) volume ∧
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ (1 - d : ℝ) =
        d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * r := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set g : ℝ → ℝ := fun t => t ^ (1 - d : ℝ) with hg
  have key : ∀ y ∈ Ioo (0 : ℝ) r, y ^ (d - 1) • g y = 1 := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only [hg, smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    rw [Nat.cast_sub (by omega)]
    simp
  have hint : IntegrableOn (fun y : ℝ => y ^ (d - 1) • g y) (Ioo 0 r) := by
    refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y hy => (key y hy).symm)
      measurableSet_Ioo
  refine ⟨?_, ?_⟩
  · have := (integrableOn_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (f := g) (r := r)).2 (by rw [hfin]; exact hint)
    exact this
  · have h1 : ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ (1 - d : ℝ) =
        ∫ x : EuclideanSpace ℝ (Fin d), (Iio r).indicator g ‖x‖ := by
      rw [← integral_indicator measurableSet_ball]
      congr 1; ext x
      simp [indicator, mem_ball_zero_iff, hg]
    rw [h1, integral_fun_norm_addHaar volume ((Iio r).indicator g), hfin]
    have h2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (Iio r).indicator g y = r := by
      have h3 : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) • (Iio r).indicator g y =
          (Ioo 0 r).indicator (fun _ => (1 : ℝ)) y := by
        intro y hy
        by_cases hyr : y < r
        · rw [indicator_of_mem (show y ∈ Iio r from hyr),
            indicator_of_mem (show y ∈ Ioo 0 r from ⟨hy, hyr⟩)]
          exact key y ⟨hy, hyr⟩
        · rw [indicator_of_notMem (show y ∉ Iio r from hyr),
            indicator_of_notMem (show y ∉ Ioo 0 r from fun h => hyr h.2)]
          simp
      rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo]
      rw [inter_eq_left.2 Ioo_subset_Ioi_self]
      simp [hr.le]
    rw [h2, nsmul_eq_mul, smul_eq_mul]
    ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (hd : 0 < d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (1 - d : ℝ)) (ball 0 r) volume ∧
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ (1 - d : ℝ) =
        d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * r :=
  DbarRegularity.integral_ball_norm_rpow_one_sub hd r hr
