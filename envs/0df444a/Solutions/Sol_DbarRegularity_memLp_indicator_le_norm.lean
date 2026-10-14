-- Prove2me | solution 1 for DbarRegularity.memLp_indicator_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:37:45.458029+00:00
-- url     : https://prove2.me/submissions/fa6931d6-7636-4da0-b772-0ce2b574b076

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- If `|K(x)| ≤ B |x|^{-d}` for `x ≠ 0`, then `K · 1_{|x| ≥ ε}` lies in `L^q(ℝ^d)` for every
`q > 1` and `ε > 0`. -/
theorem memLp_indicator_le_norm {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ) (hB : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) (hq : 1 < q) :
    MemLp ({x | ε ≤ ‖x‖}.indicator K) (ENNReal.ofReal q) volume := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set h : ℝ → ℝ := (Ici ε).indicator (fun t => B * t ^ (-(d : ℝ))) with hh
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun x => h ‖x‖ with hG
  have hq0 : (0 : ℝ) < q := by linarith
  have hGm : AEStronglyMeasurable G volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact ((Measurable.indicator (by fun_prop : Measurable (fun t : ℝ => B * t ^ (-(d : ℝ))))
      measurableSet_Ici).comp measurable_norm)
  -- `G ∈ L^q`
  have hGq : MemLp G (ENNReal.ofReal q) volume := by
    rw [← integrable_norm_rpow_iff hGm (by simpa using hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    have := (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (f := fun t => ‖h t‖ ^ q)).2
    refine this ?_
    rw [hfin]
    have hIoi : IntegrableOn (fun y : ℝ => |B| ^ q * y ^ ((d : ℝ) - 1 - d * q)) (Ioi ε) := by
      refine Integrable.const_mul ?_ _
      refine integrableOn_Ioi_rpow_of_lt ?_ hε
      have : (d : ℝ) < d * q := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        nlinarith
      linarith
    have hIci : IntegrableOn (fun y : ℝ => |B| ^ q * y ^ ((d : ℝ) - 1 - d * q)) (Ici ε) :=
      (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 hIoi
    have hind : Integrable ((Ici ε).indicator
        (fun y : ℝ => |B| ^ q * y ^ ((d : ℝ) - 1 - d * q))) :=
      (integrable_indicator_iff measurableSet_Ici).2 hIci
    refine (hind.integrableOn (s := Ioi 0)).congr_fun ?_ measurableSet_Ioi
    intro y (hy : 0 < y)
    by_cases hyε : ε ≤ y
    · simp only [hh, smul_eq_mul, indicator_of_mem (show y ∈ Ici ε from hyε)]
      rw [Real.norm_eq_abs, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
        abs_of_pos (Real.rpow_pos_of_pos hy _), ← Real.rpow_mul hy.le]
      rw [← Real.rpow_natCast y (d - 1), Nat.cast_sub (by omega), Nat.cast_one]
      rw [mul_left_comm, ← Real.rpow_add hy]
      congr 2; ring
    · simp only [hh, smul_eq_mul, indicator_of_notMem (show y ∉ Ici ε from hyε)]
      simp [Real.zero_rpow hq0.ne']
  refine hGq.mono (hK.indicator (measurableSet_le measurable_const measurable_norm)) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : ε ≤ ‖x‖
  · have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    rw [indicator_of_mem (show x ∈ {x | ε ≤ ‖x‖} from hx)]
    simp only [hG, hh, indicator_of_mem (show ‖x‖ ∈ Ici ε from hx)]
    refine (hB x hx0).trans (le_of_eq ?_)
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv]
    have hB0 : 0 ≤ B := by
      have := (norm_nonneg _).trans (hB x hx0)
      exact (div_nonneg_iff.1 this).elim (fun h => h.1)
        (fun h => absurd h.2 (not_le.2 (by positivity)))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rw [indicator_of_notMem (show x ∉ {x | ε ≤ ‖x‖} from hx)]
    simp

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ) (hB : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) (hq : 1 < q) :
    MemLp ({x | ε ≤ ‖x‖}.indicator K) (ENNReal.ofReal q) volume :=
  DbarRegularity.memLp_indicator_le_norm hd K hK B hB ε hε q hq
