-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_vanishes_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:40:02.538797+00:00
-- url     : https://prove2.me/submissions/7950dc45-944b-4bca-8f75-091f7eba44a2

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_abs_le_finite_mass
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      K (x - s) * V s ∂volume)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
  let g : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, |K s| ∂volume
  let M : ℝ := sSup ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) 1)
  have hKi : IntegrableOn (fun s : ℝ => |K s|)
      (Ioi (0 : ℝ)) volume := by
    change Integrable (fun s : ℝ => |K s|)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [Real.norm_eq_abs] using hK.norm
  have hgCont : ContinuousOn g (Ici (0 : ℝ)) :=
    causal_l1_primitive_continuousOn_nonnegative
      (fun s : ℝ => |K s|) hKi
  have hg0 : g 0 = 0 := by simp [g]
  have hsubset : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := by
    intro s hs
    change (0 : ℝ) < s at hs
    exact le_of_lt hs
  have hgTend : Tendsto g (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds 0) := by
    have ht := (hgCont.continuousWithinAt (by simp : (0 : ℝ) ∈ Ici (0 : ℝ))).tendsto
    have hs := ht.mono_left (nhdsWithin_mono (0 : ℝ) hsubset)
    simpa only [hg0] using hs
  have hMb := causal_weighted_sup_bddAbove_of_locally_bounded
    V 0 (le_refl (0 : ℝ)) hVb 1 (by norm_num)
  have hMb' : BddAbove ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) 1) := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using hMb
  have hMnonneg : 0 ≤ M := by
    calc
      0 ≤ |V 1| := abs_nonneg _
      _ ≤ M := le_csSup hMb' ⟨1, by norm_num, rfl⟩
  have hNear : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      x ∈ Ioc (0 : ℝ) 1 := by
    have hsmall : Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds hsmall] with x hx0 hx1
    exact ⟨hx0, le_of_lt hx1⟩
  have hBound : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      |∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume| ≤
        M * g x := by
    filter_upwards [hNear] with x hx
    exact causal_l1_convolution_abs_le_finite_mass
      K V hK hVc hVb 1 x (by norm_num) hx
  have hMlimit : Tendsto (fun x => M * g x)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
    convert (tendsto_const_nhds.mul hgTend) using 1 <;> simp
  have hBoundNorm : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ‖∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume‖ ≤
        M * g x := by
    simpa only [Real.norm_eq_abs] using hBound
  exact squeeze_zero_norm' hBoundNorm hMlimit
