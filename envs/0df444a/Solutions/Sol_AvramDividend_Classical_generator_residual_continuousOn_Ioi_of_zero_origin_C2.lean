-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_Ioi_of_zero_origin_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T04:45:14.393788+00:00
-- url     : https://prove2.me/submissions/8cd95453-3762-4287-a5e3-ea963a352b40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioo_of_continuousOn_all_compact_subintervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The generator residual of the scale function is continuous on the whole
positive half-line, for a scale function that vanishes at the origin and is
twice continuously differentiable there.

This is the zero-origin counterpart of
`generator_residual_continuousOn_Ioi_of_standing_bv_C2`, and it discharges the
`hcont` hypothesis of the prescribed `C²` branch theorem
`scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing` and of
the aggregator `scaleFunction_generator_q_harmonic_of_nonzero_factor`.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi (0 : ℝ)) := by
  have hone : ∀ a : {a : ℝ // 0 < a},
      ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioo (0 : ℝ) ↑a) := by
    intro a
    have hcompact : ∀ l u : ℝ, 0 < l → l < u → u < ↑a →
        ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Icc l u) := by
      intro l u hl hlu hu
      have hu' : u < ↑a + 1 := by linarith
      exact generator_residual_continuousOn_compact_of_zero_origin_C2
        X q W hW hzero (↑a + 1) l u hl hlu hu'
        (hC2.mono (by
          intro z hz
          obtain ⟨hz1, hz2⟩ := Set.mem_Ioo.mp hz
          exact mem_Ioi.mpr (by linarith [hz1])))
    exact continuousOn_Ioo_of_continuousOn_all_compact_subintervals
      (fun x : ℝ => X.generator W x - q * W x) ↑a a.property hcompact
  have hopen : ∀ a : {a : ℝ // 0 < a}, IsOpen (Ioo (0 : ℝ) ↑a) :=
    fun _ => isOpen_Ioo
  have hiu : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (⋃ a : {a : ℝ // 0 < a}, Ioo (0 : ℝ) ↑a) :=
    ContinuousOn.iUnion_of_isOpen hone hopen
  have hcov : (⋃ a : {a : ℝ // 0 < a}, Ioo (0 : ℝ) ↑a) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion.mp hx
      exact mem_Ioi.mpr ha
    · intro hx
      have hx0 : 0 < x := mem_Ioi.mp hx
      refine Set.mem_iUnion.mpr ⟨⟨x + 1, by linarith⟩, mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  rw [hcov] at hiu
  exact hiu
