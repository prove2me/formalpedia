-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_Ioi_of_standing_bv_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T04:37:39.313476+00:00
-- url     : https://prove2.me/submissions/fc6d1d38-09af-4285-83a2-cd4223e1e56a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioo_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioo_of_continuousOn_all_compact_subintervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The generator residual of the scale function is continuous on the whole
positive half-line, for a standing bounded-variation Lévy process and a
twice continuously differentiable scale function.

The proof has two parts.  On a bounded open interval `(0, a)` the continuity
is the Proved local statement `generator_residual_continuousOn_Ioo_of_standing_bv_C2`.
Passing from the *compact* subintervals of `(0, a)` to the whole interval is
the Proved `continuousOn_Ioo_of_continuousOn_all_compact_subintervals`, fed by
the compact statement `generator_residual_continuousOn_compact_of_standing_bv_C2`.
Finally the half-line is the union of the intervals `(0, a)` over `a > 0`, and
`ContinuousOn.iUnion_of_isOpen` glues them.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi (0 : ℝ)) := by
  -- On each `(0, a)` the residual is continuous: first on the compact
  -- subintervals, then lifted to the whole interval.
  have hone : ∀ a : {a : ℝ // 0 < a},
      ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioo (0 : ℝ) ↑a) := by
    intro a
    have hcompact : ∀ l u : ℝ, 0 < l → l < u → u < ↑a →
        ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Icc l u) := by
      intro l u hl hlu hu
      have hu' : u < ↑a + 1 := by linarith
      exact generator_residual_continuousOn_compact_of_standing_bv_C2
        X hX hbv q W hW (↑a + 1) l u hl hlu hu'
        (hC2.mono (by
          intro z hz
          obtain ⟨hz1, hz2⟩ := Set.mem_Ioo.mp hz
          exact mem_Ioi.mpr (by linarith [hz1])))
    exact continuousOn_Ioo_of_continuousOn_all_compact_subintervals
      (fun x : ℝ => X.generator W x - q * W x) ↑a a.property hcompact
  -- The half-line is open and the pieces cover it, so the continuity glues.
  have hopen : ∀ a : {a : ℝ // 0 < a}, IsOpen (Ioo (0 : ℝ) ↑a) :=
    fun _ => isOpen_Ioo
  have hiu : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (⋃ a : {a : ℝ // 0 < a}, Ioo (0 : ℝ) ↑a) :=
    ContinuousOn.iUnion_of_isOpen hone hopen
  -- Every positive point is covered: `x < x + 1` and `x + 1` is admissible.
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
