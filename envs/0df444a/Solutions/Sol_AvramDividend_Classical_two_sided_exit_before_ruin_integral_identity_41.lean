-- Prove2me | solution 41 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T03:09:46.903129+00:00
-- url     : https://prove2.me/submissions/a051a460-0c02-4c36-b936-e7d0f4c294ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Repair of CE 18063 (single group E01): the generic `eq_div_iff_mul_eq`
-- cannot engage ENNReal here — three orientations (18019/18047/18061/18063)
-- all died with fully schematic `?m/?u` expected types, i.e. the
-- GroupWithZero unification never fires for ENNReal. Pinned
-- `ENNReal.eq_div_iff : a ≠ 0 → a ≠ ⊤ → (b = c / a ↔ a * b = c)`
-- (index-confirmed at rev 0df444a3 with compiler-printed type) is the
-- ENNReal-native bridge: goal after `rw [hdiv]` is `J = Ox / Oa`, and
-- `(mul_comm _ _).trans hStop : Oa * J = Ox` feeds `.mpr` with closed types.
-- `hbTop` is unconditional `ENNReal.ofReal_ne_top`. Full `import Mathlib`
-- so the Inv-module lemma resolves. All else byte-identical to CE parent.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  have hStop :=
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  have hpos :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hb : ENNReal.ofReal (W a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hpos
  have hdiv : ENNReal.ofReal (W x / W a)
      = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
    ENNReal.ofReal_div_of_pos hpos
  have hbTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hdiv]
  exact (ENNReal.eq_div_iff hb hbTop).mpr ((mul_comm _ _).trans hStop)
