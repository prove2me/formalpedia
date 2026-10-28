-- Prove2me | solution 4 for AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:42:08.191226+00:00
-- url     : https://prove2.me/submissions/6008973a-be55-4cbe-9f58-6cb4a5191887
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_reflected_reward_of_renewal_finite_difference_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  -- Repair of candidate 15693 (terminal CE, 3 independent groups), sorry-free
  -- reduction per lint-submit 'prove' semantics (Open children imported; an
  -- Open-dependent reduction may return SKETCH_ACCEPTED, never ACCEPTED).
  -- E01 (unknown `scaleFunction_strict_pos_of_standing` at old L20): fixed by
  --   the added Theorems import. The declaration is Proved 59531c77 with
  --   signature (X hX q hq W hW a ha) : 0 < W a, matching this call exactly.
  -- E02 (`ha_mem : a ∈ Ici 0` passed where `Ici 0 ∈ 𝓝 a` is required):
  --   step down to Ioi 0 (Set.Ioi_subset_Ici_self) and use
  --   isOpen_Ioi.mem_nhds from ha : 0 < a; no filter-membership guess.
  -- E03 (bare `simp` no progress at old L27): replaced by the explicit
  --   C1 -> DifferentiableAt -> HasDerivAt chain plus the Proved sandwich
  --   319da48e fed by the two Open renewal bounds. Uses only
  --   ContDiffOn.differentiableOn with one_ne_zero: remote CE 16995 shows the
  --   Mathlib entry point now takes (1 : WithTop ENat) ≠ 0, not 1 ≤ 1.
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hmem : a ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr ha
  have hcont : ContinuousAt W a :=
    (hW.2.2.1.mono Set.Ioi_subset_Ici_self).continuousAt
      (isOpen_Ioi.mem_nhds hmem)
  have hC1 :=
    AvramDividend.Classical.scaleFunction_contDiff_one
      X hX q hq W hW
  have hDiffOn : DifferentiableOn ℝ W (Set.Ioi (0 : ℝ)) :=
    hC1.differentiableOn one_ne_zero
  have hDiff : DifferentiableAt ℝ W a :=
    hDiffOn.differentiableAt (isOpen_Ioi.mem_nhds hmem)
  have hD : HasDerivAt W (deriv W a) a := hDiff.hasDerivAt
  have hpos : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos
      X hX q hq W hW a ha
  have hd : deriv W a ≠ 0 := ne_of_gt hpos
  have hLo :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hD hd
  have hHi :=
    AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hD hd
  exact AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
    W a (deriv W a) hD hd (barrierSupValue X a q) hLo hHi
