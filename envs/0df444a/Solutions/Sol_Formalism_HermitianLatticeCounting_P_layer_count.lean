-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.layer_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:29.539711+00:00
-- url     : https://prove2.me/submissions/61a9a7dd-ea9b-4b25-913b-a68ab212ae9f

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LayerCount := by
  intro ι _ _ N de la laM hde hla hlaM
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 : (∏ _v : ι, 3 * de) ^ ((1 : ℝ) / Fintype.card ι) = 3*de := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [mul_one_div_cancel hc.ne', Real.rpow_one]
  rw [h1]
  have hM : 0 < laM := by linarith
  apply pow_le_pow_left₀ (by positivity)
  have : 2*(3*de)/laM ≤ 12*de/la := by
    rw [div_le_div_iff₀ hM hla]; nlinarith
  linarith
end Formalism.HermitianLatticeCounting.P
