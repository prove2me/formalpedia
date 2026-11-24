-- Prove2me | solution 1 for Formalism.HN.sizeMu_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:36.941881+00:00
-- url     : https://prove2.me/submissions/8d34a6bc-83ba-4e31-af7b-fe23490f4844

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (f J C d : ℝ) (hf : 0 < f) (hJ : 0 < J) (hC : 0 < C) (hd : 0 < d) :
    ((2 : ℝ) ^ (f * J) * d ^ (-J / 2) * C) ^ ((1 : ℝ) / (2 * f * J)) =
      Real.exp (Real.log 2 / 2 - Real.log d / (2 * (2 * f)) - (-Real.log C) / ((2 * f) * J)) := by
  have h2 : (0 : ℝ) < 2 ^ (f * J) := Real.rpow_pos_of_pos two_pos _
  have hd' : 0 < d ^ (-J / 2) := Real.rpow_pos_of_pos hd _
  rw [Real.rpow_def_of_pos (mul_pos (mul_pos h2 hd') hC), Real.log_mul (mul_pos h2 hd').ne' hC.ne',
    Real.log_mul h2.ne' hd'.ne', Real.log_rpow two_pos, Real.log_rpow hd]
  congr 1
  field_simp
  ring
end Formalism.HN
