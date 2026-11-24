-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.gExp_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.086948+00:00
-- url     : https://prove2.me/submissions/a92769de-432f-4897-a5f0-7b018efe237d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {t : ℝ} (ht : 0 < t) : gExp t ≤ 0 := by
  unfold gExp
  have h1 : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have : 1 / (Real.exp t - 1) ≤ 1 / t := one_div_le_one_div_of_le ht h1
  linarith
end Formalism.HermitianLattices.Ext.SupplyAP
