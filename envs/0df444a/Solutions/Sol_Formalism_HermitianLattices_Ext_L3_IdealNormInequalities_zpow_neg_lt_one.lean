-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.zpow_neg_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:24.624326+00:00
-- url     : https://prove2.me/submissions/7d9a3b18-7f01-4257-95a3-ba941e67d743

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution {x : ℝ} (hx : 1 < x) {M : ℕ} (hM : 1 ≤ M) : x ^ (-(M : ℤ)) < 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
