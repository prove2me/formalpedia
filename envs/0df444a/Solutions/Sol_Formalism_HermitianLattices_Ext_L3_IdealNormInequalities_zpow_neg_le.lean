-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.zpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:10.121099+00:00
-- url     : https://prove2.me/submissions/a287da41-5d33-4a6f-9c15-bf150160a55c

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
theorem _root_.solution {x p : ℝ} (hp : 1 ≤ p) (hx : p ≤ x) {M : ℕ} (hM : 2 ≤ M) :
    x ^ (-(M : ℤ)) ≤ (p ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_natCast]
  refine inv_anti₀ (by positivity) ?_
  calc p ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hx 2
    _ ≤ x ^ M := pow_le_pow_right₀ (by linarith) hM
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
