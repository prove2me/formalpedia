-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.abs_log_eulerFac_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:53.93343+00:00
-- url     : https://prove2.me/submissions/3ae15d15-f1fe-4ce8-8375-4576f168ca12

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_add_smallTerm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_eulerFac_eq

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P)| ≤ |Real.log (1 + smallTerm M P)| := by
  rw [eulerFac_eq]
  split_ifs with hc
  · rw [Real.log_inv, abs_neg]
  · rw [Real.log_rpow (one_add_smallTerm_pos hP hM), abs_mul]
    have : |(-(1 : ℝ) / 2)| = 1 / 2 := by rw [abs_of_nonpos (by norm_num)]; norm_num
    rw [this]
    nlinarith [abs_nonneg (Real.log (1 + smallTerm M P))]
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
