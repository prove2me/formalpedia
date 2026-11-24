-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.eulerFac_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:18.676846+00:00
-- url     : https://prove2.me/submissions/103c8c2f-e7de-4c08-908b-3aa3935ae140

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
open IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (M : ℕ)
    (hM : 1 ≤ M) : 0 < Formalism.HermitianLatticesTheory.eulerFac K M P := by
  rw [eulerFac_eq]
  split_ifs with hc
  · exact inv_pos.mpr (one_add_smallTerm_pos hP hM)
  · exact Real.rpow_pos_of_pos (one_add_smallTerm_pos hP hM) _
end Formalism.HermitianLattices.Ext.L3
