-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.eulerFac_mul_conj_inv_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:50.7826+00:00
-- url     : https://prove2.me/submissions/5315e1ff-0577-421a-99db-8e2824afc9ec

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_zpow_neg_lt_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_conjIdeal


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ =
      1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
      Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [conjIdeal_conjIdeal hK]; exact hc.symm
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) :=
    sub_pos.mpr (zpow_neg_lt_one (one_lt_absNorm hP) hM)
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [if_neg hc, if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx]
  norm_num [Real.rpow_neg_one]
end Formalism.HermitianLattices.Ext.L3
