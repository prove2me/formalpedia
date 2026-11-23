-- Prove2me | solution 1 for Formalism.L2.G.ServJoint.VGeq.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:16.117801+00:00
-- url     : https://prove2.me/submissions/c3c175d6-0c90-4bbc-b84d-cbb10f6569bb

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
namespace Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vAdd_le_of_valuation_le {w : HeightOneSpectrum (𝓞 K)} {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : w.valuation K y ≤ w.valuation K x) : vAdd w x ≤ vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have h' : WithZero.exp (WithZero.log (w.valuation K y)) ≤ WithZero.exp (WithZero.log (w.valuation K x)) := by
    rwa [WithZero.exp_log hx', WithZero.exp_log hy']
  have h'' := WithZero.exp_le_exp.mp h'
  unfold Formalism.BasicNotions.vAdd
  linarith
end Formalism.L2.G.ServJoint
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.G.ServJoint
namespace VGeq
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a b : K} (ha : VGeq w s a) (hb : VGeq w s b) :
    VGeq w s (a + b) := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hb
  by_cases hb0 : b = 0
  · simpa [hb0] using ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  rcases ha with h | ha
  · exact absurd h ha0
  rcases hb with h | hb
  · exact absurd h hb0
  right
  rcases le_max_iff.mp ((w.valuation K).map_add a b) with h | h
  · exact ha.trans (by exact_mod_cast vAdd_le_of_valuation_le ha0 hab h)
  · exact hb.trans (by exact_mod_cast vAdd_le_of_valuation_le hb0 hab h)
end VGeq
end Formalism.L2.G.ServJoint
