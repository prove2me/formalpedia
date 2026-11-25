-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.supI_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:03.387301+00:00
-- url     : https://prove2.me/submissions/59aecf76-6e18-4669-bd27-66a55dc0758e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_q_ne
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_P_ne
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_bdd_cutI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
private theorem mul_be_pos_of_isWord (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm)
    (hN : 11 / 4 ≤ c.Del / 2) : 0 < gm * c.be ka de de' T T' (11 / 4 - c.v l) := by
  have hP0 : c.P (11 / 4 - c.v l) ≠ 0 := P_ne c hOk hb1 hl (by norm_num) (by norm_num)
  have hP1 : c.P (11 / 4 - c.v l + 1) ≠ 0 := by
    have h := P_ne c hOk hb1 hl (t := 15 / 4) (by norm_num) (by norm_num)
    rwa [show (15 / 4 : ℝ) - c.v l = 11 / 4 - c.v l + 1 by ring] at h
  have hq : c.q de de' T T' (11 / 4 - c.v l) ≠ 0 :=
    q_ne c hOk hb1 hw hw' hl hT hT' (by linarith) (by linarith)
  have hs : 0 < Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  show 0 < gm * ((ka ^ (c.m - 1))⁻¹ *
    Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)|)
  exact mul_pos hgm (mul_pos (inv_pos.mpr (pow_pos hka _)) hs)
end Formalism.L2.SG.Pf.ThresholdBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) (hD : 11 / 2 ≤ c.Del) {de de' : ℕ → ℝ}
    (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0)
    (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  have hbdd := bdd_cutI c hOk hb1 hw hw' hl hT hT' ka gm
  have hY0 : (11 / 4 - c.v l) ∈ c.cutI l := by
    show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ c.Del / 2
    constructor <;> linarith
  exact lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith))
    (le_csSup hbdd ⟨_, hY0, rfl⟩)
end Formalism.L2.SG.Pf.ThresholdBounds
