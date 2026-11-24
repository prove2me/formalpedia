-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.bdd_cutI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:40.593091+00:00
-- url     : https://prove2.me/submissions/b90c3adf-7038-4a8e-bcc2-3354b283a8de

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_q_ne
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_cutI_eq
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
private theorem continuousOn_mul_be_of_window (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) {S : Set ℝ}
    (hS : ∀ Y ∈ S, 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2) :
    ContinuousOn (fun Y => gm * c.be ka de de' T T' Y) S := by
  have hP : Continuous c.P := by
    show Continuous (fun Y : ℝ => ∏ s ∈ Icc 1 (c.k + c.m - 1), (Y + c.lam s))
    exact continuous_finsetProd _ (fun s _ => continuous_add_const _)
  have hq : Continuous (fun Y => c.q de de' T T' Y) := by
    show Continuous (fun Y : ℝ =>
      -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)))
    exact continuous_const.mul (continuous_finsetProd _ (fun i _ => by fun_prop))
  have hP1 : Continuous (fun Y : ℝ => c.P (Y + 1)) := hP.comp (continuous_add_const 1)
  have hd : ContinuousOn (fun Y => c.P Y * c.P (Y + 1) / c.q de de' T T' Y) S :=
    (hP.mul hP1).continuousOn.div hq.continuousOn
      (fun Y hY => q_ne c hOk hb1 hw hw' hl hT hT' (hS Y hY).1 (hS Y hY).2)
  have h : ContinuousOn (fun Y => gm * ((ka ^ (c.m - 1))⁻¹ *
      Real.sqrt |c.P Y * c.P (Y + 1) / c.q de de' T T' Y|)) S :=
    continuousOn_const.mul (continuousOn_const.mul hd.abs.sqrt)
  exact h
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
theorem _root_.solution (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) :
    BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  rw [cutI_eq c l]
  exact isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm
    (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))
end Formalism.L2.SG.Pf.ThresholdBounds
