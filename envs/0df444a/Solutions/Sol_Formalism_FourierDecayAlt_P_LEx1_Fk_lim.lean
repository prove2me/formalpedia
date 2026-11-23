-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.Fk_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:29.423665+00:00
-- url     : https://prove2.me/submissions/b0696f89-da95-449c-8d39-9aa643d7cfbe

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (k : ℕ) (s : ℝ) : Tendsto (Fk k s) atTop (𝓝 (if k = 0 then 1 else 0)) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-t)) ^ (-s)) atTop (𝓝 1) := by
    have := (h0.const_add 1).rpow_const (p := -s) (Or.inl (by norm_num))
    simpa using this
  unfold Fk
  split_ifs with hk
  · subst hk; simpa using h1
  · have h2 : Tendsto (fun t : ℝ => Real.exp (-(k:ℝ) * t)) atTop (𝓝 0) := by
      have hk' : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have : Tendsto (fun t : ℝ => (k:ℝ) * t) atTop atTop := tendsto_id.const_mul_atTop hk'
      have := h0.comp this
      simpa [Function.comp_def] using this
    simpa using h2.mul h1
end Formalism.FourierDecayAlt.P.LEx1
