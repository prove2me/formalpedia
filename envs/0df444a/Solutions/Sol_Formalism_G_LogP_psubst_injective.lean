-- Prove2me | solution 1 for Formalism.G.LogP.psubst_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:24.414816+00:00
-- url     : https://prove2.me/submissions/d1f1c3aa-a9aa-489b-b6fd-430d532b9946

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by
  have : Invertible (PowerSeries.coeff 1 f) := hf1 ▸ invertibleOne
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c := by
    intro c hc
    have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero hc
    rw [← PowerSeries.subst_comp_subst_apply hfs hcs, PowerSeries.subst_substInv_left f hf0,
      PowerSeries.subst_X hcs]
  rw [← inv a ha, h, inv b hb]
end Formalism.G.LogP
