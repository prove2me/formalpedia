-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.eab_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:02:53.373022+00:00
-- url     : https://prove2.me/submissions/40c1dbcd-c4ac-49b5-85d9-b497965c4a03

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_rdV_ext
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  set X₁ := hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)
  set X₂ := hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)
  obtain ⟨h1, h2⟩ := hpart_mem (k := k) i p q
  refine ⟨U, fun x => fderiv ℝ F x (x * X₁) + Complex.I • fderiv ℝ F x (x * X₂), hU, hg₀U, ?_, ?_⟩
  · have hd := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have s1 : ContDiffOn ℝ ∞ (fun x : Mx k r => fderiv ℝ F x (x * X₁)) U :=
      hd.clm_apply (mulRightRealCLM X₁).contDiff.contDiffOn
    have s2 : ContDiffOn ℝ ∞ (fun x : Mx k r => fderiv ℝ F x (x * X₂)) U :=
      hd.clm_apply (mulRightRealCLM X₂).contDiff.contDiffOn
    exact s1.add (s2.const_smul Complex.I)
  · intro x hx hxG
    show RdV X₁ f x + Complex.I • RdV X₂ f x = _
    rw [rdV_ext i X₁ h1 f F U x hU hx hxG hF hfF, rdV_ext i X₂ h2 f F U x hU hx hxG hF hfF]
end Formalism.FourierDecayAlt.Q.EabLie
