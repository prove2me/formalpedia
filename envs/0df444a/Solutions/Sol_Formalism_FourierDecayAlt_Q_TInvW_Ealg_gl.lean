-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.Ealg_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:29.526694+00:00
-- url     : https://prove2.me/submissions/9855b965-93e8-4b57-a936-41d0929ed069

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_E_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD
variable (hG : EabGlLev)
include hG
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution : GlRel (Ealg (E := E) (i := i) hP hC hD) := by
  intro a b c d
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have r0 : Rep (ext k r i D x.1) x.1 := rep_ext x.1
  have hab := E_rep hP hC hD (E_rep hP hC hD r0 c d) a b g hg
  have hcd := E_rep hP hC hD (E_rep hP hC hD r0 a b) c d g hg
  have had := E_rep hP hC hD r0 a d g hg
  have hcb := E_rep hP hC hD r0 c b g hg
  have key := hG E k r i D a b c d (ext k r i D x.1) hD x.2 g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← hab, ← hcd, key]
  split_ifs <;> simp [had, hcb]
end Formalism.FourierDecayAlt.Q.TInvW
