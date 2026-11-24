-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.forms_induction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:51.989891+00:00
-- url     : https://prove2.me/submissions/c7aa701f-6572-4c30-b596-fd664375b012

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : FormsStep := by
  intro O _ A _ _ G _ Γ K jK T _ V W _ _ _ _ _ _ _ _ _ _ S F F' ψ hst hnat hker hsub f hf
  have hmem : (fun g => ψ ⟨(f : G → V) g, hf g⟩) ∈ Forms O Γ jK W := by
    intro γ g κ
    have h1 : (⟨(f : G → V) ((γ : G) * g * κ), hf _⟩ : F') = jK κ⁻¹ • ⟨(f : G → V) g, hf g⟩ :=
      Subtype.ext (f.2 γ g κ)
    show ψ _ = jK κ⁻¹ • ψ _
    rw [h1, map_smul]
  let φ : Forms O Γ jK W := ⟨_, hmem⟩
  have h0 : LocalizedModule.mk φ (1 : S) = LocalizedModule.mk 0 (1 : S) := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h0
  have hu' : (u : T) • φ = 0 := by
    simpa [Submonoid.smul_def] using hu
  refine ⟨u, u.2, fun g => ?_⟩
  apply hker ⟨_, hst F' u f hf g⟩
  rw [← hnat F' ψ u f φ hf (hst F' u f hf) (fun _ => rfl) g, hu']
  rfl
end Formalism.CohomologicalDescent.DepthNonnegative
