-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.diff_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:56.712201+00:00
-- url     : https://prove2.me/submissions/1079d453-f2b7-4486-8dbb-ae62e1db4b85

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_comm_of
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_diff_smul_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_diff_smul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b)) :
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := by
  refine le_antisymm (diff_smul_le hqd h σ (comm_of hqd h σ)) ?_
  intro z hz
  have h2 := Ideal.smul_mem_pointwise_smul σ _ _
    (diff_smul_mem hqd h σ⁻¹ (comm_of hqd h σ⁻¹) z hz)
  rwa [smul_inv_smul] at h2
end Formalism.FrobeniusOrbits.Principal
