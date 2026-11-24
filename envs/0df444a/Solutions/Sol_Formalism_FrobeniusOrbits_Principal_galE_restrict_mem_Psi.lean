-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.galE_restrict_mem_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:19.362605+00:00
-- url     : https://prove2.me/submissions/1ef8c276-5605-4f65-bae4-7183c5bda3e2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_bE_mem_KinE
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) :
    galE e ζ a b (σ.restrictScalars ℚ) ∈ Psi e := by
  have h1 : (σ.restrictScalars ℚ) (bE ζ a b) = bE ζ a b := by
    first
    | exact σ.commutes ⟨bE ζ a b, bE_mem_KinE ζ a b⟩
    | simpa using σ.commutes ⟨bE ζ a b, bE_mem_KinE ζ a b⟩
  rw [Psi, MonoidHom.mem_ker]
  simp [chD, galE, sgn, h1]
end Formalism.FrobeniusOrbits.Principal
