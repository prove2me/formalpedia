-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrdUnimod.integ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:50.748216+00:00
-- url     : https://prove2.me/submissions/7b5bd6e6-e1b4-46be-bd04-a672d24e305d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod
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
open Formalism.FrobeniusOrbits.OrdUnimod
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.OrdUnimod
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (t : hostE ζ a b) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t := by
  first
  | exact isIntegral_algEquiv (σ.restrictScalars ℤ)
  | exact ⟨fun h => by simpa using h.map (σ.symm.toAlgHom.restrictScalars ℤ),
      fun h => h.map (σ.toAlgHom.restrictScalars ℤ)⟩
end Formalism.FrobeniusOrbits.OrdUnimod
