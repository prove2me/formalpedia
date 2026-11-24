-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrdUnimod.smul_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:39.049803+00:00
-- url     : https://prove2.me/submissions/82421b39-2066-46f4-b0c9-ab047ea762cc

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
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (B : Ideal (𝓞 (hostE ζ a b)))
    (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h' : σ⁻¹ • σ • B = σ⁻¹ • (⊥ : Ideal (𝓞 (hostE ζ a b))) := by rw [h]
  rw [inv_smul_smul] at h'
  rw [h']
  first
  | exact smul_bot _
  | exact Ideal.map_bot
  | (rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)
  | simp
end Formalism.FrobeniusOrbits.OrdUnimod
