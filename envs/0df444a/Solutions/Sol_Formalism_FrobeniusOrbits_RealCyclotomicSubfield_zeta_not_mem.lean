-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.zeta_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:40.961547+00:00
-- url     : https://prove2.me/submissions/0f3cf4a3-5938-4fdb-b1d6-b5f90510775b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_not_real_zeta
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_two_pow_not_dvd
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_subfield_real_embeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) : ζ ∉ F1 ζ := by
  intro h
  let φ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  exact not_real_zeta (by positivity) (two_pow_not_dvd e) hζ φ (real_subfield_real_embeddings hζ ζ h φ)
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
