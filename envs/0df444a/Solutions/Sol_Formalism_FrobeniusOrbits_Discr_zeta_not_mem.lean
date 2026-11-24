-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.zeta_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:12.213637+00:00
-- url     : https://prove2.me/submissions/6cf5269a-9841-4144-aab8-5672b9b88c1e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_not_real_zeta
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_real_on_adjoin
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_two_pow_not_dvd

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
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : z ∉ ℚ⟮z + z⁻¹⟯ := by
  intro h
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  let φ : K →+* ℂ := ((IsAlgClosed.lift : K →ₐ[ℚ] ℂ) : K →+* ℂ)
  have h1 := real_theta hm hz φ
  have h2 := real_on_adjoin (z + z⁻¹) φ h1 z h
  exact not_real_zeta hm (two_pow_not_dvd e) hz φ h2
end Formalism.FrobeniusOrbits.Discr
