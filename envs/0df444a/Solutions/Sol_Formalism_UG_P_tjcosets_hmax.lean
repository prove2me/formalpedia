-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_hmax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:30.813266+00:00
-- url     : https://prove2.me/submissions/1078ae85-771d-4a2f-9034-97995a772e00

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Theorems.Thm_Formalism_UG_P_tjcosets_lt_one_iff
import Theorems.Thm_Formalism_UG_P_tjcosets_mem_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (ϖ : v.adicCompletion F) (hϖ : IsUnifV F v ϖ) (x : Ov F v) :
    ϖ⁻¹ * (x : v.adicCompletion F) ∈ Ov F v ↔ IsLocalRing.residue (Ov F v) x = 0 := by
  rw [tjcosets_mem_max v x, tjcosets_lt_one_iff, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hϖ]
  have hc : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) ≠ 0 := WithZero.coe_ne_zero
  constructor
  · intro h
    have := mul_le_mul' (le_refl ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)) h
    rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul, mul_one] at this
  · intro h
    have := mul_le_mul' (le_refl (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)⁻¹)) h
    rwa [inv_mul_cancel₀ hc] at this
end Formalism.UG.P
