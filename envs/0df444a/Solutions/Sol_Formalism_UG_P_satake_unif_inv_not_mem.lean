-- Prove2me | solution 1 for Formalism.UG.P.satake_unif_inv_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:29.919688+00:00
-- url     : https://prove2.me/submissions/4711a347-6e11-4b99-8365-8526d4ca2410

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
private theorem mem_Ov_iff' (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  unfold Ov
  first
    | exact Iff.rfl
    | exact mem_adicCompletionIntegers
    | simp [mem_adicCompletionIntegers]
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by
  unfold IsUnifV at h
  intro hm
  have hm' : Valued.v ϖ⁻¹ ≤ 1 := (mem_Ov_iff' v _).mp hm
  rw [map_inv₀, h] at hm'
  have h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_inv]
    first | exact_mod_cast hm' | simpa using hm'
  have h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ) := h4
  simp at h5
end Formalism.UG.P
