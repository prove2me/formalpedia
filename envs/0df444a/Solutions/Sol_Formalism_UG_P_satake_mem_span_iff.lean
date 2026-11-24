-- Prove2me | solution 1 for Formalism.UG.P.satake_mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:04.234863+00:00
-- url     : https://prove2.me/submissions/cab63c44-6931-4800-a062-8ef61d754142

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Theorems.Thm_Formalism_UG_P_satake_unif_ne_zero
import Theorems.Thm_Formalism_UG_P_satake_lt_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ)
    (y : Ov F v) : y ∈ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)} ↔ Valued.v (y : v.adicCompletion F) < 1 := by
  have h0 := satake_unif_ne_zero v h
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1 := z.2
    show Valued.v ((z : v.adicCompletion F) * ϖ) < 1
    rw [Valuation.map_mul, h]
    calc Valued.v (z : v.adicCompletion F) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]
          show (-1 : ℤ) < 0
          omega
  · intro hy
    have hle := satake_lt_one_le hy
    have hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v := by
      show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1
      rw [Valuation.map_mul, Valuation.map_inv, h]
      calc Valued.v (y : v.adicCompletion F) * (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹
          ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
              (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ :=
            by gcongr
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y
    field_simp
end Formalism.UG.P
