-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:53.394124+00:00
-- url     : https://prove2.me/submissions/d96cbce6-355c-480a-9921-93b9d0009716

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hF : IsFixF K F) (u : 𝓞 K) : ∃ n₀ : 𝓞 F, ι n₀ = u * conjO K u := by
  have hs : star (jK (u * conjO K u)) = jK (u * conjO K u) := by
    rw [map_mul]
    show star (jK u * star (jK u)) = jK u * star (jK u)
    rw [star_mul, star_star, mul_comm]
  obtain ⟨f, hf⟩ := (hF _).mp hs
  have hint : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact (u * conjO K u).isIntegral_coe
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  exact ⟨⟨f, hint⟩, RingOfIntegers.ext hf⟩
end Formalism.HermitianLattices.Ext.L3.HU
