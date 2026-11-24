-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.span_pow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.010159+00:00
-- url     : https://prove2.me/submissions/d713b4c8-454a-4661-af43-aa8db755d32c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {π₀ s₀ : 𝓞 F}
    (h : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}) (k : ℕ) :
    Ideal.span {ι (s₀ ^ k)} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π₀ ^ k)} := by
  have h1 : (Ideal.span {s₀} * 𝔭) ^ k ≤ Ideal.span {π₀} ^ k := Ideal.pow_right_mono h k
  rw [mul_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  have h2 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h1
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.map_pow] at h2
  exact h2
end Formalism.HermitianLattices.Ext.L3.HU
