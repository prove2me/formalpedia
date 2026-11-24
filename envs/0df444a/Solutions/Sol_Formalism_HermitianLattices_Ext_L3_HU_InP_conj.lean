-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.InP.conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:32:59.631598+00:00
-- url     : https://prove2.me/submissions/f3f17d70-4b2b-4c63-a72b-990be53a2697

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
namespace InP
theorem _root_.solution (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) :
    InP 𝔭 k (star a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  have hι : ∀ c : 𝓞 F, conjO K (ι c) = ι c := by
    intro c
    apply RingOfIntegers.ext
    show star (algebraMap F K (c : F)) = algebraMap F K (c : F)
    exact (hF _).mpr ⟨_, rfl⟩
  have hι' : (conjO K).comp (algebraMap (𝓞 F) (𝓞 K)) = algebraMap (𝓞 F) (𝓞 K) := RingHom.ext hι
  refine ⟨t, ht, conjO K z, ?_, ?_⟩
  · have h1 : conjO K z ∈ (extP K 𝔭 ^ k).map (conjO K) := Ideal.mem_map_of_mem _ hz
    rwa [Ideal.map_pow, extP, Ideal.map_map, hι'] at h1
  · have s1 : jK (conjO K z) = star (jK z) := rfl
    have s2 : star (jK (ι t)) = jK (ι t) := (hF _).mpr ⟨_, rfl⟩
    rw [s1, e, star_mul, s2, mul_comm]
end InP
end Formalism.HermitianLattices.Ext.L3.HU
