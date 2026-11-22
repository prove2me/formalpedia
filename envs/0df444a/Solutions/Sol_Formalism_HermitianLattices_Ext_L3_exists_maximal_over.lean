-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_maximal_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:45.283293+00:00
-- url     : https://prove2.me/submissions/a534370a-02a8-4f85-919e-f565a42f334e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact FaithfulSMul.algebraMap_injective _ _
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       exact congrArg (fun z : 𝓞 K => (z : K)) hab)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hker
end Formalism.HermitianLattices.Ext.L3
