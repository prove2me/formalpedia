-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.vF_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:20.054779+00:00
-- url     : https://prove2.me/submissions/13103088-3956-4fe7-8b22-f403d306c5aa

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_L2_SG_Pf_G1_vF_eq_multiplicity

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {F : Type} [Field F] [NumberField F] {𝔭 : Ideal (𝓞 F)}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    vF 𝔭 (a * b) = vF 𝔭 a + vF 𝔭 b := by
  have hz : ∀ {t : 𝓞 F}, t ≠ 0 → Ideal.span {t} ≠ 0 := fun ht => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ht
  have hne : 𝔭 ≠ ⊥ := fun h =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h ▸ h𝔭))
  have hp : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  rw [vF_eq_multiplicity h𝔭 ha, vF_eq_multiplicity h𝔭 hb, vF_eq_multiplicity h𝔭 (mul_ne_zero ha hb),
    ← Ideal.span_singleton_mul_span_singleton]
  refine multiplicity_mul hp (FiniteMultiplicity.of_not_isUnit hp.not_unit ?_)
  rw [Ideal.span_singleton_mul_span_singleton]
  exact hz (mul_ne_zero ha hb)
end Formalism.L2.SG.Pf.G1
