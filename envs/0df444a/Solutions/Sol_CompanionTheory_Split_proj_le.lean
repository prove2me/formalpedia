-- Prove2me | solution 1 for CompanionTheory.Split.proj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:20.601334+00:00
-- url     : https://prove2.me/submissions/99d8c066-23ba-4e5d-9927-161085601a06

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
namespace CompanionTheory.Split
theorem _root_.solution {z : AL L} (hz : z ∈ ALint L) : Valued.v (s.proj z) ≤ 1 := by
  have : ALint L ≤ (s.v.adicCompletionIntegers L⁺).toSubring.comap s.proj := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show Valued.v (s.i y * 1) ≤ 1
      rw [mul_one]
      exact s.split_le_one y
    · show s.i 1 * a s.v ∈ s.v.adicCompletionIntegers L⁺
      rw [map_one, one_mul]
      exact ha _
  exact this hz
end CompanionTheory.Split
