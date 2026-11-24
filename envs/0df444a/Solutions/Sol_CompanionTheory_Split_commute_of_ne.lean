-- Prove2me | solution 1 for CompanionTheory.Split.commute_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:25.638117+00:00
-- url     : https://prove2.me/submissions/ff7a6842-3cd4-41b7-854b-215bf3215b97

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
theorem _root_.solution {v v' : HeightOneSpectrum (𝓞 L⁺)} (h : v ≠ v') {x y : GA L n} (hx : TrivOutside {v} x)
    (hy : TrivOutside {v'} y) : x * y = y * x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_compAt _ fun w => ?_)))
  have : (ent x * ent y).map (compAt L w) = (ent y * ent x).map (compAt L w) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rcases eq_or_ne w v with rfl | hw
    · rw [hy w h, mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun this i) j
end CompanionTheory.Split
