-- Prove2me | solution 1 for CompanionTheory.Split.emb_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:47:18.781752+00:00
-- url     : https://prove2.me/submissions/768bc3cc-950e-4d57-b94e-43c4404ec1df

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
theorem _root_.solution (g : GL (Fin n) (s.v.adicCompletion L⁺)) : TrivOutside {s.v} (emb s n g) :=
  mem_Gv.1 ((locEquiv s n).symm g).2
end CompanionTheory.Split
