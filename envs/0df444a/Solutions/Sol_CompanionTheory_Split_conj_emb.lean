-- Prove2me | solution 1 for CompanionTheory.Split.conj_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:10.979386+00:00
-- url     : https://prove2.me/submissions/aa0e790e-389a-42bf-b5af-f93f3ce3266d

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Theorems.Thm_CompanionTheory_Split_emb_triv
import Theorems.Thm_CompanionTheory_Split_loc_emb
import Theorems.Thm_CompanionTheory_Split_emb_loc

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
theorem _root_.solution (x : GA L n) (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    x * emb s n g * x⁻¹ = emb s n (s.loc n x * g * (s.loc n x)⁻¹) := by
  rw [← emb_loc s (mem_Gv.1 ((Gv_normal _).conj_mem _ (mem_Gv.2 (emb_triv s g)) x)), map_mul (s.loc n), map_mul (s.loc n), map_inv (s.loc n), loc_emb]
end CompanionTheory.Split
