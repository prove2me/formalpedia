-- Prove2me | solution 1 for CompanionTheory.Split.loc_mem_KL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:11.88414+00:00
-- url     : https://prove2.me/submissions/93039013-9c86-42c0-af42-777721c68f5c

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Theorems.Thm_CompanionTheory_Split_proj_le
import Theorems.Thm_CompanionTheory_Split_mem_KL

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
theorem _root_.solution {x : GA L n} (hx : x ∈ Umax L n) : s.loc n x ∈ KL s n :=
  (mem_KL s).2 ⟨fun i j => proj_le s (hx i j), fun i j => by
    rw [← map_inv]
    exact proj_le s ((Umax L n).inv_mem hx i j)⟩
end CompanionTheory.Split
