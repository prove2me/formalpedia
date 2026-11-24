-- Prove2me | solution 1 for CompanionTheory.Split.mem_KL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:20.401694+00:00
-- url     : https://prove2.me/submissions/f95e3050-76d4-4c3a-a8aa-0c4728fcca27

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Theorems.Thm_Formalism_UG_P_levelaf_mem_range_of_integral


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
theorem _root_.solution {g : GL (Fin n) (s.v.adicCompletion L⁺)} : g ∈ KL s n ↔
    (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [← map_inv]
    exact ⟨fun i j => ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring) i j).2,
      fun i j => (((a⁻¹ : GL (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring) i j).2⟩
  · rintro ⟨h1, h2⟩
    exact Formalism.UG.P.levelaf_mem_range_of_integral _ g ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, rfl⟩
      ⟨Matrix.of fun i j => ⟨_, h2 i j⟩, rfl⟩
end CompanionTheory.Split
