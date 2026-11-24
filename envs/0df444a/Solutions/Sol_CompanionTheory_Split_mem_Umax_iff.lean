-- Prove2me | solution 1 for CompanionTheory.Split.mem_Umax_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:31.248311+00:00
-- url     : https://prove2.me/submissions/214409f1-fef7-4ed7-9ef9-e3401ae03421

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Theorems.Thm_CompanionTheory_Split_mem_KL
import Theorems.Thm_CompanionTheory_Split_loc_mem_KL
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep
import Theorems.Thm_GlobalTheory_mem_ALint_of_supported_at_split


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
theorem _root_.solution {x : GA L n} (hx : TrivOutside {s.v} x) : x ∈ Umax L n ↔ s.loc n x ∈ KL s n := by
  refine ⟨loc_mem_KL s, fun h i j => ?_⟩
  obtain ⟨h1, h2⟩ := (mem_KL s).1 h
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hz := GlobalTheory.mem_ALint_of_supported_at_split L s e he he' _ (fun w => sub_one_supp hx i j)
    (by rw [map_sub, map_one_apply]; exact (Valuation.map_sub _ _ _).trans (max_le (h1 i j) (hone i j)))
    (by
      rw [map_sub, map_sub, ← ent_inv, map_one_apply, map_one_apply, ← loc_apply, map_inv]
      exact (Valuation.map_sub _ _ _).trans (max_le (h2 j i) (hone i j)))
  have := add_mem hz ((Umax L n).one_mem i j)
  rwa [show ((1 : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) = 1 from rfl, sub_add_cancel] at this
end CompanionTheory.Split
