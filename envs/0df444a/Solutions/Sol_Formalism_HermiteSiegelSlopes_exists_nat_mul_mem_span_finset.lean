-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.exists_nat_mul_mem_span_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:26.84149+00:00
-- url     : https://prove2.me/submissions/0193f7ef-1c66-47bf-8f0e-d6cbc6b3a978

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_exists_nat_ne_zero_smul_mem_span_ringOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {K ι : Type} [Field K] [NumberField K] [Fintype ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → K) (s : Finset (ι → K))
    (hs : (s : Set (ι → K)) ⊆ Submodule.span K (Set.range e)) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x ∈ Submodule.span (𝓞 K) (s : Set (ι → K)),
      m • x ∈ Submodule.span (𝓞 K) (Set.range e) := by
  classical
  have h := fun z : s => exists_nat_ne_zero_smul_mem_span_ringOfIntegers e (z : ι → K) (hs z.2)
  choose m hm0 hmz using h
  refine ⟨∏ z : s, m z, Finset.prod_ne_zero_iff.2 fun z _ => hm0 z, ?_⟩
  let N : Submodule (𝓞 K) (ι → K) :=
    { carrier := {x | (∏ z : s, m z) • x ∈ Submodule.span (𝓞 K) (Set.range e)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *
        exact Submodule.add_mem _ ha hb
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hx }
  have hle : Submodule.span (𝓞 K) (s : Set (ι → K)) ≤ N := by
    rw [Submodule.span_le]
    intro z hz
    show (∏ w : s, m w) • z ∈ Submodule.span (𝓞 K) (Set.range e)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨z, hz⟩ : s)), mul_smul]
    exact Submodule.smul_of_tower_mem _ _ (hmz ⟨z, hz⟩)
  intro x hx
  exact hle hx
end Formalism.HermiteSiegelSlopes
