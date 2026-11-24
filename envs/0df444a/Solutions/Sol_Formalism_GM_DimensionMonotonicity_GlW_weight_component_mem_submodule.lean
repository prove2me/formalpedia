-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.weight_component_mem_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:10.536282+00:00
-- url     : https://prove2.me/submissions/28036a1c-c3ae-4392-9899-248e6088d1a8

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_Ecc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution [CharZero K] (U : Submodule K V) (hU : ∀ c, ∀ x ∈ U, G.E c c x ∈ U) :
    ∀ (S : Finset (Fin r → ℤ)) (x : V), x ∈ U → (∀ μ ∉ S, G.comp μ x = 0) → ∀ μ, G.comp μ x ∈ U := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro x hx hS μ
  by_cases hsub : ∃ ν ∈ S, ∃ ν' ∈ S, ν ≠ ν'
  · obtain ⟨ν, hν, ν', hν', hne⟩ := hsub
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ ν' c := by
      by_contra hcon
      push_neg at hcon
      exact hne (funext hcon)
    have key : ∀ κ ∈ S, μ c ≠ κ c → G.comp μ x ∈ U := by
      intro κ hκ hμκ
      have hyU : G.E c c x - ((κ c : ℤ) : K) • x ∈ U := U.sub_mem (hU c x hx) (U.smul_mem _ hx)
      have hcy : ∀ ρ, G.comp ρ (G.E c c x - ((κ c : ℤ) : K) • x) =
          (((ρ c : ℤ) : K) - ((κ c : ℤ) : K)) • G.comp ρ x := by
        intro ρ
        rw [map_sub, map_smul, G.comp_Ecc, sub_smul]
      have hyS : ∀ ρ ∉ S.erase κ, G.comp ρ (G.E c c x - ((κ c : ℤ) : K) • x) = 0 := by
        intro ρ hρ
        rw [hcy]
        by_cases hρκ : ρ = κ
        · rw [hρκ, sub_self, zero_smul]
        · have hρS : ρ ∉ S := fun h' => hρ (Finset.mem_erase.mpr ⟨hρκ, h'⟩)
          rw [hS ρ hρS, smul_zero]
      have h1 := ih (S.erase κ) (Finset.erase_ssubset hκ) _ hyU hyS μ
      rw [hcy] at h1
      have hne' : (((μ c : ℤ) : K) - ((κ c : ℤ) : K)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hμκ
      have h2 := U.smul_mem ((((μ c : ℤ) : K) - ((κ c : ℤ) : K))⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at h2
    by_cases h1 : μ c = ν c
    · exact key ν' hν' (by rw [h1]; exact hc)
    · exact key ν hν h1
  · push_neg at hsub
    by_cases hμ : μ ∈ S
    · have hsing : ∀ ρ ∉ ({μ} : Finset (Fin r → ℤ)), G.comp ρ x = 0 := by
        intro ρ hρ
        apply hS
        intro hρS
        exact hρ (Finset.mem_singleton.mpr (hsub ρ hρS μ hμ))
      have h2 := G.sum_comp x {μ} hsing
      rw [Finset.sum_singleton] at h2
      rw [h2]
      exact hx
    · rw [hS μ hμ]
      exact U.zero_mem
end Formalism.GM.DimensionMonotonicity.GlW
