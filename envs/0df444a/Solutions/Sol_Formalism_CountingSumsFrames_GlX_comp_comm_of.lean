-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.comp_comm_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.019448+00:00
-- url     : https://prove2.me/submissions/1ab9a03b-aa80-4077-9dbb-6a3a55eb700b

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_isWt_of_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution {W : Submodule K V} (hW : G.Graded W) (φ : V →ₗ[K] V)
    (hφ : ∀ x ∈ W, ∀ c, φ (G.E c c x) = G.E c c (φ x)) :
    ∀ x ∈ W, ∀ μ, φ (G.comp μ x) = G.comp μ (φ x) := by
  classical
  intro x hx μ
  have hwt : ∀ ν, G.IsWt ν (φ (G.comp ν x)) := fun ν => isWt_of_eig G (fun c => by
    rw [← hφ _ (hW ν x hx) c, G.diag, map_smul])
  obtain ⟨S, hS⟩ := G.dec x
  have hx' := G.sum_comp x (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx']
  rw [map_sum, map_sum, Finset.sum_eq_single μ (fun ν _ hν => by rw [G.comp_of_isWt (hwt ν), if_neg (Ne.symm hν)])
    (fun h => absurd (Finset.mem_insert_self μ S) h), G.comp_of_isWt (hwt μ), if_pos rfl]
end Formalism.CountingSumsFrames.GlX
