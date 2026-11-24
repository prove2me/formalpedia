-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.isWt_of_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:33.991902+00:00
-- url     : https://prove2.me/submissions/83c0950a-b4b0-431b-8d64-b03f9e0506cf

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_Ecc


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
theorem _root_.solution {μ : Fin r → ℤ} {z : V} (hz : ∀ c, G.E c c z = ((μ c : ℤ) : K) • z) : G.IsWt μ z := by
  classical
  obtain ⟨S, hS⟩ := G.dec z
  have hz' := G.sum_comp z (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  have h0 : ∀ ν, ν ≠ μ → G.comp ν z = 0 := by
    intro ν hν
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ μ c := by
      by_contra h; exact hν (funext fun c => by by_contra hc; exact h ⟨c, hc⟩)
    have e1 := G.comp_Ecc ν c z
    rw [hz c, map_smul] at e1
    have : (((μ c : ℤ) : K) - ((ν c : ℤ) : K)) • G.comp ν z = 0 := by rw [sub_smul, e1, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exfalso; apply hc
      have : ((μ c : ℤ) : K) = ((ν c : ℤ) : K) := sub_eq_zero.mp h
      exact_mod_cast this.symm
    · exact h
  show G.comp μ z = z
  conv_rhs => rw [← hz']
  rw [Finset.sum_eq_single μ (fun ν _ hν => h0 ν hν) (fun h => absurd (Finset.mem_insert_self μ S) h)]
end Formalism.CountingSumsFrames.GlX
