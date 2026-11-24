-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.form_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:18.336908+00:00
-- url     : https://prove2.me/submissions/815f6481-7bf9-40ed-8d8c-7231b2b67a6a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le_Lw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution {W : Submodule K V} (hW : G.Stable W) {ι : Type} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hsp : W ≤ ⨆ i, G.gS {h i})
    (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x ∈ W, ∀ y ∈ W, ∀ a b, B (G.E a b x) y = B x (G.E b a y))
    (h0 : ∀ i j, la i = la j → B (h i) (h j) = 0) : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by

  have h1 : ∀ i j, B (h i) (h j) = 0 := by
    intro i j
    by_cases hij : la i = la j
    · exact h0 i j hij
    · obtain ⟨c, hc⟩ : ∃ c, la i c ≠ la j c := by
        by_contra hcon; exact hij (funext fun c => by by_contra hc; exact hcon ⟨c, hc⟩)
      have e := hB (h i) (hhW i) (h j) (hhW j) c c
      rw [G.E_diag_of_isWt (hh i).1, G.E_diag_of_isWt (hh j).1, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul] at e
      have e2 : (((la i c : ℤ) : K) - ((la j c : ℤ) : K)) * B (h i) (h j) = 0 := by rw [sub_mul, e, sub_self]
      rcases mul_eq_zero.mp e2 with h3 | h3
      · exfalso; apply hc
        have : ((la i c : ℤ) : K) = ((la j c : ℤ) : K) := sub_eq_zero.mp h3
        exact_mod_cast this
      · exact h3

  have h2 : ∀ i, ∀ y ∈ W, B (h i) y = 0 := by
    intro i y hy
    have hle : ∀ j, G.gS {h j} ≤ W ⊓ LinearMap.ker (B (h i)) := by
      intro j
      refine (G.gS_le_Lw (hh j)).trans (G.Lw_le (h j) ⟨hhW j, LinearMap.mem_ker.mpr (h1 i j)⟩ ?_)
      intro a b hba x hx
      refine ⟨hW a b x hx.1, LinearMap.mem_ker.mpr ?_⟩
      rw [← hB (h i) (hhW i) x hx.1 b a, (hh i).2 b a hba, map_zero, LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp ((iSup_le hle) (hsp hy)).2

  let U : Submodule K V :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ W, B x y = 0}
      add_mem' := fun {x x'} hx hx' => ⟨W.add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, add_zero]⟩
      zero_mem' := ⟨W.zero_mem, fun y _ => by rw [map_zero, LinearMap.zero_apply]⟩
      smul_mem' := fun t x hx => ⟨W.smul_mem t hx.1, fun y hy => by
        rw [map_smul, LinearMap.smul_apply, hx.2 y hy, smul_zero]⟩ }
  have hU : G.Stable U := fun a b x hx => ⟨hW a b x hx.1, fun y hy => by
    rw [hB x hx.1 y hy a b]; exact hx.2 _ (hW b a y hy)⟩
  have hle : ∀ i, G.gS {h i} ≤ U := fun i =>
    G.gS_le (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact ⟨hhW i, h2 i⟩) hU
  intro x hx y hy
  exact ((iSup_le hle) (hsp hx)).2 y hy
end Formalism.CountingSumsFrames.TO.GlX
