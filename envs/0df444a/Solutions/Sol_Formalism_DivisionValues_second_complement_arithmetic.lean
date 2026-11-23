-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:53.666412+00:00
-- url     : https://prove2.me/submissions/b5b4abb1-38e1-4c1e-90ed-acf8a1242863

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_finite
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_finsum_over
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_conj_nat
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_conj
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_sum_conj
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_sum_lw_vw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain Finset
noncomputable section
namespace Formalism.DivisionValues
namespace PlaceSumConjugation
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Star
end PlaceSumConjugation
open PlaceSumConjugation
private theorem lw_conjPl_lemma {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  have h : Ideal.absNorm (conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl).toEquiv.symm
  unfold lw
  rw [h]
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : Complement2Arith := by
  unfold Complement2Arith
  intro K _ _ _ _ g hg E F nn cg m Dpi Dp Dm er hE hF hcg hnn
  have hS := plOver_finite (K := K) g
  rw [finsum_over hS]
  have hmem : ∀ w, w ∈ hS.toFinset ↔ PlOver g w := fun w => by simp
  have hsc := sum_conj hS (fun w => lw w * E w)
  simp only [lw_conjPl_lemma] at hsc
  have hlog : ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) = Real.log g := sum_lw_vw K hg hS
  have hpt : ∀ w ∈ hS.toFinset, |lw w * E w + lw w * E (conjPl w) -
      (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))| ≤ 2 * er * (lw w * (vw w (g : K) : ℝ)) := by
    intro w hw
    have hw' := (hmem w).1 hw
    have hwc : PlOver g (conjPl w) := (plOver_conj g w).2 hw'
    have h1 := hE w hw'
    have h2 := hE (conjPl w) hwc
    rw [hF w hw'] at h1
    rw [hF (conjPl w) hwc, vw_conj_nat g w] at h2
    have h3 : ((vw w cg : ℤ) : ℝ) + ((vw (conjPl w) cg : ℤ) : ℝ) = 0 := by exact_mod_cast hcg w hw'
    have h5 : ((vw w cg : ℤ) : ℝ) / m + ((vw (conjPl w) cg : ℤ) : ℝ) / m = 0 := by
      rw [← add_div, h3, zero_div]
    have h4 := hnn w hw'
    have hl := lw_pos w
    have key : |E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ)| ≤
        2 * er * (vw w (g : K) : ℝ) := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc |lw w * E w + lw w * E (conjPl w) - (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))|
        = |lw w * (E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ))| := by
          congr 1; ring
      _ = lw w * |E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ)| := by
          rw [abs_mul, abs_of_pos hl]
      _ ≤ lw w * (2 * er * (vw w (g : K) : ℝ)) := mul_le_mul_of_nonneg_left key hl.le
      _ = 2 * er * (lw w * (vw w (g : K) : ℝ)) := by ring
  have h2sum : 2 * ∑ w ∈ hS.toFinset, lw w * E w =
      ∑ w ∈ hS.toFinset, (lw w * E w + lw w * E (conjPl w)) := by
    rw [Finset.sum_add_distrib, hsc]; ring
  rw [h2sum, ← hlog, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ w ∈ hS.toFinset, |lw w * E w + lw w * E (conjPl w) -
        (Dpi - Dp - Dm) * (lw w * (vw w (g : K) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ hS.toFinset, 2 * er * (lw w * (vw w (g : K) : ℝ)) := Finset.sum_le_sum hpt
end Formalism.DivisionValues
