-- Prove2me | solution 1 for Formalism.DivisionValues.place_sum_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:17.301164+00:00
-- url     : https://prove2.me/submissions/dbaa3588-db74-4e6f-9b11-d52a8bbf6753

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_lw_nonneg
import Theorems.Thm_Formalism_DivisionValues_W5_vw_nat_nonneg
import Theorems.Thm_Formalism_LatticeIndexTer_log_product_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : PlaceSumNat := by
  intro K _ _ n hn
  classical
  have ha : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  set I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (n : K) with hIdef
  have hD := Formalism.LatticeIndexTer.log_product_formula K (n : K) ha
  have hdeg : (finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  set g : HeightOneSpectrum (𝓞 K) → ℝ := fun w =>
    (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) with hg
  have hgfin : (Function.support g).Finite := by
    have hf := FractionalIdeal.finite_factors (K := K) I
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    intro h0
    apply hw
    simp only [hg, h0, Int.cast_zero, zero_mul]
  have hfun : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)) =
      fun w => (finrank ℚ K : ℝ)⁻¹ * g w := by
    funext w
    simp only [lw, vw, hg, hIdef]
    field_simp
  have hfin : (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (vw w (n : K) : ℝ)).Finite := by
    rw [hfun]
    exact hgfin.subset (Function.support_mul_subset_right _ _)
  have hlhs : ∑ σ : K →+* ℂ, Real.log ‖σ (n : K)‖ = (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    have : ∀ σ : K →+* ℂ, Real.log ‖σ (n : K)‖ = Real.log (n : ℝ) := by
      intro σ
      rw [map_natCast, Complex.norm_natCast]
    rw [Finset.sum_congr rfl (fun σ _ => this σ), Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card, nsmul_eq_mul]
  have hsum : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) := by
    rw [hfun, ← mul_finsum, hg, ← hD, hlhs]
    field_simp
  refine ⟨hfin, hsum, fun S => ?_⟩
  rw [← hsum, finsum_eq_sum_of_support_subset (s := S ∪ hfin.toFinset) _ (by
    intro w hw
    rw [Finset.coe_union]
    exact Or.inr (by simpa using hw))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun w _ _ => mul_nonneg (W5.lw_nonneg w) (by exact_mod_cast W5.vw_nat_nonneg w n))
end Formalism.DivisionValues
