-- Prove2me | solution 1 for Formalism.GM.lieRoots_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:26.963586+00:00
-- url     : https://prove2.me/submissions/5898e628-f5a6-4a98-9968-ba29263f50c5

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_C
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_lin
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_multiset_prod
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_le_sum
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_neg
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_add
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_sum_mul_left
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_card_filter_eq_sum
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_prod_pos
import Theorems.Thm_Formalism_GM_GaussNormRoots_logb_multiset_prod
import Theorems.Thm_Formalism_GM_GaussNormRoots_vmin_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open GaussNormRoots
namespace Formalism.GM
theorem _root_.solution (hG : GaussMulRad) : LieRoots := by
  unfold LieRoots
  intro p _ K _ _ _ h β E D lead roots t₀ hE hlead hD hbound
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hρ : 0 < ((p : ℝ) ^ (-E)).toNNReal := Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos hp0 _)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] K) p, norm_algebraMap', Padic.norm_p]
  have hnph : ‖(p : K) ^ h‖ = (p : ℝ) ^ (-(h : ℤ)) := by
    rw [norm_pow, hnp, inv_pow, zpow_neg, zpow_natCast]
  have hcomp : D.comp (C ((p : K) ^ h) * X + C (t₀ : K)) =
      C lead * (roots.map fun ζ => C ((p : K) ^ h) * X + C ((t₀ : K) - ζ)).prod := by
    rw [hD, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  have hpt : ∀ ζ : K, ((max ‖(t₀ : K) - ζ‖₊ (‖(p : K) ^ h‖₊ * ((p : ℝ) ^ (-E)).toNNReal) : NNReal) : ℝ) =
      max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) := by
    intro ζ
    rw [NNReal.coe_max, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, hnph,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos hp0 _).le]
    congr 1
    rw [← Real.rpow_intCast, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  have hreal : ((gaussR ((p : ℝ) ^ (-E)).toNNReal (D.comp (C ((p : K) ^ h) * X + C (t₀ : K))) : NNReal) : ℝ) =
      ‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod := by
    rw [hcomp, hG K _ _ _ hρ, gaussR_C, gaussR_multiset_prod hG _ hρ]
    simp only [gaussR_lin]
    rw [NNReal.coe_mul, coe_nnnorm, NNReal.coe_multiset_prod, Multiset.map_map]
    congr 1
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun ζ _ => hpt ζ)
  rw [hreal] at hbound
  have hFpos : ∀ ζ : K, 0 < max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) :=
    fun ζ => lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) (le_max_right _ _)
  have hlpos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead
  have hPpos := multiset_prod_pos roots _ hFpos
  have hlog : Real.logb p (‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod)
      ≤ -(E * β) := by
    calc _ ≤ Real.logb p ((p : ℝ) ^ (-(E * β))) :=
          Real.logb_le_logb_of_le hp1 (mul_pos hlpos hPpos) hbound
      _ = -(E * β) := Real.logb_rpow hp0 hp1.ne'
  rw [Real.logb_mul hlpos.ne' hPpos.ne', logb_multiset_prod _ _ _ hFpos] at hlog
  have hstep := multiset_sum_le_sum roots
    (fun ζ => -Real.logb p (max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))))
    (fun ζ => vmin p h ((t₀ : K) - ζ) +
      E * (if ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0)) (fun ζ => by
        have := vmin_step p hp1 h E hE ‖(t₀ : K) - ζ‖ (norm_nonneg _)
        unfold vmin
        simpa only using this)
  rw [multiset_sum_add, multiset_sum_mul_left, multiset_sum_neg] at hstep
  rw [multiset_card_filter_eq_sum]
  linarith
end Formalism.GM
