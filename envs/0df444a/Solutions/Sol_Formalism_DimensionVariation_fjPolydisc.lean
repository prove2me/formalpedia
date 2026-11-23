-- Prove2me | solution 1 for Formalism.DimensionVariation.fjPolydisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:14.537403+00:00
-- url     : https://prove2.me/submissions/60bbbe3e-a6e4-4d23-9dac-22fd553bb804

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_measurable_productCutoff
import Theorems.Thm_Formalism_DimensionVariation_fjProd_orth
import Theorems.Thm_Formalism_DimensionVariation_fjMono_cut
import Theorems.Thm_Formalism_DimensionVariation_fjIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
namespace Formalism.DimensionVariation
private theorem continuous_nsq' {κ : Type} [Fintype κ] :
    Continuous fun u : κ → ℂ => nsq u := by
  show Continuous fun u : κ → ℂ => ∑ x, ‖u x‖ ^ 2
  exact continuous_finsetSum _ fun x _ => (continuous_norm.comp (continuous_apply x)).pow 2
private theorem continuous_exp_neg_nsq {κ : Type} [Fintype κ] :
    Continuous fun u : κ → ℂ => (Real.exp (-(nsq u)) : ℂ) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_nsq'.neg)
private theorem continuous_mono_cj {κ : Type} [Fintype κ] (e : κ → ℕ) :
    Continuous fun u : κ → ℂ => mono (cj u) e := by
  show Continuous fun u : κ → ℂ => ∏ x, conj (u x) ^ e x
  exact continuous_finsetProd _ fun x _ => (Complex.continuous_conj.comp (continuous_apply x)).pow _
private theorem nsq_nonneg_gaussian_shift_bounds {κ : Type} [Fintype κ] (u : κ → ℂ) : 0 ≤ nsq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
private theorem continuous_mono' {κ : Type} [Fintype κ] (e : κ → ℕ) :
    Continuous fun u : κ → ℂ => mono u e := by
  show Continuous fun u : κ → ℂ => ∏ x, u x ^ e x
  exact continuous_finsetProd _ fun x _ => (continuous_apply x).pow _
end Formalism.DimensionVariation
end
end

set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ)
    (hs : ∀ u, HasSum (fun e => c e * mono u e) (F u)) (e : κ → ℕ) (N : ℕ) :
    ∫ u : κ → ℂ, fjChiP N u * (F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
      c e * ∫ u : κ → ℂ, fjChiP N u * (mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
  have hI : ∀ n : κ → ℕ, ∫ u : κ → ℂ, fjChiP N u *
      (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
      c n * ∫ u : κ → ℂ, fjChiP N u *
        (mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
    intro n
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have h1 : Integrable fun u : κ → ℂ =>
      (1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) :=
    fjIntegrable (fun _ => 1) 1 continuous_const
      (fun u => by
        simp only [norm_one, one_mul]
        exact Real.one_le_exp (div_nonneg (nsq_nonneg_gaussian_shift_bounds u) two_pos.le)) e
  have hsN : Summable fun n : κ → ℕ => ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ :=
    summable_norm_iff.mpr (hs _).summable
  have hsum : HasSum (fun n : κ → ℕ => ∫ u : κ → ℂ, fjChiP N u *
      (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)))
      (∫ u : κ → ℂ, fjChiP N u *
        (F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ))) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n u => ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ *
        ‖(1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖)
      (fun n => ?_) (fun n => Filter.Eventually.of_forall fun u => ?_)
      (Filter.Eventually.of_forall fun u => hsN.mul_right _) ?_
      (Filter.Eventually.of_forall fun u => ?_)
    · exact (measurable_productCutoff N).aestronglyMeasurable.mul
        ((((continuous_const.mul (continuous_mono' n)).mul
          (continuous_mono_cj e)).mul continuous_exp_neg_nsq).aestronglyMeasurable)
    · show ‖fjChiP N u *
          (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ))‖ ≤
        ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ *
          ‖(1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖
      have hre : fjChiP N u *
          (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
          c n * (fjChiP N u * mono u n) *
            ((1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by ring
      have hb := fjMono_cut N n u
      rw [norm_mul] at hb
      rw [hre]
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        (by positivity)
    · simp_rw [tsum_mul_right]
      exact h1.norm.const_mul _
    · exact (((hs u).mul_right _).mul_right _).mul_left _
  rw [← hI e]
  exact hsum.unique (hasSum_single e fun n hn => (hI n).trans (by
    rw [fjProd_orth N n e hn, mul_zero]))
end Formalism.DimensionVariation
