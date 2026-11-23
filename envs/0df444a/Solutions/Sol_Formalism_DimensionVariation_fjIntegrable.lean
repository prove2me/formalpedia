-- Prove2me | solution 1 for Formalism.DimensionVariation.fjIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:26.101789+00:00
-- url     : https://prove2.me/submissions/1b838e29-34c3-4337-92c5-d391ef3fe87a

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjMoment
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
end Formalism.DimensionVariation
end
end

set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (S : ℝ) (hF : Continuous F)
    (hg : ∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) (e : κ → ℕ) :
    Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
  have hbd : Integrable (fun u : κ → ℂ =>
      S * ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2))) :=
    (Integrable.fintype_prod (f := fun x (z : ℂ) => ‖z‖ ^ e x * Real.exp (-(1 / 2) * ‖z‖ ^ 2))
      fun x => (fjMoment (1 / 2) (by norm_num) (e x)).1).const_mul S
  refine hbd.mono' ((hF.mul (continuous_mono_cj e)).mul
    continuous_exp_neg_nsq).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  show ‖F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖ ≤
    S * ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2))
  have hprod : ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2)) =
      (∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u / 2)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
    unfold nsq
    congr 2
    ring
  have hnorm : ‖F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖ =
      ‖F u‖ * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u))) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_assoc]
    congr 2
    simp only [mono, cj, norm_prod, norm_pow, Complex.norm_conj]
  have hP : 0 ≤ (∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u)) :=
    mul_nonneg (Finset.prod_nonneg fun x _ => pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hexp : Real.exp (-(nsq u / 2)) =
      Real.exp (nsq u / 2) * Real.exp (-(nsq u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hnorm, hprod]
  calc ‖F u‖ * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u)))
      ≤ S * Real.exp (nsq u / 2) * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u))) :=
        mul_le_mul_of_nonneg_right (hg u) hP
    _ = S * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u / 2))) := by
        rw [hexp]
        ring
end Formalism.DimensionVariation
