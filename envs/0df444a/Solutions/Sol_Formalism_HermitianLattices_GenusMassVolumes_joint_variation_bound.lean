-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.joint_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:00.702295+00:00
-- url     : https://prove2.me/submissions/7e3443b3-1229-493d-9f1e-1d26a3dc5319

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : NormalizedLogRatioVandermondeVariation := by
  intro f k Dstar massk Ipi V u u' hf hk hD hm hI hV
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hfac : (0:ℝ) < ∏ i ∈ range k, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hF : ∀ x : ℕ → ℝ, 0 < vandN x k → 0 < dimVN x k := fun x hx => by
    unfold dimVN
    exact div_pos hx hfac
  have hlog : ∀ x : ℕ → ℝ, 0 < vandN x k →
      Real.log (dimVN x k) = Real.log (vandN x k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) :=
    fun x hx => by
      unfold dimVN
      rw [Real.log_div hx.ne' hfac.ne']
  have hP : ∀ w : ℕ → ℕ → ℝ, (∀ ρ, ρ < f → 0 < vandN (w ρ) k) →
      Real.log (Dstar / (massk * Ipi * ∏ ρ ∈ range f, dimVN (w ρ) k)) =
        Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (w ρ) k) := by
    intro w hw
    have hpos : ∀ ρ ∈ range f, 0 < dimVN (w ρ) k := fun ρ hρ => hF _ (hw ρ (Finset.mem_range.1 hρ))
    rw [Real.log_div hD.ne' (mul_pos (mul_pos hm hI) (Finset.prod_pos hpos)).ne',
      Real.log_mul (mul_pos hm hI).ne' (Finset.prod_pos hpos).ne',
      Real.log_prod (fun ρ hρ => (hpos ρ hρ).ne')]
    ring
  rw [hP u (fun ρ hρ => (hV ρ hρ).1), hP u' (fun ρ hρ => (hV ρ hρ).2.1)]
  have hsum : |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)| ≤ f * V := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ ρ ∈ range f, (Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k))|
        ≤ ∑ ρ ∈ range f, |Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ range f, V := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have h := hV ρ (Finset.mem_range.1 hρ)
        rw [hlog _ h.1, hlog _ h.2.1]
        have e : Real.log (vandN (u ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) -
            (Real.log (vandN (u' ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ))) =
            Real.log (vandN (u ρ) k) - Real.log (vandN (u' ρ) k) := by ring
        rw [e]
        exact h.2.2
      _ = f * V := by simp
  have hN : (0:ℝ) < 1 / ((f:ℝ) * k) := by positivity
  have e : 1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u ρ) k)) -
      1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) =
      1 / ((f:ℝ) * k) * -(∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) := by
    ring
  rw [e, abs_mul, abs_neg, abs_of_pos hN]
  calc 1 / ((f:ℝ) * k) * |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)|
      ≤ 1 / ((f:ℝ) * k) * (f * V) := mul_le_mul_of_nonneg_left hsum hN.le
    _ = V / k := by field_simp
end Formalism.HermitianLattices.GenusMassVolumes
