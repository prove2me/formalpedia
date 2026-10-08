-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_quadratic_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T10:19:30.066124+00:00
-- url     : https://prove2.me/submissions/1d7213a5-9269-485c-a26c-69d96cd3d295

import Mathlib
import Theorems.Thm_AvramDividend_Classical_laplace_tail_shift_bound
import Theorems.Thm_AvramDividend_Classical_laplace_integral_restrict_tail_of_monotone_zero
import Theorems.Thm_AvramDividend_Classical_quadratic_exponential_tail_eventually_lt_one

open MeasureTheory Set Filter
open AvramDividend.Classical

theorem solution
    (W ψ : ℝ → ℝ) (q β0 C : ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici 0))
    (hLap : ∀ β : ℝ, β0 ≤ β →
      0 < ψ β - q ∧
      IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * W x) =
        (ψ β - q)⁻¹)
    (hquadratic : ∀ β : ℝ, β0 ≤ β →
      ψ β - q ≤ C * (1 + β ^ 2)) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  intro a ha
  by_contra hnot
  have hzero : W a = 0 :=
    le_antisymm (le_of_not_gt hnot) (hW a ha.le)
  obtain ⟨hψ0, hint0, heq0⟩ := hLap β0 le_rfl
  let K : ℝ :=
    ∫ x in Ioi (0 : ℝ), Real.exp (-β0 * x) * W x
  have hK : 0 ≤ K := by
    dsimp [K]
    rw [heq0]
    exact inv_nonneg.mpr hψ0.le
  have hs : Ioi a ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_trans ha hx
  have hintTail0 :
      IntegrableOn (fun x : ℝ => Real.exp (-β0 * x) * W x)
        (Ioi a) :=
    hint0.mono_set hs
  have heqTail0 :
      (∫ x in Ioi a, Real.exp (-β0 * x) * W x) = K := by
    simpa only [K] using
      (laplace_integral_restrict_tail_of_monotone_zero
        W a β0 ha hW hmono hzero).symm
  obtain ⟨β, hβ, hlt⟩ :=
    quadratic_exponential_tail_eventually_lt_one a β0 C K ha
  obtain ⟨hψβ, hintβ, heqβ⟩ := hLap β hβ
  have hintTailβ :
      IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x)
        (Ioi a) :=
    hintβ.mono_set hs
  have hWtail : ∀ x : ℝ, x ∈ Ioi a → 0 ≤ W x := by
    intro x hx
    exact hW x (lt_trans ha hx).le
  have htail_bound :=
    laplace_tail_shift_bound W a β0 β
      hβ hWtail hintTail0 hintTailβ
  have hinv_bound :
      (ψ β - q)⁻¹ ≤
        Real.exp (-(β - β0) * a) * K := by
    calc
      (ψ β - q)⁻¹ =
          ∫ x in Ioi a, Real.exp (-β * x) * W x :=
        heqβ.symm.trans
          (laplace_integral_restrict_tail_of_monotone_zero
            W a β ha hW hmono hzero)
      _ ≤ Real.exp (-(β - β0) * a) *
            ∫ x in Ioi a, Real.exp (-β0 * x) * W x :=
        htail_bound
      _ = Real.exp (-(β - β0) * a) * K := by
        rw [heqTail0]
  have hprod_nn :
      0 ≤ Real.exp (-(β - β0) * a) * K :=
    mul_nonneg (Real.exp_pos _).le hK
  have hone :
      (1 : ℝ) ≤
        (ψ β - q) * (Real.exp (-(β - β0) * a) * K) := by
    calc
      (1 : ℝ) = (ψ β - q) * (ψ β - q)⁻¹ := by
        field_simp [ne_of_gt hψβ]
      _ ≤ (ψ β - q) *
            (Real.exp (-(β - β0) * a) * K) :=
        mul_le_mul_of_nonneg_left hinv_bound hψβ.le
  have htwo :
      (ψ β - q) * (Real.exp (-(β - β0) * a) * K) ≤
        C * (1 + β ^ 2) *
          (Real.exp (-(β - β0) * a) * K) :=
    mul_le_mul_of_nonneg_right (hquadratic β hβ) hprod_nn
  exact (not_lt_of_ge (hone.trans htwo)) hlt
