-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:52.217283+00:00
-- url     : https://prove2.me/submissions/7358d1d9-d401-445e-87a6-235b80bc93c7

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement
import Theorems.Thm_FunctionalInequalities_Analysis_exists_smooth_compact_translate_majorant_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_hessian_increment_energy_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_hessian_increment_le_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_memLp_cutoff_mul_hessianMatrix_entry_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
noncomputable section
open scoped Topology ContDiff RealInnerProductSpace
private lemma FunctionalInequalities.Analysis.n11d3_entry_sq_le_total {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    P i j ^ 2 ≤
      (∑ k, ∑ l, P k l ^ 2) + ∑ k, ∑ l, Q k l ^ 2 := by
  classical
  have hj : P i j ^ 2 ≤ ∑ l, P i l ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (P i l)) (Finset.mem_univ j)
  have hi : (∑ l, P i l ^ 2) ≤ ∑ k, ∑ l, P k l ^ 2 :=
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (P k l)))
      (Finset.mem_univ i)
  exact (hj.trans hi).trans
    (le_add_of_nonneg_right
      (Finset.sum_nonneg
        (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Q k l)))))
set_option maxHeartbeats 800000 in
/-- Produce the actual global L2 difference-quotient bound for a compact cutoff
times a Hessian entry from the original Monge-Ampere/increment hypotheses.
The bound is a conclusion, never a supplied regularity or energy premise. -/
theorem solution {n : ℕ}
    {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
      Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x, (χ (x + t • v) * FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) i j -
        χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2 := by
  classical
  obtain ⟨η, hη, hηc, hη0, hmajor⟩ :=
    FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_readable hu.continuous hχ.continuous hχc v
  have hη2 : ContDiff ℝ 2 η :=
    hη.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨L, hL⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ one_ne_zero
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    (tsupport η).indicator (fun _ => (1 : ℝ))
  have hqint : Integrable q (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff (isClosed_tsupport η).measurableSet).mpr
      (integrableOn_const hηc.isCompact.measure_lt_top.ne)
  have hq0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ q x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  let J : ℝ := ∫ x, q x
  have hJ : 0 ≤ J := integral_nonneg hq0
  let I : ℝ :=
    ∫ x, |η x + (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
      fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
  let A : ℝ := |2 * K ^ 2 * D * I| * ‖v‖ ^ 2
  let B : ℝ := ((G : ℝ) * (L : ℝ) * ‖v‖) ^ 2
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hB : 0 ≤ B := sq_nonneg _
  let e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x =>
    η x *
      ((∑ k, ∑ l,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) +
        ∑ k, ∑ l,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) *
      Real.exp (-u x)
  have heint (t : ℝ) :
      Integrable (e t) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.integrable_hessian_increment_energy_readable hu.continuous hG hη.continuous hηc (t • v)
  have hebound (t : ℝ) : (∫ x, e t x) ≤ A * t ^ 2 := by
    have hh :=
      FunctionalInequalities.Analysis.integral_mul_hessian_increment_le_readable hu hconv hG hV hVc hF hK hdata
        hη2 hηc hη0 (t • v) (fun x => hw x (t • v))
    calc
      (∫ x, e t x) ≤ 2 * K ^ 2 * (D * ‖t • v‖ ^ 2) * I := hh
      _ = (2 * K ^ 2 * D * I) * ‖v‖ ^ 2 * t ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      _ ≤ |2 * K ^ 2 * D * I| * ‖v‖ ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
          (sq_nonneg _)
      _ = A * t ^ 2 := rfl
  have henvelope (t : ℝ) (ht : |t| ≤ 1) (x : EuclideanSpace ℝ (Fin n)) :
      χ (x + t • v) ^ 2 ≤ η x * Real.exp (-u x) := by
    calc
      χ (x + t • v) ^ 2 =
          (χ (x + t • v) ^ 2 * Real.exp (u x)) * Real.exp (-u x) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ η x * Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (hmajor t ht x) (Real.exp_pos _).le
  have hvanish (t : ℝ) (ht : |t| ≤ 1)
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport η) :
      χ (x + t • v) = 0 := by
    have hh := henvelope t ht x
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul] at hh
    exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
  have hf : MemLp (fun x => χ x * H x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_readable hG i j hχ.continuous hχc
  refine ⟨2 * A + 2 * B * J, ?_, ?_⟩
  · positivity
  · intro t _ht0 ht
    have htranslated : MemLp (fun x => χ (x + t • v) * H (x + t • v)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hf.comp_measurePreserving (measurePreserving_add_right volume (t • v))
    have hdiff : MemLp
        (fun x => χ (x + t • v) * H (x + t • v) - χ x * H x) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      htranslated.sub hf
    have hdiffint : Integrable
        (fun x => (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [pow_two, Pi.mul_def] using hdiff.integrable_mul hdiff
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 ≤
          2 * e t x + (2 * B * t ^ 2) * q x := by
      let a : ℝ := χ (x + t • v) * (H (x + t • v) - H x)
      let b : ℝ := H x * (χ (x + t • v) - χ x)
      have ha : a ^ 2 ≤ e t x := by
        have hentry :=
          FunctionalInequalities.Analysis.n11d3_entry_sq_le_total
            (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x)
            (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j
        change (H (x + t • v) - H x) ^ 2 ≤ _ at hentry
        calc
          a ^ 2 =
              χ (x + t • v) ^ 2 * (H (x + t • v) - H x) ^ 2 := by
            dsimp only [a]
            ring
          _ ≤ (η x * Real.exp (-u x)) *
              ((∑ k, ∑ l,
                  (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) +
                ∑ k, ∑ l,
                  (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - t • v) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) k l ^ 2) :=
            mul_le_mul (henvelope t ht x) hentry (sq_nonneg _)
              (mul_nonneg (hη0 x) (Real.exp_pos _).le)
          _ = e t x := by
            dsimp only [e]
            ring
      have hb : b ^ 2 ≤ (B * t ^ 2) * q x := by
        by_cases hx : x ∈ tsupport η
        · have hqx : q x = 1 := Set.indicator_of_mem hx _
          rw [hqx, mul_one]
          have hH : H x ^ 2 ≤ (G : ℝ) ^ 2 := by
            have hh := pow_le_pow_left₀ (norm_nonneg (H x))
              (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG x i j) 2
            simpa only [Real.norm_eq_abs, sq_abs] using hh
          have hcut :
              (χ (x + t • v) - χ x) ^ 2 ≤
                (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
            have hh := hL.norm_sub_le (x + t • v) x
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
            have hs := pow_le_pow_left₀
              (norm_nonneg (χ (x + t • v) - χ x)) hh 2
            calc
              (χ (x + t • v) - χ x) ^ 2 =
                  ‖χ (x + t • v) - χ x‖ ^ 2 := by
                rw [Real.norm_eq_abs, sq_abs]
              _ ≤ ((L : ℝ) * (|t| * ‖v‖)) ^ 2 := hs
              _ = (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
                simp only [mul_pow, sq_abs]
                ring
          calc
            b ^ 2 = H x ^ 2 * (χ (x + t • v) - χ x) ^ 2 := by
              dsimp only [b]
              ring
            _ ≤ (G : ℝ) ^ 2 * ((L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2) :=
              mul_le_mul hH hcut (sq_nonneg _) (sq_nonneg _)
            _ = B * t ^ 2 := by
              dsimp only [B]
              ring
        · have hqx : q x = 0 := Set.indicator_of_notMem hx _
          have hχt : χ (x + t • v) = 0 := hvanish t ht x hx
          have hχ0 : χ x = 0 := by
            simpa only [zero_smul, add_zero] using
              hvanish 0 (by norm_num) x hx
          have hb0 : b = 0 := by
            dsimp only [b]
            rw [hχt, hχ0]
            ring
          rw [hb0, hqx]
          norm_num
      have hsplit :
          χ (x + t • v) * H (x + t • v) - χ x * H x = a + b := by
        dsimp only [a, b]
        ring
      calc
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 =
            (a + b) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hsplit
        _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
          nlinarith [sq_nonneg (a - b)]
        _ ≤ 2 * e t x + (2 * B * t ^ 2) * q x := by
          nlinarith [ha, hb]
    calc
      (∫ x, (χ (x + t • v) * FunctionalInequalities.Probability.Stein.hessianMatrix u (x + t • v) i j -
          χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) ≤
          ∫ x, 2 * e t x + (2 * B * t ^ 2) * q x :=
        integral_mono hdiffint
          (((heint t).const_mul 2).add (hqint.const_mul (2 * B * t ^ 2)))
          hpoint
      _ = 2 * (∫ x, e t x) + (2 * B * t ^ 2) * J := by
        rw [integral_add ((heint t).const_mul 2)
          (hqint.const_mul (2 * B * t ^ 2)),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * (A * t ^ 2) + (2 * B * t ^ 2) * J := by
        have hscaled : 2 * (∫ x, e t x) ≤ 2 * (A * t ^ 2) :=
          mul_le_mul_of_nonneg_left (hebound t) (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add hscaled (le_refl ((2 * B * t ^ 2) * J))
      _ = (2 * A + 2 * B * J) * t ^ 2 := by ring
