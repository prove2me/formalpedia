-- Prove2me | solution 1 for ConvexOptimization.barrier_centering_potential_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T04:08:13.980476+00:00
-- url     : https://prove2.me/submissions/053beb34-0f22-4f59-ae80-fa43f18392bb

import Mathlib
import Definitions.Def_ConvexOptimization_logBarrier
import Theorems.Thm_ConvexOptimization_convexOn_iff_gradient_inequality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {n mI : ℕ} (t μ : ℝ)
    (ht : 0 < t) (hμ : 1 < μ)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hfc_diff : ∀ i, Differentiable ℝ (fc i)) (hf₀_diff : Differentiable ℝ f₀)
    (xc xc' : EuclideanSpace ℝ (Fin n))
    (hxc_str : ∀ i, fc i xc < 0) (hxc'_str : ∀ i, fc i xc' < 0)
    (hxc_min : IsMinOn (fun x => t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc)
    (hxc'_min : IsMinOn (fun x => μ * t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc') :
    μ * t * f₀ xc + logBarrier fc xc - (μ * t * f₀ xc' + logBarrier fc xc') ≤
      (mI : ℝ) * (μ - 1 - Real.log μ) := by
  set Ω : Set (EuclideanSpace ℝ (Fin n)) := {z | ∀ i, fc i z < 0} with hΩ
  -- The strictly feasible set is open.
  have hΩopen : IsOpen Ω := by
    have : Ω = ⋂ i, (fc i) ⁻¹' (Set.Iio 0) := by
      ext z; simp [hΩ]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (hfc_diff i).continuous.isOpen_preimage _ isOpen_Iio
  have hxcΩ : xc ∈ Ω := hxc_str
  -- Multipliers from the barrier: `λᵢ = 1 / (t · (−fᵢ(xc))) > 0`.
  set lam : Fin mI → ℝ := fun i => 1 / (t * (-(fc i xc))) with hlam
  have hneg : ∀ i, (0 : ℝ) < -(fc i xc) := fun i => by linarith [hxc_str i]
  have hlampos : ∀ i, 0 < lam i := fun i =>
    div_pos one_pos (mul_pos ht (hneg i))
  -- Stationarity of the barrier objective at `xc`.
  have hΦderiv : HasFDerivAt (fun z => t * f₀ z + logBarrier fc z)
      (t • fderiv ℝ f₀ xc + ∑ i, (-(fc i xc))⁻¹ • fderiv ℝ (fc i) xc) xc := by
    have h₀ : HasFDerivAt (fun z => t * f₀ z) (t • fderiv ℝ f₀ xc) xc :=
      ((hf₀_diff xc).hasFDerivAt).const_mul t
    have hlog : ∀ i, HasFDerivAt (fun z => Real.log (-(fc i z)))
        ((-(fc i xc))⁻¹ • (-(fderiv ℝ (fc i) xc))) xc := by
      intro i
      have hu : HasFDerivAt (fun z => -(fc i z)) (-(fderiv ℝ (fc i) xc)) xc :=
        ((hfc_diff i xc).hasFDerivAt).neg
      exact (Real.hasDerivAt_log (ne_of_gt (hneg i))).comp_hasFDerivAt xc hu
    have hbar : HasFDerivAt (logBarrier fc)
        (∑ i, (-(fc i xc))⁻¹ • fderiv ℝ (fc i) xc) xc := by
      have hsum := (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hlog i)).neg
      have hrw : -∑ i, (-(fc i xc))⁻¹ • (-(fderiv ℝ (fc i) xc))
          = ∑ i, (-(fc i xc))⁻¹ • fderiv ℝ (fc i) xc := by
        simp [smul_neg]
      rw [hrw] at hsum
      exact hsum
    exact h₀.add hbar
  have hΦzero : t • fderiv ℝ f₀ xc + ∑ i, (-(fc i xc))⁻¹ • fderiv ℝ (fc i) xc = 0 :=
    (hxc_min.isLocalMin (hΩopen.mem_nhds hxcΩ)).hasFDerivAt_eq_zero hΦderiv
  -- The Lagrangian `L(z) = f₀(z) + Σ λᵢ fᵢ(z)`.
  set L : EuclideanSpace ℝ (Fin n) → ℝ := fun z => f₀ z + ∑ i, lam i * fc i z with hL
  have hLdiff : Differentiable ℝ L := by
    refine hf₀_diff.add (Differentiable.fun_sum fun i _ => ?_)
    exact (hfc_diff i).const_mul (lam i)
  have hLconv : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) L := by
    refine hf₀.add ?_
    have : ∀ s : Finset (Fin mI),
        ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
          (fun z => ∑ i ∈ s, lam i * fc i z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using convexOn_const (0 : ℝ) (convex_univ)
      | insert i s hi ih =>
          simp only [Finset.sum_insert hi]
          have h1 : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
              (fun z => lam i * fc i z) := by
            simpa [smul_eq_mul] using (hfc i).smul (hlampos i).le
          exact h1.add ih
    exact this Finset.univ
  -- `∇L(xc) = 0`: divide the stationarity identity by `t`.
  have hLfderiv : fderiv ℝ L xc = fderiv ℝ f₀ xc + ∑ i, lam i • fderiv ℝ (fc i) xc := by
    have hd : HasFDerivAt L (fderiv ℝ f₀ xc + ∑ i, lam i • fderiv ℝ (fc i) xc) xc := by
      refine (hf₀_diff xc).hasFDerivAt.add ?_
      exact HasFDerivAt.fun_sum fun i _ => ((hfc_diff i xc).hasFDerivAt).const_mul (lam i)
    exact hd.fderiv
  have hLzero : fderiv ℝ L xc = 0 := by
    rw [hLfderiv]
    have hscale : ∀ i, lam i • fderiv ℝ (fc i) xc
        = t⁻¹ • ((-(fc i xc))⁻¹ • fderiv ℝ (fc i) xc) := by
      intro i
      rw [smul_smul, hlam]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl fun i _ => hscale i, ← Finset.smul_sum]
    have ht' : t ≠ 0 := ne_of_gt ht
    have : fderiv ℝ f₀ xc = t⁻¹ • (t • fderiv ℝ f₀ xc) := by
      rw [smul_smul, inv_mul_cancel₀ ht', one_smul]
    rw [this, ← smul_add, hΦzero, smul_zero]
  have hLgradzero : gradient L xc = 0 := by
    simp [gradient, hLzero]
  -- The first-order characterization of convexity (previous milestone) makes `xc`
  -- a global minimiser of `L`.
  have hgradineq :=
    (ConvexOptimization.convexOn_iff_gradient_inequality Set.univ isOpen_univ convex_univ L
      (fun z => gradient L z) (fun z _ => (hLdiff z).hasGradientAt)).mp hLconv
  have hLmin : L xc ≤ L xc' := by
    have := hgradineq xc (Set.mem_univ _) xc' (Set.mem_univ _)
    rwa [hLgradzero, inner_zero_left, add_zero] at this
  have hLexpand : f₀ xc + ∑ i, lam i * fc i xc ≤
      f₀ xc' + ∑ i, lam i * fc i xc' := hLmin
  have hobj : μ * t * (f₀ xc - f₀ xc') ≤
      ∑ i, μ * (1 - fc i xc' / fc i xc) := by
    have hterm : ∀ i, t * (lam i * fc i xc' - lam i * fc i xc) =
        1 - fc i xc' / fc i xc := by
      intro i
      dsimp [lam]
      have ht0 : t ≠ 0 := ne_of_gt ht
      have hfi : fc i xc ≠ 0 := ne_of_lt (hxc_str i)
      field_simp
      <;> ring
    have hbase : t * (f₀ xc - f₀ xc') ≤
        ∑ i, (1 - fc i xc' / fc i xc) := by
      rw [← Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
      have hd : f₀ xc - f₀ xc' ≤
          ∑ i, (lam i * fc i xc' - lam i * fc i xc) := by
        rw [Finset.sum_sub_distrib]
        linarith
      exact mul_le_mul_of_nonneg_left hd ht.le
    rw [← Finset.mul_sum]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hbase (le_trans zero_le_one hμ.le))
  let u : Fin mI → ℝ := fun i => fc i xc' / fc i xc
  have hu : ∀ i, 0 < u i := fun i => div_pos_of_neg_of_neg (hxc'_str i) (hxc_str i)
  have hlogbar : logBarrier fc xc - logBarrier fc xc' = ∑ i, Real.log (u i) := by
    dsimp [logBarrier, u]
    rw [neg_sub_neg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.log_div (ne_of_gt (neg_pos.mpr (hxc'_str i)))
      (ne_of_gt (neg_pos.mpr (hxc_str i)))]
    congr 1
    field_simp
  have hscalar : ∀ i, μ * (1 - u i) + Real.log (u i) ≤ μ - 1 - Real.log μ := by
    intro i
    have hμ0 : 0 < μ := lt_trans zero_lt_one hμ
    have hp : 0 < μ * u i := mul_pos hμ0 (hu i)
    have hl := Real.log_le_sub_one_of_pos hp
    rw [Real.log_mul (ne_of_gt hμ0) (ne_of_gt (hu i))] at hl
    linarith
  rw [show μ * t * f₀ xc + logBarrier fc xc -
      (μ * t * f₀ xc' + logBarrier fc xc') =
      μ * t * (f₀ xc - f₀ xc') +
        (logBarrier fc xc - logBarrier fc xc') by ring, hlogbar]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hscalar i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  nlinarith
