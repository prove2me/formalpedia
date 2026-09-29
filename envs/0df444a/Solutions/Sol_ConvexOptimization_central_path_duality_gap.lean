-- Prove2me | solution 1 for ConvexOptimization.central_path_duality_gap
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:31:00.212375+00:00
-- url     : https://prove2.me/submissions/a4fb7c08-d9ab-4066-8e71-f39c881acc9f

import Mathlib
import Definitions.Def_ConvexOptimization_logBarrier
import Theorems.Thm_ConvexOptimization_convexOn_iff_gradient_inequality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {n mI : ℕ} (t : ℝ) (ht : 0 < t)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hfc_diff : ∀ i, Differentiable ℝ (fc i)) (hf₀_diff : Differentiable ℝ f₀)
    (xc : EuclideanSpace ℝ (Fin n)) (hxc_str : ∀ i, fc i xc < 0)
    (hxc_min : IsMinOn (fun x => t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ i, fc i x ≤ 0) :
    f₀ xc - (mI : ℝ) / t ≤ f₀ x := by
  classical
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
  have hLmin : L xc ≤ L x := by
    have := hgradineq xc (Set.mem_univ _) x (Set.mem_univ _)
    rwa [hLgradzero, inner_zero_left, add_zero] at this
  -- Read off the duality gap.
  have hxcval : ∑ i, lam i * fc i xc = -(mI : ℝ) / t := by
    have htne : t ≠ 0 := ne_of_gt ht
    have hterm : ∀ i, lam i * fc i xc = -(1 / t) := by
      intro i
      have hne : fc i xc ≠ 0 := ne_of_lt (hxc_str i)
      show 1 / (t * -(fc i xc)) * fc i xc = -(1 / t)
      field_simp
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hxfeas : ∑ i, lam i * fc i x ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlampos i).le (hx i)
  have h1 : L xc = f₀ xc - (mI : ℝ) / t := by
    have e : L xc = f₀ xc + ∑ i, lam i * fc i xc := rfl
    rw [e, hxcval]; ring
  have h2 : L x ≤ f₀ x := by
    have e : L x = f₀ x + ∑ i, lam i * fc i x := rfl
    rw [e]; linarith
  rw [h1] at hLmin
  linarith
