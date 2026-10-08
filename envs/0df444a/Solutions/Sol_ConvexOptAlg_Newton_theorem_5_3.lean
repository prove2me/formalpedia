-- Prove2me | solution 1 for ConvexOptAlg.Newton.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:11:44.879018+00:00
-- url     : https://prove2.me/submissions/6cc16d08-8c35-4bdd-a339-474189d28580

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

set_option autoImplicit false

/- One Newton step inside the ball: the Hessian is bijective and any
Newton successor satisfies the quadratic bound. -/
open ConvexOptAlg.Newton in
theorem Newton53Aux.step {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (M μ : ℝ) (hM : 0 < M) (hHL : IsLipschitzHessian H M)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMin f xstar) (hμ : 0 < μ)
    (hHstar : ∀ v : EuclideanSpace ℝ (Fin n), μ * ‖v‖ ^ 2 ≤ inner ℝ (H xstar v) v)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y - xstar‖ ≤ μ / (2 * M)) :
    Function.Bijective (H y) ∧
      ∀ yp : EuclideanSpace ℝ (Fin n), H y (y - yp) = g y →
        ‖yp - xstar‖ ≤ M / μ * ‖y - xstar‖ ^ 2 := by
  obtain ⟨_, h2, h3⟩ := hfgH
  -- coercivity of H y
  have hMy : M * ‖y - xstar‖ ≤ μ / 2 := by
    have := mul_le_mul_of_nonneg_left hy hM.le
    rw [show M * (μ / (2 * M)) = μ / 2 by field_simp] at this
    exact this
  have hc : ∀ v : EuclideanSpace ℝ (Fin n), μ / 2 * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v := by
    intro v
    have hdiff : inner ℝ (H xstar v) v - inner ℝ (H y v) v
        = inner ℝ ((H xstar - H y) v) v := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    have hci : inner ℝ ((H xstar - H y) v) v ≤ ‖(H xstar - H y) v‖ * ‖v‖ :=
      real_inner_le_norm _ _
    have hop : ‖(H xstar - H y) v‖ ≤ ‖H xstar - H y‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hL : ‖H xstar - H y‖ ≤ M * ‖y - xstar‖ := by
      have := hHL xstar y
      rwa [norm_sub_rev xstar y] at this
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    have hb : ‖(H xstar - H y) v‖ * ‖v‖ ≤ μ / 2 * ‖v‖ ^ 2 := by
      calc ‖(H xstar - H y) v‖ * ‖v‖ ≤ (‖H xstar - H y‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right hop hv
        _ ≤ (M * ‖y - xstar‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hv) hv
        _ ≤ (μ / 2 * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMy hv) hv
        _ = μ / 2 * ‖v‖ ^ 2 := by ring
    have := hHstar v
    have : μ * ‖v‖ ^ 2 = μ / 2 * ‖v‖ ^ 2 + μ / 2 * ‖v‖ ^ 2 := by ring
    linarith
  have hlow : ∀ v : EuclideanSpace ℝ (Fin n), μ / 2 * ‖v‖ ≤ ‖H y v‖ := by
    intro v
    have h1 := hc v
    have h2' : inner ℝ (H y v) v ≤ ‖H y v‖ * ‖v‖ := real_inner_le_norm _ _
    rcases (norm_nonneg v).eq_or_lt with hv | hv
    · rw [← hv]; simp
    · have : (μ / 2 * ‖v‖) * ‖v‖ ≤ ‖H y v‖ * ‖v‖ := by nlinarith
      exact le_of_mul_le_mul_right this hv
  have hinj : Function.Injective (H y) := by
    intro a b hab
    have h0 : H y (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have := hlow (a - b)
    rw [h0, norm_zero] at this
    have hn : ‖a - b‖ = 0 := by
      have := norm_nonneg (a - b)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 hn)
  have hsurj : Function.Surjective (H y) :=
    LinearMap.injective_iff_surjective (f := (H y).toLinearMap) |>.mp hinj
  refine ⟨⟨hinj, hsurj⟩, ?_⟩
  intro yp hstep
  -- gradient vanishes at the local minimum
  have hg0 : g xstar = 0 := by
    have := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.1 (h2 xstar))
    exact (InnerProductSpace.toDual ℝ _).map_eq_zero_iff.1 this
  have hLip : LipschitzWith (Real.toNNReal M) H := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
    calc ‖H a - H b‖ ≤ M * ‖a - b‖ := hHL a b
      _ ≤ max M 0 * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  set h := y - xstar with hh
  have hcont : Continuous fun s : ℝ => H (xstar + s • h) h :=
    (hLip.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (xstar + s • h)) (H (xstar + s • h) h) s := by
    intro s
    have hp : HasDerivAt (fun s : ℝ => xstar + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add xstar
    exact (h3 _).comp_hasDerivAt s hp
  have hint : IntervalIntegrable (fun s : ℝ => H (xstar + s • h) h) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hFTC : (∫ s in (0 : ℝ)..1, H (xstar + s • h) h) = g y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint]
    simp [hh, hg0]
  have hrep : H y (yp - xstar) = ∫ s in (0 : ℝ)..1, (H y h - H (xstar + s • h) h) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint, hFTC,
      intervalIntegral.integral_const, ← hstep, sub_zero, one_smul, ← map_sub, hh]
    congr 1
    abel
  have hbnd : ‖∫ s in (0 : ℝ)..1, (H y h - H (xstar + s • h) h)‖
      ≤ ∫ s in (0 : ℝ)..1, M * ‖h‖ ^ 2 * (1 - s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · refine MeasureTheory.ae_of_all _ fun s hs => ?_
      have hs1 : s ≤ 1 := hs.2
      have e1 : H y h - H (xstar + s • h) h = (H y - H (xstar + s • h)) h := by
        rw [ContinuousLinearMap.sub_apply]
      rw [e1]
      have hL1 := hHL y (xstar + s • h)
      have e2 : y - (xstar + s • h) = (1 - s) • h := by
        rw [sub_smul, one_smul, hh]; abel
      rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hL1
      calc ‖(H y - H (xstar + s • h)) h‖ ≤ ‖H y - H (xstar + s • h)‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (M * ((1 - s) * ‖h‖)) * ‖h‖ :=
            mul_le_mul_of_nonneg_right hL1 (norm_nonneg _)
        _ = M * ‖h‖ ^ 2 * (1 - s) := by ring
    · exact (by fun_prop : Continuous fun s : ℝ => M * ‖h‖ ^ 2 * (1 - s)).intervalIntegrable 0 1
  have hval : ∫ s in (0 : ℝ)..1, M * ‖h‖ ^ 2 * (1 - s) = M / 2 * ‖h‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    ring
  have hA : μ / 2 * ‖yp - xstar‖ ≤ M / 2 * ‖h‖ ^ 2 := by
    have := hlow (yp - xstar)
    rw [hrep] at this
    linarith
  have hμ2 : 0 < μ / 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith

/-- Contraction arithmetic: inside the ball the quadratic bound halves the radius. -/
theorem Newton53Aux.contract (M μ r : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr : r ≤ μ / (2 * M)) : M / μ * r ^ 2 ≤ r / 2 := by
  have hMR : M / μ * (μ / (2 * M)) = 1 / 2 := by field_simp
  have hk : 0 ≤ M / μ * r := by positivity
  calc M / μ * r ^ 2 = (M / μ * r) * r := by ring
    _ ≤ (M / μ * (μ / (2 * M))) * r := by
        apply mul_le_mul_of_nonneg_right _ hr0
        exact mul_le_mul_of_nonneg_left hr (by positivity)
    _ = r / 2 := by rw [hMR]; ring

open ConvexOptAlg.Newton Filter Topology in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (M μ : ℝ) (hM : 0 < M) (hHL : IsLipschitzHessian H M)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMin f xstar) (hμ : 0 < μ)
    (hHstar : ∀ v : EuclideanSpace ℝ (Fin n), μ * ‖v‖ ^ 2 ≤ inner ℝ (H xstar v) v)
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : ‖x0 - xstar‖ ≤ μ / (2 * M)) :
    (∃! x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 ∧ IsNewtonRun g H x) ∧
    ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → IsNewtonRun g H x →
      (∀ k, Function.Bijective (H (x k))) ∧
      (∀ k, ‖x (k + 1) - xstar‖ ≤ M / μ * ‖x k - xstar‖ ^ 2) ∧
      Tendsto x atTop (𝓝 xstar) := by
  have hstep := Newton53Aux.step f g H hfgH M μ hM hHL xstar hmin hμ hHstar
  set R := μ / (2 * M) with hR
  have hR0 : 0 ≤ R := by positivity
  -- along any run from x0 the error is at most R * (1/2)^k
  have hrun : ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → IsNewtonRun g H x →
      ∀ k, ‖x k - xstar‖ ≤ R * (1 / 2) ^ k := by
    intro x hx0' hx k
    induction k with
    | zero => simpa [hx0'] using hx0
    | succ k ih =>
      have hk : ‖x k - xstar‖ ≤ R := by
        have : R * (1 / 2) ^ k ≤ R := by
          apply mul_le_of_le_one_right hR0
          exact pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      have h1 := (hstep (x k) hk).2 (x (k + 1)) (hx k)
      have h2 := Newton53Aux.contract M μ _ hM hμ (norm_nonneg _) hk
      rw [pow_succ]
      linarith
  have hball : ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → IsNewtonRun g H x →
      ∀ k, ‖x k - xstar‖ ≤ R := by
    intro x hx0' hx k
    have := hrun x hx0' hx k
    have : R * (1 / 2) ^ k ≤ R := by
      apply mul_le_of_le_one_right hR0
      exact pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  refine ⟨?_, ?_⟩
  · -- existence and uniqueness
    classical
    let nx : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y =>
      if hy : ∃ z, H y (y - z) = g y then Classical.choose hy else y
    let X : ℕ → EuclideanSpace ℝ (Fin n) := fun k => nx^[k] x0
    have hXs : ∀ k, X (k + 1) = nx (X k) := fun k => Function.iterate_succ_apply' nx k x0
    have hXb : ∀ k, ‖X k - xstar‖ ≤ R ∧ H (X k) (X k - X (k + 1)) = g (X k) := by
      intro k
      induction k with
      | zero =>
        refine ⟨by simpa [X] using hx0, ?_⟩
        have hex : ∃ z, H (X 0) (X 0 - z) = g (X 0) := by
          obtain ⟨v, hv⟩ := (hstep (X 0) (by simpa [X] using hx0)).1.2 (g (X 0))
          exact ⟨X 0 - v, by rw [sub_sub_cancel]; exact hv⟩
        rw [hXs 0]
        simp only [nx, dif_pos hex]
        exact Classical.choose_spec hex
      | succ k ih =>
        have hb : ‖X (k + 1) - xstar‖ ≤ R := by
          have h1 := (hstep (X k) ih.1).2 (X (k + 1)) ih.2
          have h2 := Newton53Aux.contract M μ _ hM hμ (norm_nonneg _) ih.1
          have : ‖X k - xstar‖ / 2 ≤ R := by linarith [ih.1, norm_nonneg (X k - xstar)]
          linarith
        refine ⟨hb, ?_⟩
        have hex : ∃ z, H (X (k + 1)) (X (k + 1) - z) = g (X (k + 1)) := by
          obtain ⟨v, hv⟩ := (hstep (X (k + 1)) hb).1.2 (g (X (k + 1)))
          exact ⟨X (k + 1) - v, by rw [sub_sub_cancel]; exact hv⟩
        rw [hXs (k + 1)]
        simp only [nx, dif_pos hex]
        exact Classical.choose_spec hex
    refine ⟨X, ⟨by simp [X], fun k => (hXb k).2⟩, ?_⟩
    rintro y ⟨hy0, hy⟩
    have hYb := hball y hy0 hy
    funext k
    induction k with
    | zero => simp [X, hy0]
    | succ k ih =>
      have hinj := (hstep (y k) (hYb k)).1.1
      have e : H (y k) (y k - y (k + 1)) = H (y k) (y k - X (k + 1)) := by
        rw [hy k]
        have := (hXb k).2
        rw [← ih] at this
        exact this.symm
      have := hinj e
      exact sub_right_injective this
  · intro x hx0' hx
    have hb := hball x hx0' hx
    refine ⟨fun k => (hstep (x k) (hb k)).1, fun k => (hstep (x k) (hb k)).2 _ (hx k), ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (hrun x hx0' hx) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
