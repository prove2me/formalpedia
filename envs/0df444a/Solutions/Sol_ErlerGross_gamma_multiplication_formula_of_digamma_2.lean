-- Prove2me | solution 2 for ErlerGross.gamma_multiplication_formula_of_digamma
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T03:52:49.921782+00:00
-- url     : https://prove2.me/submissions/cc9a7e51-58ce-46ea-9881-19d1e30cc873

import Mathlib
theorem solution (n : Nat) (hn : 0 < n)
    (hpsi : forall z : Complex, 0 < z.re ->
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
        n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex)) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  have hnC : (n : Complex) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have npole : ∀ s : Complex, 0 < s.re → ∀ m : ℕ, s ≠ -m := by
    intro s hs m h
    rw [h] at hs
    simp at hs
    linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hkre : ∀ z : Complex, 0 < z.re → ∀ k : ℕ, 0 < (z + (k : Complex) / n).re := by
    intro z hz k
    have : ((k : Complex) / n).re = k / n := by
      rw [show ((k : Complex) / n) = ((k / n : ℝ) : Complex) by push_cast; rfl, Complex.ofReal_re]
    rw [Complex.add_re, this]
    positivity
  have hnre : ∀ z : Complex, 0 < z.re → 0 < ((n : Complex) * z).re := by
    intro z hz
    simp [Complex.mul_re]
    positivity
  set F : Complex → Complex := fun z => ∏ k ∈ Finset.range n, Complex.Gamma (z + (k : Complex) / n)
    with hF
  set G : Complex → Complex := fun z => Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z) with hG
  set U : Set Complex := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have dGam : ∀ s : Complex, 0 < s.re → DifferentiableAt ℂ Complex.Gamma s :=
    fun s hs => Complex.differentiableAt_Gamma s (npole s hs)
  have hFd : DifferentiableOn ℂ F U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    simp only [hF]
    apply DifferentiableAt.fun_finsetProd
    intro k _
    exact (dGam _ (hkre z hz k)).comp z (by fun_prop)
  have hGd : DifferentiableOn ℂ G U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    simp only [hG]
    apply DifferentiableAt.mul (by fun_prop)
    exact (dGam _ (hnre z hz)).comp z (by fun_prop)
  have hFn : ∀ z ∈ U, F z ≠ 0 := by
    intro z hz
    simp only [hF]
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact Complex.Gamma_ne_zero (npole _ (hkre z hz k))
  have hGn : ∀ z ∈ U, G z ≠ 0 := by
    intro z hz
    simp only [hG]
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero (npole _ (hnre z hz)))
  have hlog : Set.EqOn (logDeriv F) (logDeriv G) U := by
    intro z hz
    have hz' : 0 < z.re := hz
    have e1 : logDeriv F z = ∑ k ∈ Finset.range n, Complex.digamma (z + (k : Complex) / n) := by
      simp only [hF]
      rw [logDeriv_prod]
      · apply Finset.sum_congr rfl
        intro k _
        have := logDeriv_comp (f := Complex.Gamma) (g := fun z => z + (k : Complex) / n) (x := z)
          (dGam _ (hkre z hz' k)) (by fun_prop)
        simp only [Function.comp_def] at this
        rw [this]
        simp [Complex.digamma]
      · intro k _
        exact Complex.Gamma_ne_zero (npole _ (hkre z hz' k))
      · intro k _
        exact (dGam _ (hkre z hz' k)).comp z (by fun_prop)
    have e2 : logDeriv G z = n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
      simp only [hG]
      rw [logDeriv_mul]
      · have := logDeriv_comp (f := Complex.Gamma) (g := fun z => (n : Complex) * z) (x := z)
          (dGam _ (hnre z hz')) (by fun_prop)
        simp only [Function.comp_def] at this
        rw [this]
        have h2 := logDeriv_comp (f := Complex.exp)
          (g := fun z => -(n : Complex) * z * (Real.log n : Complex)) (x := z)
          (by fun_prop) (by fun_prop)
        simp only [Function.comp_def] at h2
        rw [h2]
        simp [Complex.digamma, logDeriv_apply, Complex.exp_ne_zero]
        ring
      · exact Complex.exp_ne_zero _
      · exact Complex.Gamma_ne_zero (npole _ (hnre z hz'))
      · fun_prop
      · exact (dGam _ (hnre z hz')).comp z (by fun_prop)
    rw [e1, e2, hpsi z hz']
  obtain ⟨c, hc0, hc⟩ := (logDeriv_eqOn_iff hFd hGd hUo hUc hGn hFn).1 hlog
  refine ⟨c, hc0, ?_⟩
  have hFG : ∀ z, 0 < z.re → F z = c * G z := by
    intro z hz
    have := hc hz
    simpa [hG, mul_assoc] using this
  -- shift relations
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have shiftF : ∀ z : Complex, z ≠ 0 → F (z + 1 / (N + 1 : ℕ)) = z * F z := by
    intro z hz
    simp only [hF]
    rw [Finset.prod_range_succ, Finset.prod_range_succ']
    have e : z + 1 / ((N + 1 : ℕ) : Complex) + (N : Complex) / ((N + 1 : ℕ) : Complex) = z + 1 := by
      field_simp
      push_cast
      ring
    rw [e, Complex.Gamma_add_one _ hz]
    have : ∀ k ∈ Finset.range N, Complex.Gamma (z + 1 / ((N + 1 : ℕ) : Complex) + (k : Complex) / ((N + 1 : ℕ) : Complex)) =
        Complex.Gamma (z + ((k + 1 : ℕ) : Complex) / ((N + 1 : ℕ) : Complex)) := by
      intro k _
      congr 1
      push_cast
      ring
    rw [Finset.prod_congr rfl this]
    simp
    ring
  have shiftG : ∀ z : Complex, z ≠ 0 → G (z + 1 / (N + 1 : ℕ)) = z * G z := by
    intro z hz
    simp only [hG]
    have hnz : ((N + 1 : ℕ) : Complex) * z ≠ 0 := mul_ne_zero hnC hz
    have e : ((N + 1 : ℕ) : Complex) * (z + 1 / ((N + 1 : ℕ) : Complex)) =
        ((N + 1 : ℕ) : Complex) * z + 1 := by
      field_simp
    rw [e, Complex.Gamma_add_one _ hnz]
    have e2 : -((N + 1 : ℕ) : Complex) * (z + 1 / ((N + 1 : ℕ) : Complex)) * (Real.log (N + 1 : ℕ) : Complex)
        = -((N + 1 : ℕ) : Complex) * z * (Real.log (N + 1 : ℕ) : Complex) + -(Real.log (N + 1 : ℕ) : Complex) := by
      field_simp
      ring
    rw [e2, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hnr]
    field_simp
    push_cast
    ring
  have key : ∀ m : ℕ, ∀ z : Complex, -(m : ℝ) / (N + 1 : ℕ) < z.re → F z = c * G z := by
    intro m
    induction m with
    | zero => intro z hz; simp at hz; exact hFG z hz
    | succ m ih =>
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        have a : F 0 = 0 := by
          simp only [hF]
          apply Finset.prod_eq_zero (i := 0) (by simp)
          simp
        have b : G 0 = 0 := by simp [hG]
        rw [a, b, mul_zero]
      · have h1 := ih (z + 1 / (N + 1 : ℕ)) (by
          have : ((1 : Complex) / ((N + 1 : ℕ) : Complex)).re = 1 / (N + 1 : ℕ) := by
            rw [show ((1 : Complex) / ((N + 1 : ℕ) : Complex)) = ((1 / (N + 1 : ℕ) : ℝ) : Complex) by push_cast; rfl,
              Complex.ofReal_re]
          rw [Complex.add_re, this]
          push_cast at hz ⊢
          have : -((m : ℝ) + 1) / (N + 1) + 1 / (N + 1) = -(m:ℝ) / (N + 1) := by field_simp; ring
          linarith)
        rw [shiftF z hz0, shiftG z hz0] at h1
        have : z * F z = z * (c * G z) := by rw [h1]; ring
        exact mul_left_cancel₀ hz0 this
  intro z
  obtain ⟨m, hm⟩ := exists_nat_gt (-(z.re) * (N + 1 : ℕ))
  have := key m z (by
    rw [div_lt_iff₀ hnr]
    linarith)
  simpa [hF, hG, mul_assoc] using this
