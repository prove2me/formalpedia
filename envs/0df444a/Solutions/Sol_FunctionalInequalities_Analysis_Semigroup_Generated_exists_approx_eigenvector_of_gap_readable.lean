-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:26.295008+00:00
-- url     : https://prove2.me/submissions/7b278d77-8dc9-4379-a4ee-b1a4ef7502da

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_ApproximateEigenvector

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- The scalar core of the estimate: from the paired equation and the gap inequality at
`y / 2 - z`, `‖y - z‖² ≤ (‖T y‖² - λ ‖y‖²) / (8 λ)`, written without division. -/
private theorem FunctionalInequalities.Analysis.Semigroup.Generated.mul_norm_sub_sq_le (T : H₀ →ₗ.[ℝ] H₁) {lam : ℝ} (y z : T.domain)
    (heq : 2 * lam * ‖(y : H₀) - (z : H₀)‖ ^ 2 =
      ⟪T z, T y - T z⟫ - lam * ⟪(z : H₀), (y : H₀) - (z : H₀)⟫)
    (hgap : lam * ‖(2 : ℝ)⁻¹ • (y : H₀) - (z : H₀)‖ ^ 2 ≤ ‖(2 : ℝ)⁻¹ • T y - T z‖ ^ 2) :
    8 * lam * ‖(y : H₀) - (z : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2 - lam * ‖(y : H₀)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq] at hgap heq ⊢
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    at hgap heq ⊢
  rw [real_inner_comm (T y) (T z), real_inner_comm (y : H₀) (z : H₀)] at hgap heq
  rw [real_inner_comm (y : H₀) (z : H₀)]
  nlinarith [hgap, heq]
/-- **Approximate eigenvectors at the bottom of `T†T` on `(ker T)ᗮ`.** Under the gap inequality
`λ ‖y‖² ≤ ‖T y‖²` on `D(T) ∩ (ker T)ᗮ`, a unit `y` there with `‖T y‖² ≤ λ (1 + η)` lies within
`√(η / 8)` of some `z ∈ D(T†T) ∩ (ker T)ᗮ` with `‖T†T z - λ z‖ ≤ λ √(η / 2)`.

The route statement also assumes `0 ≤ η`; it is not needed, since the gap inequality at `y`
already forces `λ ≤ ‖T y‖² ≤ λ (1 + η)`. -/
theorem solution (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {lam η : ℝ} (hlam : 0 < lam)
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2)
    (y : T.domain) (hy : ∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0)
    (hy1 : ‖(y : H₀)‖ = 1) (hTy : ‖T y‖ ^ 2 ≤ lam * (1 + η)) :
    ∃ z : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2) := by
  have hs : 0 < lam⁻¹ := inv_pos.mpr hlam
  set f : H₀ := (2 : ℝ) • (y : H₀) with hf
  set u : T.domain := FunctionalInequalities.Analysis.Semigroup.resolventDomain T hT hs f with hu
  have hweak : FunctionalInequalities.Analysis.Semigroup.WeakResolvent T lam⁻¹ f u := FunctionalInequalities.Analysis.Semigroup.resolventDomain_spec T hT hs f
  have hmem : (u : H₀) ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    FunctionalInequalities.Analysis.Semigroup.mem_adjointComp_domain_resolventDomain T hT hs f
  let z : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain := ⟨(u : H₀), hmem⟩
  have hAz : FunctionalInequalities.Analysis.Semigroup.adjointComp T z = lam • (f - (u : H₀)) := by
    have h := FunctionalInequalities.Analysis.Semigroup.adjointComp_resolventDomain T hT hd hs f hmem
    rwa [inv_inv] at h
  have hzu : (⟨(z : H₀), z.2.2⟩ : T.domain) = u := rfl
  -- orthogonality to `ker T`
  have horth : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0 := by
    intro k hk
    have h := hweak k
    rw [hk, inner_zero_right, mul_zero, add_zero, hf, real_inner_smul_left, hy k hk,
      mul_zero] at h
    exact h
  -- the vector `B z = A z - λ z = 2 λ (y - z)`
  have hB : FunctionalInequalities.Analysis.Semigroup.adjointComp T z - lam • (z : H₀) = (2 * lam) • ((y : H₀) - (u : H₀)) := by
    rw [hAz, hf]
    change lam • ((2 : ℝ) • (y : H₀) - (u : H₀)) - lam • (u : H₀) = _
    module
  -- the paired equation `2 λ ‖y - z‖² = q(z, y - z)`
  have heq : 2 * lam * ‖(y : H₀) - (u : H₀)‖ ^ 2 =
      ⟪T u, T y - T u⟫ - lam * ⟪(u : H₀), (y : H₀) - (u : H₀)⟫ := by
    have hpair : ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀) - (u : H₀)⟫ = ⟪T u, T (y - u)⟫ :=
      FunctionalInequalities.Analysis.Semigroup.inner_adjointComp hd z (y - u).2
    rw [LinearPMap.map_sub] at hpair
    have hcalc : ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z - lam • (z : H₀), (y : H₀) - (u : H₀)⟫ =
        2 * lam * ‖(y : H₀) - (u : H₀)‖ ^ 2 := by
      rw [hB, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [← hcalc, inner_sub_left, real_inner_smul_left]
    change ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀) - (u : H₀)⟫ - lam * ⟪(u : H₀), (y : H₀) - (u : H₀)⟫ = _
    rw [hpair]
  -- the gap inequality at `y / 2 - z`
  have hgap' : lam * ‖(2 : ℝ)⁻¹ • (y : H₀) - (u : H₀)‖ ^ 2 ≤
      ‖(2 : ℝ)⁻¹ • T y - T u‖ ^ 2 := by
    have h := hgap ((2 : ℝ)⁻¹ • y - u) (by
      intro k hk
      change ⟪(2 : ℝ)⁻¹ • (y : H₀) - (u : H₀), (k : H₀)⟫ = 0
      rw [inner_sub_left, real_inner_smul_left, hy k hk, horth k hk, mul_zero, sub_zero])
    have hT : T ((2 : ℝ)⁻¹ • y - u) = (2 : ℝ)⁻¹ • T y - T u := by
      rw [LinearPMap.map_sub, LinearPMap.map_smul]
    rw [hT] at h
    exact h
  have hkey := FunctionalInequalities.Analysis.Semigroup.Generated.mul_norm_sub_sq_le T y u heq hgap'
  rw [hy1] at hkey
  have hsq : ‖(y : H₀) - (u : H₀)‖ ^ 2 ≤ η / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hkey, hTy]
  refine ⟨z, horth, ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le hsq
  · rw [hB, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hle : ‖(y : H₀) - (u : H₀)‖ ≤ Real.sqrt (η / 8) := Real.le_sqrt_of_sq_le hsq
    have hsqrt : Real.sqrt (η / 2) = 2 * Real.sqrt (η / 8) := by
      rw [show η / 2 = 2 ^ 2 * (η / 8) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [hsqrt]
    nlinarith [hle, hlam]
