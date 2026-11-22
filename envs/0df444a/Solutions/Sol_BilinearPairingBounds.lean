-- Prove2me | solution 1 for BilinearPairingBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:18:43.502025+00:00
-- url     : https://prove2.me/submissions/9093b704-2221-44f4-8301-eee0dc88995c

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_BilinearPairingLeibnizStep
import Definitions.Def_PHigherOrder_BilinearPairingBounds
import Theorems.Thm_BilinearPairingLeibnizStep


set_option autoImplicit false

theorem _root_.solution (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (_hd : 0 < d)
    (m : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ q : ℝ, 0 < q ∧
      ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
        [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
        [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
        (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
      ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
      ∀ (F : Plane → Z₁) (G : Plane → Z₂),
        ContDiffOn ℝ (⊤ : ℕ∞) F U →
        (∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ K) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ m F x - iteratedFDeriv ℝ m F y‖ ≤ K * ‖x - y‖ ^ κ) →
        ContDiffOn ℝ (⊤ : ℕ∞) G U →
        (∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ K) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ m G x - iteratedFDeriv ℝ m G y‖ ≤ K * ‖x - y‖ ^ κ) →
        ((∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ m (fun y => B (F y) (G y)) x
            - iteratedFDeriv ℝ m (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ) := by
  -- Order ZERO, two-point form:  `norm_iteratedFDeriv_zero` is one-point only.
  have hzero : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : Plane → Z)
      (x y : Plane), ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
    intro Z _ _ f x y
    have e : ∀ z : Plane, iteratedFDeriv ℝ 0 f z
        = (continuousMultilinearCurryFin0 ℝ Plane Z).symm (f z) := by
      intro z
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [e x, e y, ← map_sub, LinearIsometryEquiv.norm_map]
  -- The induction, with the constant quantified outside the spaces and the data.
  have key : ∀ n : ℕ, ∀ L : ℝ, 0 < L → ∃ q : ℝ, 0 < q ∧
      ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
        [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
        [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
        (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
      ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
      ∀ (F : Plane → Z₁) (G : Plane → Z₂),
        ContDiffOn ℝ (⊤ : ℕ∞) F U →
        (∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ n F x - iteratedFDeriv ℝ n F y‖ ≤ L * ‖x - y‖ ^ κ) →
        ContDiffOn ℝ (⊤ : ℕ∞) G U →
        (∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ n G x - iteratedFDeriv ℝ n G y‖ ≤ L * ‖x - y‖ ^ κ) →
        ((∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ n (fun y => B (F y) (G y)) x
            - iteratedFDeriv ℝ n (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ) := by
    intro n
    induction n with
    | zero =>
      intro L hL
      refine ⟨2 * L * L + 1, by positivity, ?_⟩
      intro Z₁ Z₂ Z₃ _ _ _ _ _ _ B hB U hUo hUc hdiam F G hFsm hFsup hFhol hGsm hGsup hGhol
      have hFv : ∀ x ∈ U, ‖F x‖ ≤ L := by
        intro x hx
        have h := hFsup 0 le_rfl x hx
        rwa [norm_iteratedFDeriv_zero] at h
      have hGv : ∀ x ∈ U, ‖G x‖ ≤ L := by
        intro x hx
        have h := hGsup 0 le_rfl x hx
        rwa [norm_iteratedFDeriv_zero] at h
      have hFd : ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ L * ‖x - y‖ ^ κ := by
        intro x hx y hy
        have h := hFhol x hx y hy
        rwa [hzero Z₁ F x y] at h
      have hGd : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ L * ‖x - y‖ ^ κ := by
        intro x hx y hy
        have h := hGhol x hx y hy
        rwa [hzero Z₂ G x y] at h
      refine ⟨?_, ?_⟩
      · intro i hi x hx
        have hi0 : i = 0 := by omega
        subst hi0
        rw [norm_iteratedFDeriv_zero]
        have hA : ‖B (F x) (G x)‖ ≤ L * L :=
          le_trans (hB _ _) (mul_le_mul (hFv x hx) (hGv x hx) (norm_nonneg _) hL.le)
        nlinarith [hA]
      · intro x hx y hy
        rw [hzero Z₃ (fun y => B (F y) (G y)) x y]
        have hid : B (F x - F y) (G x) + B (F y) (G x - G y)
            = B (F x) (G x) - B (F y) (G y) := by
          rw [map_sub B, sub_apply, map_sub (B (F y))]
          abel
        calc ‖B (F x) (G x) - B (F y) (G y)‖
            = ‖B (F x - F y) (G x) + B (F y) (G x - G y)‖ := by rw [hid]
          _ ≤ ‖B (F x - F y) (G x)‖ + ‖B (F y) (G x - G y)‖ := norm_add_le _ _
          _ ≤ (2 * L * L + 1) * ‖x - y‖ ^ κ := by
              have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
              have hA : ‖B (F x - F y) (G x)‖ ≤ (L * ‖x - y‖ ^ κ) * L :=
                le_trans (hB _ _) (mul_le_mul (hFd x hx y hy) (hGv x hx)
                  (norm_nonneg _) (by positivity))
              have hC : ‖B (F y) (G x - G y)‖ ≤ L * (L * ‖x - y‖ ^ κ) :=
                le_trans (hB _ _) (mul_le_mul (hFv y hy) (hGd x hx y hy)
                  (norm_nonneg _) hL.le)
              nlinarith [hA, hC, hnn]
    | succ n ih => exact BilinearPairingLeibnizStep κ d hκ0 hκ1 n ih
  obtain ⟨q, hq, hbd⟩ := key m K hK
  exact ⟨q, hq, hbd⟩
