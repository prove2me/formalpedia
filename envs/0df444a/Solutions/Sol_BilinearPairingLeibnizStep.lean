-- Prove2me | solution 1 for BilinearPairingLeibnizStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:33.554299+00:00
-- url     : https://prove2.me/submissions/e5bfd2fa-1374-4ea4-ad66-70e4ebe78dfe

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetSumBounds
import Definitions.Def_PHigherOrder_JetHolderDescent
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint
import Definitions.Def_PHigherOrder_BilinearPairingLeibnizStep
import Theorems.Thm_IteratedFDerivShiftTwoPoint
import Theorems.Thm_JetHolderDescent
import Theorems.Thm_JetSumBounds


set_option autoImplicit false

theorem _root_.solution (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (n : ℕ)
    (ih : ∀ L : ℝ, 0 < L → ∃ q : ℝ, 0 < q ∧
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
                - iteratedFDeriv ℝ n (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ)) :
    ∀ L : ℝ, 0 < L → ∃ q : ℝ, 0 < q ∧
      ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
        [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
        [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
        (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
      ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
      ∀ (F : Plane → Z₁) (G : Plane → Z₂),
        ContDiffOn ℝ (⊤ : ℕ∞) F U →
        (∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ (n + 1) F x - iteratedFDeriv ℝ (n + 1) F y‖ ≤ L * ‖x - y‖ ^ κ) →
        ContDiffOn ℝ (⊤ : ℕ∞) G U →
        (∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ (n + 1) G x - iteratedFDeriv ℝ (n + 1) G y‖ ≤ L * ‖x - y‖ ^ κ) →
        ((∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ (n + 1) (fun y => B (F y) (G y)) x
            - iteratedFDeriv ℝ (n + 1) (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ) := by
  obtain ⟨θ, hθ1, hdesc⟩ := JetHolderDescent κ d hκ0 hκ1
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le one_pos hθ1
  -- Jets of a sum on an open set: additivity, and that sup and two-point bounds add.
  obtain ⟨hsumAdd, hsumBd, hsumHol⟩ := JetSumBounds
  intro L hL
  obtain ⟨q, hq, hstep⟩ := ih (L * θ) (mul_pos hL hθ0)
  have hQ : 2 * q ≤ L * L + 2 * q + 1 := by linarith [mul_self_nonneg L]
  refine ⟨L * L + 2 * q + 1, by positivity, ?_⟩
  intro Z₁ Z₂ Z₃ _ _ _ _ _ _ B hB U hUo hUc hdiam F G hFsm hFsup hFhol hGsm hGsup hGhol
  -- The two pairings the product rule produces.  Each satisfies the POINTWISE bound,
  -- which is the whole reason the hypothesis on `B` is pointwise.
  have hBan : ∀ a : Z₁, ‖B a‖ ≤ ‖a‖ := fun a =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (fun b => hB a b)
  have hflipn : ∀ b : Z₂, ‖B.flip b‖ ≤ ‖b‖ := by
    intro b
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b) ?_
    intro a
    rw [ContinuousLinearMap.flip_apply]
    calc ‖B a b‖ ≤ ‖a‖ * ‖b‖ := hB a b
      _ = ‖b‖ * ‖a‖ := by ring
  obtain ⟨B₁, hB₁def⟩ : ∃ T : Z₂ →L[ℝ] (Plane →L[ℝ] Z₁) →L[ℝ] (Plane →L[ℝ] Z₃),
      T = (ContinuousLinearMap.compL ℝ Plane Z₁ Z₃).comp B.flip := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂def⟩ : ∃ T : Z₁ →L[ℝ] (Plane →L[ℝ] Z₂) →L[ℝ] (Plane →L[ℝ] Z₃),
      T = (ContinuousLinearMap.compL ℝ Plane Z₂ Z₃).comp B := ⟨_, rfl⟩
  have hB₁p : ∀ (b : Z₂) (S : Plane →L[ℝ] Z₁), ‖B₁ b S‖ ≤ ‖b‖ * ‖S‖ := by
    intro b S
    rw [hB₁def]
    show ‖(B.flip b).comp S‖ ≤ ‖b‖ * ‖S‖
    calc ‖(B.flip b).comp S‖ ≤ ‖B.flip b‖ * ‖S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖b‖ * ‖S‖ := mul_le_mul_of_nonneg_right (hflipn b) (norm_nonneg S)
  have hB₂p : ∀ (a : Z₁) (T : Plane →L[ℝ] Z₂), ‖B₂ a T‖ ≤ ‖a‖ * ‖T‖ := by
    intro a T
    rw [hB₂def]
    show ‖(B a).comp T‖ ≤ ‖a‖ * ‖T‖
    calc ‖(B a).comp T‖ ≤ ‖B a‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖a‖ * ‖T‖ := mul_le_mul_of_nonneg_right (hBan a) (norm_nonneg T)
  -- Derivative fields, smooth on `U`.
  have hdF : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U := hFsm.fderiv_of_isOpen hUo (by norm_cast)
  have hdG : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ G) U := hGsm.fderiv_of_isOpen hUo (by norm_cast)
  -- Name the two summands, so the terms below stay short.
  obtain ⟨E₁, hE₁def⟩ : ∃ f : Plane → (Plane →L[ℝ] Z₃),
      f = fun z => B₁ (G z) (fderiv ℝ F z) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂def⟩ : ∃ f : Plane → (Plane →L[ℝ] Z₃),
      f = fun z => B₂ (F z) (fderiv ℝ G z) := ⟨_, rfl⟩
  have hsm1 : ContDiffOn ℝ (⊤ : ℕ∞) E₁ U := by
    rw [hE₁def]; exact (B₁.contDiff.comp_contDiffOn hGsm).clm_apply hdF
  have hsm2 : ContDiffOn ℝ (⊤ : ℕ∞) E₂ U := by
    rw [hE₂def]; exact (B₂.contDiff.comp_contDiffOn hFsm).clm_apply hdG
  -- The product rule, as an `EqOn` on `U`.
  have hEq : Set.EqOn (fderiv ℝ (fun y => B (F y) (G y))) (fun z => E₁ z + E₂ z) U := by
    as_aux_lemma =>
    intro z hz
    have hFd : HasFDerivAt F (fderiv ℝ F z) z :=
      (((hFsm.differentiableOn (by simp)) z hz).differentiableAt
        (hUo.mem_nhds hz)).hasFDerivAt
    have hGd : HasFDerivAt G (fderiv ℝ G z) z :=
      (((hGsm.differentiableOn (by simp)) z hz).differentiableAt
        (hUo.mem_nhds hz)).hasFDerivAt
    have hc : HasFDerivAt (fun y => B (F y)) (B.comp (fderiv ℝ F z)) z :=
      B.hasFDerivAt.comp z hFd
    rw [(hc.clm_apply hGd).fderiv, hE₁def, hE₂def, hB₁def, hB₂def]
    show (B (F z)).comp (fderiv ℝ G z) + (B.comp (fderiv ℝ F z)).flip (G z)
      = (B.flip (G z)).comp (fderiv ℝ F z) + (B (F z)).comp (fderiv ℝ G z)
    rw [add_comm]
    congr 1
  -- Goodness of the four arguments at order `n`, with the single constant `L * theta`.
  have hLLθ : L ≤ L * θ := by nlinarith [hL.le]
  have hdFg : (∀ i ≤ n, ∀ z ∈ U, ‖iteratedFDeriv ℝ i (fderiv ℝ F) z‖ ≤ L * θ) ∧
      ∀ z ∈ U, ∀ w ∈ U, ‖iteratedFDeriv ℝ n (fderiv ℝ F) z
        - iteratedFDeriv ℝ n (fderiv ℝ F) w‖ ≤ L * θ * ‖z - w‖ ^ κ := by
    refine ⟨fun i hi z hz => ?_, fun z hz w hw => ?_⟩
    · rw [norm_iteratedFDeriv_fderiv]
      exact le_trans (hFsup (i + 1) (by omega) z hz) hLLθ
    · rw [← IteratedFDerivShiftTwoPoint Z₁ F n z w]
      exact le_trans (hFhol z hz w hw)
        (mul_le_mul_of_nonneg_right hLLθ (Real.rpow_nonneg (norm_nonneg _) κ))
  have hdGg : (∀ i ≤ n, ∀ z ∈ U, ‖iteratedFDeriv ℝ i (fderiv ℝ G) z‖ ≤ L * θ) ∧
      ∀ z ∈ U, ∀ w ∈ U, ‖iteratedFDeriv ℝ n (fderiv ℝ G) z
        - iteratedFDeriv ℝ n (fderiv ℝ G) w‖ ≤ L * θ * ‖z - w‖ ^ κ := by
    refine ⟨fun i hi z hz => ?_, fun z hz w hw => ?_⟩
    · rw [norm_iteratedFDeriv_fderiv]
      exact le_trans (hGsup (i + 1) (by omega) z hz) hLLθ
    · rw [← IteratedFDerivShiftTwoPoint Z₂ G n z w]
      exact le_trans (hGhol z hz w hw)
        (mul_le_mul_of_nonneg_right hLLθ (Real.rpow_nonneg (norm_nonneg _) κ))
  obtain ⟨hFsup', hFhol'⟩ := hdesc Z₁ U hUo hUc hdiam n L F hL.le hFsm hFsup
  obtain ⟨hGsup', hGhol'⟩ := hdesc Z₂ U hUo hUc hdiam n L G hL.le hGsm hGsup
  -- Apply the inductive hypothesis to each summand.
  obtain ⟨hS1sup, hS1hol⟩ := hstep Z₂ (Plane →L[ℝ] Z₁) (Plane →L[ℝ] Z₃) B₁ hB₁p U hUo hUc
    hdiam G (fderiv ℝ F) hGsm hGsup' hGhol' hdF hdFg.1 hdFg.2
  obtain ⟨hS2sup, hS2hol⟩ := hstep Z₁ (Plane →L[ℝ] Z₂) (Plane →L[ℝ] Z₃) B₂ hB₂p U hUo hUc
    hdiam F (fderiv ℝ G) hFsm hFsup' hFhol' hdG hdGg.1 hdGg.2
  rw [← hE₁def] at hS1sup hS1hol
  rw [← hE₂def] at hS2sup hS2hol
  -- Transfer the goodness of the sum to `fderiv (B(F,G))` through the `EqOn`.
  have hcong : ∀ (i : ℕ), ∀ z ∈ U,
      iteratedFDeriv ℝ i (fderiv ℝ (fun y => B (F y) (G y))) z
        = iteratedFDeriv ℝ i E₁ z + iteratedFDeriv ℝ i E₂ z := by
    as_aux_lemma =>
    intro i z hz
    rw [← iteratedFDerivWithin_of_isOpen i hUo hz,
      iteratedFDerivWithin_congr hEq hz i, iteratedFDerivWithin_of_isOpen i hUo hz]
    exact hsumAdd (Plane →L[ℝ] Z₃) U hUo i E₁ E₂ hsm1 hsm2 z hz
  have hFv0 : ∀ x ∈ U, ‖F x‖ ≤ L := by
    intro x hx
    have h := hFsup 0 (by omega) x hx
    rwa [norm_iteratedFDeriv_zero] at h
  have hGv0 : ∀ x ∈ U, ‖G x‖ ≤ L := by
    intro x hx
    have h := hGsup 0 (by omega) x hx
    rwa [norm_iteratedFDeriv_zero] at h
  refine ⟨?_, ?_⟩
  · -- Sup bounds:  order `0` from the pointwise bilinear bound, higher orders by the
    -- order shift from the sup bounds for the derivative.  No Leibniz bound is needed.
    intro i hi x hx
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [norm_iteratedFDeriv_zero]
      have hA : ‖B (F x) (G x)‖ ≤ L * L :=
        le_trans (hB _ _) (mul_le_mul (hFv0 x hx) (hGv0 x hx) (norm_nonneg _) hL.le)
      linarith [hq.le]
    · obtain ⟨i', hi'⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
      subst hi'
      rw [← norm_iteratedFDeriv_fderiv, hcong i' x hx]
      exact hsumBd _ _ _ q (L * L + 2 * q + 1) (hS1sup i' (by omega) x hx)
        (hS2sup i' (by omega) x hx) hQ
  · -- Holder at order `n+1`, by the order shift and the triangle inequality.
    intro x hx y hy
    rw [IteratedFDerivShiftTwoPoint Z₃ (fun y => B (F y) (G y)) n x y, hcong n x hx, hcong n y hy]
    have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
    exact hsumHol _ _ _ _ _ q (L * L + 2 * q + 1) (‖x - y‖ ^ κ)
      (hS1hol x hx y hy) (hS2hol x hx y hy) hQ hnn
