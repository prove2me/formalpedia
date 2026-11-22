-- Prove2me | solution 1 for CoeffFieldBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:21:23.723642+00:00
-- url     : https://prove2.me/submissions/7e4ea7c9-7a25-4457-ab9a-4e35e198a18b

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_BilinearPairingBounds
import Definitions.Def_PHigherOrder_JetHolderDescent
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint
import Definitions.Def_PHigherOrder_CoeffFieldBounds
import Theorems.Thm_BilinearPairingBounds
import Theorems.Thm_IteratedFDerivShiftTwoPoint
import Theorems.Thm_JetHolderDescent


set_option autoImplicit false

theorem _root_.solution (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C D d : ℝ) (hC : 0 < C) (hD : 0 < D) (hd : 0 < d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (U V : Set Plane) (Φ : Plane → W) (H : Plane → Plane),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, H x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ j + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ C) →
        ContDiffOn ℝ (⊤ : ℕ∞) H U →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i H x‖ ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ j H x - iteratedFDeriv ℝ j H y‖ ≤ D * ‖x - y‖ ^ κ) →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ H) x‖ ≤ M)
          ∧ (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ j (Φ ∘ H) x - iteratedFDeriv ℝ j (Φ ∘ H) y‖
                ≤ M * ‖x - y‖ ^ κ) := by
  -- The diameter-dependent descent factor, and the one-order jet descent it buys.
  obtain ⟨θ, hθ1, hdesc⟩ := JetHolderDescent κ d hκ0 hκ1
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le one_pos hθ1
  -- Step 2:  the composition estimate, by induction on the order.
  have step2 : ∀ n : ℕ, ∀ Cc Dd : ℝ, 0 < Cc → 0 < Dd → ∃ Mm : ℝ, 0 < Mm ∧
      ∀ (W' : Type) [NormedAddCommGroup W'] [NormedSpace ℝ W']
        (U V : Set Plane) (Φ : Plane → W') (H : Plane → Plane),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, H x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ n + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ Cc) →
        ContDiffOn ℝ (⊤ : ℕ∞) H U →
        (∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i H x‖ ≤ Dd) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ n H x - iteratedFDeriv ℝ n H y‖ ≤ Dd * ‖x - y‖ ^ κ) →
        ((∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ H) x‖ ≤ Mm)
          ∧ ∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ n (Φ ∘ H) x - iteratedFDeriv ℝ n (Φ ∘ H) y‖
                ≤ Mm * ‖x - y‖ ^ κ) := by
    intro n
    induction n with
    | zero =>
      intro Cc Dd hCc hDd
      refine ⟨Cc + Cc * Dd + 1, by positivity, ?_⟩
      intro W' _ _ U V Φ H hUo hUc hdiam hVo hVc hmaps hΦ hΦb hH hHb hHh
      have hΦv : ∀ ξ ∈ V, ‖Φ ξ‖ ≤ Cc := by
        intro ξ hξ
        have h := hΦb 0 (by omega) ξ hξ
        rwa [norm_iteratedFDeriv_zero] at h
      have hdΦ : ∀ ξ ∈ V, ‖fderiv ℝ Φ ξ‖ ≤ Cc := by
        intro ξ hξ
        have h := hΦb 1 (by omega) ξ hξ
        rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h
        exact h
      have hΦd : ∀ ξ ∈ V, DifferentiableAt ℝ Φ ξ := by
        intro ξ hξ
        exact ((hΦ.differentiableOn (by simp)) ξ hξ).differentiableAt (hVo.mem_nhds hξ)
      refine ⟨fun i hi x hx => ?_, fun x hx y hy => ?_⟩
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [norm_iteratedFDeriv_zero]
        show ‖Φ (H x)‖ ≤ Cc + Cc * Dd + 1
        have := hΦv (H x) (hmaps x hx)
        nlinarith [mul_pos hCc hDd]
      · -- The mean value inequality on `V`, then the order-zero Holder bound for `H`.
        have hHd : ‖H x - H y‖ ≤ Dd * ‖x - y‖ ^ κ := by
          have h := hHh x hx y hy
          have e : ∀ z : Plane, iteratedFDeriv ℝ 0 H z
              = (continuousMultilinearCurryFin0 ℝ Plane Plane).symm (H z) := by
            intro z
            rw [iteratedFDeriv_zero_eq_comp]
            rfl
          rw [e x, e y, ← map_sub, LinearIsometryEquiv.norm_map] at h
          exact h
        have hmv : ‖Φ (H x) - Φ (H y)‖ ≤ Cc * ‖H x - H y‖ :=
          hVc.norm_image_sub_le_of_norm_fderiv_le hΦd hdΦ (hmaps y hy) (hmaps x hx)
        have e0 : ∀ z : Plane, iteratedFDeriv ℝ 0 (Φ ∘ H) z
            = (continuousMultilinearCurryFin0 ℝ Plane W').symm ((Φ ∘ H) z) := by
          intro z
          rw [iteratedFDeriv_zero_eq_comp]
          rfl
        rw [e0 x, e0 y, ← map_sub, LinearIsometryEquiv.norm_map]
        show ‖Φ (H x) - Φ (H y)‖ ≤ (Cc + Cc * Dd + 1) * ‖x - y‖ ^ κ
        have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
        nlinarith [hmv, hHd, hCc.le, norm_nonneg (H x - H y)]
    | succ n ih =>
      intro Cc Dd hCc hDd
      obtain ⟨M', hM'0, hM'⟩ := ih Cc (Dd * θ) hCc (mul_pos hDd hθ0)
      obtain ⟨qq, hqq0, hqq⟩ :=
        BilinearPairingBounds κ d hκ0 hκ1 hd n (max M' Dd) (by positivity)
      obtain ⟨Dd', hDd'def⟩ : ∃ t : ℝ, t = max Dd 1 := ⟨_, rfl⟩
      have hDd'1 : (1 : ℝ) ≤ Dd' := by rw [hDd'def]; exact le_max_right _ _
      have hDdDd' : Dd ≤ Dd' := by rw [hDd'def]; exact le_max_left _ _
      have hDd'0 : (0 : ℝ) < Dd' := lt_of_lt_of_le one_pos hDd'1
      refine ⟨(Nat.factorial (n + 1) : ℝ) * Cc * Dd' ^ (n + 1) + qq + 1, by positivity, ?_⟩
      intro W' _ _ U V Φ H hUo hUc hdiam hVo hVc hmaps hΦ hΦb hH hHb hHh
      have hUu : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
      have hVu : UniqueDiffOn ℝ V := hVo.uniqueDiffOn
      have hmt : Set.MapsTo H U V := fun x hx => hmaps x hx
      refine ⟨?_, ?_⟩
      · -- Sup half:  the chain-rule bound, with `Dd' = max Dd 1` because it wants `D ^ i`.
        intro i hi x hx
        have hCb : ∀ l ≤ i, ‖iteratedFDerivWithin ℝ l Φ V (H x)‖ ≤ Cc := by
          intro l hl
          rw [iteratedFDerivWithin_of_isOpen l hVo (hmaps x hx)]
          exact hΦb l (by omega) (H x) (hmaps x hx)
        have hDb : ∀ l : ℕ, 1 ≤ l → l ≤ i → ‖iteratedFDerivWithin ℝ l H U x‖ ≤ Dd' ^ l := by
          intro l hl1 hl2
          rw [iteratedFDerivWithin_of_isOpen l hUo hx]
          calc ‖iteratedFDeriv ℝ l H x‖ ≤ Dd := hHb l (by omega) x hx
            _ ≤ Dd' := hDdDd'
            _ = Dd' ^ 1 := (pow_one Dd').symm
            _ ≤ Dd' ^ l := pow_le_pow_right₀ hDd'1 hl1
        have hL := norm_iteratedFDerivWithin_comp_le hΦ hH
          (by exact_mod_cast le_top) hVu hUu hmt hx hCb hDb
        rw [iteratedFDerivWithin_of_isOpen i hUo hx] at hL
        refine le_trans hL ?_
        have hfac : (Nat.factorial i : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
          exact_mod_cast Nat.factorial_le hi
        have hpw : Dd' ^ i ≤ Dd' ^ (n + 1) := pow_le_pow_right₀ hDd'1 hi
        have hfacpos : (0 : ℝ) ≤ (Nat.factorial i : ℝ) := by positivity
        have hpwpos : (0 : ℝ) < Dd' ^ i := by positivity
        calc (Nat.factorial i : ℝ) * Cc * Dd' ^ i
            ≤ (Nat.factorial (n + 1) : ℝ) * Cc * Dd' ^ i :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hfac hCc.le) hpwpos.le
          _ ≤ (Nat.factorial (n + 1) : ℝ) * Cc * Dd' ^ (n + 1) := by
              have : (0 : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) * Cc := by positivity
              nlinarith [hpw]
          _ ≤ (Nat.factorial (n + 1) : ℝ) * Cc * Dd' ^ (n + 1) + qq + 1 := by linarith
      · -- Holder half:  the chain rule, then the cited bilinear-pairing bound.
        intro x hx y hy
        -- The first argument of the pairing:  `D Phi` composed with `H`, by the IH.
        have hdΦsm : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) V := hΦ.fderiv_of_isOpen hVo (by norm_cast)
        have hdΦb : ∀ i ≤ n + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i (fderiv ℝ Φ) ξ‖ ≤ Cc := by
          intro i hi ξ hξ
          rw [norm_iteratedFDeriv_fderiv]
          exact hΦb (i + 1) (by omega) ξ hξ
        obtain ⟨hHsup', hHhol'⟩ := hdesc Plane U hUo hUc hdiam n Dd H hDd.le hH hHb
        obtain ⟨hA1, hA2⟩ := hM' (Plane →L[ℝ] W') U V (fderiv ℝ Φ) H hUo hUc hdiam hVo hVc
          hmaps hdΦsm hdΦb hH hHsup' hHhol'
        -- The second argument:  `D H`, which is `(n, Dd)`-good.
        have hdHsm : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H) U := hH.fderiv_of_isOpen hUo (by norm_cast)
        have hdHb : ∀ i ≤ n, ∀ z ∈ U, ‖iteratedFDeriv ℝ i (fderiv ℝ H) z‖ ≤ Dd := by
          intro i hi z hz
          rw [norm_iteratedFDeriv_fderiv]
          exact hHb (i + 1) (by omega) z hz
        have hdHh : ∀ z ∈ U, ∀ w ∈ U, ‖iteratedFDeriv ℝ n (fderiv ℝ H) z
            - iteratedFDeriv ℝ n (fderiv ℝ H) w‖ ≤ Dd * ‖z - w‖ ^ κ := by
          intro z hz w hw
          rw [← IteratedFDerivShiftTwoPoint Plane H n z w]
          exact hHh z hz w hw
        -- Both arguments at the single constant `max M' Dd`.
        have hmM : M' ≤ max M' Dd := le_max_left _ _
        have hmD : Dd ≤ max M' Dd := le_max_right _ _
        have hnnk : ∀ z w : Plane, (0 : ℝ) ≤ ‖z - w‖ ^ κ := fun z w =>
          Real.rpow_nonneg (norm_nonneg _) κ
        obtain ⟨hPsup, hPhol⟩ := hqq (Plane →L[ℝ] W') (Plane →L[ℝ] Plane) (Plane →L[ℝ] W')
          (ContinuousLinearMap.compL ℝ Plane Plane W')
          (fun S T => ContinuousLinearMap.opNorm_comp_le S T) U hUo hUc hdiam
          (fun z => fderiv ℝ Φ (H z)) (fderiv ℝ H)
          ((hdΦsm.comp hH hmt)) (fun i hi z hz => le_trans (hA1 i hi z hz) hmM)
          (fun z hz w hw => le_trans (hA2 z hz w hw)
            (mul_le_mul_of_nonneg_right hmM (hnnk z w)))
          hdHsm (fun i hi z hz => le_trans (hdHb i hi z hz) hmD)
          (fun z hz w hw => le_trans (hdHh z hz w hw)
            (mul_le_mul_of_nonneg_right hmD (hnnk z w)))
        -- The chain rule identifies `fderiv (Phi o H)` with that pairing on `U`.
        have hEq : Set.EqOn (fderiv ℝ (Φ ∘ H))
            (fun z => ContinuousLinearMap.compL ℝ Plane Plane W'
              (fderiv ℝ Φ (H z)) (fderiv ℝ H z)) U := by
          intro z hz
          have hHd : HasFDerivAt H (fderiv ℝ H z) z :=
            (((hH.differentiableOn (by simp)) z hz).differentiableAt
              (hUo.mem_nhds hz)).hasFDerivAt
          have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (H z)) (H z) :=
            (((hΦ.differentiableOn (by simp)) (H z) (hmaps z hz)).differentiableAt
              (hVo.mem_nhds (hmaps z hz))).hasFDerivAt
          rw [(hΦd.comp z hHd).fderiv]
          rfl
        have hcong : ∀ z ∈ U, iteratedFDeriv ℝ n (fderiv ℝ (Φ ∘ H)) z
            = iteratedFDeriv ℝ n (fun w => ContinuousLinearMap.compL ℝ Plane Plane W'
                (fderiv ℝ Φ (H w)) (fderiv ℝ H w)) z := by
          intro z hz
          rw [← iteratedFDerivWithin_of_isOpen n hUo hz,
            iteratedFDerivWithin_congr hEq hz n, iteratedFDerivWithin_of_isOpen n hUo hz]
        rw [IteratedFDerivShiftTwoPoint W' (Φ ∘ H) n x y, hcong x hx, hcong y hy]
        refine le_trans (hPhol x hx y hy) ?_
        have hfacnn : (0 : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) * Cc * Dd' ^ (n + 1) := by positivity
        nlinarith [hnnk x y]
  obtain ⟨M, hM, hbd⟩ := step2 j C D hC hD
  exact ⟨M, hM, fun U V Φ H hUo hUc hdiam hVo hVc hmaps hΦ hΦb hH hHb hHh =>
    hbd W U V Φ H hUo hUc hdiam hVo hVc hmaps hΦ hΦb hH hHb hHh⟩
