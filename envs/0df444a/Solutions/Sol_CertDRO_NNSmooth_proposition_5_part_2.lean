-- Prove2me | solution 1 for CertDRO.NNSmooth.proposition_5_part_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:01:18.287324+00:00
-- url     : https://prove2.me/submissions/732963ae-6c32-4bd8-bd25-e48c039fb9a9

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

set_option autoImplicit false

open CertDRO.NNSmooth CertDRO.NNSmooth.Network

theorem norm_fderiv_le' {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (f : E' → F') (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ u v, ‖f u - f v‖ ≤ C * ‖u - v‖) (x : E') : ‖fderiv ℝ f x‖ ≤ C := by
  have : LipschitzWith C.toNNReal f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa [dist_eq_norm, Real.coe_toNNReal _ hC] using h a b
  simpa [Real.coe_toNNReal _ hC] using norm_fderiv_le_of_lipschitz ℝ this

theorem core (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ)
    (hE : N.AssumptionE L L0 L1) :
    (∀ l ≤ L, Differentiable ℝ (N.F l)) ∧
    (∀ l ≤ L, ∀ x x' : E (N.dO 0), ‖N.F l x - N.F l x'‖ ≤ N.α L0 l * ‖x - x'‖) ∧
    (∀ l ≤ L, ∀ x : E (N.dO 0), ‖fderiv ℝ (N.F l) x‖ ≤ N.α L0 l) ∧
    (∀ l ≤ L, ∀ x x' : E (N.dO 0),
      ‖fderiv ℝ (N.F l) x - fderiv ℝ (N.F l) x'‖ ≤ N.β L0 L1 l * ‖x - x'‖) := by
  have hα : ∀ l, N.α L0 (l + 1) = L0 l * ‖N.θ l‖ * N.α L0 l := by
    intro l
    unfold Network.α
    rw [Finset.prod_range_succ]; ring
  have hαnn : ∀ l ≤ L, 0 ≤ N.α L0 l := by
    intro l
    induction l with
    | zero => intro _; simp [Network.α]
    | succ l ih =>
      intro hl
      rw [hα]
      have := (hE.L0_pos l (by omega)).le
      have := ih (by omega)
      positivity
  have hβ : ∀ l, N.β L0 L1 (l + 1) =
      L0 l * ‖N.θ l‖ * N.β L0 L1 l + (L1 l / (L0 l) ^ 2) * N.α L0 (l + 1) ^ 2 := by
    intro l
    unfold Network.β
    rw [Finset.sum_range_succ, hα l]
    ring
  have hdiff : ∀ l ≤ L, Differentiable ℝ (N.F l) := by
    intro l
    induction l with
    | zero => intro _; exact differentiable_id
    | succ l ih =>
      intro hl
      have h1 := ih (by omega)
      have : N.F (l + 1) = fun x => N.σ l (N.θ l (N.F l x)) := rfl
      rw [this]
      exact (hE.differentiable l (by omega)).comp ((N.θ l).differentiable.comp h1)
  have hstep : ∀ l < L, ∀ x : E (N.dO 0),
      fderiv ℝ (N.F (l + 1)) x =
        (fderiv ℝ (N.σ l) (N.θ l (N.F l x))).comp ((N.θ l).comp (fderiv ℝ (N.F l) x)) := by
    intro l hl x
    have h1 : HasFDerivAt (N.F l) (fderiv ℝ (N.F l) x) x :=
      ((hdiff l (by omega)) x).hasFDerivAt
    have h2 : HasFDerivAt (fun x => N.θ l (N.F l x)) ((N.θ l).comp (fderiv ℝ (N.F l) x)) x :=
      (N.θ l).hasFDerivAt.comp x h1
    have h3 : HasFDerivAt (N.σ l) (fderiv ℝ (N.σ l) (N.θ l (N.F l x))) (N.θ l (N.F l x)) :=
      ((hE.differentiable l hl) _).hasFDerivAt
    exact (h3.comp x h2).fderiv
  -- Lipschitz bound for F l
  have hlip : ∀ l ≤ L, ∀ x x' : E (N.dO 0), ‖N.F l x - N.F l x'‖ ≤ N.α L0 l * ‖x - x'‖ := by
    intro l
    induction l with
    | zero =>
      intro _ x x'
      simp [Network.α, Network.F]
    | succ l ih =>
      intro hl x x'
      have h1 := ih (by omega) x x'
      have hL0 : 0 ≤ L0 l := (hE.L0_pos l (by omega)).le
      have h2 := hE.lipschitz l (by omega) (N.θ l (N.F l x)) (N.θ l (N.F l x'))
      have h3 : ‖N.θ l (N.F l x) - N.θ l (N.F l x')‖ ≤ ‖N.θ l‖ * ‖N.F l x - N.F l x'‖ := by
        rw [← map_sub]; exact (N.θ l).le_opNorm _
      have h4 : N.F (l + 1) x - N.F (l + 1) x' =
          N.σ l (N.θ l (N.F l x)) - N.σ l (N.θ l (N.F l x')) := rfl
      rw [h4, hα]
      calc _ ≤ L0 l * ‖N.θ l (N.F l x) - N.θ l (N.F l x')‖ := h2
        _ ≤ L0 l * (‖N.θ l‖ * ‖N.F l x - N.F l x'‖) := by gcongr
        _ ≤ L0 l * (‖N.θ l‖ * (N.α L0 l * ‖x - x'‖)) := by gcongr
        _ = _ := by ring
  have hJ : ∀ l ≤ L, ∀ x : E (N.dO 0), ‖fderiv ℝ (N.F l) x‖ ≤ N.α L0 l := fun l hl x =>
    norm_fderiv_le' _ _ (hαnn l hl) (hlip l hl) x
  refine ⟨hdiff, hlip, hJ, ?_⟩
  intro l
  induction l with
  | zero =>
    intro _ x x'
    have : N.F 0 = id := rfl
    simp [this, Network.β]
  | succ l ih =>
    intro hl x x'
    have hl' : l < L := by omega
    have hL0 : 0 < L0 l := hE.L0_pos l hl'
    have hL1 : 0 ≤ L1 l := hE.L1_nonneg l hl'
    set A := fderiv ℝ (N.σ l) (N.θ l (N.F l x)) with hA
    set A' := fderiv ℝ (N.σ l) (N.θ l (N.F l x')) with hA'
    set T := N.θ l with hT
    set J := fderiv ℝ (N.F l) x with hJdef
    set J' := fderiv ℝ (N.F l) x' with hJ'def
    have hdecomp : fderiv ℝ (N.F (l + 1)) x - fderiv ℝ (N.F (l + 1)) x' =
        A'.comp (T.comp (J - J')) + (A - A').comp (T.comp J) := by
      rw [hstep l hl' x, hstep l hl' x']
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    have hA'n : ‖A'‖ ≤ L0 l :=
      norm_fderiv_le' _ _ hL0.le (hE.lipschitz l hl') _
    have hAA : ‖A - A'‖ ≤ L1 l * (‖T‖ * (N.α L0 l * ‖x - x'‖)) := by
      calc ‖A - A'‖ ≤ L1 l * ‖N.θ l (N.F l x) - N.θ l (N.F l x')‖ := hE.jacobian_lipschitz l hl' _ _
        _ ≤ L1 l * (‖T‖ * ‖N.F l x - N.F l x'‖) := by
          gcongr
          rw [← map_sub]; exact (N.θ l).le_opNorm _
        _ ≤ _ := by gcongr; exact hlip l hl'.le x x'
    have hJn : ‖J‖ ≤ N.α L0 l := hJ l hl'.le x
    have hαl := hαnn l hl'.le
    have hxx : 0 ≤ ‖x - x'‖ := norm_nonneg _
    have hTn : 0 ≤ ‖T‖ := norm_nonneg _
    have b1 : ‖A'.comp (T.comp (J - J'))‖ ≤ L0 l * (‖T‖ * (N.β L0 L1 l * ‖x - x'‖)) := by
      calc ‖A'.comp (T.comp (J - J'))‖ ≤ ‖A'‖ * ‖T.comp (J - J')‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A'‖ * (‖T‖ * ‖J - J'‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ L0 l * (‖T‖ * (N.β L0 L1 l * ‖x - x'‖)) := by
          gcongr
          exact ih (by omega) x x'
    have b2 : ‖(A - A').comp (T.comp J)‖ ≤
        (L1 l * (‖T‖ * (N.α L0 l * ‖x - x'‖))) * (‖T‖ * N.α L0 l) := by
      calc ‖(A - A').comp (T.comp J)‖ ≤ ‖A - A'‖ * ‖T.comp J‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A - A'‖ * (‖T‖ * ‖J‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ _ := by gcongr
    rw [hdecomp, hβ l, hα l]
    have heq : (L1 l / L0 l ^ 2) * (L0 l * ‖T‖ * N.α L0 l) ^ 2 =
        L1 l * ‖T‖ * ‖T‖ * N.α L0 l * N.α L0 l := by
      field_simp
    calc _ ≤ ‖A'.comp (T.comp (J - J'))‖ + ‖(A - A').comp (T.comp J)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add b1 b2
      _ = _ := by rw [add_mul, heq]; ring

theorem solution (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ)
    (hE : N.AssumptionE L L0 L1) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0),
      ‖fderiv ℝ (N.F l) x - fderiv ℝ (N.F l) x'‖ ≤ N.β L0 L1 l * ‖x - x'‖ :=
  (core N L L0 L1 hE).2.2.2
