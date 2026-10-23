-- Prove2me | solution 1 for BoydADMM2011.admm_convergence_with_dual_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:25:03.254916+00:00
-- url     : https://prove2.me/submissions/ca8b9a8f-0926-4277-bd21-0ad3ceb93c08

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model
import Theorems.Thm_BoydADMM_Convergence_admm_convergence
import Theorems.Thm_BoydADMM_Convergence_summed_bound
import Theorems.Thm_BoydADMM_Convergence_ineq_A1


open RealInnerProductSpace

namespace AD87

lemma lim_le (A B C : ℝ) (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t * A ≤ t * B + t ^ 2 * C) : A ≤ B := by
  by_contra hlt
  push Not at hlt
  set t := min 1 ((A - B) / (2 * (C + 1))) with ht
  have hpos : 0 < (A - B) / (2 * (C + 1)) := by
    apply div_pos <;> linarith
  have ht0 : 0 < t := lt_min one_pos hpos
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ (A - B) / (2 * (C + 1)) := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : A ≤ B + t * C := by
    have : t * A ≤ t * (B + t * C) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have h3 : t * C ≤ (A - B) / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right ht2 hC
  have h4 : (A - B) / (2 * (C + 1)) * C ≤ (A - B) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- First-order condition for minimizing `f + ⟪a, u⟫ + ρ/2‖u‖²` with `u = L x + b` affine and
`f` convex on `F`. -/
lemma sg {X V : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {F : Set X} {f : X → ℝ}
    (hf : ConvexOn ℝ F f) {ρ : ℝ} (hρ : 0 ≤ ρ) (L : X →ₗ[ℝ] V) (b a : V) {x0 : X}
    (hx0 : x0 ∈ F)
    (hmin : ∀ x ∈ F, f x0 + (⟪a, L x0 + b⟫ + ρ / 2 * ‖L x0 + b‖ ^ 2) ≤
      f x + (⟪a, L x + b⟫ + ρ / 2 * ‖L x + b‖ ^ 2)) :
    ∀ x ∈ F, f x0 - f x ≤ ⟪a + ρ • (L x0 + b), L x - L x0⟫ := by
  intro x hx
  set e := L x0 + b
  set d := L x - L x0
  apply lim_le _ _ (ρ / 2 * ‖d‖ ^ 2) (by positivity)
  intro t ht0 ht1
  have hmem : x0 + t • (x - x0) ∈ F := hf.1.add_smul_sub_mem hx0 hx ⟨ht0.le, ht1⟩
  have hconv := hf.2 hx0 hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
  have heq : (1 - t) • x0 + t • x = x0 + t • (x - x0) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [heq, smul_eq_mul, smul_eq_mul] at hconv
  have hL : L (x0 + t • (x - x0)) + b = e + t • d := by
    simp only [map_add, map_smul, map_sub, e, d]; abel
  have hm := hmin _ hmem
  rw [hL] at hm
  have hn : ‖e + t • d‖ ^ 2 = ‖e‖ ^ 2 + 2 * t * ⟪e, d⟫ + t ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have hi : ⟪a, e + t • d⟫ = ⟪a, e⟫ + t * ⟪a, d⟫ := by
    rw [inner_add_right, inner_smul_right]
  rw [hn, hi] at hm
  have hi2 : ⟪a + ρ • e, d⟫ = ⟪a, d⟫ + ρ * ⟪e, d⟫ := by
    rw [inner_add_left, inner_smul_left]; simp
  rw [hi2]
  nlinarith

/-- Lyapunov decrease for an anchor satisfying the two monotonicity inequalities. -/
lemma dec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ρ : ℝ} (hρ : 0 < ρ)
    (Y r D W : V) (M2 : 0 ≤ ⟪Y + ρ • r, -W⟫) (M1 : 0 ≤ ⟪Y + ρ • r - ρ • D, W - r⟫) :
    (1 / ρ) * ‖Y + ρ • r‖ ^ 2 + ρ * ‖W‖ ^ 2 ≤ (1 / ρ) * ‖Y‖ ^ 2 + ρ * ‖W - D‖ ^ 2 := by
  have e1 : ‖Y + ρ • r‖ ^ 2 = ‖Y‖ ^ 2 + 2 * ρ * ⟪Y, r⟫ + ρ ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have e2 : ‖W - D‖ ^ 2 = ‖W‖ ^ 2 - 2 * ⟪W, D⟫ + ‖D‖ ^ 2 := norm_sub_sq_real W D
  have e3 : ‖r - D‖ ^ 2 = ‖r‖ ^ 2 - 2 * ⟪r, D⟫ + ‖D‖ ^ 2 := norm_sub_sq_real r D
  have hM2 : ⟪Y + ρ • r, -W⟫ = -⟪Y, W⟫ - ρ * ⟪r, W⟫ := by
    simp only [inner_neg_right, inner_add_left, inner_smul_left]; simp; ring
  have hM1 : ⟪Y + ρ • r - ρ • D, W - r⟫ = ⟪Y, W⟫ - ⟪Y, r⟫ + ρ * ⟪r, W⟫ - ρ * ‖r‖ ^ 2
      - ρ * ⟪D, W⟫ + ρ * ⟪D, r⟫ := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq]; simp; ring
  rw [hM2] at M2; rw [hM1] at M1
  rw [e1, e2]
  have hsym1 : ⟪W, D⟫ = ⟪D, W⟫ := real_inner_comm _ _
  have hsym2 : ⟪r, D⟫ = ⟪D, r⟫ := real_inner_comm _ _
  have hnn : 0 ≤ ‖r - D‖ ^ 2 := sq_nonneg _
  have key : 2 * ⟪Y, r⟫ + ρ * ‖r‖ ^ 2 + 2 * ρ * ⟪D, W⟫ - ρ * ‖D‖ ^ 2 ≤ 0 := by
    nlinarith
  have : (1 / ρ) * (‖Y‖ ^ 2 + 2 * ρ * ⟪Y, r⟫ + ρ ^ 2 * ‖r‖ ^ 2) =
      (1 / ρ) * ‖Y‖ ^ 2 + 2 * ⟪Y, r⟫ + ρ * ‖r‖ ^ 2 := by
    field_simp
  rw [this]
  nlinarith

end AD87

open Filter Topology RealInnerProductSpace BoydADMM.Convergence

theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) :
    Filter.Tendsto (fun k => P.resid (x k) (z k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => P.f (x k) + P.g (z k)) Filter.atTop (nhds P.optVal) ∧
    ∃ yinf : EuclideanSpace ℝ (Fin p), P.IsSaddlePoint xs zs yinf ∧
      Filter.Tendsto y Filter.atTop (nhds yinf) := by
  obtain ⟨hr, ho, -⟩ := admm_convergence P hA1 hρ hsp hrun
  obtain ⟨-, -, hD⟩ := summed_bound P hA1 hρ hsp hrun
  refine ⟨hr, ho, ?_⟩
  -- notation
  have hBsub : ∀ a b, P.Bmul (a - b) = P.Bmul a - P.Bmul b := fun a b => by
    simp [Problem.Bmul, map_sub]
  set w : ℕ → EuclideanSpace ℝ (Fin p) := fun k => P.Bmul (z k) with hw
  set yh : ℕ → EuclideanSpace ℝ (Fin p) := fun k => y (k + 1) - ρ • (w (k + 1) - w k) with hyh
  have hres : ∀ x' z', P.resid x' z' = P.Amul x' + P.Bmul z' - P.c := fun _ _ => rfl
  -- first-order conditions of the two subproblems
  have FX : ∀ k, ∀ x' ∈ P.Cf, P.f (x (k + 1)) - P.f x' ≤ ⟪yh k, P.Amul x' - P.Amul (x (k + 1))⟫ := by
    intro k
    have h := AD87.sg hA1.1.convexOn hρ.le (Matrix.toEuclideanLin P.A) (P.Bmul (z k) - P.c) (y k)
      (hrun.x_mem k) (fun x' hx' => by
        have := hrun.x_min k x' hx'
        simp only [Problem.augLag, hres, Problem.Amul, add_sub_assoc] at this
        linarith)
    intro x' hx'
    have e : y k + ρ • (Matrix.toEuclideanLin P.A (x (k + 1)) + (P.Bmul (z k) - P.c)) = yh k := by
      simp only [hyh, hw, hrun.y_succ k, hres, Problem.Amul]
      simp only [smul_sub, smul_add]; abel
    have := h x' hx'
    rw [e] at this
    exact this
  have GZ : ∀ k, ∀ z' ∈ P.Cg, P.g (z (k + 1)) - P.g z' ≤ ⟪y (k + 1), P.Bmul z' - w (k + 1)⟫ := by
    intro k
    have h := AD87.sg hA1.2.convexOn hρ.le (Matrix.toEuclideanLin P.B) (P.Amul (x (k + 1)) - P.c) (y k)
      (hrun.z_mem k) (fun z' hz' => by
        have := hrun.z_min k z' hz'
        have e : ∀ z'', P.resid (x (k + 1)) z'' =
            Matrix.toEuclideanLin P.B z'' + (P.Amul (x (k + 1)) - P.c) := fun z'' => by
          rw [hres]; simp only [Problem.Bmul]; abel
        simp only [Problem.augLag, e] at this
        linarith)
    intro z' hz'
    have e : y k + ρ • (Matrix.toEuclideanLin P.B (z (k + 1)) + (P.Amul (x (k + 1)) - P.c)) =
        y (k + 1) := by
      simp only [hrun.y_succ k, hres, Problem.Bmul]
      simp only [smul_sub, smul_add]; abel
    have := h z' hz'
    rw [e] at this
    exact this
  -- boundedness via the saddle-point Lyapunov function
  set Vs : ℕ → ℝ := fun k => P.lyapunov ρ zs ys (z (k + 1)) (y (k + 1)) with hVs
  have hVsle : ∀ k, Vs k ≤ Vs 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have h := ineq_A1 P hA1 hρ hsp hrun k
      have h1 := mul_nonneg hρ.le (sq_nonneg ‖P.resid (x (k + 2)) (z (k + 2))‖)
      have h2 := mul_nonneg hρ.le (sq_nonneg ‖P.Bmul (z (k + 2) - z (k + 1))‖)
      change Vs (k + 1) ≤ Vs k - _ - _ at h
      linarith
  have hyb : ∀ k, ‖y (k + 1) - ys‖ ^ 2 ≤ ρ * Vs 0 := by
    intro k
    have hv := hVsle k
    simp only [hVs, Problem.lyapunov] at hv
    have := mul_nonneg hρ.le (sq_nonneg ‖P.Bmul (z (k + 1) - zs)‖)
    have h2 : (1 / ρ) * ‖y (k + 1) - ys‖ ^ 2 ≤ Vs 0 := by simp only [hVs, Problem.lyapunov]; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hρ.le
    rwa [← mul_assoc, mul_one_div_cancel hρ.ne', one_mul] at h3
  have hwb : ∀ k, ‖w (k + 1) - P.Bmul zs‖ ^ 2 ≤ Vs 0 / ρ := by
    intro k
    have hv := hVsle k
    have := mul_nonneg (one_div_nonneg.mpr hρ.le) (sq_nonneg ‖y (k + 1) - ys‖)
    have h2 : ρ * ‖P.Bmul (z (k + 1) - zs)‖ ^ 2 ≤ Vs 0 := by
      simp only [hVs, Problem.lyapunov] at hv ⊢; linarith
    rw [hBsub] at h2
    rw [le_div_iff₀ hρ]; linarith
  set R : ℝ := (Vs 0 / ρ + 1 + ‖P.Bmul zs‖) + (ρ * Vs 0 + 1 + ‖ys‖) with hR
  have hu : ∀ j, (w (j + 1), y (j + 1)) ∈ Metric.closedBall (0 : _ × _) R := by
    intro j
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    have a1 := hwb j
    have a2 := hyb j
    have b1 : ‖w (j + 1)‖ ≤ ‖w (j + 1) - P.Bmul zs‖ + ‖P.Bmul zs‖ := by
      simpa using norm_add_le (w (j + 1) - P.Bmul zs) (P.Bmul zs)
    have b2 : ‖y (j + 1)‖ ≤ ‖y (j + 1) - ys‖ + ‖ys‖ := by
      simpa using norm_add_le (y (j + 1) - ys) ys
    have c1 : ‖w (j + 1) - P.Bmul zs‖ ≤ ‖w (j + 1) - P.Bmul zs‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖w (j + 1) - P.Bmul zs‖ - 1)]
    have c2 : ‖y (j + 1) - ys‖ ≤ ‖y (j + 1) - ys‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖y (j + 1) - ys‖ - 1)]
    have hV0 : 0 ≤ Vs 0 := by
      simp only [hVs, Problem.lyapunov]; have := hρ.le; positivity
    have d1 : 0 ≤ Vs 0 / ρ + 1 + ‖P.Bmul zs‖ := by
      have := div_nonneg hV0 hρ.le; positivity
    have d2 : 0 ≤ ρ * Vs 0 + 1 + ‖ys‖ := by
      have := mul_nonneg hρ.le hV0; positivity
    constructor <;> linarith
  obtain ⟨⟨wb, yb⟩, -, φ, hφm, hlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hu
  have hφ : Tendsto φ atTop atTop := hφm.tendsto_atTop
  have hψ : Tendsto (fun i => φ i + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hφ
  have hwφ : Tendsto (fun i => w (φ i + 1)) atTop (𝓝 wb) :=
    (continuous_fst.tendsto _).comp hlim
  have hyφ : Tendsto (fun i => y (φ i + 1)) atTop (𝓝 yb) :=
    (continuous_snd.tendsto _).comp hlim
  have hDφ : Tendsto (fun i => w (φ i + 1) - w (φ i)) atTop (𝓝 0) := by
    have := hD.comp hφ
    refine this.congr (fun i => ?_)
    simp [Function.comp, hw, hBsub]
  have hyhφ : Tendsto (fun i => yh (φ i)) atTop (𝓝 yb) := by
    have := hyφ.sub (hDφ.const_smul ρ)
    simpa [hyh] using this
  have hAφ : Tendsto (fun i => P.Amul (x (φ i + 1))) atTop (𝓝 (P.c - wb)) := by
    have h1 := ((hr.comp hψ).sub hwφ).add_const P.c
    have e : (0 : EuclideanSpace ℝ (Fin p)) - wb + P.c = P.c - wb := by abel
    rw [e] at h1
    refine h1.congr (fun i => ?_)
    simp only [Function.comp, hres, hw]; abel
  -- the cluster point is an anchor
  have S2 : ∀ k, 0 ≤ ⟪y (k + 1) - yb, wb - w (k + 1)⟫ := by
    intro k
    have hl : Tendsto (fun i => ⟪y (k + 1) - y (φ i + 1), w (φ i + 1) - w (k + 1)⟫) atTop
        (𝓝 ⟪y (k + 1) - yb, wb - w (k + 1)⟫) :=
      (tendsto_const_nhds.sub hyφ).inner (hwφ.sub tendsto_const_nhds)
    refine ge_of_tendsto' hl (fun i => ?_)
    have g1 := GZ k (z (φ i + 1)) (hrun.z_mem _)
    have g2 := GZ (φ i) (z (k + 1)) (hrun.z_mem _)
    have e : ⟪y (k + 1) - y (φ i + 1), w (φ i + 1) - w (k + 1)⟫ =
        ⟪y (k + 1), P.Bmul (z (φ i + 1)) - w (k + 1)⟫ +
          ⟪y (φ i + 1), P.Bmul (z (k + 1)) - w (φ i + 1)⟫ := by
      have : P.Bmul (z (k + 1)) - w (φ i + 1) = -(w (φ i + 1) - w (k + 1)) := by
        simp [hw]
      rw [this, inner_neg_right, inner_sub_left]; simp [hw]; ring
    rw [e]; linarith
  have S1 : ∀ k, 0 ≤ ⟪yh k - yb, (P.c - wb) - P.Amul (x (k + 1))⟫ := by
    intro k
    have hl : Tendsto (fun i => ⟪yh k - yh (φ i), P.Amul (x (φ i + 1)) - P.Amul (x (k + 1))⟫)
        atTop (𝓝 ⟪yh k - yb, (P.c - wb) - P.Amul (x (k + 1))⟫) :=
      (tendsto_const_nhds.sub hyhφ).inner (hAφ.sub tendsto_const_nhds)
    refine ge_of_tendsto' hl (fun i => ?_)
    have f1 := FX k (x (φ i + 1)) (hrun.x_mem _)
    have f2 := FX (φ i) (x (k + 1)) (hrun.x_mem _)
    have e : ⟪yh k - yh (φ i), P.Amul (x (φ i + 1)) - P.Amul (x (k + 1))⟫ =
        ⟪yh k, P.Amul (x (φ i + 1)) - P.Amul (x (k + 1))⟫ +
          ⟪yh (φ i), P.Amul (x (k + 1)) - P.Amul (x (φ i + 1))⟫ := by
      have : P.Amul (x (k + 1)) - P.Amul (x (φ i + 1)) =
          -(P.Amul (x (φ i + 1)) - P.Amul (x (k + 1))) := by simp
      rw [this, inner_neg_right, inner_sub_left]; ring
    rw [e]; linarith
  -- Lyapunov function at the anchor
  set Va : ℕ → ℝ := fun k => (1 / ρ) * ‖y k - yb‖ ^ 2 + ρ * ‖w k - wb‖ ^ 2 with hVa
  have hVa0 : ∀ k, 0 ≤ Va k := fun k => by simp only [hVa]; positivity
  have hdec : ∀ k, Va (k + 1) ≤ Va k := by
    intro k
    set r := P.resid (x (k + 1)) (z (k + 1)) with hrdef
    have e1 : y (k + 1) - yb = (y k - yb) + ρ • r := by rw [hrun.y_succ k]; abel
    have e2 : yh k - yb = (y k - yb) + ρ • r - ρ • (w (k + 1) - w k) := by
      simp only [hyh]; rw [hrun.y_succ k]; abel
    have e3 : (P.c - wb) - P.Amul (x (k + 1)) = (w (k + 1) - wb) - r := by
      simp only [hrdef, hres, hw]; abel
    have e4 : wb - w (k + 1) = -(w (k + 1) - wb) := by abel
    have e5 : w k - wb = (w (k + 1) - wb) - (w (k + 1) - w k) := by abel
    have M2 := S2 k
    rw [e1, e4] at M2
    have M1 := S1 k
    rw [e2, e3] at M1
    have := AD87.dec hρ (y k - yb) r (w (k + 1) - w k) (w (k + 1) - wb) M2 M1
    simp only [hVa]
    rw [e1, e5]
    exact this
  have hanti : Antitone Va := antitone_nat_of_succ_le hdec
  have hinf := tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨k, rfl⟩; exact hVa0 k⟩
  have hsub0 : Tendsto (fun i => Va (φ i + 1)) atTop (𝓝 0) := by
    have := ((hyφ.sub_const yb).norm.pow 2).const_mul (1 / ρ) |>.add
      (((hwφ.sub_const wb).norm.pow 2).const_mul ρ)
    simpa [hVa] using this
  have hinf0 : (⨅ i, Va i) = 0 := tendsto_nhds_unique (hinf.comp hψ) hsub0
  rw [hinf0] at hinf
  have hy2 : Tendsto (fun k => ‖y k - yb‖ ^ 2) atTop (𝓝 0) := by
    have h := hinf.const_mul ρ
    rw [mul_zero] at h
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) h
    have := mul_nonneg hρ.le (sq_nonneg ‖w k - wb‖)
    simp only [hVa, mul_add, ← mul_assoc, mul_one_div_cancel hρ.ne', one_mul]
    nlinarith
  have hyconv : Tendsto y atTop (𝓝 yb) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := (Real.continuous_sqrt.tendsto 0).comp hy2
    rw [Real.sqrt_zero] at this
    refine this.congr (fun k => ?_)
    simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]
  -- the limit is dual optimal
  have hr0 : P.resid xs zs = 0 := by
    have h := hsp.2.2.1 (ys + P.resid xs zs)
    simp only [Problem.augLag, inner_add_left] at h
    have : ‖P.resid xs zs‖ ^ 2 ≤ 0 := by rw [← real_inner_self_eq_norm_sq]; linarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (P.resid xs zs)])
  have hopt : P.optVal = P.f xs + P.g zs := by
    apply IsLeast.csInf_eq
    refine ⟨⟨xs, hsp.1, zs, hsp.2.1, hr0, rfl⟩, ?_⟩
    rintro t ⟨x', hx', z', hz', hr', rfl⟩
    have h := hsp.2.2.2 x' hx' z' hz'
    simp only [Problem.augLag, hr0, hr', inner_zero_right] at h
    linarith
  refine ⟨yb, ⟨hsp.1, hsp.2.1, fun y' => by simp [Problem.augLag, hr0], ?_⟩, hyconv⟩
  intro x' hx' z' hz'
  have hL : Tendsto (fun i => P.f (x (φ i + 1)) + P.g (z (φ i + 1)) - (P.f x' + P.g z')) atTop
      (𝓝 (P.optVal - (P.f x' + P.g z'))) := (ho.comp hψ).sub_const _
  have hRt : Tendsto (fun i => ⟪yh (φ i), P.Amul x' - P.Amul (x (φ i + 1))⟫ +
      ⟪y (φ i + 1), P.Bmul z' - w (φ i + 1)⟫) atTop
      (𝓝 (⟪yb, P.Amul x' - (P.c - wb)⟫ + ⟪yb, P.Bmul z' - wb⟫)) :=
    (hyhφ.inner (tendsto_const_nhds.sub hAφ)).add (hyφ.inner (tendsto_const_nhds.sub hwφ))
  have hle := le_of_tendsto_of_tendsto' hL hRt (fun i => by
    have f1 := FX (φ i) x' hx'
    have g1 := GZ (φ i) z' hz'
    linarith)
  have e : ⟪yb, P.Amul x' - (P.c - wb)⟫ + ⟪yb, P.Bmul z' - wb⟫ = ⟪yb, P.resid x' z'⟫ := by
    rw [← inner_add_right, hres]; congr 1; abel
  rw [e, hopt] at hle
  simp only [Problem.augLag, hr0, inner_zero_right]
  linarith
