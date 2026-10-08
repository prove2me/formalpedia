-- Prove2me | solution 1 for FirstOrderOpt.Stochastic.stochastic_mirror_descent_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:09:19.107989+00:00
-- url     : https://prove2.me/submissions/79ff18cb-c388-4742-b71a-b433a8d8983e

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

namespace C60

open FirstOrderOpt.Prox MeasureTheory

theorem three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (ν : DistanceGeneratingFunction X)
    (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + ν.V xt xt1 ≤ γt * Gt x + ν.V xt x) :
    ∀ x ∈ X, γt * Gt (xt1 - x) + ν.V xt xt1 ≤ ν.V xt x - ν.V xt1 x := by
  intro x hx
  set f : E → ℝ := fun u => γt * Gt u + ν.V xt u with hf
  have hloc : IsLocalMinOn f X xt1 := by
    have : IsMinOn f X xt1 := fun u hu => hmin u hu
    exact this.localize
  have h1 : HasFDerivWithinAt (fun u => γt * Gt u) (γt • Gt) X xt1 :=
    (Gt.hasFDerivWithinAt).const_mul γt
  have h2 : HasFDerivWithinAt (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt))
      (ν.dω xt1 - ν.dω xt) X xt1 :=
    ((ν.hasFDerivWithinAt xt1 hxt1).sub_const _).sub
      ((ν.dω xt).hasFDerivWithinAt.sub_const _)
  have h3 : HasFDerivWithinAt f (γt • Gt + (ν.dω xt1 - ν.dω xt)) X xt1 := by
    have heq : f = (fun u => γt * Gt u) +
        (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt)) := by
      funext u
      simp only [hf, DistanceGeneratingFunction.V, map_sub, Pi.add_apply]
    rw [heq]
    exact h1.add h2
  have hy : x - xt1 ∈ posTangentConeAt X xt1 :=
    sub_mem_posTangentConeAt_of_segment_subset (hXconv.segment_subset hxt1 hx)
  have key := hloc.hasFDerivWithinAt_nonneg h3 hy
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, map_sub, smul_eq_mul] at key
  simp only [DistanceGeneratingFunction.V, map_sub]
  linarith

theorem V_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ν : DistanceGeneratingFunction X) {a b : E} (ha : a ∈ X) (hb : b ∈ X) :
    (1 / 2) * ‖b - a‖ ^ 2 ≤ ν.V a b := by
  have := ν.strongConvex a ha b hb
  unfold DistanceGeneratingFunction.V
  linarith

theorem step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (M : ℝ) (xt xt1 xs : E) (Gt gt : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X) (hxs : xs ∈ X)
    (hsub : f xt + gt (xs - xt) ≤ f xs) (hgn : ‖gt‖ ≤ M)
    (hmin : ∀ y ∈ X, γ * Gt xt1 + ν.V xt xt1 ≤ γ * Gt y + ν.V xt y) :
    γ * (f xt - f xs) + ν.V xt1 xs ≤
      ν.V xt xs + γ ^ 2 * (M ^ 2 + ‖Gt - gt‖ ^ 2) - γ * (Gt - gt) (xt - xs) := by
  have h3 := three_point X hXconv ν xt xt1 Gt γ hxt1 hmin xs hxs
  have hV := V_ge X ν hxt hxt1
  have hd : ‖xt1 - xt‖ = ‖xt - xt1‖ := norm_sub_rev _ _
  have e1 : Gt (xt - xs) = Gt (xt - xt1) + Gt (xt1 - xs) := by
    rw [← map_add]; congr 1; abel
  have e2 : (Gt - gt) (xt - xs) = Gt (xt - xs) - gt (xt - xs) :=
    ContinuousLinearMap.sub_apply _ _ _
  have e3 : gt (xs - xt) = - gt (xt - xs) := by rw [← map_neg, neg_sub]
  have hG : Gt (xt - xt1) ≤ ‖Gt‖ * ‖xt - xt1‖ :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact Gt.le_opNorm _)
  have hGn : ‖Gt‖ ≤ M + ‖Gt - gt‖ := by
    calc ‖Gt‖ = ‖gt + (Gt - gt)‖ := by rw [add_sub_cancel]
      _ ≤ ‖gt‖ + ‖Gt - gt‖ := norm_add_le _ _
      _ ≤ M + ‖Gt - gt‖ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hgn
  have ha0 := norm_nonneg Gt
  have hb0 := norm_nonneg (Gt - gt)
  have ha2 : ‖Gt‖ ^ 2 ≤ (M + ‖Gt - gt‖) ^ 2 := pow_le_pow_left₀ ha0 hGn 2
  have k1 := mul_le_mul_of_nonneg_left ha2 (sq_nonneg γ)
  have k2 := mul_nonneg (sq_nonneg γ) (sq_nonneg (M - ‖Gt - gt‖))
  have k3 := mul_le_mul_of_nonneg_left hG hγ.le
  rw [hd] at hV
  rw [e2, e1]
  nlinarith [sq_nonneg (γ * ‖Gt‖ - ‖xt - xt1‖)]

theorem tele (a W c : ℕ → ℝ) (s : ℕ) (h : ∀ t, s ≤ t → a t + W (t + 1) ≤ W t + c t)
    (n : ℕ) :
    ∑ t ∈ Finset.Ico s (s + n), a t + W (s + n) ≤ W s + ∑ t ∈ Finset.Ico s (s + n), c t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have := h (s + n) (by omega)
    linarith

theorem jensen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (hfconv : ConvexOn ℝ X f) (I : Finset ℕ) (γ : ℕ → ℝ)
    (hγ : ∀ t, 0 < γ t) (hI : I.Nonempty) (y : ℕ → E) (hy : ∀ t ∈ I, y t ∈ X) (c : ℝ) :
    (∑ t ∈ I, γ t) * (f ((∑ t ∈ I, γ t)⁻¹ • ∑ t ∈ I, γ t • y t) - c) ≤
      ∑ t ∈ I, γ t * (f (y t) - c) := by
  set S := ∑ t ∈ I, γ t with hSdef
  have hS : 0 < S := Finset.sum_pos (fun t _ => hγ t) hI
  have hS0 : S ≠ 0 := hS.ne'
  have h1 : S⁻¹ • ∑ t ∈ I, γ t • y t = ∑ t ∈ I, (γ t / S) • y t := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  have hw1 : ∑ t ∈ I, γ t / S = 1 := by rw [← Finset.sum_div]; exact div_self hS0
  have hj := hfconv.map_sum_le (t := I) (w := fun t => γ t / S) (p := y)
    (fun t _ => (div_pos (hγ t) hS).le) hw1 hy
  rw [h1]
  have h3 : S * ∑ t ∈ I, (γ t / S) • f (y t) = ∑ t ∈ I, γ t * f (y t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul]
    field_simp
  have h4 : ∑ t ∈ I, γ t * (f (y t) - c) = ∑ t ∈ I, γ t * f (y t) - S * c := by
    simp only [mul_sub, Finset.sum_sub_distrib, hSdef, Finset.sum_mul]
  rw [h4, ← h3]
  have := mul_le_mul_of_nonneg_left hj hS.le
  linarith

end C60

open MeasureTheory FirstOrderOpt.Prox in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ m0)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f : E → ℝ) (hfconv : ConvexOn ℝ X f)
    (ν : DistanceGeneratingFunction X) (M σ : ℝ) (hM : 0 < M) (hσ : 0 < σ)
    (x : ℕ → Ω → E) (G : ℕ → Ω → E →L[ℝ] ℝ) (g : E → E →L[ℝ] ℝ) (γ : ℕ → ℝ)
    (hx : ∀ t ω, x t ω ∈ X) (hγ : ∀ t, 0 < γ t)
    (hxMeas : ∀ t, StronglyMeasurable[𝒢 t] (x t))
    (hGMeas : ∀ t, StronglyMeasurable[𝒢 (t + 1)] (G t))
    (hsub : ∀ x' ∈ X, ∀ y ∈ X, f x' + (g x') (y - x') ≤ f y)
    (hgnorm : ∀ x' ∈ X, ‖g x'‖ ≤ M)
    (hGint : ∀ t, Integrable (fun ω => G t ω - g (x t ω)) P)
    (hunbiased : ∀ t, condExp (𝒢 t) P (fun ω => G t ω - g (x t ω)) =ᵐ[P] 0)
    (hintsecmom : ∀ t, Integrable (fun ω => ‖G t ω - g (x t ω)‖ ^ 2) P)
    (hsecmom : ∀ t, condExp (𝒢 t) P (fun ω => ‖G t ω - g (x t ω)‖ ^ 2) ≤ᵐ[P]
      (fun _ => σ ^ 2))
    (hmin : ∀ t ω, ∀ y ∈ X, γ t * (G t ω) (x (t + 1) ω) + ν.V (x t ω) (x (t + 1) ω) ≤
      γ t * (G t ω) y + ν.V (x t ω) y)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y)
    (s k : ℕ) (hsk : s ≤ k)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω = (∑ t ∈ Finset.Icc s k, γ t)⁻¹ • ∑ t ∈ Finset.Icc s k, γ t • x t ω)
    (hintf : Integrable (fun ω => f (xbar ω)) P)
    (hintV : Integrable (fun ω => ν.V (x s ω) xstar) P) :
    ∫ ω, f (xbar ω) ∂P - f xstar ≤ (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (∫ ω, ν.V (x s ω) xstar ∂P + (M ^ 2 + σ ^ 2) * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2) := by
  classical
  set δ : ℕ → Ω → (E →L[ℝ] ℝ) := fun t ω => G t ω - g (x t ω) with hδdef
  have hδint : ∀ t, Integrable (δ t) P := hGint
  have hδsq : ∀ t, Integrable (fun ω => ‖δ t ω‖ ^ 2) P := hintsecmom
  have hun' : ∀ t, condExp (𝒢 t) P (δ t) =ᵐ[P] 0 := hunbiased
  have hsec' : ∀ t, condExp (𝒢 t) P (fun ω => ‖δ t ω‖ ^ 2) ≤ᵐ[P] (fun _ => σ ^ 2) :=
    hsecmom
  -- pointwise one-step inequality
  have hstep : ∀ t ω, γ t * (f (x t ω) - f xstar) + ν.V (x (t + 1) ω) xstar ≤
      ν.V (x t ω) xstar + γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2) - γ t * (δ t ω) (x t ω - xstar) :=
    fun t ω => C60.step X hXconv ν f M (x t ω) (x (t + 1) ω) xstar (G t ω) (g (x t ω)) (γ t)
      (hγ t) (hx t ω) (hx (t + 1) ω) hxstar (hsub _ (hx t ω) _ hxstar)
      (hgnorm _ (hx t ω)) (hmin t ω)
  have hfopt : ∀ t ω, 0 ≤ f (x t ω) - f xstar := fun t ω => sub_nonneg.2 (hxstar_opt _ (hx t ω))
  have hVge : ∀ t ω, (1 / 2) * ‖x t ω - xstar‖ ^ 2 ≤ ν.V (x t ω) xstar := fun t ω => by
    have := C60.V_ge X ν (hx t ω) hxstar
    rwa [norm_sub_rev] at this
  -- integrable upper bounds for V(x_t, x*)
  have hbound : ∀ n, ∃ B : Ω → ℝ, Integrable B P ∧ ∀ ω, ν.V (x (s + n) ω) xstar ≤ B ω := by
    intro n
    induction n with
    | zero => exact ⟨_, hintV, fun ω => le_rfl⟩
    | succ n ih =>
      obtain ⟨B, hB, hle⟩ := ih
      refine ⟨fun ω => B ω + γ (s + n) ^ 2 * (M ^ 2 + ‖δ (s + n) ω‖ ^ 2) +
        γ (s + n) * (‖δ (s + n) ω‖ ^ 2 / 2 + B ω), ?_, ?_⟩
      · exact (hB.add (((integrable_const _).add (hδsq _)).const_mul _)).add
          ((((hδsq _).div_const 2).add hB).const_mul _)
      · intro ω
        have h1 := hstep (s + n) ω
        have h2 := hfopt (s + n) ω
        have h3 := hVge (s + n) ω
        have h4 := hle ω
        have h5 : -((δ (s + n) ω) (x (s + n) ω - xstar)) ≤
            ‖δ (s + n) ω‖ * ‖x (s + n) ω - xstar‖ := by
          have := (δ (s + n) ω).le_opNorm (x (s + n) ω - xstar)
          rw [Real.norm_eq_abs] at this
          linarith [neg_abs_le ((δ (s + n) ω) (x (s + n) ω - xstar))]
        have hg := hγ (s + n)
        have h6 : ‖δ (s + n) ω‖ * ‖x (s + n) ω - xstar‖ ≤ ‖δ (s + n) ω‖ ^ 2 / 2 + B ω := by
          nlinarith [sq_nonneg (‖δ (s + n) ω‖ - ‖x (s + n) ω - xstar‖)]
        have h7 := mul_le_mul_of_nonneg_left (h5.trans h6) hg.le
        have h8 := mul_nonneg hg.le h2
        rw [show s + (n + 1) = s + n + 1 by omega]
        linarith
  have hxm : ∀ t, StronglyMeasurable (x t) := fun t => (hxMeas t).mono (𝒢.le t)
  have hqint : ∀ t, s ≤ t → Integrable (fun ω => ‖x t ω - xstar‖ ^ 2) P := by
    intro t ht
    obtain ⟨B, hB, hle⟩ := hbound (t - s)
    rw [show s + (t - s) = t by omega] at hle
    refine Integrable.mono' (hB.const_mul 2) ?_ (ae_of_all _ fun ω => ?_)
    · exact (((hxm t).sub stronglyMeasurable_const).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [hVge t ω, hle ω]
  have hYint : ∀ t, s ≤ t → Integrable (fun ω => (δ t ω) (x t ω - xstar)) P := by
    intro t ht
    refine Integrable.mono' (((hδsq t).add (hqint t ht)).div_const 2) ?_ (ae_of_all _ fun ω => ?_)
    · have hh : AEStronglyMeasurable (fun ω => x t ω - xstar) P :=
        (hxm t).aestronglyMeasurable.sub aestronglyMeasurable_const
      have := (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ).aestronglyMeasurable_comp₂
        hh (hδint t).aestronglyMeasurable
      simpa only [ContinuousLinearMap.apply_apply] using this
    · show _ ≤ (‖δ t ω‖ ^ 2 + ‖x t ω - xstar‖ ^ 2) / 2
      have := (δ t ω).le_opNorm (x t ω - xstar)
      nlinarith [sq_nonneg (‖δ t ω‖ - ‖x t ω - xstar‖)]
  have hYzero : ∀ t, s ≤ t → ∫ ω, (δ t ω) (x t ω - xstar) ∂P = 0 := by
    intro t ht
    have hh : StronglyMeasurable[𝒢 t] (fun ω => x t ω - xstar) :=
      (hxMeas t).sub stronglyMeasurable_const
    have hpull := condExp_bilin_of_stronglyMeasurable_left (m := 𝒢 t) (μ := P)
      (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) hh
      (by simpa only [ContinuousLinearMap.apply_apply] using hYint t ht) (hδint t)
    simp only [ContinuousLinearMap.apply_apply] at hpull
    rw [← integral_condExp (𝒢.le t)]
    calc ∫ ω, (P[fun ω => (δ t ω) (x t ω - xstar) | 𝒢 t]) ω ∂P
        = ∫ ω, (P[δ t | 𝒢 t] ω) (x t ω - xstar) ∂P := integral_congr_ae hpull
      _ = ∫ _, (0 : ℝ) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hun' t] with ω hω
          rw [hω]
          simp
      _ = 0 := by simp
  have hsecint : ∀ t, ∫ ω, ‖δ t ω‖ ^ 2 ∂P ≤ σ ^ 2 := by
    intro t
    rw [← integral_condExp (𝒢.le t)]
    calc ∫ ω, (P[fun ω => ‖δ t ω‖ ^ 2 | 𝒢 t]) ω ∂P ≤ ∫ _, σ ^ 2 ∂P :=
          integral_mono_ae integrable_condExp (integrable_const _) (hsec' t)
      _ = σ ^ 2 := by simp
  have hne : (Finset.Icc s k).Nonempty := ⟨s, Finset.mem_Icc.2 ⟨le_rfl, hsk⟩⟩
  set S := ∑ t ∈ Finset.Icc s k, γ t with hSdef
  have hS : 0 < S := Finset.sum_pos (fun t _ => hγ t) hne
  -- pointwise summed inequality
  have hpt : ∀ ω, S * (f (xbar ω) - f xstar) ≤ ν.V (x s ω) xstar +
      ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2) -
      ∑ t ∈ Finset.Icc s k, γ t * (δ t ω) (x t ω - xstar) := by
    intro ω
    have hj := C60.jensen X f hfconv (Finset.Icc s k) γ hγ hne (fun t => x t ω)
      (fun t _ => hx t ω) (f xstar)
    rw [← hxbar ω] at hj
    have ht := C60.tele (fun t => γ t * (f (x t ω) - f xstar)) (fun t => ν.V (x t ω) xstar)
      (fun t => γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2) - γ t * (δ t ω) (x t ω - xstar)) s
      (fun t _ => by have := hstep t ω; linarith) (k + 1 - s)
    have hIco : Finset.Ico s (s + (k + 1 - s)) = Finset.Icc s k := by
      ext t; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, Finset.sum_sub_distrib] at ht
    have hW := hVge (s + (k + 1 - s)) ω
    have hW0 : 0 ≤ ν.V (x (s + (k + 1 - s)) ω) xstar :=
      le_trans (by positivity) hW
    linarith
  have hLint : Integrable (fun ω => S * (f (xbar ω) - f xstar)) P :=
    (hintf.sub (integrable_const _)).const_mul _
  have hA : Integrable (fun ω => ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2)) P :=
    integrable_finsetSum (f := fun t ω => γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2)) _
      (fun t _ => ((integrable_const _).add (hδsq t)).const_mul _)
  have hC : Integrable (fun ω => ∑ t ∈ Finset.Icc s k, γ t * (δ t ω) (x t ω - xstar)) P :=
    integrable_finsetSum (f := fun t ω => γ t * (δ t ω) (x t ω - xstar)) _
      (fun t ht => (hYint t (Finset.mem_Icc.1 ht).1).const_mul _)
  have hRint : Integrable (fun ω => ν.V (x s ω) xstar +
      ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2) -
      ∑ t ∈ Finset.Icc s k, γ t * (δ t ω) (x t ω - xstar)) P := (hintV.add hA).sub hC
  have hmono := integral_mono hLint hRint hpt
  have hEL : ∫ ω, S * (f (xbar ω) - f xstar) ∂P = S * (∫ ω, f (xbar ω) ∂P - f xstar) := by
    rw [integral_const_mul, integral_sub hintf (integrable_const _)]
    simp
  have hER : ∫ ω, (ν.V (x s ω) xstar +
      ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2) -
      ∑ t ∈ Finset.Icc s k, γ t * (δ t ω) (x t ω - xstar)) ∂P =
      ∫ ω, ν.V (x s ω) xstar ∂P +
      ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ∫ ω, ‖δ t ω‖ ^ 2 ∂P) -
      ∑ t ∈ Finset.Icc s k, γ t * ∫ ω, (δ t ω) (x t ω - xstar) ∂P := by
    rw [integral_sub (f := fun ω => ν.V (x s ω) xstar +
        ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2)) (hintV.add hA) hC,
      integral_add hintV hA,
      integral_finsetSum (f := fun t ω => γ t ^ 2 * (M ^ 2 + ‖δ t ω‖ ^ 2)) _
        (fun t _ => ((integrable_const _).add (hδsq t)).const_mul _),
      integral_finsetSum (f := fun t ω => γ t * (δ t ω) (x t ω - xstar)) _
        (fun t ht => (hYint t (Finset.mem_Icc.1 ht).1).const_mul _)]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_const_mul, integral_add (integrable_const _) (hδsq t)]
      simp
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_const_mul]
  have h1 : ∑ t ∈ Finset.Icc s k, γ t ^ 2 * (M ^ 2 + ∫ ω, ‖δ t ω‖ ^ 2 ∂P) ≤
      (M ^ 2 + σ ^ 2) * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    have := mul_le_mul_of_nonneg_left (add_le_add_left (hsecint t) (M ^ 2)) (sq_nonneg (γ t))
    linarith
  have h2 : ∑ t ∈ Finset.Icc s k, γ t * ∫ ω, (δ t ω) (x t ω - xstar) ∂P = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hYzero t (Finset.mem_Icc.1 ht).1, mul_zero]
  rw [hEL, hER, h2] at hmono
  rw [le_inv_mul_iff₀ hS]
  linarith
