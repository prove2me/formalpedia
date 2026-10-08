-- Prove2me | solution 1 for GaussMagnetism.exists_vector_potential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:28:34.42699+00:00
-- url     : https://prove2.me/submissions/bef8f985-f76b-4e62-a849-b9c33d682b5e

import Mathlib
import Definitions.Def_GaussMagnetism_box_flux

set_option autoImplicit false

namespace VP04

open MeasureTheory intervalIntegral Set Metric Filter

section general

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem stepA {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × ℝ → F) (hf : ContDiff ℝ 1 f) (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t))
      (∫ t in a..b, (fderiv ℝ f (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  set D : E × ℝ → E →L[ℝ] F :=
    fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ) with hDdef
  have hD : Continuous D := (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hK : IsCompact (closedBall x₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  have hcont : ∀ x : E, Continuous (fun t : ℝ => f (x, t)) := fun x =>
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun x t => D (x, t)) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
  · exact (hcont x₀).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun t ht x hx =>
      hC (x, t) ⟨ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t _ x _ => ?_
    have h1 : HasFDerivAt f (fderiv ℝ f (x, t)) (x, t) :=
      ((hf.differentiable one_ne_zero) (x, t)).hasFDerivAt
    exact h1.comp x (hasFDerivAt_prodMk_left x t)

theorem smoothInt : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : E × ℝ → F), ContDiff ℝ (⊤ : ℕ∞) f → ∀ a b : ℝ,
    ContDiff ℝ n (fun x => ∫ t in a..b, f (x, t)) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ f hf a b
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
    exact contDiff_zero.2
      (Differentiable.continuous fun x => (stepA f h1 a b x).differentiableAt)
  | succ n ih =>
    intro F _ _ _ f hf a b
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ t in a..b,
      (fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)) (x, t), ?_,
      fun x => stepA f h1 a b x⟩
    exact ih (fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ))
      ((hf.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))).clm_comp contDiff_const) a b

theorem smoothUpper (g : E × ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : E → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in (0:ℝ)..c x, g (x, s)) := by
  have heq : (fun x => ∫ s in (0:ℝ)..c x, g (x, s)) =
      fun x => c x * ∫ t in (0:ℝ)..1, g (x, c x * t) := by
    funext x
    have := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := 1) (c := c x)
      (f := fun s => g (x, s))
    simp only [mul_zero, mul_one] at this
    exact this.symm
  rw [heq]
  refine hc.mul ?_
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => g (p.1, c p.1 * p.2)) :=
    hg.comp (contDiff_fst.prodMk ((hc.comp contDiff_fst).mul contDiff_snd))
  exact contDiff_infty.2 fun n => smoothInt n _ h2 0 1

end general

open Larmor TongEM

theorem line_deriv (B : Vec → Vec) (hB : Differentiable ℝ B) (w v : Vec) (i : Fin 3) (h : ℝ) :
    HasDerivAt (fun h : ℝ => B (w + h • v) i) (fderiv ℝ B (w + h • v) v i) h := by
  have hl : HasDerivAt (fun h : ℝ => w + h • v) v h := by
    simpa using ((hasDerivAt_id h).smul_const v).const_add w
  have h2 := (hB (w + h • v)).hasFDerivAt.comp_hasDerivAt h hl
  have h3 := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h h2
  simpa [Function.comp_def] using h3

theorem L1 (B : Vec → Vec) (hB : ContDiff ℝ 1 B) (p : ℝ → Vec) (hp : Continuous p) (v : Vec)
    (i : Fin 3) (a b : ℝ) :
    HasDerivAt (fun h : ℝ => ∫ s in a..b, B (p s + h • v) i)
      (∫ s in a..b, fderiv ℝ B (p s) v i) 0 := by
  set F' : ℝ → ℝ → ℝ := fun h s => fderiv ℝ B (p s + h • v) v i with hF'
  have hF'c : Continuous (fun q : ℝ × ℝ => F' q.1 q.2) := by
    have : Continuous (fun q : ℝ × ℝ => fderiv ℝ B (p q.2 + q.1 • v)) :=
      (hB.continuous_fderiv one_ne_zero).comp
        ((hp.comp continuous_snd).add (continuous_fst.smul continuous_const))
    exact (PiLp.continuous_apply 2 _ i).comp (this.clm_apply continuous_const)
  have hBc : Continuous B := hB.continuous
  have hFc : ∀ h : ℝ, Continuous (fun s => B (p s + h • v) i) := fun h =>
    (PiLp.continuous_apply 2 _ i).comp (hBc.comp (hp.add continuous_const))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0:ℝ) 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hF'c.continuousOn
  have hdiff : Differentiable ℝ B := hB.differentiable one_ne_zero
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := a) (b := b) (bound := fun _ => C) (F' := F') (x₀ := 0)
    (F := fun h s => B (p s + h • v) i)
    (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun h => (hFc h).aestronglyMeasurable)
    ((hFc 0).intervalIntegrable a b)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun t ht h hh => hC (h, t) ⟨ball_subset_closedBall hh, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (ae_of_all _ fun t _ h _ => line_deriv B hdiff (p t) v i h)
  simpa [F'] using this.2

end VP04

namespace VP04

open Larmor TongEM MeasureTheory intervalIntegral

noncomputable def e (j : Fin 3) : Vec := EuclideanSpace.single j 1

noncomputable def pi0 (x : Vec) : Vec := x - x 0 • e 0
noncomputable def pi01 (x : Vec) : Vec := x - x 0 • e 0 - x 1 • e 1

noncomputable def Pf (B : Vec → Vec) (x : Vec) : ℝ := ∫ s in (0:ℝ)..x 0, B (pi0 x + s • e 0) 2
noncomputable def Qf (B : Vec → Vec) (x : Vec) : ℝ :=
  -(∫ s in (0:ℝ)..x 0, B (pi0 x + s • e 0) 1) + ∫ u in (0:ℝ)..x 1, B (pi01 x + u • e 1) 0
noncomputable def Af (B : Vec → Vec) (x : Vec) : Vec := !₂[0, Pf B x, Qf B x]

theorem Af_0 (B : Vec → Vec) (y : Vec) : Af B y 0 = 0 := by simp [Af]
theorem Af_1 (B : Vec → Vec) (y : Vec) : Af B y 1 = Pf B y := by simp [Af]
theorem Af_2 (B : Vec → Vec) (y : Vec) : Af B y 2 = Qf B y := by simp [Af]

theorem e_apply (j k : Fin 3) : e j k = if k = j then 1 else 0 := by
  simp [e]

theorem c00 (x : Vec) (h : ℝ) : (x + h • e 0) 0 = x 0 + h := by simp [e_apply]
theorem c01 (x : Vec) (h : ℝ) : (x + h • e 0) 1 = x 1 := by simp [e_apply]
theorem c10 (x : Vec) (h : ℝ) : (x + h • e 1) 0 = x 0 := by simp [e_apply]
theorem c11 (x : Vec) (h : ℝ) : (x + h • e 1) 1 = x 1 + h := by simp [e_apply]
theorem c20 (x : Vec) (h : ℝ) : (x + h • e 2) 0 = x 0 := by simp [e_apply]

theorem v1 (x : Vec) (h : ℝ) : pi0 (x + h • e 0) = pi0 x := by
  ext k; fin_cases k <;> simp [pi0, e_apply]
theorem v2 (x : Vec) (h : ℝ) : pi0 (x + h • e 1) = pi0 x + h • e 1 := by
  ext k; fin_cases k <;> simp [pi0, e_apply]
theorem v3 (x : Vec) (h : ℝ) : pi0 (x + h • e 2) = pi0 x + h • e 2 := by
  ext k; fin_cases k <;> simp [pi0, e_apply]
theorem v4 (x : Vec) (h : ℝ) : pi01 (x + h • e 0) = pi01 x := by
  ext k; fin_cases k <;> simp [pi01, e_apply]
theorem v5 (x : Vec) (h : ℝ) : pi01 (x + h • e 1) = pi01 x := by
  ext k; fin_cases k <;> simp [pi01, e_apply]
theorem v6 (x : Vec) : pi0 x + x 0 • e 0 = x := by simp [pi0]
theorem v7 (x : Vec) : pi01 x + x 1 • e 1 = pi0 x := by simp [pi01, pi0]

theorem coord_contDiff (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec => x k) :=
  contDiff_piLp_apply 2

theorem comp_contDiff (B : Vec → Vec) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => B x k) := (contDiff_piLp 2).1 hB k

theorem pi0_contDiff : ContDiff ℝ (⊤ : ℕ∞) pi0 := by
  show ContDiff ℝ _ (fun x : Vec => x - x 0 • e 0)
  exact contDiff_id.sub ((coord_contDiff 0).smul contDiff_const)

theorem pi01_contDiff : ContDiff ℝ (⊤ : ℕ∞) pi01 := by
  show ContDiff ℝ _ (fun x : Vec => x - x 0 • e 0 - x 1 • e 1)
  exact (contDiff_id.sub ((coord_contDiff 0).smul contDiff_const)).sub
    ((coord_contDiff 1).smul contDiff_const)

theorem int_smooth (B : Vec → Vec) (hB : SmoothV B) (q : Vec → Vec)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (v : Vec) (i k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in (0:ℝ)..x k, B (q x + s • v) i) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec × ℝ => B (q p.1 + p.2 • v) i) :=
    (comp_contDiff B hB i).comp ((hq.comp contDiff_fst).add (contDiff_snd.smul contDiff_const))
  exact smoothUpper _ hg _ (coord_contDiff k)

theorem Af_smooth (B : Vec → Vec) (hB : SmoothV B) : SmoothV (Af B) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (Pf B) := int_smooth B hB pi0 pi0_contDiff (e 0) 2 0
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (Qf B) :=
    (int_smooth B hB pi0 pi0_contDiff (e 0) 1 0).neg
      |>.add (int_smooth B hB pi01 pi01_contDiff (e 1) 0 1)
  unfold SmoothV
  refine (contDiff_piLp 2).2 fun k => ?_
  fin_cases k
  · simpa [Af_0] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec => (0:ℝ)))
  · simpa [Af_1] using hP
  · simpa [Af_2] using hQ

theorem pd_of (A : Vec → Vec) (hA : Differentiable ℝ A) (x : Vec) (j i : Fin 3) (c : ℝ)
    (h : HasDerivAt (fun h : ℝ => A (x + h • e j) i) c 0) :
    partialDeriv A j i x = c := by
  have h1 := line_deriv A hA x (e j) i 0
  have := h1.unique h
  simpa [partialDeriv, e] using this

theorem Af_curl (B : Vec → Vec) (hB : SmoothV B) (hdiv : ∀ x, divg B x = 0) (x : Vec) :
    curl (Af B) x = B x := by
  have hB1 : ContDiff ℝ 1 B := hB.of_le (by exact_mod_cast le_top)
  have hBd : Differentiable ℝ B := hB1.differentiable one_ne_zero
  have hA1 : ContDiff ℝ 1 (Af B) := (Af_smooth B hB).of_le (by exact_mod_cast le_top)
  have hA : Differentiable ℝ (Af B) := hA1.differentiable one_ne_zero
  have hline : ∀ w v : Vec, Continuous (fun s : ℝ => w + s • v) := fun w v =>
    continuous_const.add (continuous_id.smul continuous_const)
  have hBc : ∀ (w v : Vec) (i : Fin 3), Continuous (fun s : ℝ => B (w + s • v) i) :=
    fun w v i => (PiLp.continuous_apply 2 _ i).comp (hB1.continuous.comp (hline w v))
  have hpdc : ∀ (w v : Vec) (j i : Fin 3),
      Continuous (fun s : ℝ => partialDeriv B j i (w + s • v)) := fun w v j i =>
    (PiLp.continuous_apply 2 _ i).comp
      (((hB1.continuous_fderiv one_ne_zero).comp (hline w v)).clm_apply continuous_const)
  have h10 : partialDeriv (Af B) 1 0 x = 0 := by
    apply pd_of _ hA
    simpa [Af_0] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have h20 : partialDeriv (Af B) 2 0 x = 0 := by
    apply pd_of _ hA
    simpa [Af_0] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have h01 : partialDeriv (Af B) 0 1 x = B x 2 := by
    apply pd_of _ hA
    have hf : (fun h : ℝ => Af B (x + h • e 0) 1) =
        fun h => ∫ s in (0:ℝ)..(x 0 + h), B (pi0 x + s • e 0) 2 := by
      funext h; rw [Af_1]; unfold Pf; rw [v1, c00]
    rw [hf]
    have := ((hBc (pi0 x) (e 0) 2).integral_hasStrictDerivAt 0 (x 0 + 0)).hasDerivAt.comp_const_add
      (x 0) 0
    simpa [v6] using this
  have h02 : partialDeriv (Af B) 0 2 x = -(B x 1) := by
    apply pd_of _ hA
    have hf : (fun h : ℝ => Af B (x + h • e 0) 2) =
        fun h => -(∫ s in (0:ℝ)..(x 0 + h), B (pi0 x + s • e 0) 1) +
          ∫ u in (0:ℝ)..x 1, B (pi01 x + u • e 1) 0 := by
      funext h; rw [Af_2]; unfold Qf; rw [v1, v4, c00, c01]
    rw [hf]
    have := (((hBc (pi0 x) (e 0) 1).integral_hasStrictDerivAt 0 (x 0 + 0)).hasDerivAt.comp_const_add
      (x 0) 0).neg.add_const (∫ u in (0:ℝ)..x 1, B (pi01 x + u • e 1) 0)
    simpa [v6] using this
  have h12 : partialDeriv (Af B) 1 2 x =
      -(∫ s in (0:ℝ)..x 0, partialDeriv B 1 1 (pi0 x + s • e 0)) + B (pi0 x) 0 := by
    apply pd_of _ hA
    have hf : (fun h : ℝ => Af B (x + h • e 1) 2) =
        fun h => -(∫ s in (0:ℝ)..x 0, B (pi0 x + s • e 0 + h • e 1) 1) +
          ∫ u in (0:ℝ)..(x 1 + h), B (pi01 x + u • e 1) 0 := by
      funext h; rw [Af_2]; unfold Qf; rw [v2, v5, c10, c11]
      simp only [add_right_comm (pi0 x) (h • e 1)]
    rw [hf]
    have this1 := L1 B hB1 (fun s => pi0 x + s • e 0) (hline _ _) (e 1) 1 0 (x 0)
    have this2 := ((hBc (pi01 x) (e 1) 0).integral_hasStrictDerivAt 0 (x 1 + 0)).hasDerivAt.comp_const_add
      (x 1) 0
    refine (this1.neg.add this2).congr_deriv ?_
    rw [add_zero, v7]
    rfl
  have h21 : partialDeriv (Af B) 2 1 x =
      ∫ s in (0:ℝ)..x 0, partialDeriv B 2 2 (pi0 x + s • e 0) := by
    apply pd_of _ hA
    have hf : (fun h : ℝ => Af B (x + h • e 2) 1) =
        fun h => ∫ s in (0:ℝ)..x 0, B (pi0 x + s • e 0 + h • e 2) 2 := by
      funext h; rw [Af_1]; unfold Pf; rw [v3, c20]
      simp only [add_right_comm (pi0 x) (h • e 2)]
    rw [hf]
    exact L1 B hB1 (fun s => pi0 x + s • e 0) (hline _ _) (e 2) 2 0 (x 0)
  have hftc : ∫ s in (0:ℝ)..x 0, partialDeriv B 0 0 (pi0 x + s • e 0) = B x 0 - B (pi0 x) 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => B (pi0 x + s • e 0) 0)
      (f' := fun s => partialDeriv B 0 0 (pi0 x + s • e 0))
      (fun s _ => line_deriv B hBd (pi0 x) (e 0) 0 s) ((hpdc _ _ 0 0).intervalIntegrable _ _)]
    simp [v6]
  have hdivpt : ∀ s : ℝ, partialDeriv B 0 0 (pi0 x + s • e 0) + partialDeriv B 1 1 (pi0 x + s • e 0)
      + partialDeriv B 2 2 (pi0 x + s • e 0) = 0 := by
    intro s
    have := hdiv (pi0 x + s • e 0)
    simpa [divg, Fin.sum_univ_three] using this
  have hint : ∫ s in (0:ℝ)..x 0, partialDeriv B 0 0 (pi0 x + s • e 0) =
      -(∫ s in (0:ℝ)..x 0, partialDeriv B 1 1 (pi0 x + s • e 0))
        - ∫ s in (0:ℝ)..x 0, partialDeriv B 2 2 (pi0 x + s • e 0) := by
    have i1 : IntervalIntegrable (fun s : ℝ => -partialDeriv B 1 1 (pi0 x + s • e 0)) volume 0 (x 0) :=
      (hpdc _ _ 1 1).neg.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s : ℝ => partialDeriv B 2 2 (pi0 x + s • e 0)) volume 0 (x 0) :=
      (hpdc _ _ 2 2).intervalIntegrable _ _
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub i1 i2]
    apply intervalIntegral.integral_congr
    intro s _
    simp only
    linarith [hdivpt s]
  ext k
  fin_cases k
  · show partialDeriv (Af B) 1 2 x - partialDeriv (Af B) 2 1 x = B x 0
    rw [h12, h21]; linarith
  · show partialDeriv (Af B) 2 0 x - partialDeriv (Af B) 0 2 x = B x 1
    rw [h20, h02]; ring
  · show partialDeriv (Af B) 0 1 x - partialDeriv (Af B) 1 0 x = B x 2
    rw [h01, h10]; ring

end VP04

open Larmor TongEM GaussMagnetism in
theorem solution (B : Vec → Vec) (hB : SmoothV B)
    (hdiv : ∀ x, divg B x = 0) :
    ∃ A : Vec → Vec, SmoothV A ∧ ∀ x, curl A x = B x := by
  exact ⟨VP04.Af B, VP04.Af_smooth B hB, fun x => VP04.Af_curl B hB hdiv x⟩
