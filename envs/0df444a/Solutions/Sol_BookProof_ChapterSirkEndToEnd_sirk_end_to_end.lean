-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.sirk_end_to_end
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:35:58.072095+00:00
-- url     : https://prove2.me/submissions/974ae0d1-35ca-4f8a-a473-4b717fd8f694

import Definitions.Def_ChapterSirkEndToEnd
/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkEndToEnd.lean -/
noncomputable section
open Filter Topology
open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd ContinuousLinearMap
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem compress_rational_transfer (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E)
    (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (v : E) (hv : V ((adjoint V) v) = v) :
    (Polynomial.aeval X p) (qXinv v) =
      V ((Polynomial.aeval (compress V X) p) (qBinv ((adjoint V) v))) := by
  have hb (Y : E →L[ℂ] E) (hY : ∀ x : F, ∃ y : F, Y (V x) = V y) (x : F) :
      Y (V x) = V (compress V Y x) := by
    obtain ⟨y, hy⟩ := hY x
    have hyy := congrArg (fun A : F →L[ℂ] F => A y) hVV
    simp only [compress, comp_apply, id_apply] at hyy ⊢
    rw [hy, hyy]
  have hInv (u : F) : qXinv (V u) = V (qBinv u) := by
    have hB := congrArg (fun A : F →L[ℂ] F => A u) hqBr
    have hQ := congrArg (fun A : E →L[ℂ] E => A (V (qBinv u))) hqXl
    simp only [comp_apply, id_apply] at hB hQ
    calc
      qXinv (V u) = qXinv (V (compress V qX (qBinv u))) := congrArg (fun w => qXinv (V w)) hB.symm
      _ = qXinv (qX (V (qBinv u))) := congrArg qXinv (hb qX hinvq (qBinv u)).symm
      _ = V (qBinv u) := hQ
  have hpow (n : ℕ) (u : F) : (X ^ n) (V u) = V (((compress V X) ^ n) u) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply]
      rw [ih, hb X hinvX]
  have hpoly (r : Polynomial ℂ) (u : F) :
      (Polynomial.aeval X r) (V u) = V ((Polynomial.aeval (compress V X) r) u) := by
    induction r using Polynomial.induction_on' with
    | add r s hr hs =>
      simp only [map_add, ContinuousLinearMap.add_apply, hr, hs]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, ContinuousLinearMap.smul_apply, hpow, map_smul]
  have hvinv : qXinv v = V (qBinv ((adjoint V) v)) :=
    (congrArg qXinv hv.symm).trans (hInv ((adjoint V) v))
  rw [hvinv, hpoly]

theorem sirk_error_decay_exponential (C Dmin h nv : ℝ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => sirkBound C Dmin h nv m) atTop (𝓝 0) := by
  have hlin : Tendsto (fun m : ℕ => -(h * (m : ℝ))) atTop atBot := by
    have : Tendsto (fun m : ℕ => h * (m : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hh tendsto_natCast_atTop_atTop
    exact tendsto_neg_atTop_atBot.comp this
  have hexp : Tendsto (fun m : ℕ => Real.exp (-(h * (m : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have := ((hexp.const_mul (2 * C)).mul_const Dmin).mul_const nv
  simpa [sirkBound, mul_zero, zero_mul] using this

theorem sirk_error_tendsto_zero (C Dmin h nv : ℝ) (hh : 0 < h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, |sirkBound C Dmin h nv m| < ε := by
  have h0 := sirk_error_decay_exponential C Dmin h nv hh
  have := h0 (Metric.ball_mem_nhds (0 : ℝ) hε)
  simpa [Real.dist_eq, Metric.mem_ball] using this

theorem krylov_rayleigh_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by
  rw [compress]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_right V y (X (V y))
theorem numRange_compress_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X := by
  rintro c ⟨y, hy, rfl⟩
  exact ⟨V y, by rw [hViso, hy], (krylov_rayleigh_transfer V X y).symm⟩

omit [CompleteSpace E] in

theorem numRange_subset_closedBall (X : E →L[ℂ] E) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by
  rintro c ⟨x, hx, rfl⟩
  have hcs : ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := norm_inner_le_norm _ _
  have hXb : ‖X x‖ ≤ ‖X‖ := by simpa [hx] using X.le_opNorm x
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := hcs
    _ = ‖X x‖ := by rw [hx, one_mul]
    _ ≤ ‖X‖ := hXb
@[simp] theorem sirkApprox_apply (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) :
    sirkApprox V psiB v = V (psiB (V.adjoint v)) := rfl
theorem sirk_error_bound_at
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (v : E) (hrt : rX v = V (rB (V.adjoint v))) :
    ‖phiA v - sirkApprox V psiB v‖ ≤ 2 * C * D * ‖v‖ := by
  have hCD : 0 ≤ C * D := le_trans (norm_nonneg _) hcx2
  have key : phiA v - sirkApprox V psiB v
      = (psiX - rX) v + V ((rB - psiB) (V.adjoint v)) := by
    have h1 : V ((rB - psiB) (V.adjoint v))
        = V (rB (V.adjoint v)) - V (psiB (V.adjoint v)) := by
      rw [ContinuousLinearMap.sub_apply, map_sub]
    rw [h1, ContinuousLinearMap.sub_apply, ← hrt, hphi, sirkApprox_apply]
    abel
  rw [key]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(psiX - rX) v‖ ≤ C * D * ‖v‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg _))
  have h2 : ‖V ((rB - psiB) (V.adjoint v))‖ ≤ C * D * ‖v‖ := by
    rw [hViso]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    exact mul_le_mul (by simpa only [norm_sub_rev] using hcx2) (hVadj v) (norm_nonneg _) hCD
  linarith
theorem crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S :=
  convexHull_min ((numRange_compress_subset V X hViso).trans hS) hconv
theorem crouzeix_domain_uniform (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
    (numRange_subset_closedBall X)
theorem sirk_end_to_end
    (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F)
    (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - (Polynomial.aeval X p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  have hrt : ((Polynomial.aeval X p).comp qXinv) v
      = V (((Polynomial.aeval (compress V X) p).comp qBinv) (V.adjoint v)) := by
    simpa using
      compress_rational_transfer V X qX qXinv qBinv p hVV hinvX hinvq hqXl hqBr v hv
  have := sirk_error_bound_at V flow psiX ((Polynomial.aeval X p).comp qXinv)
    psiB ((Polynomial.aeval (compress V X) p).comp qBinv)
    C (Real.exp (-(h * m)) * Dmin) hflow hViso hVadj hcx1 hcx2 v hrt
  simpa [sirkBound, mul_assoc] using this
theorem solution
    (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F)
    (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - (Polynomial.aeval X p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  exact sirk_end_to_end V X qX qXinv qBinv p flow psiX psiB C Dmin h m hVV hViso hVadj hinvX hinvq hqXl hqBr hflow hcx1 hcx2 v hv
#print axioms solution
