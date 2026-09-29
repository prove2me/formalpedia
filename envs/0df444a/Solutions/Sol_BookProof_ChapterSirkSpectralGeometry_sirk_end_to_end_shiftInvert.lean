-- Prove2me | solution 1 for BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:51.977977+00:00
-- url     : https://prove2.me/submissions/cb7590df-210d-4fab-b25a-7781a91199d0

import Definitions.Def_ChapterSirkSpectralGeometry
/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkEndToEnd.lean -/
noncomputable section EndToEndSupport
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
theorem tendsto_zero_of_le_sirkBound (err : ℕ → ℝ) (C Dmin h nv : ℝ) (hh : 0 < h)
    (hnn : ∀ m, 0 ≤ err m) (hle : ∀ m, err m ≤ sirkBound C Dmin h nv m) :
    Tendsto err atTop (𝓝 0) :=
  squeeze_zero hnn hle (sirk_error_decay_exponential C Dmin h nv hh)
theorem sirk_flow_error_tendsto_zero
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ m, ‖flow v - sirkApprox (V m) (psiB m) v‖ ≤ sirkBound C Dmin h ‖v‖ m) :
    Tendsto (fun m => ‖flow v - sirkApprox (V m) (psiB m) v‖) atTop (𝓝 0) :=
  tendsto_zero_of_le_sirkBound _ C Dmin h ‖v‖ hh (fun _ => norm_nonneg _) hbound
theorem sirk_flow_error_uniform_in_time
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : ℝ → E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, ℝ → G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ (t : ℝ) (m : ℕ),
      ‖flow t v - sirkApprox (V m) (psiB m t) v‖ ≤ sirkBound C Dmin h ‖v‖ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ t : ℝ, ‖flow t v - sirkApprox (V m) (psiB m t) v‖ < ε := by
  have hb := sirk_error_tendsto_zero C Dmin h ‖v‖ hh hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 hb
  refine ⟨M, fun m hm t => ?_⟩
  exact lt_of_le_of_lt (hbound t m) (lt_of_abs_lt (hM m hm))
theorem sirk_end_to_end_satisfiable
    (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (m : ℕ) (v : E) (hv : V (V.adjoint v) = v) :
    ‖X v - sirkApprox V (compress V X) v‖ ≤ sirkBound 1 1 1 ‖v‖ m := by
  refine sirk_end_to_end V X (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E)
    (ContinuousLinearMap.id ℂ F) (Polynomial.X : Polynomial ℂ) X X (compress V X) 1 1 1 m
    hVV hViso hVadj hinvX (fun x => ⟨x, rfl⟩) (by ext x; simp) ?_ rfl ?_ ?_ v hv
  · have hcid : compress V (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ F := by
      ext x; simpa [compress] using congrArg (fun f : F →L[ℂ] F => f x) hVV
    rw [hcid]; ext x; simp
  · have : (Polynomial.aeval X (Polynomial.X : Polynomial ℂ) : E →L[ℂ] E).comp
        (ContinuousLinearMap.id ℂ E) = X := by ext x; simp
    rw [this, sub_self, norm_zero]
    positivity
  · have : (Polynomial.aeval (compress V X) (Polynomial.X : Polynomial ℂ) : F →L[ℂ] F).comp
        (ContinuousLinearMap.id ℂ F) = compress V X := by ext x; simp
    rw [this, sub_self, norm_zero]
    positivity

end EndToEndSupport
/- Further source adaptation, same Apache-2.0 attribution:
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkSpectralGeometry.lean
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean -/
noncomputable section
namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
@[simp] theorem shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl

theorem norm_shiftMap_ge {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hxy : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    simp only [shiftMap_apply, inner_add_right, inner_smul_right, Complex.add_re, quadForm]
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h1 : γ * ‖(x : F)‖ ^ 2 ≤ (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re := by
    rw [hxy]; linarith [hpos x]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]
    simp
  · nlinarith

theorem IsShiftInvert.mem {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) : R u ∈ Dom := (h.2 u).choose

theorem IsShiftInvert.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) :
    A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := (h.2 u).choose_spec

theorem IsShiftInvert.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    ‖R u‖ ≤ γ⁻¹ * ‖u‖ := by
  have hb : γ * ‖((⟨R u, h.mem u⟩ : Dom) : F)‖ ≤ ‖shiftMap A γ ⟨R u, h.mem u⟩‖ :=
    norm_shiftMap_ge hpos _
  rw [show shiftMap A γ ⟨R u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
  simpa using hb

theorem IsShiftInvert.isSelfAdjoint [CompleteSpace F] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) : IsSelfAdjoint R := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_
  intro u v
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have hv : A ⟨R v, h.mem v⟩ + (γ : ℂ) • R v = v := h.shift_apply v
  have hcross : (inner ℂ (A ⟨R u, h.mem u⟩) (R v) : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) := hsym ⟨R u, h.mem u⟩ ⟨R v, h.mem v⟩
  have e1 : (inner ℂ (R u) v : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hv]
    rw [inner_add_right, inner_smul_right]
  have e2 : (inner ℂ u (R v) : ℂ)
      = inner ℂ (A ⟨R u, h.mem u⟩) (R v) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hu]
    rw [inner_add_left, inner_smul_left]
    simp
  change (inner ℂ (R u) v : ℂ) = inner ℂ u (R v)
  rw [e1, e2, hcross]

theorem IsShiftInvert.inner_nonneg {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    0 ≤ (inner ℂ u (R u) : ℂ).re := by
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have key : ∀ (y : F) (hy : y ∈ Dom),
      (inner ℂ (A ⟨y, hy⟩ + (γ : ℂ) • y) y : ℂ).re = quadForm A ⟨y, hy⟩ + γ * ‖y‖ ^ 2 := by
    intro y hy
    have hq : (inner ℂ (A ⟨y, hy⟩) y : ℂ).re = quadForm A ⟨y, hy⟩ := by
      rw [quadForm, ← inner_conj_symm (A ⟨y, hy⟩) y, Complex.conj_re]
    rw [inner_add_left, inner_smul_left, Complex.add_re, hq, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hexp := key (R u) (h.mem u)
  rw [hu] at hexp
  rw [hexp]
  have := hpos ⟨R u, h.mem u⟩
  positivity
theorem IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := (h.2 u).choose

theorem IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, h.mem u⟩ = u := (h.2 u).choose_spec

theorem IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hb : |γ.im| * ‖((⟨X u, h.mem u⟩ : Dom) : F)‖ ≤ ‖cshiftMap A γ ⟨X u, h.mem u⟩‖ :=
    norm_cshiftMap_ge hsym _ _
  rw [show cshiftMap A γ ⟨X u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  simpa using hb

theorem IsShiftInvertC.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    ‖X‖ ≤ |γ.im|⁻¹ :=
  X.opNorm_le_bound (by positivity) (h.norm_apply_le hsym hγ)
end BookProof.HashimotoShiftInvert
namespace OtherSpectral
open BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
theorem convex_realSegment (a b : ℝ) : Convex ℝ (realSegment a b) := by
  rintro x ⟨hxi, hxl, hxu⟩ y ⟨hyi, hyl, hyu⟩ s t hs ht hst
  have him : (s • x + t • y : ℂ).im = 0 := by
    simp [Complex.real_smul, hxi, hyi]
  have hre : (s • x + t • y : ℂ).re = s * x.re + t * y.re := by
    simp [Complex.real_smul, Complex.mul_re, hxi, hyi]
  have hsa : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
  have hsb : s * b + t * b = b := by rw [← add_mul, hst, one_mul]
  refine ⟨him, ?_, ?_⟩ <;> rw [hre]
  · linarith [mul_le_mul_of_nonneg_left hxl hs, mul_le_mul_of_nonneg_left hyl ht]
  · linarith [mul_le_mul_of_nonneg_left hxu hs, mul_le_mul_of_nonneg_left hyu ht]
theorem numRange_subset_realSegment_of_shiftInvert {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    numRange R ⊆ realSegment 0 γ⁻¹ := by
  rintro c ⟨x, hx, rfl⟩
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint hsym
  have hsymm : ∀ u v : F, (inner ℂ (R u) v : ℂ) = inner ℂ u (R v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (starRingEnd ℂ) (inner ℂ x (R x) : ℂ) = (inner ℂ x (R x) : ℂ) := by
      rw [inner_conj_symm, hsymm x x]
    have := Complex.conj_eq_iff_im.mp h1
    simpa using this
  · simpa using hR.inner_nonneg hpos hγ x
  · have hR' : ‖R x‖ ≤ γ⁻¹ * ‖x‖ := hR.norm_apply_le hpos hγ x
    calc (inner ℂ x (R x) : ℂ).re
        ≤ ‖(inner ℂ x (R x) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖R x‖ := norm_inner_le_norm _ _
      _ ≤ γ⁻¹ := by rw [hx, one_mul]; simpa [hx] using hR'
theorem crouzeix_domain_shiftInvert {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹ :=
  crouzeix_domain_transfer V R hViso _ (convex_realSegment 0 γ⁻¹)
    (numRange_subset_realSegment_of_shiftInvert hR hsym hpos hγ)
theorem numRange_subset_closedBall_of_shiftInvertC {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  (numRange_subset_closedBall X).trans
    (Metric.closedBall_subset_closedBall (hX.opNorm_le hsym hγ))
theorem crouzeix_domain_shiftInvertC {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
    (numRange_subset_closedBall_of_shiftInvertC hX hsym hγ)
theorem sirk_end_to_end_crouzeix_domain
    (V : G →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : G →L[ℂ] G)
    (C Dmin h : ℝ) (m : ℕ) (S : Set ℂ)
    (hS : numRange X ⊆ S)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, X (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange X ⊆ S →
      ‖psiX - (Polynomial.aeval X p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V X) ⊆ S →
      ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  have hSB : numRange (compress V X) ⊆ S :=
    ((numRange_compress_subset V X hViso).trans hS)
  exact sirk_end_to_end V X qX qXinv qBinv p flow psiX psiB C Dmin h m hVV hViso hVadj
    hinvX hinvq hqXl hqBr hflow (hcxX hS) (hcxB hSB) v hv
theorem crouzeix_domain_convexHull (V : G →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S) (hS : numRange X ⊆ S) :
    convexHull ℝ (numRange (compress V X)) ⊆ S :=
  crouzeix_domain_transfer V X hViso S hconv hS
theorem sirk_end_to_end_shiftInvert
    {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (qX qXinv : F →L[ℂ] F) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : F →L[ℂ] F) (psiB : G →L[ℂ] G) (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : F, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, R (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ F)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange R ⊆ realSegment 0 γ⁻¹ →
      ‖psiX - (Polynomial.aeval R p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V R) ⊆ realSegment 0 γ⁻¹ →
      ‖psiB - (Polynomial.aeval (compress V R) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : F) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m :=
  sirk_end_to_end_crouzeix_domain V R qX qXinv qBinv p flow psiX psiB C Dmin h m
    (realSegment 0 γ⁻¹)
    (numRange_subset_realSegment_of_shiftInvert hR hsym hpos hγ)
    hVV hViso hVadj hinvX hinvq hqXl hqBr hflow hcxX hcxB v hv
end OtherSpectral
-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}







variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
open OtherSpectral
theorem solution
    {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (qX qXinv : F →L[ℂ] F) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : F →L[ℂ] F) (psiB : G →L[ℂ] G) (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : F, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, R (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ F)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange R ⊆ realSegment 0 γ⁻¹ →
      ‖psiX - (Polynomial.aeval R p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V R) ⊆ realSegment 0 γ⁻¹ →
      ‖psiB - (Polynomial.aeval (compress V R) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : F) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  exact sirk_end_to_end_shiftInvert hR hsym hpos hγ V qX qXinv qBinv p flow psiX psiB C Dmin h m hVV hViso hVadj hinvX hinvq hqXl hqBr hflow hcxX hcxB v hv
#print axioms solution
