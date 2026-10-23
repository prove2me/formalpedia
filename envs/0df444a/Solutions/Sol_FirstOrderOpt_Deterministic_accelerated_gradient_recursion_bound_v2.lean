-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_gradient_recursion_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T01:42:07.209036+00:00
-- url     : https://prove2.me/submissions/50d512d3-54f2-4385-9411-54f849a0a442

/- Reuses the accepted descent and proximal helpers by Nickrobbins95,
submission 00aeb2e7-65f2-4637-afd6-cd9b4b2af53b, target
3b65df88-28c9-4a57-912c-f4f6f9e247c6. New arbitrary-schedule step and
energy induction: Alexander Richard Towell (queelius), assisted by OpenAI Codex. -/
import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

namespace AGDRate3b65

open FirstOrderOpt.Prox

/-- Descent lemma along a convex set. -/
theorem descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (L : ℝ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + fGrad x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let p : ℝ → E := fun s => x + s • d
  have hpX : ∀ s ∈ Set.Icc (0:ℝ) 1, p s ∈ X := by
    intro s hs
    have e : p s = (1 - s) • x + s • y := by
      simp only [p, d, smul_sub, sub_smul, one_smul]; abel
    rw [e]
    exact hXconv hx hy (by linarith [hs.2]) hs.1 (by ring)
  let φ : ℝ → ℝ := fun s => f (p s) - s * fGrad x d - L / 2 * s ^ 2 * ‖d‖ ^ 2
  let φ' : ℝ → ℝ := fun s => fGrad (p s) d - fGrad x d - L * s * ‖d‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s := by
    intro s hs
    have hp : HasDerivWithinAt p d (Set.Icc 0 1) s := by
      have := ((hasDerivAt_id s).smul_const d).const_add x
      simpa [p] using this.hasDerivWithinAt
    have h1 : HasDerivWithinAt (f ∘ p) (fGrad (p s) d) (Set.Icc 0 1) s :=
      (hGrad (p s) (hpX s hs)).comp_hasDerivWithinAt s hp (fun r hr => hpX r hr)
    have h2 : HasDerivWithinAt (fun s : ℝ => s * fGrad x d) (fGrad x d) (Set.Icc 0 1) s := by
      simpa using ((hasDerivAt_id s).mul_const (fGrad x d)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * s * ‖d‖ ^ 2)
        (Set.Icc 0 1) s := by
      have := (((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖d‖ ^ 2)).hasDerivWithinAt
        (s := Set.Icc (0:ℝ) 1)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) (f' := φ')
    · intro s hs; exact (hderiv s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs ⊢
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).mono Set.Ioo_subset_Icc_self
    · intro s hs
      rw [interior_Icc] at hs
      have hsX := hpX s (Set.Ioo_subset_Icc_self hs)
      have hb : fGrad (p s) d - fGrad x d ≤ ‖fGrad (p s) - fGrad x‖ * ‖d‖ := by
        have := (fGrad (p s) - fGrad x).le_opNorm d
        rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
      have hn : ‖fGrad (p s) - fGrad x‖ ≤ L * (s * ‖d‖) := by
        have := hSmooth (p s) hsX x hx
        have e : p s - x = s • d := by simp [p]
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1] at this
        exact this
      have := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
      simp only [φ']
      nlinarith [norm_nonneg d]
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  have e1 : p 1 = y := by simp [p, d]
  have e0 : p 0 = x := by simp [p]
  simp only [φ] at h01
  rw [e1, e0] at h01
  norm_num at h01
  linarith

/-- Strong convexity lower bound for the Bregman distance. -/
theorem V_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ν : DistanceGeneratingFunction X) (u w : E) (hu : u ∈ X) (hw : w ∈ X) :
    (1 / 2) * ‖w - u‖ ^ 2 ≤ ν.V u w := by
  have := ν.strongConvex u hu w hw
  unfold DistanceGeneratingFunction.V
  linarith

/-- Three-point lemma from the minimality of the prox step. -/
theorem three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (γ : ℝ) (g : E →L[ℝ] ℝ) (u w : E) (hw : w ∈ X)
    (hmin : ∀ y ∈ X, γ * g w + ν.V u w ≤ γ * g y + ν.V u y) :
    ∀ y ∈ X, γ * g w + ν.V u w + ν.V w y ≤ γ * g y + ν.V u y := by
  intro y hy
  let h : E → ℝ := fun z => γ * g z + ν.V u z
  have hloc : IsLocalMinOn h X w := IsMinOn.localize (fun z hz => hmin z hz)
  have hVeq : (fun z => ν.V u z) = fun z => (ν.ω z - ν.ω u) - (ν.dω u z - ν.dω u u) := by
    funext z; simp [DistanceGeneratingFunction.V, map_sub]
  have h1 : HasFDerivWithinAt (fun z => γ * g z) (γ • g) X w := by
    exact (g.hasFDerivWithinAt (s := X) (x := w)).const_mul γ
  have h2 : HasFDerivWithinAt (fun z => ν.V u z) (ν.dω w - ν.dω u) X w := by
    rw [hVeq]
    exact ((ν.hasFDerivWithinAt w hw).sub_const (ν.ω u)).sub
      (((ν.dω u).hasFDerivWithinAt).sub_const (ν.dω u u))
  have hder : HasFDerivWithinAt h (γ • g + (ν.dω w - ν.dω u)) X w := h1.add h2
  have hcone : y - w ∈ posTangentConeAt X w :=
    sub_mem_posTangentConeAt_of_segment_subset (hXconv.segment_subset hw hy)
  have hnn := hloc.hasFDerivWithinAt_nonneg hder hcone
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, map_sub, smul_eq_mul] at hnn
  unfold DistanceGeneratingFunction.V
  simp only [map_sub]
  nlinarith [hnn]

/-- The pure algebra of one step. -/
theorem alg (T L Fbar Fx Fb Fs gq gp gb gxs gx n Vp Vq Vpq : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (D : (T + 1) * Fbar ≤ (T + 1) * Fx + 2 * (gq - gp) + 2 * L * n ^ 2 / (T + 1))
    (G : (T + 1) * gx = (T - 1) * gb + 2 * gp) (C1 : Fx + (gb - gx) ≤ Fb)
    (C2 : Fx + (gxs - gx) ≤ Fs)
    (T3 : T * gq + 2 * L * (Vpq + Vq) ≤ T * gxs + 2 * L * Vp) (S : 1 / 2 * n ^ 2 ≤ Vpq) :
    T * (T + 1) * (Fbar - Fs) + 4 * L * Vq ≤ (T - 1) * T * (Fb - Fs) + 4 * L * Vp := by
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hq : T * (2 * L * n ^ 2 / (T + 1)) ≤ 2 * L * n ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    have : 0 ≤ 2 * L * n ^ 2 := by positivity
    nlinarith
  have P1 := mul_le_mul_of_nonneg_left D hT0
  have P2 := mul_le_mul_of_nonneg_left C1 (show (0:ℝ) ≤ T * (T - 1) by nlinarith)
  have P3 := mul_le_mul_of_nonneg_left C2 (show (0:ℝ) ≤ 2 * T by linarith)
  have P4 : T * ((T + 1) * gx) = T * ((T - 1) * gb + 2 * gp) := by rw [G]
  have P5 := mul_le_mul_of_nonneg_left S (show (0:ℝ) ≤ 4 * L by linarith)
  nlinarith [P1, P2, P3, P4, P5, hq, T3]

end AGDRate3b65



namespace AGDGeneral9307

open FirstOrderOpt.Prox

theorem algebra_step (a γ L Fn Ft Fp Fs gn gp gb gs gt N Vp Vn Vpn : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hγ : 0 < γ)
    (hreg : γ * L * a ≤ 1)
    (D : Fn ≤ Ft + a * (gn - gp) + L / 2 * (a * N) ^ 2)
    (G : gt = (1-a)*gb + a*gp)
    (C1 : Ft + (gb-gt) ≤ Fp) (C2 : Ft + (gs-gt) ≤ Fs)
    (T3 : γ*gn + Vpn + Vn ≤ γ*gs + Vp)
    (S : 1/2*N^2 ≤ Vpn) :
    γ*(Fn-Fs) + a*Vn ≤ γ*(1-a)*(Fp-Fs) + a*Vp := by
  have herr : γ * (L / 2 * (a * N)^2) ≤ a * Vpn := by
    calc
      γ * (L / 2 * (a * N)^2) = (γ*L*a)*(a/2*N^2) := by ring
      _ ≤ 1*(a/2*N^2) := mul_le_mul_of_nonneg_right hreg (by positivity)
      _ ≤ a*Vpn := by nlinarith [mul_le_mul_of_nonneg_left S ha.le]
  have d := mul_le_mul_of_nonneg_left D hγ.le
  have c1 := mul_le_mul_of_nonneg_left C1 (mul_nonneg hγ.le (sub_nonneg.mpr ha1))
  have c2 := mul_le_mul_of_nonneg_left C2 (show 0 ≤ γ*a by positivity)
  have t3 := mul_le_mul_of_nonneg_left T3 ha.le
  have g : γ*gt = γ*((1-a)*gb + a*gp) := congrArg (γ * ·) G
  nlinarith [d,c1,c2,t3,g,herr]

theorem one_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (L : ℝ) (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x-y‖)
    (hConvex : ∀ x ∈ X, ∀ y ∈ X, f x + fGrad x (y-x) ≤ f y)
    (a γ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hγ : 0 < γ) (hreg : L*a ≤ 1/γ)
    (xp bp xn z bn s : E) (hxp : xp ∈ X) (hbp : bp ∈ X) (hxn : xn ∈ X)
    (hs : s ∈ X) (hz : z = (1-a) • bp + a • xp) (hbn : bn = (1-a) • bp + a • xn)
    (hmin : ∀ y ∈ X, γ * fGrad z xn + ν.V xp xn ≤ γ * fGrad z y + ν.V xp y) :
    γ*(f bn-f s) + a*ν.V xn s ≤ γ*(1-a)*(f bp-f s) + a*ν.V xp s := by
  have hzX : z ∈ X := by rw [hz]; exact hXconv hbp hxp (by linarith) ha.le (by ring)
  have hbnX : bn ∈ X := by rw [hbn]; exact hXconv hbp hxn (by linarith) ha.le (by ring)
  have hdiff : bn-z = a • (xn-xp) := by rw [hbn,hz,smul_sub]; abel
  have D := AGDRate3b65.descent X hXconv f L fGrad hGrad hSmooth z bn hzX hbnX
  rw [hdiff,map_smul,map_sub,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos ha] at D
  have G : fGrad z z = (1-a)*fGrad z bp + a*fGrad z xp := by
    simpa only [map_add,map_smul,smul_eq_mul] using congrArg (fGrad z) hz
  have C1 := hConvex z hzX bp hbp
  have C2 := hConvex z hzX s hs
  rw [map_sub] at C1 C2
  have T3 := AGDRate3b65.three_point X hXconv ν γ (fGrad z) xp xn hxn hmin s hs
  have S := AGDRate3b65.V_ge X ν xp xn hxp hxn
  have hreg' : γ*L*a ≤ 1 := by
    have := (le_div_iff₀ hγ).mp hreg
    nlinarith
  exact algebra_step a γ L (f bn) (f z) (f bp) (f s)
    (fGrad z xn) (fGrad z xp) (fGrad z bp) (fGrad z s) (fGrad z z)
    ‖xn-xp‖ (ν.V xp s) (ν.V xn s) (ν.V xp xn) ha ha1 hγ hreg' D G C1 C2 T3 S

end AGDGeneral9307

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x-y‖)
    (hConvex : ∀ x ∈ X, ∀ y ∈ X, f x + fGrad x (y-x) ≤ f y)
    (x xTilde xBar : ℕ → E) (q γ α : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hxBar0 : xBar 0 = x 0)
    (k : ℕ) (hk : 1 ≤ k)
    (hγpos : ∀ t, 1 ≤ t → t ≤ k → 0 < γ t)
    (hαpos : ∀ t, 1 ≤ t → t ≤ k → 0 < α t)
    (hαle : ∀ t, 1 ≤ t → t ≤ k → α t ≤ 1)
    (hTildeDef : ∀ t, 1 ≤ t → t ≤ k →
      xTilde t = (1-q t) • xBar (t-1) + q t • x (t-1))
    (hxDef : ∀ t, 1 ≤ t → t ≤ k → ∀ y ∈ X,
      γ t * fGrad (xTilde t) (x t) + ν.V (x (t-1)) (x t) ≤
        γ t * fGrad (xTilde t) y + ν.V (x (t-1)) y)
    (hBarDef : ∀ t, 1 ≤ t → t ≤ k →
      xBar t = (1-α t) • xBar (t-1) + α t • x t)
    (h13 : ∀ t, 1 ≤ t → t ≤ k → α t = q t)
    (h14 : ∀ t, 1 ≤ t → t ≤ k → L * α t ≤ 1 / γ t)
    (h15 : ∀ t, 2 ≤ t → t ≤ k →
      γ t * (1-α t) / α t ≤ γ (t-1) / α (t-1))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y) :
    f (xBar k) - f xstar + (α k / γ k) * ν.V (x k) xstar ≤
      (α k * γ 1 * (1-α 1) / (γ k * α 1)) * (f (xBar 0)-f xstar) +
        (α k / γ k) * ν.V (x 0) xstar := by
  have hBarX : ∀ t, t ≤ k → xBar t ∈ X := by
    intro t
    induction t with
    | zero => intro _; rw [hxBar0]; exact hx 0
    | succ n ih =>
      intro hn
      rw [hBarDef (n+1) (by omega) hn]
      simp only [Nat.add_sub_cancel]
      exact hXconv (ih (by omega)) (hx (n+1))
        (sub_nonneg.mpr (hαle (n+1) (by omega) hn))
        (hαpos (n+1) (by omega) hn).le (by ring)
  have step : ∀ t, 1 ≤ t → t ≤ k →
      γ t / α t * (f (xBar t)-f xstar) + ν.V (x t) xstar ≤
        γ t * (1-α t) / α t * (f (xBar (t-1))-f xstar) +
          ν.V (x (t-1)) xstar := by
    intro t h1 h2
    have ht : xTilde t = (1-α t) • xBar (t-1) + α t • x (t-1) := by
      rw [h13 t h1 h2]
      exact hTildeDef t h1 h2
    have hs := AGDGeneral9307.one_step X hXconv ν f L fGrad hGrad hSmooth hConvex
      (α t) (γ t) (hαpos t h1 h2) (hαle t h1 h2) (hγpos t h1 h2) (h14 t h1 h2)
      (x (t-1)) (xBar (t-1)) (x t) (xTilde t) (xBar t) xstar
      (hx (t-1)) (hBarX (t-1) (by omega)) (hx t) hxstar ht (hBarDef t h1 h2)
      (hxDef t h1 h2)
    have ha0 : α t ≠ 0 := (hαpos t h1 h2).ne'
    have hs' := div_le_div_of_nonneg_right hs (hαpos t h1 h2).le
    convert hs' using 1 <;> first | rfl | (field_simp [ha0] <;> ring)
  have energy : ∀ t, 1 ≤ t → t ≤ k →
      γ t / α t * (f (xBar t)-f xstar) + ν.V (x t) xstar ≤
        γ 1 * (1-α 1) / α 1 * (f (xBar 0)-f xstar) + ν.V (x 0) xstar := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ n ih =>
      intro h1 h2
      by_cases hn : n = 0
      · subst n
        simpa using step 1 (by omega) h2
      · have hn1 : 1 ≤ n := by omega
        have hgap : 0 ≤ f (xBar n)-f xstar :=
          sub_nonneg.mpr (hxstar_opt (xBar n) (hBarX n (by omega)))
        have hc := mul_le_mul_of_nonneg_right (h15 (n+1) (by omega) h2) hgap
        have hs := step (n+1) (by omega) h2
        simp only [Nat.add_sub_cancel] at hs hc
        exact le_trans (le_trans hs (add_le_add hc (le_refl _))) (ih hn1 (by omega))
  have he := energy k hk le_rfl
  have hg0 : γ k ≠ 0 := (hγpos k hk le_rfl).ne'
  have ha0 : α k ≠ 0 := (hαpos k hk le_rfl).ne'
  have ha10 : α 1 ≠ 0 := (hαpos 1 le_rfl hk).ne'
  have h := mul_le_mul_of_nonneg_left he
    (div_nonneg (hαpos k hk le_rfl).le (hγpos k hk le_rfl).le)
  convert h using 1 <;> first | rfl | (field_simp [hg0,ha0,ha10] <;> ring)
