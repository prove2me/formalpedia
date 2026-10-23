-- Prove2me | solution 1 for FiniteEnergyPlane.eq_trivialCylinder_of_dlambdaEnergy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:00:44.034631+00:00
-- url     : https://prove2.me/submissions/b3048651-fe55-4b39-bb32-5dcccc4bec10

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn

set_option linter.all false


-- ===== DP_bloch =====


open Set Metric Filter Topology

namespace SchottkyDev

/-- **Bloch's theorem** (quantitative form, constant `1/128`): a holomorphic function on a disc
of radius `s` covers some disc of radius `s ‖f' z‖ / 128`. -/
theorem bloch (f : ℂ → ℂ) (z : ℂ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableOn ℂ f (ball z s)) :
    ∃ b, ball b (s * ‖deriv f z‖ / 128) ⊆ f '' ball z s := by
  rcases eq_or_ne (deriv f z) 0 with h0 | h0
  · exact ⟨0, by simp [h0]⟩
  have hfa : AnalyticOnNhd ℂ f (ball z s) := hf.analyticOnNhd isOpen_ball
  have hdc : ContinuousOn (deriv f) (ball z s) := hfa.deriv.continuousOn
  set K := closedBall z (s / 2) with hK
  have hKsub : K ⊆ ball z s := closedBall_subset_ball (by linarith)
  have hKc : IsCompact K := isCompact_closedBall _ _
  let u : ℂ → ℝ := fun w => (s / 2 - dist w z) * ‖deriv f w‖
  have hu : ContinuousOn u K :=
    ((continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn)).mul
      ((hdc.mono hKsub).norm)
  have hzK : z ∈ K := mem_closedBall_self (by linarith)
  obtain ⟨a, haK, hamax⟩ := hKc.exists_isMaxOn ⟨z, hzK⟩ hu
  have hua : u z ≤ u a := hamax hzK
  have huz : u z = s / 2 * ‖deriv f z‖ := by simp [u]
  have huz_pos : 0 < u z := by rw [huz]; positivity
  have hdpos : 0 < s / 2 - dist a z := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (norm_nonneg _)
    linarith
  set d := s / 2 - dist a z with hd
  set A := ‖deriv f a‖ with hA
  have hApos : 0 < A := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := by
      show d * A ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos hdpos.le hcon
    linarith
  set ρ := d / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  -- derivative bound on the closed ball of radius ρ about a
  have hball_sub : closedBall a ρ ⊆ K := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have := dist_triangle w a z
    linarith
  have hderiv_bd : ∀ w ∈ closedBall a ρ, ‖deriv f w‖ ≤ 2 * A := by
    intro w hw
    have hwK := hball_sub hw
    have h1 : u w ≤ u a := hamax hwK
    have hw' : dist w z ≤ dist a z + ρ := by
      have := dist_triangle w a z
      rw [mem_closedBall] at hw
      linarith
    have h2 : ρ ≤ s / 2 - dist w z := by linarith
    have h3 : ρ * ‖deriv f w‖ ≤ u w := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    nlinarith
  -- Schwarz lemma applied to f' - f'(a)
  have hsub_ball : ball a ρ ⊆ ball z s := ball_subset_closedBall.trans (hball_sub.trans hKsub)
  have hschw : ∀ w ∈ ball a ρ, ‖deriv f w - deriv f a‖ ≤ 3 * A / ρ * ‖w - a‖ := by
    intro w hw
    have hd' : DifferentiableOn ℂ (deriv f) (ball a ρ) :=
      (hfa.deriv.differentiableOn).mono hsub_ball
    have hmaps : MapsTo (deriv f) (ball a ρ) (closedBall (deriv f a) (3 * A)) := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm]
      have := hderiv_bd x (ball_subset_closedBall hx)
      calc ‖deriv f x - deriv f a‖ ≤ ‖deriv f x‖ + ‖deriv f a‖ := norm_sub_le _ _
        _ ≤ 3 * A := by rw [← hA]; linarith
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd' hmaps hw
    simpa [dist_eq_norm] using this
  set t := ρ / 8 with ht
  have htpos : 0 < t := by positivity
  have htρ : t < ρ := by linarith
  have hcl_sub : closedBall a t ⊆ ball a ρ := closedBall_subset_ball htρ
  -- k(w) = f w - f a - f'(a) (w - a) is (A/2)-Lipschitz on closedBall a t
  have hk : ∀ w ∈ closedBall a t,
      ‖(f w - deriv f a * w) - (f a - deriv f a * a)‖ ≤ A / 2 * ‖w - a‖ := by
    intro w hw
    have hdiff : ∀ x ∈ closedBall a t, DifferentiableAt ℂ (fun x => f x - deriv f a * x) x := by
      intro x hx
      have : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      exact this.sub ((differentiableAt_id).const_mul _)
    have hbound : ∀ x ∈ closedBall a t, ‖deriv (fun x => f x - deriv f a * x) x‖ ≤ A / 2 := by
      intro x hx
      have hfx : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      have : deriv (fun x => f x - deriv f a * x) x = deriv f x - deriv f a := by
        have := ((hfx.hasDerivAt).sub ((hasDerivAt_id x).const_mul (deriv f a))).deriv
        rw [mul_one] at this
        exact this
      rw [this]
      have h1 := hschw x (hcl_sub hx)
      have h2 : ‖x - a‖ ≤ t := by rw [← dist_eq_norm]; exact hx
      calc ‖deriv f x - deriv f a‖ ≤ 3 * A / ρ * ‖x - a‖ := h1
        _ ≤ 3 * A / ρ * t := by gcongr
        _ ≤ A / 2 := by rw [ht]; field_simp; nlinarith
    exact (convex_closedBall a t).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (mem_closedBall_self htpos.le) hw
  -- lower bound on the sphere
  have hsphere : ∀ w ∈ sphere a t, A * t / 2 ≤ ‖f w - f a‖ := by
    intro w hw
    have hw' : w ∈ closedBall a t := sphere_subset_closedBall hw
    have h1 := hk w hw'
    have h2 : ‖w - a‖ = t := by rw [← dist_eq_norm]; exact hw
    have h3 : ‖deriv f a * (w - a)‖ = A * t := by rw [norm_mul, h2]
    have : f w - f a = deriv f a * (w - a) +
        ((f w - deriv f a * w) - (f a - deriv f a * a)) := by ring
    rw [this]
    have := norm_sub_norm_le (deriv f a * (w - a))
      (-((f w - deriv f a * w) - (f a - deriv f a * a)))
    rw [norm_neg, sub_neg_eq_add] at this
    rw [h2] at h1
    linarith
  have hdcl : DiffContOnCl ℂ f (ball a t) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a htpos.ne']
    exact hf.mono (hcl_sub.trans hsub_ball)
  have hfreq : ∃ᶠ w in 𝓝 a, f w ≠ f a := by
    intro hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεf⟩ := hev
    set r := min ε t / 2 with hr
    have hrpos : 0 < r := by positivity
    have hrε : r < ε := by have := min_le_left ε t; linarith
    have hrt : r ≤ t := by have := min_le_right ε t; linarith
    have hw : dist (a + r) a = r := by simp [abs_of_pos hrpos]
    have hfeq : f (a + r) = f a := not_not.mp (hεf (by rw [hw]; exact hrε))
    have h1 := hk (a + r) (by rw [mem_closedBall, hw]; exact hrt)
    have h2 : ‖(a + r) - a‖ = r := by rw [← dist_eq_norm]; exact hw
    rw [h2, hfeq] at h1
    have : (f a - deriv f a * (a + ↑r)) - (f a - deriv f a * a) = -(deriv f a * r) := by ring
    rw [this, norm_neg, norm_mul] at h1
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] at h1
    rw [← hA] at h1
    nlinarith
  have himg := hdcl.ball_subset_image_closedBall htpos hsphere hfreq
  refine ⟨f a, ?_⟩
  intro v hv
  have hv' : v ∈ ball (f a) (A * t / 2 / 2) := by
    refine mem_of_mem_of_subset hv (ball_subset_ball ?_)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    rw [huz] at hua
    rw [ht]
    nlinarith
  obtain ⟨w, hw, rfl⟩ := himg hv'
  exact ⟨w, hsub_ball (hcl_sub hw), rfl⟩

end SchottkyDev


-- ===== DP_a =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

/-- partner index -/
def pt (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

lemma j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

lemma j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] lemma j0L_apply (u : V n) : j0L u = j0 u := rfl

lemma dot_j0_anti (u v : V n) : dot (j0 u) v = - dot (j0 v) u := by
  rw [eq_neg_iff_add_eq_zero, dot, dot, ← Finset.sum_add_distrib]
  refine Finset.sum_involution (fun k _ => pt k) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro k _
    simp only [pt, j0]
    by_cases hk : (k : ℕ) % 2 = 0
    · have h1 : ((k : ℕ) + 1) % 2 ≠ 0 := by omega
      simp only [hk, h1, ↓reduceIte, ↓reduceDIte]
      have : (⟨(k:ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
        ext; simp
      rw [this]; ring
    · have h1 : ((k : ℕ) - 1) % 2 = 0 := by omega
      simp only [hk, h1, ↓reduceIte, ↓reduceDIte]
      have : (⟨(k:ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
        ext; simp; omega
      rw [this]; ring
  · intro k _ _ h
    simp only [pt] at h; split_ifs at h with hk <;> simp only [Fin.ext_iff] at h <;> omega
  · intro k _
    by_cases hk : (k : ℕ) % 2 = 0
    · have h1 : ((k : ℕ) + 1) % 2 ≠ 0 := by omega
      simp only [pt, hk, h1, ↓reduceDIte, Fin.ext_iff]; omega
    · have h1 : ((k : ℕ) - 1) % 2 = 0 := by omega
      simp only [pt, hk, h1, ↓reduceDIte, Fin.ext_iff]; omega

lemma omega0_anti (u v : V n) : omega0 u v = - omega0 v u := dot_j0_anti u v

lemma omega0_self (u : V n) : omega0 u u = 0 := by
  have := omega0_anti u u; linarith

lemma omega0_add_left (u u' v : V n) : omega0 (u + u') v = omega0 u v + omega0 u' v := by
  simp [omega0, dot, j0_add, add_mul, Finset.sum_add_distrib]

lemma omega0_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  simp [omega0, dot, j0_smul, Finset.mul_sum, mul_assoc]

lemma omega0_add_right (u v v' : V n) : omega0 u (v + v') = omega0 u v + omega0 u v' := by
  simp [omega0, dot, mul_add, Finset.sum_add_distrib]

lemma omega0_smul_right (c : ℝ) (u v : V n) : omega0 u (c • v) = c * omega0 u v := by
  simp [omega0, dot, Finset.mul_sum]; congr 1; funext k; ring

lemma omega0_sub_right (u v v' : V n) : omega0 u (v - v') = omega0 u v - omega0 u v' := by
  rw [sub_eq_add_neg, omega0_add_right, show -v' = (-1:ℝ) • v' by simp, omega0_smul_right]; ring

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot]
  ring

lemma scaleToS_pos (H : V n → ℝ) (y : V n) : 0 < scaleToS H y := by
  unfold scaleToS; split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

lemma proj_eq (H : V n → ℝ) (y : V n) : proj H y = scaleToS H y • y := rfl

lemma exp_aCoord (H : V n → ℝ) (y : V n) : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
  rw [aCoord, show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
    Real.exp_neg, Real.exp_log (scaleToS_pos H y)]

end DP


-- ===== DP_b =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

/-- Algebra of `J̃` at `y ≠ 0` with `x = proj y ∈ S`. -/
lemma jtilde_AL (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y : V n)
    (hx : H (proj H y) = 1) (v : V n) :
    fderiv ℝ H (proj H y) (Jtilde H J y v) =
        -(scaleToS H y * liouvilleCLM (proj H y) v) * (2 * fderiv ℝ H (proj H y) y) ∧
      liouvilleCLM (proj H y) (Jtilde H J y v) =
        (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) *
          (scaleToS H y)⁻¹ := by
  set x := proj H y with hxdef
  set r := scaleToS H y with hrdef
  have hr : 0 < r := scaleToS_pos H y
  have hxS : x ∈ energySurface H := hx
  obtain ⟨-, hLR, hAR, -⟩ := reeb_spec H hH x hxS
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hyx : y = r⁻¹ • x := by rw [hxdef, proj_eq, ← hrdef, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hLy : liouvilleCLM x y = 0 := by
    rw [liouvilleCLM_apply, liouville, hyx, omega0_smul_right, omega0_self]; simp
  have hAy : fderiv ℝ H x y = r⁻¹ * fderiv ℝ H x x := by rw [hyx, map_smul, smul_eq_mul]
  set α : ℝ := r / (2 * (fderiv ℝ H x) x) * (fderiv ℝ H x) v
  set β : ℝ := r * (liouvilleCLM x) v
  set ζ : V n := v - α • ((2:ℝ) • y) - β • (r⁻¹ • reeb H x)
  have hLR' : (liouvilleCLM x) (reeb H x) = 1 := by rw [liouvilleCLM_apply]; exact hLR
  have hζ : IsInXi H x ζ := by
    constructor
    · rw [← liouvilleCLM_apply]
      simp only [ζ, map_sub, map_smul, smul_eq_mul, hLy, hLR']
      field_simp; ring
    · simp only [ζ, map_sub, map_smul, smul_eq_mul, hAR, hAy, α]
      field_simp; ring
  have hJζ := (hJ.2 x hxS ζ ζ hζ hζ).1
  have hJt : Jtilde H J y v = α • (r⁻¹ • reeb H x) - β • ((2:ℝ) • y) + J x ζ := by
    simp only [Jtilde, ← hxdef, ← hrdef, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  have hLJ : (liouvilleCLM x) (J x ζ) = 0 := by rw [liouvilleCLM_apply]; exact hJζ.1
  constructor
  · rw [hJt]; simp only [map_add, map_sub, map_smul, smul_eq_mul, hAR, hJζ.2, β, hAy]; ring
  · rw [hJt]; simp only [map_add, map_sub, map_smul, smul_eq_mul, hLR', hLy, hLJ, α]; ring

end DP


-- ===== DP_c =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

lemma smooth_aw (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) :
    ContDiff ℝ ∞ (fun z => aCoord H (u z)) ∧ ContDiff ℝ ∞ (fun z => proj H (u z)) := by
  obtain ⟨-, hP, hAc, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  exact ⟨hAc.comp_contDiff hsm hu0, hP.comp_contDiff hsm hu0⟩

lemma fderiv_u (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (z v : ℂ) :
    fderiv ℝ u z v = (Real.exp (2 * aCoord H (u z)) * (2 * fderiv ℝ (fun z => aCoord H (u z)) z v)) •
        proj H (u z) + Real.exp (2 * aCoord H (u z)) • fderiv ℝ (fun z => proj H (u z)) z v := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ u hsm hu0
  have hueq : u = fun z => Real.exp (2 * aCoord H (u z)) • proj H (u z) :=
    funext fun z => (hrel _ (hu0 z)).2
  have hA := (ha.differentiable (by simp) z).hasFDerivAt
  have hW := (hw.differentiable (by simp) z).hasFDerivAt
  have hE := (hA.const_mul 2).exp
  have hD := hE.smul hW
  have hD' : HasFDerivAt u _ z :=
    hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => congrFun hueq w)
  rw [hD'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

lemma dH_w (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (z v : ℂ) :
    fderiv ℝ H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z v) = 0 := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ u hsm hu0
  have hW := (hw.differentiable (by simp) z).hasFDerivAt
  have hc := (hH.1.differentiable (by simp) (proj H (u z))).hasFDerivAt.comp z hW
  have hconst : (fun z => H (proj H (u z))) = fun _ => (1:ℝ) := funext fun z => (hrel _ (hu0 z)).1
  have h2 : HasFDerivAt (fun z => H (proj H (u z))) (0 : ℂ →L[ℝ] ℝ) z := by
    rw [hconst]; exact hasFDerivAt_const _ _
  have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hc.unique h2)
  simpa using this

theorem cr_rel (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) univ u) (z : ℂ) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
      dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z (mem_univ z)).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z)).2
  obtain ⟨hJA, hJL⟩ := jtilde_AL H hH J hJ (u z) hx (fderiv ℝ u z Complex.I)
  have hfu := fderiv_u H hH J hJ u hsm hu0 z
  have hAw := dH_w H hH J hJ u hsm hu0 z
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hre : r * e = 1 := by rw [he, exp_aCoord, ← hr, mul_inv_cancel₀ (scaleToS_pos H y).ne']
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hAy : fderiv ℝ H x y = e * fderiv ℝ H x x := by
    conv_lhs => rw [hyeq]
    rw [map_smul, smul_eq_mul]
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  have e1 := congrArg (fderiv ℝ H x) hdb
  have e2 := congrArg (liouvilleCLM x) hdb
  rw [map_add, hJA, map_zero] at e1
  rw [map_add, hJL, map_zero] at e2
  rw [hfu 1, hfu Complex.I] at e1 e2
  simp only [map_add, map_smul, smul_eq_mul, hLx, hAw, hAy] at e1 e2
  simp only [ds, dt, ← liouvilleCLM_apply]
  change as = (liouvilleCLM x) wt ∧ at' = -(liouvilleCLM x) ws
  have hAx' := hAx.ne'
  constructor
  · have : 2 * e * fderiv ℝ H x x * (as - r * e * liouvilleCLM x wt) = 0 := by linear_combination e1
    rw [hre, one_mul] at this
    have h3 : 2 * e * fderiv ℝ H x x ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp this).resolve_left h3]
  · have k : r / (2 * fderiv ℝ H x x) * (e * (2 * at') * fderiv ℝ H x x + e * 0) * r⁻¹ = e * at' := by
      field_simp; ring
    have : e * (liouvilleCLM x ws + at') = 0 := by
      have := e2; simp only [mul_zero, zero_add, add_zero] at this k ⊢; linear_combination this - k
    linarith [(mul_eq_zero.mp this).resolve_left hepos.ne']

end DP


-- ===== DP_d =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

noncomputable def omB : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V n) (F' := ℝ)).toLinearMap.comp
      (LinearMap.mk₂ ℝ omega0 omega0_add_left (fun c u v => by rw [omega0_smul_left]; rfl)
        omega0_add_right (fun c u v => by rw [omega0_smul_right]; rfl)))

@[simp] lemma omB_apply (p q : V n) : omB p q = omega0 p q := rfl

lemma fderiv_omega0 {f g : ℂ → V n} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    fderiv ℝ (fun z => omega0 (f z) (g z)) z v =
      omega0 (fderiv ℝ f z v) (g z) + omega0 (f z) (fderiv ℝ g z v) := by
  have h := omB.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt
  simp only [omB_apply] at h
  rw [h.fderiv]
  simp [add_comm]

lemma diff_om {f g : ℂ → V n} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : DifferentiableAt ℝ (fun z => omega0 (f z) (g z)) z := by
  have h := omB.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt
  simp only [omB_apply] at h
  exact h.differentiableAt

/-- derivative of `z ↦ fderiv f z c` -/
lemma fderiv_dir {f : ℂ → V n} (hf : ContDiff ℝ ∞ f) (c v z : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma fderiv_dir_real {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c v z : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma symm2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v :=
  (hf.contDiffAt.isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)) v w

/-- `g = ∂ₛa - i ∂ₜa` is holomorphic when `a` is harmonic. -/
theorem g_differentiable (a : ℂ → ℝ) (w : ℂ → V n) (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hcr : ∀ z, ds a z = liouville (w z) (dt w z) ∧ dt a z = -liouville (w z) (ds w z))
    (hd : ∀ z, omega0 (ds w z) (dt w z) = 0) :
    Differentiable ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) := by
  intro z
  have hP : (fun z => fderiv ℝ a z 1) = fun z => (1/2:ℝ) * omega0 (w z) (fderiv ℝ w z Complex.I) :=
    funext fun z => by rw [show fderiv ℝ a z 1 = ds a z from rfl, (hcr z).1, liouville, dt]; ring
  have hQ : (fun z => fderiv ℝ a z Complex.I) = fun z => (-1/2:ℝ) * omega0 (w z) (fderiv ℝ w z 1) :=
    funext fun z => by rw [show fderiv ℝ a z Complex.I = dt a z from rfl, (hcr z).2, liouville, ds]; ring
  have hwd : ∀ c : ℂ, Differentiable ℝ (fun z => fderiv ℝ w z c) := fun c =>
    ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hwz : DifferentiableAt ℝ w z := hw.differentiable (by simp) z
  -- Laplacian
  have hlap : fderiv ℝ (fderiv ℝ a) z 1 1 + fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I = 0 := by
    rw [← fderiv_dir_real ha, ← fderiv_dir_real ha, hP, hQ]
    rw [fderiv_const_mul (diff_om hwz (hwd _ z)), fderiv_const_mul (diff_om hwz (hwd _ z))]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_omega0 hwz (hwd _ z), fderiv_omega0 hwz (hwd _ z), fderiv_dir hw, fderiv_dir hw,
      symm2 hw z 1 Complex.I, omega0_anti (fderiv ℝ w z Complex.I)]
    have := hd z; simp only [ds, dt] at this
    linear_combination this
  have had : ∀ c : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ a z c) z := fun c =>
    (((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) z
  have h1 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z 1)).comp z (had 1).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z Complex.I)).comp z
    (had Complex.I).hasFDerivAt
  have hg := h1.sub (h2.const_mul Complex.I)
  set D := Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z 1) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z Complex.I) z) with hD
  have hB : D Complex.I = Complex.I • D 1 := by
    simp only [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rw [fderiv_dir_real ha, fderiv_dir_real ha, fderiv_dir_real ha, fderiv_dir_real ha,
      symm2 ha z Complex.I 1]
    have hl : (fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I : ℂ) =
        -(fderiv ℝ (fderiv ℝ a) z 1 1 : ℂ) := by
      rw [← Complex.ofReal_neg]; congr 1; linarith
    rw [hl]
    ring_nf; rw [Complex.I_sq]; ring
  let D' : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  refine (hasFDerivAt_of_restrictScalars ℝ (g' := D) (f' := D') hg ?_).differentiableAt
  ext v
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  simp only [D', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]
  calc v • D 1 = ((v.re:ℂ) + v.im * Complex.I) • D 1 := by rw [Complex.re_add_im]
   _ = v.re • D 1 + v.im • (Complex.I • D 1) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
   _ = D v := by rw [← hB, ← map_smul, ← map_smul, ← map_add, ← hv]

end DP


-- ===== DP_e =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

lemma det_mul (c : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ).det = Complex.normSq c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have e : (((1 : ℂ →L[ℂ] ℂ).smulRight c : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) = c • LinearMap.id := by
    ext; simp
  rw [e, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]; simp

lemma vol_rect (x0 y0 h k : ℝ) (hk : 0 ≤ k) (hh : 0 ≤ h) :
    volume (Complex.measurableEquivRealProd ⁻¹' (Ioo (x0 - h) (x0 + h) ×ˢ Ioo (y0 - k) (y0 + k))) =
      ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * k) := by
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  congr 2 <;> ring

noncomputable def phiC (m : ℝ) (t : ℝ) : ℝ := Real.arctan (t - m) / Real.pi + 1 / 2

lemma phiC_adm (m : ℝ) : Admissible (phiC m) := by
  refine ⟨?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · unfold phiC
    exact ((Real.contDiff_arctan.comp (contDiff_id.sub contDiff_const)).div_const _).add contDiff_const
  · intro s t hst
    unfold phiC
    have := Real.arctan_strictMono.monotone (sub_le_sub_right hst m)
    gcongr
  · unfold phiC
    have := Real.neg_pi_div_two_lt_arctan (t - m)
    have hp := Real.pi_pos
    rw [div_add' _ _ _ hp.ne']; apply div_nonneg _ hp.le; linarith
  · unfold phiC
    have := Real.arctan_lt_pi_div_two (t - m)
    have hp := Real.pi_pos
    rw [div_add' _ _ _ hp.ne', div_le_one hp]; linarith

lemma deriv_phiC (m t : ℝ) : deriv (phiC m) t = 1 / (1 + (t - m) ^ 2) / Real.pi := by
  have h := ((((hasDerivAt_id' t).sub_const m).arctan).div_const Real.pi).add_const (1/2 : ℝ)
  unfold phiC
  rw [h.deriv]; simp

lemma deriv_phiC_ge (m t : ℝ) (h : |t - m| < 1) : 1 / (2 * Real.pi) ≤ deriv (phiC m) t := by
  rw [deriv_phiC]
  have hp := Real.pi_pos
  have h2 : (t - m) ^ 2 ≤ 1 := by
    have := sq_abs (t - m); nlinarith [abs_nonneg (t - m)]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end DP


-- ===== DP_f =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DP

theorem grad_zero (a : ℂ → ℝ) (ha : ContDiff ℝ ∞ a)
    (hg : Differentiable ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)))
    (E : ℝ≥0∞) (hE : E < ⊤)
    (hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z, ENNReal.ofReal (deriv φ (a z) * ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ E)
    (z : ℂ) : fderiv ℝ a z 1 = 0 ∧ fderiv ℝ a z Complex.I = 0 := by
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  have hgre : ∀ z, (g z).re = fderiv ℝ a z 1 := fun z => by simp [g]
  have hgim : ∀ z, (g z).im = -fderiv ℝ a z Complex.I := fun z => by simp [g]
  have hN : ∀ z, Complex.normSq (g z) = (fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2 := by
    intro z; rw [Complex.normSq_apply, hgre, hgim]; ring
  obtain ⟨F, hF⟩ := hg.isExactOn_univ
  have hF' : ∀ z, HasDerivAt F (g z) z := fun z => hF z (mem_univ z)
  have hFd : Differentiable ℂ F := fun z => (hF' z).differentiableAt
  -- Re F - a is constant
  have hRe : ∀ z, HasFDerivAt (fun z => (F z).re - a z) (0 : ℂ →L[ℝ] ℝ) z := by
    intro z
    have h1 := Complex.reCLM.hasFDerivAt.comp z ((hF' z).hasFDerivAt.restrictScalars ℝ)
    have h2 := (ha.differentiable (by simp) z).hasFDerivAt
    refine (h1.sub h2).congr_fderiv ?_
    ext v
    have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
    have hav : fderiv ℝ a z v = v.re * fderiv ℝ a z 1 + v.im * fderiv ℝ a z Complex.I := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply, hav, smul_eq_mul,
      Complex.mul_re, hgre, hgim]
    ring
  have hconst := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun z => (hRe z).differentiableAt)
    (fun z => (hRe z).fderiv)
  set c := (F 0).re - a 0
  have hreF : ∀ z, (F z).re = a z + c := fun z => by have := hconst z 0; linarith
  by_contra hne
  have hg0 : g z ≠ 0 := by
    intro h; apply hne
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    rw [hgre] at h1; rw [hgim] at h2; simp at h1 h2; exact ⟨h1, h2⟩
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr hg0
  set K := E.toReal
  have hEK : E = ENNReal.ofReal K := (ENNReal.ofReal_toReal hE.ne).symm
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  set ρ : ℝ := K * Real.pi / 2 + 2 with hρ
  set s : ℝ := 128 * ρ / ‖g z‖ with hs
  have hρpos : 0 < ρ := by positivity
  have hρ2 : 2 ≤ ρ := by rw [hρ]; have := Real.pi_pos; nlinarith
  have hspos : 0 < s := by positivity
  obtain ⟨b, hb⟩ := SchottkyDev.bloch F z s hspos hFd.differentiableOn
  rw [(hF' z).deriv, show s * ‖g z‖ / 128 = ρ by rw [hs]; field_simp] at hb
  set m := b.re - c
  have hφ := phiC_adm m
  set S := ball z s ∩ {z | |(F z).re - b.re| < 1} with hSdef
  have hSo : IsOpen S := isOpen_ball.inter
    (isOpen_lt ((Complex.continuous_re.comp hFd.continuous).sub continuous_const).abs continuous_const)
  -- rectangle
  set Rect := Complex.measurableEquivRealProd ⁻¹'
    (Ioo (b.re - 1) (b.re + 1) ×ˢ Ioo (b.im - (ρ - 1)) (b.im + (ρ - 1))) with hRect
  have hRS : Rect ⊆ F '' S := by
    intro v hv
    simp only [hRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo] at hv
    have hvb : v ∈ ball b ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖v - b‖ ≤ |(v - b).re| + |(v - b).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + (ρ - 1) := by
          simp only [Complex.sub_re, Complex.sub_im]
          gcongr <;> rw [abs_lt] <;> constructor <;> linarith
        _ = ρ := by ring
    obtain ⟨x, hx, hxv⟩ := hb hvb
    refine ⟨x, ⟨hx, ?_⟩, hxv⟩
    simp only [mem_setOf_eq, hxv]; rw [abs_lt]; constructor <;> linarith
  have hvol : ENNReal.ofReal (2 * 1) * ENNReal.ofReal (2 * (ρ - 1)) ≤
      ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| := by
    rw [← vol_rect b.re b.im 1 (ρ - 1) (by linarith) zero_le_one]
    refine (measure_mono hRS).trans ?_
    refine addHaar_image_le_lintegral_abs_det_fderiv volume hSo.measurableSet fun x _ => ?_
    exact ((hF' x).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hpt : ∀ x ∈ S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
        ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := by
    intro x hx
    rw [det_mul, abs_of_nonneg (Complex.normSq_nonneg _), hN, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |a x - m| < 1 := by
      have := hx.2; simp only [mem_setOf_eq, hreF] at this
      have e : a x - m = a x + c - b.re := by simp only [m]; ring
      rw [e]; exact this
    have h2 := deriv_phiC_ge m (a x) h1
    have hp := Real.pi_pos
    have h3 : 1 ≤ 2 * Real.pi * deriv (phiC m) (a x) := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    have h4 : 0 ≤ (fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2 := by positivity
    nlinarith
  have hint : ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * E := by
    calc _ ≤ ∫⁻ x in S, ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          setLIntegral_mono' hSo.measurableSet hpt
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x in S, ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact (setLIntegral_le_lintegral _ _).trans (hbound _ hφ)
  have key := hvol.trans hint
  rw [hEK, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hp := Real.pi_pos
  rw [hρ] at key
  nlinarith

end DP


-- ===== DQ_c =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

/-! Local (open set `U`) versions of the DP_c / DP_d lemmas. -/

namespace DQ

open DP

variable {n : ℕ}

lemma smooth_aw (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (u : ℂ → V n)
    (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) U ∧ ContDiffOn ℝ ∞ (fun z => proj H (u z)) U := by
  obtain ⟨-, hP, hAc, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  exact ⟨hAc.comp hsm hu0, hP.comp hsm hu0⟩

lemma fderiv_u (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) (z : ℂ) (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ u z v = (Real.exp (2 * aCoord H (u z)) * (2 * fderiv ℝ (fun z => aCoord H (u z)) z v)) •
        proj H (u z) + Real.exp (2 * aCoord H (u z)) • fderiv ℝ (fun z => proj H (u z)) z v := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hA := ((ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hW := ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hE := (hA.const_mul 2).exp
  have hD := hE.smul hW
  have hD' : HasFDerivAt u _ z :=
    hD.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => (hrel _ (hu0 w hw)).2)
  rw [hD'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

lemma dH_w (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) (z : ℂ) (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z v) = 0 := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hW := ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hH.1.differentiable (by simp) (proj H (u z))).hasFDerivAt.comp z hW
  have h2 : HasFDerivAt (fun z => H (proj H (u z))) (0 : ℂ →L[ℝ] ℝ) z :=
    (hasFDerivAt_const (1:ℝ) z).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => (hrel _ (hu0 w hw)).1)
  have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hc.unique h2)
  simpa using this

theorem cr_rel (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z : ℂ) (hz : z ∈ U) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
      dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z hz).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z hz)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z hz)).2
  obtain ⟨hJA, hJL⟩ := jtilde_AL H hH J hJ (u z) hx (fderiv ℝ u z Complex.I)
  have hfu := fderiv_u H hH J hJ U hU u hsm hu0 z hz
  have hAw := dH_w H hH J hJ U hU u hsm hu0 z hz
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hre : r * e = 1 := by rw [he, exp_aCoord, ← hr, mul_inv_cancel₀ (scaleToS_pos H y).ne']
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hAy : fderiv ℝ H x y = e * fderiv ℝ H x x := by
    conv_lhs => rw [hyeq]
    rw [map_smul, smul_eq_mul]
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  have e1 := congrArg (fderiv ℝ H x) hdb
  have e2 := congrArg (liouvilleCLM x) hdb
  rw [map_add, hJA, map_zero] at e1
  rw [map_add, hJL, map_zero] at e2
  rw [hfu 1, hfu Complex.I] at e1 e2
  simp only [map_add, map_smul, smul_eq_mul, hLx, hAw, hAy] at e1 e2
  simp only [ds, dt, ← liouvilleCLM_apply]
  change as = (liouvilleCLM x) wt ∧ at' = -(liouvilleCLM x) ws
  have hAx' := hAx.ne'
  constructor
  · have : 2 * e * fderiv ℝ H x x * (as - r * e * liouvilleCLM x wt) = 0 := by linear_combination e1
    rw [hre, one_mul] at this
    have h3 : 2 * e * fderiv ℝ H x x ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp this).resolve_left h3]
  · have k : r / (2 * fderiv ℝ H x x) * (e * (2 * at') * fderiv ℝ H x x + e * 0) * r⁻¹ = e * at' := by
      field_simp; ring
    have : e * (liouvilleCLM x ws + at') = 0 := by
      have := e2; simp only [mul_zero, zero_add, add_zero] at this k ⊢; linear_combination this - k
    linarith [(mul_eq_zero.mp this).resolve_left hepos.ne']

end DQ


-- ===== DQ_d =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DQ

open DP

variable {n : ℕ}

lemma fderiv_dir_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (c v : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma diff_dir_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (c : ℂ) : DifferentiableAt ℝ (fun z => fderiv ℝ f z c) z :=
  ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)

lemma symm2_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v :=
  (hf.isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)) v w

theorem g_differentiableOn (U : Set ℂ) (hU : IsOpen U) (a : ℂ → ℝ) (w : ℂ → V n)
    (ha : ContDiffOn ℝ ∞ a U) (hw : ContDiffOn ℝ ∞ w U)
    (hcr : ∀ z ∈ U, ds a z = liouville (w z) (dt w z) ∧ dt a z = -liouville (w z) (ds w z))
    (hd : ∀ z ∈ U, omega0 (ds w z) (dt w z) = 0) :
    DifferentiableOn ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) U := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hza := ha.contDiffAt (hU.mem_nhds hz)
  have hzw := hw.contDiffAt (hU.mem_nhds hz)
  have hP : (fun z => fderiv ℝ a z 1) =ᶠ[𝓝 z]
      fun z => (1/2:ℝ) * omega0 (w z) (fderiv ℝ w z Complex.I) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun z hz => by
      show fderiv ℝ a z 1 = _
      rw [show fderiv ℝ a z 1 = ds a z from rfl, (hcr z hz).1, liouville, dt]; ring
  have hQ : (fun z => fderiv ℝ a z Complex.I) =ᶠ[𝓝 z]
      fun z => (-1/2:ℝ) * omega0 (w z) (fderiv ℝ w z 1) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun z hz => by
      show fderiv ℝ a z Complex.I = _
      rw [show fderiv ℝ a z Complex.I = dt a z from rfl, (hcr z hz).2, liouville, ds]; ring
  have hwz : DifferentiableAt ℝ w z := hzw.differentiableAt (by simp)
  have hlap : fderiv ℝ (fderiv ℝ a) z 1 1 + fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I = 0 := by
    rw [← fderiv_dir_at hza, ← fderiv_dir_at hza, hP.fderiv_eq, hQ.fderiv_eq]
    rw [fderiv_const_mul (diff_om hwz (diff_dir_at hzw _)),
      fderiv_const_mul (diff_om hwz (diff_dir_at hzw _))]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_omega0 hwz (diff_dir_at hzw _), fderiv_omega0 hwz (diff_dir_at hzw _),
      fderiv_dir_at hzw, fderiv_dir_at hzw, symm2_at hzw 1 Complex.I,
      omega0_anti (fderiv ℝ w z Complex.I)]
    have := hd z hz; simp only [ds, dt] at this
    linear_combination this
  have h1 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z 1)).comp z (diff_dir_at hza 1).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z Complex.I)).comp z
    (diff_dir_at hza Complex.I).hasFDerivAt
  have hg := h1.sub (h2.const_mul Complex.I)
  set D := Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z 1) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z Complex.I) z) with hD
  have hB : D Complex.I = Complex.I • D 1 := by
    simp only [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rw [fderiv_dir_at hza, fderiv_dir_at hza, fderiv_dir_at hza, fderiv_dir_at hza,
      symm2_at hza Complex.I 1]
    have hl : (fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I : ℂ) =
        -(fderiv ℝ (fderiv ℝ a) z 1 1 : ℂ) := by
      rw [← Complex.ofReal_neg]; congr 1; linarith
    rw [hl]
    ring_nf; rw [Complex.I_sq]; ring
  let D' : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  refine (hasFDerivAt_of_restrictScalars ℝ (g' := D) (f' := D') hg ?_).differentiableAt
  ext v
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  simp only [D', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]
  calc v • D 1 = ((v.re:ℂ) + v.im * Complex.I) • D 1 := by rw [Complex.re_add_im]
   _ = v.re • D 1 + v.im • (Complex.I • D 1) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
   _ = D v := by rw [← hB, ← map_smul, ← map_smul, ← map_add, ← hv]

end DQ


-- ===== DQ_f =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

/-- Local Bloch–energy bound: on a ball inside `U`, `s |g(z₀)| / 128 ≤ K π / 2 + 1`. -/
theorem grad_bound (U : Set ℂ) (hU : IsOpen U) (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a U)
    (hg : DifferentiableOn ℂ
      (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) U)
    (E : ℝ≥0∞) (hE : E < ⊤)
    (hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) * ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ E)
    (z : ℂ) (s : ℝ) (hspos : 0 < s) (hsub : ball z s ⊆ U) :
    s * ‖(fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)‖ / 128 ≤
      E.toReal * Real.pi / 2 + 1 := by
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  change s * ‖g z‖ / 128 ≤ _
  have hgre : ∀ z, (g z).re = fderiv ℝ a z 1 := fun z => by simp [g]
  have hgim : ∀ z, (g z).im = -fderiv ℝ a z Complex.I := fun z => by simp [g]
  have hN : ∀ z, Complex.normSq (g z) = (fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2 := by
    intro z; rw [Complex.normSq_apply, hgre, hgim]; ring
  obtain ⟨F, hF'⟩ := (hg.mono hsub).isExactOn_ball
  have hFd : DifferentiableOn ℂ F (ball z s) := fun x hx => (hF' x hx).differentiableAt.differentiableWithinAt
  have hRe : ∀ x ∈ ball z s, HasFDerivAt (fun z => (F z).re - a z) (0 : ℂ →L[ℝ] ℝ) x := by
    intro x hx
    have h1 := Complex.reCLM.hasFDerivAt.comp x ((hF' x hx).hasFDerivAt.restrictScalars ℝ)
    have h2 := ((ha.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by simp)).hasFDerivAt
    refine (h1.sub h2).congr_fderiv ?_
    ext v
    have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
    have hav : fderiv ℝ a x v = v.re * fderiv ℝ a x 1 + v.im * fderiv ℝ a x Complex.I := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply, hav, smul_eq_mul,
      Complex.mul_re, hgre, hgim]
    ring
  set c := (F z).re - a z
  have hreF : ∀ x ∈ ball z s, (F x).re = a x + c := fun x hx => by
    have := isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (convex_ball z s).isPreconnected
      (fun y hy => (hRe y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hRe y hy).fderiv) hx (mem_ball_self hspos)
    linarith
  by_contra hne
  rw [not_le] at hne
  set K := E.toReal
  have hEK : E = ENNReal.ofReal K := (ENNReal.ofReal_toReal hE.ne).symm
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  set ρ : ℝ := s * ‖g z‖ / 128 with hρ
  have hρ2 : 1 ≤ ρ := by have := Real.pi_pos; nlinarith
  obtain ⟨b, hb⟩ := SchottkyDev.bloch F z s hspos hFd
  rw [(hF' z (mem_ball_self hspos)).deriv] at hb
  set m := b.re - c
  have hφ := phiC_adm m
  set S := ball z s ∩ F ⁻¹' {w | |w.re - b.re| < 1} with hSdef
  have hSo : IsOpen S := hFd.continuousOn.isOpen_inter_preimage isOpen_ball
    (isOpen_lt (Complex.continuous_re.sub continuous_const).abs continuous_const)
  set Rect := Complex.measurableEquivRealProd ⁻¹'
    (Ioo (b.re - 1) (b.re + 1) ×ˢ Ioo (b.im - (ρ - 1)) (b.im + (ρ - 1))) with hRect
  have hRS : Rect ⊆ F '' S := by
    intro v hv
    simp only [hRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo] at hv
    have hvb : v ∈ ball b ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖v - b‖ ≤ |(v - b).re| + |(v - b).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + (ρ - 1) := by
          simp only [Complex.sub_re, Complex.sub_im]
          gcongr <;> rw [abs_lt] <;> constructor <;> linarith
        _ = ρ := by ring
    obtain ⟨x, hx, hxv⟩ := hb hvb
    refine ⟨x, ⟨hx, ?_⟩, hxv⟩
    simp only [mem_preimage, mem_setOf_eq, hxv]; rw [abs_lt]; constructor <;> linarith
  have hvol : ENNReal.ofReal (2 * 1) * ENNReal.ofReal (2 * (ρ - 1)) ≤
      ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| := by
    rw [← vol_rect b.re b.im 1 (ρ - 1) (by linarith) zero_le_one]
    refine (measure_mono hRS).trans ?_
    refine addHaar_image_le_lintegral_abs_det_fderiv volume hSo.measurableSet fun x hx => ?_
    exact ((hF' x hx.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hpt : ∀ x ∈ S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
        ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := by
    intro x hx
    rw [det_mul, abs_of_nonneg (Complex.normSq_nonneg _), hN, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |a x - m| < 1 := by
      have := hx.2; simp only [mem_preimage, mem_setOf_eq, hreF x hx.1] at this
      have e : a x - m = a x + c - b.re := by simp only [m]; ring
      rw [e]; exact this
    have h2 := deriv_phiC_ge m (a x) h1
    have hp := Real.pi_pos
    have h3 : 1 ≤ 2 * Real.pi * deriv (phiC m) (a x) := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    have h4 : 0 ≤ (fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2 := by positivity
    nlinarith
  have hSU : S ⊆ U := fun x hx => hsub hx.1
  have hint : ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * E := by
    calc _ ≤ ∫⁻ x in S, ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          setLIntegral_mono' hSo.measurableSet hpt
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x in S, ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact (lintegral_mono_set hSU).trans (hbound _ hφ)
  have key := hvol.trans hint
  rw [hEK, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hp := Real.pi_pos
  nlinarith

end DQ


-- ===== DQ_g =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

variable {n : ℕ}

/-- (A) vanishing `dλ`-energy on an open set forces the `dλ`-density to vanish pointwise. -/
theorem dens_zero (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (h0 : dlambdaEnergy H U u = 0) :
    ∀ z ∈ U, omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z) = 0 := by
  have hu' := hu
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨-, hnn2, -, -⟩ := energyDensity_nonneg H hH J hJ U hU u hu'
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hwd : ∀ c : ℂ, ContinuousOn (fun z => fderiv ℝ (fun z => proj H (u z)) z c) U := fun c =>
    (hw.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hcont : ContinuousOn (fun z => dlambdaDensity H u z) U := by
    have h2 : ContinuousOn (fun z => omB (fderiv ℝ (fun z => proj H (u z)) z 1)
        (fderiv ℝ (fun z => proj H (u z)) z Complex.I)) U :=
      (omB.continuous.comp_continuousOn (hwd 1)).clm_apply (hwd Complex.I)
    exact h2
  have hc2 : ContinuousOn (fun z => ENNReal.ofReal (dlambdaDensity H u z)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hae : (fun z => ENNReal.ofReal (dlambdaDensity H u z)) =ᵐ[volume.restrict U] 0 :=
    (lintegral_eq_zero_iff' (hc2.aemeasurable hU.measurableSet)).mp h0
  have heq := Measure.eqOn_open_of_ae_eq hae hU hc2 continuousOn_const
  intro z hz
  have h1 : ENNReal.ofReal (dlambdaDensity H u z) = 0 := heq hz
  rw [ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (hnn2 z hz)

lemma jt_unfold (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (y v : V n) :
    Jtilde H J y v =
      (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) •
          ((scaleToS H y)⁻¹ • reeb H (proj H y)) -
        (scaleToS H y * liouvilleCLM (proj H y) v) • ((2:ℝ) • y) +
        J (proj H y) (v - (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) *
            fderiv ℝ H (proj H y) v) • ((2:ℝ) • y) -
          (scaleToS H y * liouvilleCLM (proj H y) v) • ((scaleToS H y)⁻¹ • reeb H (proj H y))) := by
  simp only [Jtilde, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- (C) the `ξ`-component: with vanishing `dλ`-density, `∂ₛw = -∂ₜa R(w)` and `∂ₜw = ∂ₛa R(w)`. -/
theorem xi_part (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z : ℂ) (hz : z ∈ U)
    (hd : omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z) = 0) :
    ds (fun z => proj H (u z)) z = -(dt (fun z => aCoord H (u z)) z) • reeb H (proj H (u z)) ∧
      dt (fun z => proj H (u z)) z = (ds (fun z => aCoord H (u z)) z) • reeb H (proj H (u z)) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z hz).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z hz)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z hz)).2
  have hfu := fderiv_u H hH J hJ U hU u hsm hu0 z hz
  have hAw := dH_w H hH J hJ U hU u hsm hu0 z hz
  obtain ⟨hcr1, hcr2⟩ := cr_rel H hH J hJ U hU u hsm hu0 hhol z hz
  rw [jt_unfold] at hdb
  rw [hfu 1, hfu Complex.I] at hdb
  have hAwI := hAw Complex.I
  have hAw1 := hAw 1
  simp only [ds, dt] at hcr1 hcr2 hd ⊢
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hre : r⁻¹ = e := by rw [he, exp_aCoord]
  have hxS : x ∈ energySurface H := hx
  obtain ⟨-, hLR, hAR, hωR⟩ := reeb_spec H hH x hxS
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hLR' : liouvilleCLM x (reeb H x) = 1 := by rw [liouvilleCLM_apply]; exact hLR
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  set R := reeb H x
  set ζs := ws - liouvilleCLM x ws • R with hζs
  set ζt := wt - liouvilleCLM x wt • R with hζt
  have hxis : ∀ v, fderiv ℝ H x v = 0 → IsInXi H x (v - liouvilleCLM x v • R) := by
    intro v hv
    constructor
    · rw [← liouvilleCLM_apply]; simp only [map_sub, map_smul, smul_eq_mul, hLR']; ring
    · simp only [map_sub, map_smul, smul_eq_mul, hAR, hv]; ring
  have hXt : IsInXi H x ζt := hxis wt hAwI
  have hXs : IsInXi H x ζs := hxis ws hAw1
  have hα : r / (2 * fderiv ℝ H x x) * fderiv ℝ H x ((e * (2 * at')) • x + e • wt) = at' := by
    rw [map_add, map_smul, map_smul, hAwI, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
      ← hre]
    field_simp
  have hβ : r * liouvilleCLM x ((e * (2 * at')) • x + e • wt) = liouvilleCLM x wt := by
    rw [map_add, map_smul, map_smul, hLx, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, ← hre]
    field_simp
  rw [hα, hβ, hre, hyeq] at hdb
  have hinner : (e * (2 * at')) • x + e • wt - at' • ((2:ℝ) • e • x) - liouvilleCLM x wt • e • R =
      e • ζt := by
    simp only [hζt]; module
  rw [hinner, map_smul] at hdb
  rw [← liouvilleCLM_apply] at hcr1 hcr2
  change as = liouvilleCLM x wt at hcr1
  change at' = -liouvilleCLM x ws at hcr2
  have hsum : e • (ζs + J x ζt) = 0 := by
    rw [← hdb, hcr2, hζs, hcr1]; module
  have hJs : ζs = -J x ζt := by
    have := (smul_eq_zero.mp hsum).resolve_left hepos.ne'
    exact eq_neg_of_add_eq_zero_left this
  -- density in terms of ζ
  have hws : ws = liouvilleCLM x ws • R + ζs := by simp [hζs]
  have hwt : wt = liouvilleCLM x wt • R + ζt := by simp [hζt]
  have hRR : omega0 R R = 0 := omega0_self R
  have hRt : omega0 R ζt = 0 := hωR _ hXt.2
  have hRs : omega0 R ζs = 0 := hωR _ hXs.2
  have hsR : omega0 ζs R = 0 := by rw [omega0_anti, hRs, neg_zero]
  have hdens : omega0 ws wt = omega0 ζt (J x ζt) := by
    rw [hws, hwt]
    simp only [omega0_add_left, omega0_add_right, omega0_smul_left, omega0_smul_right, hRR, hRt,
      hsR, mul_zero, zero_add]
    rw [hJs, omega0_anti]
    rw [show -J x ζt = (-1:ℝ) • J x ζt by simp, omega0_smul_right]; ring
  have hζ0 : ζt = 0 := by
    by_contra hne
    have := ((hJ.2 x hxS ζt ζt hXt hXt).2.2.1 hne)
    rw [← hdens] at this; linarith
  have hζs0 : ζs = 0 := by rw [hJs, hζ0, map_zero, neg_zero]
  constructor
  · rw [hws, hζs0, add_zero, hcr2, neg_neg]
  · rw [hwt, hζ0, add_zero, hcr1]

end DQ


-- ===== DQ_h =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

variable {n : ℕ}

lemma U_open : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne

lemma U_conn : IsPreconnected {z : ℂ | z ≠ 0} := by
  have := (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (0:ℂ)).isPreconnected
  convert this using 1
  ext z; simp

lemma clm_decomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℂ →L[ℝ] F) (v : ℂ) :
    L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- Removable singularity + Liouville: `z g(z)` bounded on `ℂ \ {0}` is constant. -/
lemma punct_liouville (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z | z ≠ 0}) (M : ℝ)
    (hb : ∀ z : ℂ, z ≠ 0 → ‖z * g z‖ ≤ M) : ∀ z : ℂ, z ≠ 0 → z * g z = g 1 := by
  set f := fun z => z * g z with hf
  have hd : DifferentiableOn ℂ f (univ \ {0}) :=
    (differentiableOn_id.mul hg).mono (fun z hz => hz.2)
  have hbd : BddAbove (norm ∘ f '' (univ \ {0})) :=
    ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact hb z hz.2⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove Filter.univ_mem hd hbd
  set F := Function.update f 0 (limUnder (𝓝[≠] (0:ℂ)) f) with hFdef
  have hF' : Differentiable ℂ F := fun z => (hF z (mem_univ z)).differentiableAt Filter.univ_mem
  have hFb : Bornology.IsBounded (range F) := by
    refine (isBounded_closedBall (x := (0:ℂ)) (r := max M ‖F 0‖)).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    by_cases hz : z = 0
    · subst hz; exact le_max_right _ _
    · rw [hFdef, Function.update_of_ne hz]; exact (hb z hz).trans (le_max_left _ _)
  intro z hz
  have := hF'.apply_eq_apply_of_bounded hFb z 1
  rw [hFdef, Function.update_of_ne hz, Function.update_of_ne one_ne_zero, hf] at this
  simpa using this

theorem a_w_formula (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | z ≠ 0} u) (h0 : dlambdaEnergy H {z | z ≠ 0} u = 0) :
    ∃ α c0 : ℝ, (∀ z : ℂ, z ≠ 0 → aCoord H (u z) = α * Real.log ‖z‖ + c0) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ v : ℂ,
        fderiv ℝ (fun z => proj H (u z)) z v = (α * (v / z).im) • reeb H (proj H (u z))) := by
  set U : Set ℂ := {z | z ≠ 0} with hUdef
  have hU : IsOpen U := U_open
  have hu' := hu
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hd := dens_zero H hH J hJ U hU u hu' h0
  have hcr := fun z hz => cr_rel H hH J hJ U hU u hsm hu0 hhol z hz
  have hg := g_differentiableOn U hU _ _ ha hw hcr hd
  set a := fun z => aCoord H (u z) with hadef
  set w := fun z => proj H (u z) with hwdef
  have hED : ∀ φ, ∀ z ∈ U, energyDensity H φ u z = deriv φ (a z) *
      ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2) := by
    intro φ z hz
    simp only [hadef, hwdef] at *
    have h1 := (hcr z hz).1; have h2 := (hcr z hz).2
    have hdz := hd z hz
    simp only [ds, dt] at h1 h2 hdz
    simp only [energyDensity, ds, dt, hdz, mul_zero, add_zero]
    rw [← h1]
    have h3 : liouville (proj H (u z)) ((fderiv ℝ (fun z => proj H (u z)) z) 1) =
      -(fderiv ℝ (fun z => aCoord H (u z)) z) Complex.I := by rw [h2]; ring
    rw [h3]; ring
  have hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ energy H U u := by
    intro φ hφ
    have : ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) =
        ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z) :=
      setLIntegral_congr_fun hU.measurableSet (fun z hz => by rw [hED φ z hz])
    rw [this]
    exact le_iSup₂ (f := fun φ (_ : Admissible φ) =>
      ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)) φ hφ
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  have hb : ∀ z : ℂ, z ≠ 0 → ‖z * g z‖ ≤ 128 * ((energy H U u).toReal * Real.pi / 2 + 1) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hsub : ball z ‖z‖ ⊆ U := by
      intro y hy
      simp only [hUdef, mem_setOf_eq]
      rintro rfl
      rw [mem_ball, dist_zero_left] at hy
      exact lt_irrefl _ hy
    have := grad_bound U hU a ha hg _ hE hbound z ‖z‖ hzpos hsub
    rw [norm_mul]
    change ‖z‖ * ‖g z‖ / 128 ≤ _ at this
    linarith
  have hκ := punct_liouville g hg _ hb
  set κ := g 1 with hκdef
  -- da(z) v = Re(g z * v)
  have hda : ∀ z : ℂ, z ≠ 0 → ∀ v : ℂ, fderiv ℝ a z v = (κ / z * v).re := by
    intro z hz v
    have hgz : g z = κ / z := by rw [← hκ z hz]; field_simp
    rw [← hgz, clm_decomp (fderiv ℝ a z) v]
    simp only [hgdef, smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    ring
  have hadiff : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ a z := fun z hz =>
    (ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  -- κ is real
  have hκim : κ.im = 0 := by
    set φ : ℝ → ℝ := fun t => a (Complex.exp (t * Complex.I)) + κ.im * t with hφ
    have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
        (Complex.exp (t * Complex.I) * Complex.I) t := by
      intro t
      have := ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).cexp
      simpa using this
    have hφd : ∀ t, HasDerivAt φ 0 t := by
      intro t
      have hne : Complex.exp (t * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have h1 := (hadiff _ hne).hasFDerivAt.comp_hasDerivAt t (hγ t)
      have h2 := h1.add ((hasDerivAt_id t).const_mul κ.im)
      have h3 : HasDerivAt φ (fderiv ℝ a (Complex.exp (t * Complex.I))
          (Complex.exp (t * Complex.I) * Complex.I) + κ.im * 1) t := h2
      convert h3 using 1
      rw [hda _ hne, show κ / Complex.exp (t * Complex.I) * (Complex.exp (t * Complex.I) * Complex.I)
        = κ * Complex.I by field_simp]
      simp
    have hc := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt)
      (fun t => (hφd t).deriv) (2 * Real.pi) 0
    simp only [hφ] at hc
    have he : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp (((0:ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [he] at hc
    have := Real.pi_pos
    nlinarith
  set α := κ.re with hαdef
  have hκα : κ = (α : ℂ) := Complex.ext (by simp [hαdef]) (by simp [hκim])
  -- a = α log ‖z‖ + c0
  have hlog : ∀ z : ℂ, z ≠ 0 → HasFDerivAt (fun z : ℂ => Real.log (‖z‖ ^ 2))
      ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z := by
    intro z hz
    exact (hasStrictFDerivAt_norm_sq z).hasFDerivAt.log (by positivity)
  have hG : ∀ z ∈ U, HasFDerivAt (fun z => a z - α / 2 * Real.log (‖z‖ ^ 2)) (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    refine ((hadiff z hz).hasFDerivAt.sub ((hlog z hz).const_mul (α / 2))).congr_fderiv ?_
    ext1 v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, hda z hz v, hκα]
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
    have hn : Complex.normSq z ≠ 0 := Complex.normSq_pos.mpr hz |>.ne'
    rw [div_mul_eq_mul_div, Complex.div_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, nsmul_eq_mul]
    field_simp
    ring
  have hGc : ∀ z ∈ U, a z - α / 2 * Real.log (‖z‖ ^ 2) = a 1 - α / 2 * Real.log (‖(1:ℂ)‖ ^ 2) :=
    fun z hz => hU.is_const_of_fderiv_eq_zero (𝕜 := ℝ) U_conn
      (fun y hy => (hG y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hG y hy).fderiv) hz (by simp [hUdef])
  refine ⟨α, a 1, fun z hz => ?_, fun z hz v => ?_⟩
  · have := hGc z hz
    rw [Real.log_pow] at this
    simp only [norm_one, one_pow, Real.log_one, mul_zero, sub_zero] at this
    change a z = _
    push_cast at this
    linarith
  · obtain ⟨hws, hwt⟩ := xi_part H hH J hJ U hU u hsm hu0 hhol z hz (hd z hz)
    simp only [ds, dt] at hws hwt
    rw [clm_decomp, hws, hwt, ← hadef]
    have e1 := hda z hz 1
    have e2 := hda z hz Complex.I
    rw [e1, e2, hκα, smul_smul, smul_smul, ← add_smul]
    congr 1
    have hn : Complex.normSq z ≠ 0 := Complex.normSq_pos.mpr hz |>.ne'
    simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.div_re]
    field_simp
    ring

end DQ


-- ===== DQ_i =====


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

variable {n : ℕ}

lemma exp_arg_unit (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (Complex.arg z * Complex.I) = ((‖z‖⁻¹ : ℝ) : ℂ) * z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
  push_cast
  calc Complex.exp (Complex.arg z * Complex.I)
      = (‖z‖ : ℂ)⁻¹ * ((‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I)) := by field_simp
    _ = _ := by rw [h]

lemma exp_k_arg (z : ℂ) (hz : z ≠ 0) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    Complex.exp ((k : ℂ) * Complex.arg (z ^ k) * Complex.I) = ((‖z‖⁻¹ : ℝ) : ℂ) * z := by
  rcases hk with rfl | rfl
  · simp only [Int.cast_one, one_mul, zpow_one]; exact exp_arg_unit z hz
  · have := exp_arg_unit z⁻¹ (inv_ne_zero hz)
    rw [show ((-1:ℤ):ℂ) * ((z ^ (-1:ℤ)).arg : ℂ) * Complex.I = -((z⁻¹).arg * Complex.I) by
      simp, Complex.exp_neg, this, norm_inv]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
    push_cast
    field_simp

lemma ray_const (w : ℂ → V n) (R : ℂ → V n) (α : ℝ)
    (hwd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ w z)
    (hdw : ∀ z : ℂ, z ≠ 0 → ∀ v, fderiv ℝ w z v = (α * (v / z).im) • R z)
    (z : ℂ) (hz : z ≠ 0) (t : ℝ) (ht : 0 < t) : w ((t : ℂ) * z) = w z := by
  set f : ℝ → V n := fun s => w ((s : ℂ) * z) with hf
  have hne : ∀ s : ℝ, 0 < s → (s : ℂ) * z ≠ 0 := fun s hs =>
    mul_ne_zero (by exact_mod_cast hs.ne') hz
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt f (fderiv ℝ w ((s : ℂ) * z) ((1:ℝ) * z)) s := by
    intro s hs
    have hγ : HasDerivAt (fun s : ℝ => (s : ℂ) * z) (((1:ℝ):ℂ) * z) s :=
      (hasDerivAt_id s).ofReal_comp.mul_const z
    exact (hwd _ (hne s hs)).hasFDerivAt.comp_hasDerivAt s hγ
  have h0 : ∀ s : ℝ, 0 < s → fderiv ℝ w ((s : ℂ) * z) ((1:ℝ) * z) = 0 := by
    intro s hs
    rw [hdw _ (hne s hs)]
    have : ((1:ℝ) : ℂ) * z / ((s : ℂ) * z) = ((s⁻¹ : ℝ) : ℂ) := by
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      push_cast; field_simp
    rw [this, Complex.ofReal_im, mul_zero, zero_smul]
  have := isOpen_Ioi.is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := f) isPreconnected_Ioi
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd s hs).deriv, h0 s hs]; rfl) (mem_Ioi.mpr ht) (mem_Ioi.mpr one_pos)
  simpa [hf] using this

theorem main (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | z ≠ 0} u)
    (hnc : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ u z₁ ≠ u z₂)
    (hzero : dlambdaEnergy H {z | z ≠ 0} u = 0) :
    ∃ P : ReebOrbit H, ∃ k : ℤ, k ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧
      ∀ z : ℂ, z ≠ 0 → u z = trivialCylinder P (c * z ^ k) := by
  obtain ⟨α, c0, ha, hw⟩ := a_w_formula H hH J hJ u hu hzero
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨-, hwsm⟩ := smooth_aw H hH J hJ {z | z ≠ 0} u hsm hu0
  set w := fun z => proj H (u z) with hwdef
  have hwd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ w z := fun z hz =>
    (hwsm.contDiffAt (U_open.mem_nhds hz)).differentiableAt (by simp)
  have huz : ∀ z : ℂ, z ≠ 0 → u z = Real.exp (2 * (α * Real.log ‖z‖ + c0)) • w z := fun z hz => by
    rw [← ha z hz]; exact (hrel _ (hu0 z hz)).2
  have hS : ∀ z : ℂ, z ≠ 0 → H (w z) = 1 := fun z hz => (hrel _ (hu0 z hz)).1
  by_cases hα : α = 0
  · exfalso
    obtain ⟨z₁, h1, z₂, h2, h12⟩ := hnc
    have hwc : ∀ z ∈ {z : ℂ | z ≠ 0}, w z = w 1 := fun z hz =>
      U_open.is_const_of_fderiv_eq_zero (𝕜 := ℝ) U_conn
        (fun y hy => (hwd y hy).differentiableWithinAt)
        (fun y hy => by ext1 v; simp [hw y hy v, hα]) hz (by simp)
    apply h12
    rw [huz z₁ h1, huz z₂ h2, hwc z₁ h1, hwc z₂ h2, hα]; simp
  set k : ℤ := if 0 < α then 1 else -1 with hkdef
  have hk : k = 1 ∨ k = -1 := by by_cases h : 0 < α <;> simp [hkdef, h]
  have hkα : (k : ℝ) * α = |α| := by
    by_cases h : 0 < α
    · simp [hkdef, h, abs_of_pos h]
    · simp [hkdef, h, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hα)]
  have hkabs : (k : ℝ) * |α| = α := by
    rcases hk with h | h <;> rw [h] at hkα ⊢ <;> push_cast at hkα ⊢ <;> linarith
  have habs : 0 < |α| := abs_pos.mpr hα
  set γ : ℝ → ℂ := fun τ => Complex.exp (((τ / α : ℝ) : ℂ) * Complex.I) with hγ
  have hγ0 : ∀ τ, γ τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  have hγd : ∀ τ, HasDerivAt γ (γ τ * (((1 / α : ℝ) : ℂ) * Complex.I)) τ := by
    intro τ
    have := (((hasDerivAt_id τ).div_const α).ofReal_comp.mul_const Complex.I).cexp
    simpa [hγ] using this
  let P : ReebOrbit H :=
    { x := fun τ => w (γ τ)
      T := 2 * Real.pi * |α|
      T_pos := by positivity
      mem := fun τ => hS _ (hγ0 τ)
      hasDerivAt := fun τ => by
        have h1 := (hwd _ (hγ0 τ)).hasFDerivAt.comp_hasDerivAt τ (hγd τ)
        have h2 : HasDerivAt (fun τ => w (γ τ))
            (fderiv ℝ w (γ τ) (γ τ * (((1 / α : ℝ) : ℂ) * Complex.I))) τ := h1
        refine h2.congr_deriv ?_
        rw [hw _ (hγ0 τ)]
        have : γ τ * (((1 / α : ℝ) : ℂ) * Complex.I) / γ τ = ((1 / α : ℝ) : ℂ) * Complex.I := by
          field_simp [hγ0 τ]
        rw [this]
        simp [hα, hwdef]
      periodic := fun τ => by
        show w (γ (τ + 2 * Real.pi * |α|)) = w (γ τ)
        congr 1
        simp only [hγ]
        have hr : (τ + 2 * Real.pi * |α|) / α = τ / α + k * (2 * Real.pi) := by
          rw [← hkα]; field_simp; try ring
        rw [hr, show (((τ / α + k * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I =
            ((τ / α : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
          Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one] }
  refine ⟨P, k, by rcases hk with h | h <;> simp [h], ((Real.exp (c0 / |α|) : ℝ) : ℂ),
    by exact_mod_cast (Real.exp_pos _).ne', fun z hz => ?_⟩
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  -- angular part
  have hang : P.x (P.T * Complex.arg (((Real.exp (c0 / |α|) : ℝ) : ℂ) * z ^ k) / (2 * Real.pi)) =
      w z := by
    show w (γ _) = w z
    rw [Complex.arg_real_mul _ (Real.exp_pos _)]
    have hr : 2 * Real.pi * |α| * Complex.arg (z ^ k) / (2 * Real.pi) / α =
        k * Complex.arg (z ^ k) := by
      rw [← hkα]; field_simp
    simp only [hγ]
    rw [hr]
    push_cast
    rw [exp_k_arg z hz k hk]
    exact ray_const w (fun z => reeb H (w z)) α hwd hw z hz _ (inv_pos.mpr hnz)
  -- radial part
  have hrad : ‖((Real.exp (c0 / |α|) : ℝ) : ℂ) * z ^ k‖ ^ (P.T / Real.pi) =
      Real.exp (2 * (α * Real.log ‖z‖ + c0)) := by
    have hN : ‖((Real.exp (c0 / |α|) : ℝ) : ℂ) * z ^ k‖ = Real.exp (c0 / |α|) * ‖z‖ ^ k := by
      rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hpos : 0 < Real.exp (c0 / |α|) * ‖z‖ ^ k := by positivity
    rw [hN, Real.rpow_def_of_pos hpos, Real.log_mul (Real.exp_pos _).ne' (by positivity),
      Real.log_exp, Real.log_zpow]
    congr 1
    show (c0 / |α| + k * Real.log ‖z‖) * (2 * Real.pi * |α| / Real.pi) = _
    have hp := Real.pi_pos
    field_simp
    linear_combination (Real.log ‖z‖) * hkabs
  show u z = (‖((Real.exp (c0 / |α|) : ℝ) : ℂ) * z ^ k‖ ^ (P.T / Real.pi)) •
    P.x (P.T * Complex.arg (((Real.exp (c0 / |α|) : ℝ) : ℂ) * z ^ k) / (2 * Real.pi))
  rw [hang, hrad, huz z hz]

end DQ

theorem solution {n : ℕ} (H : FiniteEnergyPlane.V n → ℝ)
    (hH : FiniteEnergyPlane.IsStrictlyStarShapedLevel H)
    (J : FiniteEnergyPlane.V n → FiniteEnergyPlane.V n →L[ℝ] FiniteEnergyPlane.V n)
    (hJ : FiniteEnergyPlane.IsCompatibleXiStructure H J) (u : ℂ → FiniteEnergyPlane.V n)
    (hu : FiniteEnergyPlane.IsFiniteEnergyCurve H J {z | z ≠ 0} u)
    (hnc : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ u z₁ ≠ u z₂)
    (hzero : FiniteEnergyPlane.dlambdaEnergy H {z | z ≠ 0} u = 0) :
    ∃ P : FiniteEnergyPlane.ReebOrbit H, ∃ k : ℤ, k ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧
      ∀ z : ℂ, z ≠ 0 → u z = FiniteEnergyPlane.trivialCylinder P (c * z ^ k) :=
  DQ.main H hH J hJ u hu hnc hzero
