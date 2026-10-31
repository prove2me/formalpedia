-- Prove2me | solution 1 for FiniteEnergyPlane.expDecay_of_dbar_expDecay
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:54:39.843274+00:00
-- url     : https://prove2.me/submissions/2e09dd0f-c9a2-474a-806a-879dbcb5fb7a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_le_div_mul_exp_of_deriv_ge
import Theorems.Thm_FiniteEnergyPlane_abs_le_exp_of_deriv_ge_abs_sub
import Theorems.Thm_FiniteEnergyPlane_le_exp_of_deriv_ge_of_lipschitz

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory
open scoped Topology ContDiff
open Set Filter MeasureTheory

/-! Plumbing for slice integrals on the half-cylinder (adapted from fizzyinc3's sub 05561728). -/


namespace HCL

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

/-- The open half-cylinder (as a strip). -/
def Ω : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

lemma isOpen_Ω : IsOpen Ω := isOpen_Ioi.prod isOpen_univ

lemma mem_Ω {s t : ℝ} (hs : 0 < s) : (s, t) ∈ Ω := ⟨hs, trivial⟩

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂ₛu`. -/
noncomputable def pS (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (1, 0)
/-- `∂ₜu`. -/
noncomputable def pT (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (0, 1)

/-- Smooth on `Ω`. -/
abbrev Sm (u : ℝ × ℝ → F) : Prop := ContDiffOn ℝ ∞ u Ω

lemma Sm.dS {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pS u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.dT {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pT u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.diffAt {u : ℝ × ℝ → F} (hu : Sm u) {x : ℝ × ℝ} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  (hu.contDiffAt (isOpen_Ω.mem_nhds hx)).differentiableAt (by simp)

lemma Sm.cont {u : ℝ × ℝ → F} (hu : Sm u) : ContinuousOn u Ω := hu.continuousOn

lemma Sm.hasDerivAt_s {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => u (σ, t)) (pS u (s, t)) s := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  exact h

lemma Sm.hasDerivAt_t {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun τ => u (s, τ)) (pT u (s, t)) t := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  exact h

lemma cont_slice {G : Type*} [TopologicalSpace G] {w : ℝ × ℝ → G} (hw : ContinuousOn w Ω)
    {s : ℝ} (hs : 0 < s) : Continuous fun t => w (s, t) :=
  hw.comp_continuous (continuous_const.prodMk continuous_id) fun _ => mem_Ω hs

end

/-- differentiation under the integral sign -/
lemma param_deriv (F F' : ℝ × ℝ → ℝ) (hF : ContinuousOn F Ω) (hF' : ContinuousOn F' Ω)
    (hd : ∀ σ t, 0 < σ → HasDerivAt (fun σ => F (σ, t)) (F' (σ, t)) σ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => ∫ t in (0:ℝ)..1, F (σ, t)) (∫ t in (0:ℝ)..1, F' (s, t)) s := by
  have hK : IsCompact (Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKΩ : Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1 ⊆ Ω := by
    rintro ⟨a, b⟩ ⟨ha, -⟩
    refine ⟨?_, trivial⟩
    rw [Metric.mem_closedBall, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKΩ)
  have hball : Metric.ball s (s / 2) ⊆ Ioi 0 := by
    intro a ha
    rw [Metric.mem_ball, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun σ t => F (σ, t)) (F' := fun σ t => F' (σ, t)) (x₀ := s)
    (bound := fun _ => M) (Metric.ball_mem_nhds s (by linarith : 0 < s / 2))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact this.2
  · filter_upwards [Ioi_mem_nhds hs] with σ hσ
    exact (cont_slice hF hσ).aestronglyMeasurable
  · exact (cont_slice hF hs).intervalIntegrable _ _
  · exact (cont_slice hF' hs).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht σ hσ => hM (σ, t) ⟨Metric.ball_subset_closedBall hσ, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · exact Eventually.of_forall fun t _ σ hσ => hd σ t (hball hσ)

/-- `∫₀¹ ⟪u(s, t), v(s, t)⟫ dt` -/
noncomputable def Ip (u v : ℝ × ℝ → Vec n) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ⟪u (s, t), v (s, t)⟫

lemma cont_inner {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : Continuous fun t => ⟪u (s, t), v (s, t)⟫ :=
  (cont_slice hu hs).inner (cont_slice hv hs)

lemma Ip_hasDerivAt {u v : ℝ × ℝ → Vec n} (hu : Sm u) (hv : Sm v) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Ip u v) (Ip (pS u) v s + Ip u (pS v) s) s := by
  have h := param_deriv (fun x => ⟪u x, v x⟫) (fun x => ⟪pS u x, v x⟫ + ⟪u x, pS v x⟫)
    (hu.cont.inner hv.cont) ((hu.dS.cont.inner hv.cont).add (hu.cont.inner hv.dS.cont))
    (fun σ t hσ => ((hu.hasDerivAt_s hσ).inner ℝ (hv.hasDerivAt_s hσ)).congr_deriv
      (add_comm _ _)) hs
  refine h.congr_deriv ?_
  simp only [Ip]
  exact intervalIntegral.integral_add ((cont_inner hu.dS.cont hv.cont hs).intervalIntegrable _ _)
    ((cont_inner hu.cont hv.dS.cont hs).intervalIntegrable _ _)

lemma Ip_comm (u v : ℝ × ℝ → Vec n) (s : ℝ) : Ip u v s = Ip v u s := by
  simp only [Ip, real_inner_comm]

/-- matrix fields as operator fields -/
lemma TL_eq_sum (M : Mat n) :
    TL n M = ∑ i, ∑ j, M i j • TL n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext a b
  simp [Matrix.single_apply]

lemma norm_TL_le (M : Mat n) :
    ‖TL n M‖ ≤ ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖ := by
  rw [TL_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

/-- entrywise smallness gives operator smallness -/
lemma op_small : ∃ c, 0 < c ∧ ∀ (M : Mat n) (δ : ℝ), 0 ≤ δ → (∀ i j, |M i j| ≤ δ) →
    ‖TL n M‖ ≤ c * δ := by
  set c0 := ∑ i, ∑ j, ‖TL n (Matrix.single i j (1:ℝ))‖
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨1 + c0, by linarith only [hc0], fun M δ hδ hM => (norm_TL_le M).trans ?_⟩
  calc ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖
      ≤ ∑ i, ∑ j, δ * ‖TL n (Matrix.single i j (1:ℝ))‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _)
    _ = δ * c0 := by simp only [c0, Finset.mul_sum]
    _ ≤ (1 + c0) * δ := by nlinarith only [hδ, hc0]

end HCL

/-! Slice quantities `F, D, G, α, q` of a smooth map on the half-cylinder and the normalized
slices `v = F^{-1/2} ζ`. -/


namespace HCL

variable {n : ℕ} (ζ : ℝ × ℝ → Vec n)

noncomputable def Fz (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2
noncomputable def Dz (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ⟪ζ (s, t), pS ζ (s, t)⟫
noncomputable def Gz (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ‖pS ζ (s, t)‖ ^ 2
noncomputable def αz (s : ℝ) : ℝ := Dz ζ s / Fz ζ s
noncomputable def qz (s : ℝ) : ℝ := Gz ζ s / Fz ζ s - (αz ζ s) ^ 2
/-- normalized slice -/
noncomputable def vz (s t : ℝ) : Vec n := (Real.sqrt (Fz ζ s))⁻¹ • ζ (s, t)
/-- its `s`-derivative -/
noncomputable def wz (s t : ℝ) : Vec n :=
  (Real.sqrt (Fz ζ s))⁻¹ • (pS ζ (s, t) - αz ζ s • ζ (s, t))

variable {ζ}

lemma Fz_eq_Ip (s : ℝ) : Fz ζ s = Ip ζ ζ s := by
  simp only [Fz, Ip, real_inner_self_eq_norm_sq]

lemma Gz_eq_Ip (s : ℝ) : Gz ζ s = Ip (pS ζ) (pS ζ) s := by
  simp only [Gz, Ip, real_inner_self_eq_norm_sq]

lemma Fz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : HasDerivAt (Fz ζ) (2 * Dz ζ s) s := by
  have h := Ip_hasDerivAt hζ hζ hs
  have e : Fz ζ = Ip ζ ζ := funext Fz_eq_Ip
  rw [e]
  refine h.congr_deriv ?_
  simp only [Dz, Ip]
  rw [show (fun t => ⟪pS ζ (s, t), ζ (s, t)⟫) = fun t => ⟪ζ (s, t), pS ζ (s, t)⟫ from
    funext fun t => real_inner_comm _ _]
  ring

lemma Fz_cont (hζ : Sm ζ) : ContinuousOn (Fz ζ) (Ioi 0) := fun s hs =>
  (Fz_hasDerivAt hζ hs).continuousAt.continuousWithinAt

lemma Dz_cont (hζ : Sm ζ) : ContinuousOn (Dz ζ) (Ioi 0) := fun s hs =>
  (Ip_hasDerivAt hζ hζ.dS hs).continuousAt.continuousWithinAt

lemma Gz_cont (hζ : Sm ζ) : ContinuousOn (Gz ζ) (Ioi 0) := by
  have e : Gz ζ = Ip (pS ζ) (pS ζ) := funext Gz_eq_Ip
  rw [e]
  exact fun s hs => (Ip_hasDerivAt hζ.dS hζ.dS hs).continuousAt.continuousWithinAt

lemma αz_cont (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) :
    ContinuousOn (αz ζ) (Ici s₀) := fun s hs => by
  have hs' : 0 < s := lt_of_lt_of_le hs₀ hs
  exact ((Dz_cont hζ s hs').continuousAt (Ioi_mem_nhds hs')).continuousWithinAt.div
    ((Fz_cont hζ s hs').continuousAt (Ioi_mem_nhds hs')).continuousWithinAt (hF s hs).ne'

lemma qz_cont (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) :
    ContinuousOn (qz ζ) (Ici s₀) := by
  have h1 : ContinuousOn (fun s => Gz ζ s / Fz ζ s) (Ici s₀) := fun s hs => by
    have hs' : 0 < s := lt_of_lt_of_le hs₀ hs
    exact ((Gz_cont hζ s hs').continuousAt (Ioi_mem_nhds hs')).continuousWithinAt.div
      ((Fz_cont hζ s hs').continuousAt (Ioi_mem_nhds hs')).continuousWithinAt (hF s hs).ne'
  exact h1.sub ((αz_cont hζ hs₀ hF).pow 2)

/-- `∫₀¹ ‖∂ₛζ - α ζ‖² = F q`. -/
lemma integral_norm_sub_sq (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) :
    ∫ t in (0:ℝ)..1, ‖pS ζ (s, t) - αz ζ s • ζ (s, t)‖ ^ 2 = Fz ζ s * qz ζ s := by
  have c1 := cont_slice hζ.cont hs
  have c2 := cont_slice hζ.dS.cont hs
  have e : ∀ t, ‖pS ζ (s, t) - αz ζ s • ζ (s, t)‖ ^ 2 =
      ‖pS ζ (s, t)‖ ^ 2 - 2 * αz ζ s * ⟪ζ (s, t), pS ζ (s, t)⟫ + αz ζ s ^ 2 * ‖ζ (s, t)‖ ^ 2 := by
    intro t
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun t => ‖pS ζ (s, t)‖ ^ 2) volume 0 1 :=
    (c2.norm.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * αz ζ s * ⟪ζ (s, t), pS ζ (s, t)⟫) volume 0 1 :=
    (continuous_const.mul (c1.inner c2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => αz ζ s ^ 2 * ‖ζ (s, t)‖ ^ 2) volume 0 1 :=
    (continuous_const.mul (c1.norm.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change Gz ζ s - 2 * αz ζ s * Dz ζ s + αz ζ s ^ 2 * Fz ζ s = Fz ζ s * qz ζ s
  simp only [qz, αz]
  field_simp
  ring

lemma qz_nonneg (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) : 0 ≤ qz ζ s := by
  have h := integral_norm_sub_sq hζ hs hF
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖pS ζ (s, t) - αz ζ s • ζ (s, t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hF

lemma integral_norm_wz_sq (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) :
    ∫ t in (0:ℝ)..1, ‖wz ζ s t‖ ^ 2 = qz ζ s := by
  have hsq : (Real.sqrt (Fz ζ s))⁻¹ ^ 2 = (Fz ζ s)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hF.le]
  simp only [wz, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsq]
  rw [intervalIntegral.integral_const_mul, integral_norm_sub_sq hζ hs hF]
  field_simp

lemma integral_norm_vz_sq {s : ℝ} (hF : 0 < Fz ζ s) :
    ∫ t in (0:ℝ)..1, ‖vz ζ s t‖ ^ 2 = 1 := by
  have hsq : (Real.sqrt (Fz ζ s))⁻¹ ^ 2 = (Fz ζ s)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hF.le]
  simp only [vz, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsq]
  rw [intervalIntegral.integral_const_mul]
  change (Fz ζ s)⁻¹ * Fz ζ s = 1
  field_simp

/-- `∂ₛ v = w`. -/
lemma vz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) (t : ℝ) :
    HasDerivAt (fun σ => vz ζ σ t) (wz ζ s t) s := by
  have h1 := ((Fz_hasDerivAt hζ hs).sqrt hF.ne').inv (Real.sqrt_pos.2 hF).ne'
  have h2 := h1.smul (hζ.hasDerivAt_s (t := t) hs)
  refine h2.congr_deriv ?_
  have hr : Real.sqrt (Fz ζ s) ≠ 0 := (Real.sqrt_pos.2 hF).ne'
  have hsq : Real.sqrt (Fz ζ s) ^ 2 = Fz ζ s := Real.sq_sqrt hF.le
  have hc : -(2 * Dz ζ s / (2 * Real.sqrt (Fz ζ s))) / Real.sqrt (Fz ζ s) ^ 2 =
      -((Real.sqrt (Fz ζ s))⁻¹ * (Dz ζ s / Fz ζ s)) := by
    rw [hsq]; field_simp
  simp only [Pi.inv_apply]
  rw [hc, neg_smul, ← sub_eq_add_neg]
  simp only [wz, αz, smul_sub, smul_smul]

end HCL

/-! The `L²` displacement of normalized slices is controlled by `∫ q`. -/


namespace HCL

variable {n : ℕ} {ζ : ℝ × ℝ → Vec n}

/-- Cauchy–Schwarz on an interval. -/
lemma cs1 {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have hL : 0 < b - a := by linarith
  have hg' : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  set I := ∫ x in a..b, g x
  set m := I / (b - a)
  have i1 : IntervalIntegrable (fun x => g x ^ 2) volume a b := (hg'.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => 2 * m * g x) volume a b :=
    (continuousOn_const.mul hg').intervalIntegrable
  have h0 : 0 ≤ ∫ x in a..b, (g x ^ 2 - 2 * m * g x + m ^ 2) :=
    intervalIntegral.integral_nonneg hab fun x _ => by nlinarith [sq_nonneg (g x - m)]
  rw [intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at h0
  have hm : m * (b - a) = I := by simp only [m]; field_simp
  nlinarith

lemma wz_contOn (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) :
    ContinuousOn (fun p : ℝ × ℝ => wz ζ p.1 p.2) (Ici s₀ ×ˢ univ) := by
  have hsub : Ici s₀ ×ˢ (univ : Set ℝ) ⊆ Ω := fun p hp =>
    ⟨lt_of_lt_of_le hs₀ (show s₀ ≤ p.1 from hp.1), trivial⟩
  have hfst : MapsTo Prod.fst (Ici s₀ ×ˢ (univ : Set ℝ)) (Ici s₀) := fun p hp => hp.1
  have hFc : ContinuousOn (fun p : ℝ × ℝ => Fz ζ p.1) (Ici s₀ ×ˢ univ) :=
    ((Fz_cont hζ).mono fun s hs => lt_of_lt_of_le hs₀ (show s₀ ≤ s from hs)).comp
      continuous_fst.continuousOn hfst
  have hαc : ContinuousOn (fun p : ℝ × ℝ => αz ζ p.1) (Ici s₀ ×ˢ univ) :=
    (αz_cont hζ hs₀ hF).comp continuous_fst.continuousOn hfst
  have hpS : ContinuousOn (fun p : ℝ × ℝ => pS ζ (p.1, p.2)) (Ici s₀ ×ˢ univ) :=
    hζ.dS.cont.mono hsub
  have hζc : ContinuousOn (fun p : ℝ × ℝ => ζ (p.1, p.2)) (Ici s₀ ×ˢ univ) :=
    hζ.cont.mono hsub
  refine (hFc.sqrt.inv₀ fun p hp => (Real.sqrt_pos.2 (hF p.1 hp.1)).ne').smul
    (hpS.sub (hαc.smul hζc))

lemma vz_slice_cont (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : Continuous fun t => vz ζ s t := by
  unfold vz
  exact (continuous_const (y := (Real.sqrt (Fz ζ s))⁻¹)).smul (cont_slice hζ.cont hs)

lemma wz_slice_s (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) {a b : ℝ}
    (ha : s₀ ≤ a) (t : ℝ) : ContinuousOn (fun s => wz ζ s t) (Icc a b) := by
  have hw := wz_contOn hζ hs₀ hF
  have hm : MapsTo (fun s : ℝ => (s, t)) (Icc a b) (Ici s₀ ×ˢ univ) := fun s hs =>
    mk_mem_prod (show s₀ ≤ s from le_trans ha hs.1) (mem_univ t)
  have h := ContinuousOn.comp (g := fun p : ℝ × ℝ => wz ζ p.1 p.2) (f := fun s : ℝ => (s, t)) hw
    (continuous_id.prodMk continuous_const).continuousOn hm
  exact h

lemma pt_bound (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) {a b : ℝ}
    (ha : s₀ ≤ a) (hab : a ≤ b) (t : ℝ) :
    ‖vz ζ b t - vz ζ a t‖ ^ 2 ≤ (b - a) * ∫ s in a..b, ‖wz ζ s t‖ ^ 2 := by
  have hsl := wz_slice_s (b := b) hζ hs₀ hF ha t
  have hft : vz ζ b t - vz ζ a t = ∫ s in a..b, wz ζ s t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun σ => vz ζ σ t)]
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have hx0 : s₀ ≤ x := le_trans ha hx.1
      exact vz_hasDerivAt hζ (lt_of_lt_of_le hs₀ hx0) (hF x hx0) t
    · exact ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab]; exact hsl)
  rw [hft]
  have h1 : ‖∫ s in a..b, wz ζ s t‖ ≤ ∫ s in a..b, ‖wz ζ s t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have h2 := cs1 hab hsl.norm
  have h0 : 0 ≤ ‖∫ s in a..b, wz ζ s t‖ := norm_nonneg _
  nlinarith

/-- `‖v_b - v_a‖²_{L²} ≤ (b - a) ∫ₐᵇ q`. -/
lemma disp (hζ : Sm ζ) {s₀ : ℝ} (hs₀ : 0 < s₀) (hF : ∀ s ≥ s₀, 0 < Fz ζ s) {a b : ℝ}
    (ha : s₀ ≤ a) (hab : a ≤ b) :
    ∫ t in (0:ℝ)..1, ‖vz ζ b t - vz ζ a t‖ ^ 2 ≤ (b - a) * ∫ s in a..b, qz ζ s := by
  have hw := wz_contOn hζ hs₀ hF
  have hK : Icc a b ×ˢ Icc (0:ℝ) 1 ⊆ Ici s₀ ×ˢ univ := fun p hp =>
    ⟨le_trans ha hp.1.1, trivial⟩
  let g : ℝ × ℝ → ℝ := fun p => ‖wz ζ p.1 p.2‖ ^ 2
  have hgc : ContinuousOn g (Icc a b ×ˢ Icc (0:ℝ) 1) := ((hw.mono hK).norm.pow 2)
  -- integrability on the rectangle
  have hint : Integrable g ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hgc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hsl : ∀ t, ContinuousOn (fun s => wz ζ s t) (Icc a b) := fun t => wz_slice_s hζ hs₀ hF ha t
  have hpt := pt_bound hζ hs₀ hF ha hab
  -- integrate in `t` and swap
  have hmarg : Integrable (fun t => ∫ s, g (s, t) ∂(volume.restrict (Ioc a b)))
      (volume.restrict (Ioc (0:ℝ) 1)) := hint.integral_prod_right
  have hswap : ∫ s in a..b, ∫ t in Ioc (0:ℝ) 1, g (s, t) =
      ∫ t in Ioc (0:ℝ) 1, ∫ s in a..b, g (s, t) := by
    have := intervalIntegral_integral_swap (a := a) (b := b) (μ := volume.restrict (Ioc (0:ℝ) 1))
      (f := fun s t => g (s, t)) (by rw [uIoc_of_le hab]; exact hint)
    exact this
  have hq : ∫ s in a..b, qz ζ s = ∫ s in a..b, ∫ t in Ioc (0:ℝ) 1, g (s, t) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    have hs0 : s₀ ≤ s := le_trans ha hs.1
    rw [← integral_norm_wz_sq hζ (lt_of_lt_of_le hs₀ hs0) (hF s hs0),
      intervalIntegral.integral_of_le zero_le_one]
  have hvc : Continuous fun t => ‖vz ζ b t - vz ζ a t‖ ^ 2 :=
    (((vz_slice_cont hζ (lt_of_lt_of_le hs₀ (ha.trans hab))).sub
      (vz_slice_cont hζ (lt_of_lt_of_le hs₀ ha))).norm.pow 2)
  rw [hq, hswap, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  refine setIntegral_mono_on (hvc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hmarg.const_mul (b - a) |>.congr ?_) measurableSet_Ioc fun t _ => ?_
  · refine Eventually.of_forall fun t => ?_
    simp only
    rw [intervalIntegral.integral_of_le hab]
  · exact hpt t

end HCL

/-! Slice calculus on the half-cylinder for the scalar decay lemma (G). -/


namespace HCL.KG

/-- mixed partials commute -/
lemma pS_pT {u : ℝ × ℝ → ℝ} (hu : Sm u) {x} (hx : x ∈ Ω) : pS (pT u) x = pT (pS u) x := by
  have hc : ContDiffAt ℝ ∞ u x := hu.contDiffAt (isOpen_Ω.mem_nhds hx)
  have hsymm := hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x := by
    have := (hu.fderiv_of_isOpen isOpen_Ω (m := 1) (WithTop.coe_le_coe.2 le_top)).contDiffAt (isOpen_Ω.mem_nhds hx)
    exact this.differentiableAt one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ u y (0, 1)) x (1, 0) =
    fderiv ℝ (fun y => fderiv ℝ u y (1, 0)) x (0, 1)
  rw [show (fun y => fderiv ℝ u y (0, 1)) = fun y => (fderiv ℝ u y) ((fun _ => ((0:ℝ), (1:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _),
    show (fun y => fderiv ℝ u y (1, 0)) = fun y => (fderiv ℝ u y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

/-- `1`-periodic in `t` on the open half-cylinder. -/
def Per (u : ℝ × ℝ → ℝ) : Prop := ∀ s > 0, ∀ t, u (s, t + 1) = u (s, t)

lemma Per.pS {u : ℝ × ℝ → ℝ} (hu : Sm u) (hp : Per u) : Per (HCL.pS u) := by
  intro s hs t
  have h1 := hu.hasDerivAt_s (t := t + 1) hs
  have hev : (fun σ => u (σ, t + 1)) =ᶠ[𝓝 s] fun σ => u (σ, t) := by
    filter_upwards [Ioi_mem_nhds hs] with σ hσ using hp σ hσ t
  exact (h1.congr_of_eventuallyEq hev.symm).unique (hu.hasDerivAt_s hs)

lemma integral_pT_eq_zero {u : ℝ × ℝ → ℝ} (hu : Sm u) (hp : Per u) {s : ℝ} (hs : 0 < s) :
    ∫ t in (0:ℝ)..1, pT u (s, t) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hu.hasDerivAt_t hs)
    ((cont_slice hu.dT.cont hs).intervalIntegrable _ _)]
  have := hp s hs 0
  simp only [zero_add] at this
  rw [this, sub_self]

/-- integration by parts over a period -/
lemma integral_mul_pT {u v : ℝ × ℝ → ℝ} (hu : Sm u) (hv : Sm v) (hpu : Per u) (hpv : Per v)
    {s : ℝ} (hs : 0 < s) :
    ∫ t in (0:ℝ)..1, u (s, t) * pT v (s, t) = -∫ t in (0:ℝ)..1, pT u (s, t) * v (s, t) := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hu.hasDerivAt_t hs)
    (fun t _ => hv.hasDerivAt_t hs) ((cont_slice hu.dT.cont hs).intervalIntegrable _ _)
    ((cont_slice hv.dT.cont hs).intervalIntegrable _ _)]
  have h1 := hpu s hs 0
  have h2 := hpv s hs 0
  simp only [zero_add] at h1 h2
  rw [h1, h2]
  ring

/-- oscillation over one period is bounded by the total variation -/
lemma abs_sub_le_integral {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    {t u : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    |φ t - φ u| ≤ ∫ x in (0:ℝ)..1, |φ' x| := by
  have key : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
      |φ b - φ a| ≤ ∫ x in (0:ℝ)..1, |φ' x| := by
    intro a b ha hb hab
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hφ x)
      (hφ'.intervalIntegrable _ _)]
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    exact intervalIntegral.integral_mono_interval ha.1 hab hb.2
      (Eventually.of_forall fun _ => abs_nonneg _) (hφ'.abs.intervalIntegrable _ _)
  rcases le_total u t with h | h
  · exact key u t hu ht h
  · rw [abs_sub_comm]; exact key t u ht hu h

lemma abs_sub_mean_le {u : ℝ × ℝ → ℝ} (hu : Sm u) {s : ℝ} (hs : 0 < s) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    |u (s, t) - ∫ x in (0:ℝ)..1, u (s, x)| ≤ ∫ x in (0:ℝ)..1, |pT u (s, x)| := by
  have hc := cont_slice hu.cont hs
  have e : u (s, t) - ∫ x in (0:ℝ)..1, u (s, x) = ∫ x in (0:ℝ)..1, (u (s, t) - u (s, x)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _)]
    simp
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := ∫ x in (0:ℝ)..1, |pT u (s, x)|) (f := fun x => u (s, t) - u (s, x)) ?_
  · simpa using this
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  exact abs_sub_le_integral (φ := fun x => u (s, x)) (fun x => hu.hasDerivAt_t hs)
    (cont_slice hu.dT.cont hs) ht (Ioc_subset_Icc_self hx)

/-- sup bound on a whole slice -/
lemma abs_le_mean_add {u : ℝ × ℝ → ℝ} (hu : Sm u) (hp : Per u) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |u (s, t)| ≤ |∫ x in (0:ℝ)..1, u (s, x)| + ∫ x in (0:ℝ)..1, |pT u (s, x)| := by
  have hper : Function.Periodic (fun x => u (s, x)) 1 := fun x => hp s hs x
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ one_pos t
  have := abs_sub_mean_le hu hs (Ico_subset_Icc_self hy)
  rw [show u (s, t) = u (s, y) from hyt]
  have := abs_sub_abs_le_abs_sub (u (s, y)) (∫ x in (0:ℝ)..1, u (s, x))
  linarith

lemma sq_integral_abs_le {u : ℝ × ℝ → ℝ} (hu : ContinuousOn u Ω) {s : ℝ} (hs : 0 < s) :
    (∫ x in (0:ℝ)..1, |u (s, x)|) ^ 2 ≤ ∫ x in (0:ℝ)..1, u (s, x) ^ 2 := by
  have := HCL.cs1 (g := fun x => |u (s, x)|) zero_le_one (cont_slice hu hs).abs.continuousOn
  simpa using this

end HCL.KG

/-! The scalar decay lemma on the normalized half-cylinder `s > 0`. -/


namespace HCL.KG

lemma ii_cont {u : ℝ × ℝ → ℝ} (hu : ContinuousOn u Ω) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun t => u (s, t)) volume 0 1 :=
  (cont_slice hu hs).intervalIntegrable _ _

lemma ii_mul {u v : ℝ × ℝ → ℝ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : IntervalIntegrable (fun t => u (s, t) * v (s, t)) volume 0 1 :=
  ((cont_slice hu hs).mul (cont_slice hv hs)).intervalIntegrable _ _

lemma abs_integral_le_const {φ : ℝ → ℝ} {K : ℝ} (h : ∀ t, |φ t| ≤ K) :
    |∫ t in (0:ℝ)..1, φ t| ≤ K := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := K)
    (f := φ) (fun t _ => by simpa [Real.norm_eq_abs] using h t)
  simpa using this

/-- exponential bound on the `t`-mean -/
lemma mean_bound {u w : ℝ × ℝ → ℝ} (hu : Sm u) (hw : Sm w) (hpw : Per w) (c K δ : ℝ)
    (hδ : 0 < δ) (hd : ∀ s > 0, ∀ t, |pS u (s, t) + c * pT w (s, t)| ≤ K * Real.exp (-(δ * s)))
    (h0 : Tendsto (fun s => ∫ t in (0:ℝ)..1, u (s, t)) atTop (𝓝 0)) :
    ∀ s > 0, |∫ t in (0:ℝ)..1, u (s, t)| ≤ K / δ * Real.exp (-(δ * s)) := by
  set m := fun s => ∫ t in (0:ℝ)..1, u (s, t) with hm
  have hder : ∀ s > 0, HasDerivAt m (∫ t in (0:ℝ)..1, pS u (s, t)) s := fun s hs =>
    param_deriv u (pS u) hu.cont hu.dS.cont (fun σ t hσ => hu.hasDerivAt_s hσ) hs
  have hbd : ∀ s > 0, |∫ t in (0:ℝ)..1, pS u (s, t)| ≤ K * Real.exp (-(δ * s)) := by
    intro s hs
    have hval : ∫ t in (0:ℝ)..1, pS u (s, t) =
        ∫ t in (0:ℝ)..1, (pS u (s, t) + c * pT w (s, t)) := by
      rw [intervalIntegral.integral_add (ii_cont hu.dS.cont hs)
        ((ii_cont hw.dT.cont hs).const_mul c), intervalIntegral.integral_const_mul,
        integral_pT_eq_zero hw hpw hs, mul_zero, add_zero]
    rw [hval]
    exact abs_integral_le_const fun t => hd s hs t
  have h1 := FiniteEnergyPlane.le_div_mul_exp_of_deriv_ge m _ 0 K δ hδ hder h0
    (fun s hs => by have := (abs_le.1 (hbd s hs)).1; linarith)
  have h2 := FiniteEnergyPlane.le_div_mul_exp_of_deriv_ge (fun s => -m s) _ 0 K δ hδ
    (fun s hs => (hder s hs).neg) (by simpa using h0.neg)
    (fun s hs => by have := (abs_le.1 (hbd s hs)).2; linarith)
  intro s hs
  rw [abs_le]
  constructor
  · have := h2 s hs
    simp only [hm] at this
    linarith
  · exact h1 s hs

/-- `∫₀¹ f ∂ₜg` -/
noncomputable def act (f g : ℝ × ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, f (s, t) * pT g (s, t)

/-- `∫₀¹ (∂ₜf)² + (∂ₜg)²` -/
noncomputable def en (f g : ℝ × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, (pT f (s, t) ^ 2 + pT g (s, t) ^ 2)

lemma integrand_ge (p q x y ε : ℝ) (h : |p - y| + |x + q| ≤ ε) :
    (x ^ 2 + y ^ 2) / 2 - ε ^ 2 / 2 ≤ p * y - x * q := by
  have h1 : (p - y) ^ 2 + (x + q) ^ 2 ≤ ε ^ 2 := by
    have ha := abs_nonneg (p - y)
    have hb := abs_nonneg (x + q)
    have : (|p - y| + |x + q|) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    nlinarith [sq_abs (p - y), sq_abs (x + q)]
  nlinarith [sq_nonneg p, sq_nonneg q]

section
variable {f g : ℝ × ℝ → ℝ}

lemma act_hasDerivAt (hf : Sm f) (hg : Sm g) (hpf : Per f) (hpg : Per g) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (act f g)
      (∫ t in (0:ℝ)..1, (pS f (s, t) * pT g (s, t) - pT f (s, t) * pS g (s, t))) s := by
  have h := param_deriv (fun x => f x * pT g x) (fun x => pS f x * pT g x + f x * pS (pT g) x)
    (hf.cont.mul hg.dT.cont) ((hf.dS.cont.mul hg.dT.cont).add (hf.cont.mul hg.dT.dS.cont))
    (fun σ t hσ => (hf.hasDerivAt_s hσ).mul (hg.dT.hasDerivAt_s hσ)) hs
  refine h.congr_deriv ?_
  rw [intervalIntegral.integral_add (ii_mul hf.dS.cont hg.dT.cont hs)
    (ii_mul hf.cont hg.dT.dS.cont hs)]
  have e1 : ∫ t in (0:ℝ)..1, f (s, t) * pS (pT g) (s, t) =
      ∫ t in (0:ℝ)..1, f (s, t) * pT (pS g) (s, t) :=
    intervalIntegral.integral_congr fun t _ => by simp only [pS_pT hg (mem_Ω hs)]
  rw [e1, integral_mul_pT hf hg.dS hpf (hpg.pS hg) hs, intervalIntegral.integral_sub
    (ii_mul hf.dS.cont hg.dT.cont hs) (ii_mul hf.dT.cont hg.dS.cont hs)]
  ring

lemma act_deriv_ge (hf : Sm f) (hg : Sm g) {s : ℝ} (hs : 0 < s) (ε : ℝ)
    (hd : ∀ t, |pS f (s, t) - pT g (s, t)| + |pT f (s, t) + pS g (s, t)| ≤ ε) :
    en f g s / 2 - ε ^ 2 / 2 ≤
      ∫ t in (0:ℝ)..1, (pS f (s, t) * pT g (s, t) - pT f (s, t) * pS g (s, t)) := by
  have hE : IntervalIntegrable (fun t => pT f (s, t) ^ 2 + pT g (s, t) ^ 2) volume 0 1 :=
    ii_cont ((hf.dT.cont.pow 2).add (hg.dT.cont.pow 2)) hs
  have e : ∫ t in (0:ℝ)..1, ((pT f (s, t) ^ 2 + pT g (s, t) ^ 2) / 2 - ε ^ 2 / 2) =
      en f g s / 2 - ε ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (hE.div_const 2) intervalIntegrable_const,
      intervalIntegral.integral_div]
    simp [en]
  rw [← e]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((hE.div_const 2).sub intervalIntegrable_const)
    (ii_cont ((hf.dS.cont.mul hg.dT.cont).sub (hf.dT.cont.mul hg.dS.cont)) hs) ?_
  intro t _
  exact integrand_ge _ _ _ _ _ (hd t)

lemma abs_act_le (hf : Sm f) (hg : Sm g) (hpg : Per g) {s : ℝ} (hs : 0 < s) :
    |act f g s| ≤ en f g s / 2 := by
  set m := ∫ x in (0:ℝ)..1, f (s, x)
  set P := ∫ x in (0:ℝ)..1, |pT f (s, x)|
  set Q := ∫ x in (0:ℝ)..1, |pT g (s, x)|
  have hP0 : 0 ≤ P := intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _
  have hQ0 : 0 ≤ Q := intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _
  have e : act f g s = ∫ t in (0:ℝ)..1, (f (s, t) - m) * pT g (s, t) := by
    unfold act
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub (ii_mul hf.cont hg.dT.cont hs)
      ((ii_cont hg.dT.cont hs).const_mul m), intervalIntegral.integral_const_mul,
      integral_pT_eq_zero hg hpg hs, mul_zero, sub_zero]
  have hfm : Continuous fun t => (f (s, t) - m) * pT g (s, t) :=
    ((cont_slice hf.cont hs).sub continuous_const).mul (cont_slice hg.dT.cont hs)
  have h1 : |act f g s| ≤ P * Q := by
    rw [e]
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one (hfm.abs.intervalIntegrable _ _)
      (((cont_slice hg.dT.cont hs).abs.const_mul P).intervalIntegrable _ _) ?_
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub_mean_le hf hs ht) (abs_nonneg _)
  have h2 := sq_integral_abs_le hf.dT.cont hs
  have h3 := sq_integral_abs_le hg.dT.cont hs
  have he : en f g s = (∫ x in (0:ℝ)..1, pT f (s, x) ^ 2) + ∫ x in (0:ℝ)..1, pT g (s, x) ^ 2 :=
    intervalIntegral.integral_add (ii_cont (hf.dT.cont.pow 2) hs) (ii_cont (hg.dT.cont.pow 2) hs)
  rw [he]
  nlinarith [sq_nonneg (P - Q)]

lemma en_hasDerivAt (hf : Sm f) (hg : Sm g) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (en f g) (∫ t in (0:ℝ)..1,
      (2 * pT f (s, t) * pS (pT f) (s, t) + 2 * pT g (s, t) * pS (pT g) (s, t))) s := by
  have h := param_deriv (fun x => pT f x ^ 2 + pT g x ^ 2)
    (fun x => 2 * pT f x * pS (pT f) x + 2 * pT g x * pS (pT g) x)
    ((hf.dT.cont.pow 2).add (hg.dT.cont.pow 2))
    (((continuousOn_const.mul hf.dT.cont).mul hf.dT.dS.cont).add
      ((continuousOn_const.mul hg.dT.cont).mul hg.dT.dS.cont))
    (fun σ t hσ => (((hf.dT.hasDerivAt_s hσ).pow 2).add ((hg.dT.hasDerivAt_s hσ).pow 2)).congr_deriv
      (by push_cast; ring)) hs
  exact h

lemma en_lipschitz (hf : Sm f) (hg : Sm g)
    (hb : ∀ s > 0, ∀ t, |pT f (s, t)| ≤ 1 ∧ |pT g (s, t)| ≤ 1 ∧ |pS (pT f) (s, t)| ≤ 1 ∧
      |pS (pT g) (s, t)| ≤ 1) :
    ∀ x > 0, ∀ y > 0, |en f g x - en f g y| ≤ 4 * |x - y| := by
  intro x hx y hy
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := en f g) (C := 4)
    (s := Ioi 0) (fun z hz => (en_hasDerivAt hf hg hz).hasDerivWithinAt) ?_ (convex_Ioi 0)
    (show y ∈ Ioi (0:ℝ) from hy) (show x ∈ Ioi (0:ℝ) from hx)
  · simpa [Real.norm_eq_abs] using this
  intro z hz
  rw [Real.norm_eq_abs]
  refine abs_integral_le_const fun t => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hb z hz t
  have k1 : |pT f (z, t) * pS (pT f) (z, t)| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ h1 (abs_nonneg _) h3
  have k2 : |pT g (z, t) * pS (pT g) (z, t)| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ h2 (abs_nonneg _) h4
  have e : 2 * pT f (z, t) * pS (pT f) (z, t) + 2 * pT g (z, t) * pS (pT g) (z, t) =
      2 * (pT f (z, t) * pS (pT f) (z, t)) + 2 * (pT g (z, t) * pS (pT g) (z, t)) := by ring
  rw [e, abs_le]
  constructor <;> linarith [abs_le.1 k1, abs_le.1 k2]

end

/-- The scalar decay lemma, normalized to `s > 0`. -/
theorem decay_normalized (f g : ℝ × ℝ → ℝ) (hf : Sm f) (hg : Sm g) (hpf : Per f) (hpg : Per g)
    (C δ : ℝ) (hδ : 0 < δ)
    (hdbar : ∀ s > 0, ∀ t, |pS f (s, t) - pT g (s, t)| + |pT f (s, t) + pS g (s, t)| ≤
      C * Real.exp (-(δ * s)))
    (hb : ∀ s > 0, ∀ t, |pT f (s, t)| ≤ 1 ∧ |pT g (s, t)| ≤ 1 ∧ |pS (pT f) (s, t)| ≤ 1 ∧
      |pS (pT g) (s, t)| ≤ 1)
    (h0 : ∀ ε > 0, ∃ S, ∀ s ≥ S, ∀ t, |f (s, t)| ≤ ε ∧ |g (s, t)| ≤ ε) :
    ∃ δ' > 0, ∃ C' s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |f (s, t)| ≤ C' * Real.exp (-(δ' * s)) ∧ |g (s, t)| ≤ C' * Real.exp (-(δ' * s)) := by
  -- limits
  have hlim : ∀ φ : ℝ → ℝ → ℝ, (∀ ε > 0, ∃ S, ∀ s ≥ S, ∀ t, |φ s t| ≤ ε) →
      Tendsto (fun s => ∫ t in (0:ℝ)..1, φ s t) atTop (𝓝 0) := by
    intro φ hφ
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨S, hS⟩ := hφ (ε / 2) (by linarith)
    refine ⟨S, fun s hs => ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (abs_integral_le_const fun t => hS s hs t) (by linarith)
  have hmf := mean_bound hf hg hpg (-1) C δ hδ
    (fun s hs t => by
      have := hdbar s hs t
      have := abs_nonneg (pT f (s, t) + pS g (s, t))
      rw [show pS f (s, t) + -1 * pT g (s, t) = pS f (s, t) - pT g (s, t) by ring]; linarith)
    (hlim (fun s t => f (s, t)) fun ε hε => by
      obtain ⟨S, hS⟩ := h0 ε hε; exact ⟨S, fun s hs t => (hS s hs t).1⟩)
  have hmg := mean_bound hg hf hpf 1 C δ hδ
    (fun s hs t => by
      have := hdbar s hs t
      have := abs_nonneg (pS f (s, t) - pT g (s, t))
      rw [show pS g (s, t) + 1 * pT f (s, t) = pT f (s, t) + pS g (s, t) by ring]; linarith)
    (hlim (fun s t => g (s, t)) fun ε hε => by
      obtain ⟨S, hS⟩ := h0 ε hε; exact ⟨S, fun s hs t => (hS s hs t).2⟩)
  -- the action
  have hsq : ∀ s, (C * Real.exp (-(δ * s))) ^ 2 = C ^ 2 * Real.exp (-(2 * δ * s)) := by
    intro s
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  set b' : ℝ → ℝ := fun s => 2 * ∫ t in (0:ℝ)..1,
    (pS f (s, t) * pT g (s, t) - pT f (s, t) * pS g (s, t)) with hb'
  have hbd : ∀ s > 0, HasDerivAt (fun s => 2 * act f g s) (b' s) s := fun s hs =>
    (act_hasDerivAt hf hg hpf hpg hs).const_mul 2
  have hbE : ∀ s > 0, en f g s - C ^ 2 * Real.exp (-(2 * δ * s)) ≤ b' s := by
    intro s hs
    have := act_deriv_ge hf hg hs _ (hdbar s hs)
    rw [hsq] at this
    simp only [hb']
    linarith
  have hb0 : Tendsto (fun s => 2 * act f g s) atTop (𝓝 0) := by
    have : Tendsto (act f g) atTop (𝓝 0) := by
      refine hlim (fun s t => f (s, t) * pT g (s, t)) fun ε hε => ?_
      obtain ⟨S, hS⟩ := h0 ε hε
      refine ⟨max S 1, fun s hs t => ?_⟩
      have hs1 : 0 < s := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hs)
      rw [abs_mul]
      have h1 := (hS s (le_trans (le_max_left _ _) hs) t).1
      have h2 := (hb s hs1 t).2.1
      nlinarith [abs_nonneg (f (s, t)), abs_nonneg (pT g (s, t))]
    simpa using this.const_mul 2
  have h2δ : 0 < 2 * δ := by linarith
  obtain ⟨κ, hκ, C₁, s₁, hC₁⟩ := FiniteEnergyPlane.abs_le_exp_of_deriv_ge_abs_sub
    (fun s => 2 * act f g s) b' 0 (C ^ 2) (2 * δ) h2δ hbd hb0 (fun s hs => by
      have := abs_act_le hf hg hpg hs
      have := hbE s hs
      simp only [abs_mul, abs_two]
      linarith)
  set s₀ := max s₁ 0 with hs₀
  obtain ⟨κ', hκ', C₂, s₂, hC₂⟩ := FiniteEnergyPlane.le_exp_of_deriv_ge_of_lipschitz
    (fun s => 2 * act f g s) b' (en f g) s₀ C₁ κ 4 (C ^ 2) (2 * δ) hκ h2δ
    (fun s hs => hbd s (lt_of_le_of_lt (le_max_right _ _) hs))
    (fun s hs => hC₁ s (le_trans (le_max_left _ _) hs.le))
    (fun x hx y hy => en_lipschitz hf hg hb x (lt_of_le_of_lt (le_max_right _ _) hx) y
      (lt_of_le_of_lt (le_max_right _ _) hy))
    (fun s hs => hbE s (lt_of_le_of_lt (le_max_right _ _) hs))
  -- assemble
  set δ' := min δ (κ' / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  refine ⟨δ', hδ'0, |C| / δ + Real.sqrt C₂, max s₂ 1, fun s hs t => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsp : 0 < s := by linarith
  have hE := hC₂ s (le_trans (le_max_left _ _) hs)
  have hexp : Real.exp (-(κ' * s)) = Real.exp (-(κ' / 2 * s)) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsqrtE : Real.sqrt (en f g s) ≤ Real.sqrt C₂ * Real.exp (-(δ' * s)) := by
    refine (Real.sqrt_le_sqrt hE).trans ?_
    rw [hexp, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by have := min_le_right δ (κ' / 2); nlinarith)) (Real.sqrt_nonneg _)
  have hmexp : ∀ x : ℝ, |x| ≤ C / δ * Real.exp (-(δ * s)) →
      |x| ≤ |C| / δ * Real.exp (-(δ' * s)) := by
    intro x hx
    refine hx.trans ?_
    calc C / δ * Real.exp (-(δ * s)) ≤ |C| / δ * Real.exp (-(δ * s)) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self C) hδ.le)
            (Real.exp_pos _).le
      _ ≤ |C| / δ * Real.exp (-(δ' * s)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by have := min_le_left δ (κ' / 2); nlinarith))
            (div_nonneg (abs_nonneg C) hδ.le)
  have hen : 0 ≤ ∫ x in (0:ℝ)..1, pT g (s, x) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
  have hen' : 0 ≤ ∫ x in (0:ℝ)..1, pT f (s, x) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
  have he : en f g s = (∫ x in (0:ℝ)..1, pT f (s, x) ^ 2) + ∫ x in (0:ℝ)..1, pT g (s, x) ^ 2 :=
    intervalIntegral.integral_add (ii_cont (hf.dT.cont.pow 2) hsp) (ii_cont (hg.dT.cont.pow 2) hsp)
  have hPf : ∫ x in (0:ℝ)..1, |pT f (s, x)| ≤ Real.sqrt (en f g s) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have := sq_integral_abs_le hf.dT.cont hsp
    linarith
  have hPg : ∫ x in (0:ℝ)..1, |pT g (s, x)| ≤ Real.sqrt (en f g s) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have := sq_integral_abs_le hg.dT.cont hsp
    linarith
  have k1 := hmexp _ (hmf s hsp)
  have k2 := hmexp _ (hmg s hsp)
  have l1 := abs_le_mean_add hf hpf hsp t
  have l2 := abs_le_mean_add hg hpg hsp t
  constructor <;> nlinarith

end HCL.KG

/-! Glue for `FiniteEnergyPlane.expDecay_of_dbar_expDecay`: shift the end to `s > 0`. -/


namespace HCL.KG

lemma pT_le (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : |pT u q| ≤ ‖iteratedFDeriv ℝ 1 u q‖ := by
  rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
  refine ((fderiv ℝ u q).le_opNorm _).trans ?_
  simp

lemma pSpT_le {u : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    {q : ℝ × ℝ} (hq : q ∈ U) : |pS (pT u) q| ≤ ‖iteratedFDeriv ℝ 2 u q‖ := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) q := by
    have := (hu.fderiv_of_isOpen hU (m := 1) (WithTop.coe_le_coe.2 le_top)).contDiffAt
      (hU.mem_nhds hq)
    exact this.differentiableAt one_ne_zero
  have e : pS (pT u) q = fderiv ℝ (fderiv ℝ u) q (1, 0) (0, 1) := by
    show fderiv ℝ (fun y => fderiv ℝ u y (0, 1)) q (1, 0) = _
    rw [show (fun y => fderiv ℝ u y (0, 1)) = fun y => (fderiv ℝ u y) ((fun _ => ((0:ℝ), (1:ℝ))) y)
      from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
    simp
  rw [e, ← Real.norm_eq_abs, show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one]
  refine ((fderiv ℝ (fderiv ℝ u) q (1, 0)).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) q).le_opNorm _)
    (norm_nonneg _)).trans ?_
  simp

lemma shift_apply (u : ℝ × ℝ → ℝ) (S s t : ℝ) : u ((s, t) + (S, 0)) = u (s + S, t) := by
  simp

lemma fderiv_shift (u : ℝ × ℝ → ℝ) (S : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (fun x => u (x + (S, 0))) p = fderiv ℝ u (p + (S, 0)) :=
  fderiv_comp_add_right _

lemma pS_shift (u : ℝ × ℝ → ℝ) (S : ℝ) (p : ℝ × ℝ) :
    pS (fun x => u (x + (S, 0))) p = pS u (p + (S, 0)) := by
  simp only [pS, fderiv_shift]

lemma pT_shift (u : ℝ × ℝ → ℝ) (S : ℝ) :
    pT (fun x => u (x + (S, 0))) = fun p => pT u (p + (S, 0)) := by
  funext p; simp only [pT, fderiv_shift]

lemma sm_shift {u : ℝ × ℝ → ℝ} {a S : ℝ} (hu : ContDiffOn ℝ ∞ u (Ioi a ×ˢ univ)) (hS : a ≤ S) :
    Sm fun x => u (x + (S, 0)) := by
  refine hu.comp (contDiff_id.add contDiff_const).contDiffOn ?_
  rintro ⟨s, t⟩ ⟨hs, -⟩
  refine ⟨?_, trivial⟩
  show a < s + S
  have : (0:ℝ) < s := hs
  linarith

end HCL.KG

namespace FiniteEnergyPlane

open HCL HCL.KG

theorem expDecay_of_dbar_expDecay_aux (f g : ℝ × ℝ → ℝ) (hf : TendstoZeroCInfty f)
    (hg : TendstoZeroCInfty g) (δ C s₀ : ℝ) (hδ : 0 < δ)
    (hper : ∀ s ≥ s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (hdbar : ∀ s ≥ s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ δ' > 0, ∃ C' s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |f (s, t)| ≤ C' * Real.exp (-(δ' * s)) ∧ |g (s, t)| ≤ C' * Real.exp (-(δ' * s)) := by
  obtain ⟨⟨af, hcf⟩, hlf⟩ := hf
  obtain ⟨⟨ag, hcg⟩, hlg⟩ := hg
  obtain ⟨b1f, hb1f⟩ := hlf 1 1 one_pos
  obtain ⟨b2f, hb2f⟩ := hlf 2 1 one_pos
  obtain ⟨b1g, hb1g⟩ := hlg 1 1 one_pos
  obtain ⟨b2g, hb2g⟩ := hlg 2 1 one_pos
  set S := max (max (max s₀ af) (max ag b1f)) (max (max b2f b1g) b2g) with hSdef
  have hS : s₀ ≤ S ∧ af ≤ S ∧ ag ≤ S ∧ b1f ≤ S ∧ b2f ≤ S ∧ b1g ≤ S ∧ b2g ≤ S := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hSdef]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hS
  set F : ℝ × ℝ → ℝ := fun x => f (x + (S, 0)) with hF
  set G : ℝ × ℝ → ℝ := fun x => g (x + (S, 0)) with hG
  have hFa : ∀ s t, F (s, t) = f (s + S, t) := fun s t => shift_apply f S s t
  have hGa : ∀ s t, G (s, t) = g (s + S, t) := fun s t => shift_apply g S s t
  have hmem : ∀ {a : ℝ}, a ≤ S → ∀ s > 0, ∀ t : ℝ, ((s, t) + (S, 0) : ℝ × ℝ) ∈ Ioi a ×ˢ univ := by
    intro a ha s hs t
    refine ⟨?_, trivial⟩
    show a < s + S
    linarith
  have hadd : ∀ s t : ℝ, ((s, t) + (S, 0) : ℝ × ℝ) = (s + S, t) := fun s t => by simp
  have hopen : ∀ a : ℝ, IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := fun a => isOpen_Ioi.prod isOpen_univ
  have hcdC : ∀ s > 0, |C * Real.exp (-(δ * (s + S)))| ≤ 0 + |C| * Real.exp (-(δ * S)) * Real.exp (-(δ * s)) := by
    intro s hs
    rw [abs_mul, abs_of_pos (Real.exp_pos _), zero_add, mul_assoc, ← Real.exp_add]
    ring_nf; rfl
  obtain ⟨δ', hδ', C', s₁, hmain⟩ := decay_normalized F G (sm_shift hcf h2) (sm_shift hcg h3)
    (fun s hs t => by rw [hFa, hFa]; exact (hper (s + S) (by linarith) t).1)
    (fun s hs t => by rw [hGa, hGa]; exact (hper (s + S) (by linarith) t).2)
    (|C| * Real.exp (-(δ * S))) δ hδ
    (fun s hs t => by
      have eS : ∀ u : ℝ × ℝ → ℝ, pS (fun x => u (x + (S, 0))) (s, t) = fderiv ℝ u (s + S, t) (1, 0) :=
        fun u => by rw [pS_shift, hadd]; rfl
      have eT : ∀ u : ℝ × ℝ → ℝ, pT (fun x => u (x + (S, 0))) (s, t) = fderiv ℝ u (s + S, t) (0, 1) :=
        fun u => by rw [pT_shift]; show pT u ((s, t) + (S, 0)) = _; rw [hadd]; rfl
      rw [hF, hG, eS f, eT g, eT f, eS g]
      have k := hdbar (s + S) (by linarith) t
      have := hcdC s hs
      rw [zero_add] at this
      exact k.trans ((le_abs_self _).trans this))
    (fun s hs t => by
      simp only [hF, hG, pT_shift]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hadd]; exact (pT_le f _).trans (hb1f _ (by linarith) t)
      · rw [hadd]; exact (pT_le g _).trans (hb1g _ (by linarith) t)
      · rw [pS_shift, hadd]
        exact (pSpT_le (hopen af) hcf (by rw [← hadd]; exact hmem h2 s hs t)).trans
          (hb2f _ (by linarith) t)
      · rw [pS_shift, hadd]
        exact (pSpT_le (hopen ag) hcg (by rw [← hadd]; exact hmem h3 s hs t)).trans
          (hb2g _ (by linarith) t))
    (fun ε hε => by
      obtain ⟨c1, hc1⟩ := hlf 0 ε hε
      obtain ⟨c2, hc2⟩ := hlg 0 ε hε
      refine ⟨max c1 c2 - S, fun s hs t => ?_⟩
      rw [hFa, hGa]
      have k1 := hc1 (s + S) (by have := le_max_left c1 c2; linarith) t
      have k2 := hc2 (s + S) (by have := le_max_right c1 c2; linarith) t
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at k1 k2
      exact ⟨k1, k2⟩)
  refine ⟨δ', hδ', |C'| * Real.exp (δ' * S), s₁ + S, fun s hs t => ?_⟩
  obtain ⟨k1, k2⟩ := hmain (s - S) (by linarith) t
  rw [hFa, sub_add_cancel] at k1
  rw [hGa, sub_add_cancel] at k2
  have e : |C'| * Real.exp (δ' * S) * Real.exp (-(δ' * s)) = |C'| * Real.exp (-(δ' * (s - S))) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hle : C' * Real.exp (-(δ' * (s - S))) ≤ |C'| * Real.exp (-(δ' * (s - S))) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  rw [e]
  exact ⟨k1.trans hle, k2.trans hle⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (f g : ℝ × ℝ → ℝ) (hf : TendstoZeroCInfty f)
    (hg : TendstoZeroCInfty g) (δ C s₀ : ℝ) (hδ : 0 < δ)
    (hper : ∀ s ≥ s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (hdbar : ∀ s ≥ s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ δ' > 0, ∃ C' s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |f (s, t)| ≤ C' * Real.exp (-(δ' * s)) ∧ |g (s, t)| ≤ C' * Real.exp (-(δ' * s)) :=
  expDecay_of_dbar_expDecay_aux f g hf hg δ C s₀ hδ hper hdbar
