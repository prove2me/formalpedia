-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen_L2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T22:48:58.34927+00:00
-- url     : https://prove2.me/submissions/a2077e90-ec1b-46ba-b46d-532d9253a300

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_tendsto_rayleigh
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoUniformly_isLoopEigen

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

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

/-! Residual of the normalized slices, good points, and uniform-to-`L²` convergence. -/


namespace HCL

variable {n : ℕ}

/-- a good point in a unit window -/
lemma exists_le_integral {q : ℝ → ℝ} {a : ℝ} (hq : ContinuousOn q (Icc a (a + 1))) :
    ∃ c ∈ Icc a (a + 1), q c ≤ ∫ x in a..a + 1, q x := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hq
  refine ⟨c, hc, ?_⟩
  have h := intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1)
    (intervalIntegrable_const (μ := volume) (c := q c))
    (hq.intervalIntegrable_of_Icc (by linarith)) (fun x hx => hmin hx)
  rw [intervalIntegral.integral_const, smul_eq_mul, show a + 1 - a = 1 by ring, one_mul] at h
  exact h

lemma tendsto_integral_sq_of_tendstoUniformly {f : ℕ → ℝ → Vec n} {e : ℝ → Vec n}
    (hf : ∀ k, Continuous (f k)) (he : Continuous e) (h : TendstoUniformly f e atTop) :
    Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Metric.tendstoUniformly_iff.1 h) (Real.sqrt (ε / 2)) (Real.sqrt_pos.2 (by linarith)))
  refine ⟨N, fun k hk => ?_⟩
  have hb : ∀ t, ‖f k t - e t‖ ^ 2 ≤ ε / 2 := fun t => by
    have h1 := hN k hk t
    rw [dist_eq_norm, norm_sub_rev] at h1
    have h0 := norm_nonneg (f k t - e t)
    calc ‖f k t - e t‖ ^ 2 ≤ Real.sqrt (ε / 2) ^ 2 := by gcongr
      _ = ε / 2 := Real.sq_sqrt (by linarith)
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity
  have h1 : ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2 ≤ ε / 2 := by
    have h2 := intervalIntegral.integral_mono_on zero_le_one
      ((((hf k).sub he).norm.pow 2).intervalIntegrable _ _) (intervalIntegrable_const (μ := volume) (c := ε / 2))
      (fun t _ => hb t)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at h2
    exact h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- uniform smallness of `S - S∞` -/
lemma op_tendsto {S : ℝ × ℝ → Mat n} {Sinf : ℝ → Mat n}
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf) :
    ∀ η > 0, ∃ s₁, ∀ s ≥ s₁, ∀ t, ‖TL n (S (s, t) - Sinf t)‖ ≤ η := by
  intro η hη
  obtain ⟨c, hc, hop⟩ := op_small (n := n)
  have h : ∀ i j, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, |S (s, t) i j - Sinf t i j| ≤ η / c := by
    intro i j
    obtain ⟨s₁, hs₁⟩ := (hSas i j).2 0 (η / c) (by positivity)
    refine ⟨s₁, fun s hs t => ?_⟩
    have := hs₁ s hs t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  choose sij hsij using h
  refine ⟨∑ i, ∑ j, |sij i j|, fun s hs t => ?_⟩
  have hle : ∀ i j, sij i j ≤ ∑ i, ∑ j, |sij i j| := fun i j =>
    (le_abs_self _).trans <|
      (Finset.single_le_sum (f := fun j => |sij i j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |sij i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have := hop (S (s, t) - Sinf t) (η / c) (by positivity) fun i j => by
    rw [Matrix.sub_apply]; exact hsij i j s ((hle i j).trans hs) t
  calc ‖TL n (S (s, t) - Sinf t)‖ ≤ c * (η / c) := this
    _ = η := by field_simp

/-- pointwise residual identity -/
lemma res_eq {S : ℝ × ℝ → Mat n} {Sinf : ℝ → Mat n} {ζ : ℝ × ℝ → Vec n}
    {s t : ℝ} (hcr : crOp S ζ (s, t) = 0) (c α μ : ℝ) :
    -(Matrix.toEuclideanLin (J₀ n) (c • pT ζ (s, t))) -
        Matrix.toEuclideanLin (Sinf t) (c • ζ (s, t)) - μ • (c • ζ (s, t)) =
      c • ((pS ζ (s, t) - α • ζ (s, t)) + (α - μ) • ζ (s, t) +
        TL n (S (s, t) - Sinf t) (ζ (s, t))) := by
  have hJ : Matrix.toEuclideanLin (J₀ n) (pT ζ (s, t)) =
      -(pS ζ (s, t)) - Matrix.toEuclideanLin (S (s, t)) (ζ (s, t)) := by
    have h : pS ζ (s, t) + Matrix.toEuclideanLin (J₀ n) (pT ζ (s, t)) +
        Matrix.toEuclideanLin (S (s, t)) (ζ (s, t)) = 0 := hcr
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h]
    abel
  rw [map_smul, map_smul, hJ, TL_apply, map_sub, LinearMap.sub_apply]
  module

/-- pointwise residual bound -/
lemma res_pt {S : ℝ × ℝ → Mat n} {Sinf : ℝ → Mat n} {ζ : ℝ × ℝ → Vec n}
    {s t : ℝ} (hcr : crOp S ζ (s, t) = 0) (c α μ η : ℝ)
    (hSη : ‖TL n (S (s, t) - Sinf t)‖ ≤ η) (hη : 0 ≤ η) :
    ‖-(Matrix.toEuclideanLin (J₀ n) (c • pT ζ (s, t))) -
        Matrix.toEuclideanLin (Sinf t) (c • ζ (s, t)) - μ • (c • ζ (s, t))‖ ^ 2 ≤
      3 * c ^ 2 * (‖pS ζ (s, t) - α • ζ (s, t)‖ ^ 2 +
        ((α - μ) ^ 2 + η ^ 2) * ‖ζ (s, t)‖ ^ 2) := by
  rw [res_eq hcr c α μ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  generalize hA : pS ζ (s, t) - α • ζ (s, t) = a
  generalize hz : ζ (s, t) = z
  generalize hD : TL n (S (s, t) - Sinf t) = D at hSη
  have hdn : ‖D z‖ ≤ η * ‖z‖ :=
    (D.le_opNorm z).trans (mul_le_mul_of_nonneg_right hSη (norm_nonneg _))
  have hbn : ‖(α - μ) • z‖ ^ 2 = (α - μ) ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h3 : ‖a + (α - μ) • z + D z‖ ^ 2 ≤
      3 * (‖a‖ ^ 2 + ‖(α - μ) • z‖ ^ 2 + ‖D z‖ ^ 2) := by
    have := norm_add₃_le (a := a) (b := (α - μ) • z) (c := D z)
    have h0 := norm_nonneg (a + (α - μ) • z + D z)
    nlinarith [sq_nonneg (‖a‖ - ‖(α - μ) • z‖), sq_nonneg (‖(α - μ) • z‖ - ‖D z‖),
      sq_nonneg (‖a‖ - ‖D z‖), norm_nonneg a, norm_nonneg ((α - μ) • z), norm_nonneg (D z)]
  have hd2 : ‖D z‖ ^ 2 ≤ η ^ 2 * ‖z‖ ^ 2 := by
    have := norm_nonneg (D z)
    calc ‖D z‖ ^ 2 ≤ (η * ‖z‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  calc c ^ 2 * ‖a + (α - μ) • z + D z‖ ^ 2
      ≤ c ^ 2 * (3 * (‖a‖ ^ 2 + ‖(α - μ) • z‖ ^ 2 + ‖D z‖ ^ 2)) := by gcongr
    _ ≤ 3 * c ^ 2 * (‖a‖ ^ 2 + ((α - μ) ^ 2 + η ^ 2) * ‖z‖ ^ 2) := by
      rw [hbn]; nlinarith

/-- the residual of a normalized slice -/
lemma res_bound {S : ℝ × ℝ → Mat n} {Sinf : ℝ → Mat n} {ζ : ℝ × ℝ → Vec n} (hSm : Sm ζ)
    (hSinf : Continuous Sinf)
    (hcr : ∀ s > 0, ∀ t : ℝ, crOp S ζ (s, t) = 0) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s)
    (μ η : ℝ) (hη : 0 ≤ η) (hSη : ∀ t, ‖TL n (S (s, t) - Sinf t)‖ ≤ η) :
    ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (J₀ n) ((Real.sqrt (Fz ζ s))⁻¹ • pT ζ (s, t))) -
        Matrix.toEuclideanLin (Sinf t) (vz ζ s t) - μ • vz ζ s t‖ ^ 2 ≤
      3 * (qz ζ s + (αz ζ s - μ) ^ 2 + η ^ 2) := by
  have hc2 : (Real.sqrt (Fz ζ s))⁻¹ ^ 2 = (Fz ζ s)⁻¹ := by rw [inv_pow, Real.sq_sqrt hF.le]
  have c1 := cont_slice hSm.cont hs
  have c2 := cont_slice hSm.dS.cont hs
  have c3 := cont_slice hSm.dT.cont hs
  have hv : Continuous fun t => vz ζ s t := by
    unfold vz; exact (continuous_const (y := (Real.sqrt (Fz ζ s))⁻¹)).smul c1
  have hSc : Continuous fun t => Matrix.toEuclideanLin (Sinf t) (vz ζ s t) := by
    show Continuous fun t => TL n (Sinf t) (vz ζ s t)
    exact ((TL n).continuous.comp hSinf).clm_apply hv
  have hlc : Continuous fun t =>
      ‖-(Matrix.toEuclideanLin (J₀ n) ((Real.sqrt (Fz ζ s))⁻¹ • pT ζ (s, t))) -
        Matrix.toEuclideanLin (Sinf t) (vz ζ s t) - μ • vz ζ s t‖ ^ 2 :=
    ((((Matrix.toEuclideanLin (J₀ n)).continuous_of_finiteDimensional.comp
      ((continuous_const (y := (Real.sqrt (Fz ζ s))⁻¹)).smul c3)).neg.sub hSc).sub
      ((continuous_const (y := μ)).smul hv)).norm.pow 2
  have i1 : IntervalIntegrable (fun t => ‖pS ζ (s, t) - αz ζ s • ζ (s, t)‖ ^ 2) volume 0 1 :=
    ((c2.sub ((continuous_const (y := αz ζ s)).smul c1)).norm.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => ((αz ζ s - μ) ^ 2 + η ^ 2) * ‖ζ (s, t)‖ ^ 2) volume 0 1 :=
    ((continuous_const (y := (αz ζ s - μ) ^ 2 + η ^ 2)).mul (c1.norm.pow 2)).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on zero_le_one (hlc.intervalIntegrable _ _)
    ((i1.add i2).const_mul (3 * (Real.sqrt (Fz ζ s))⁻¹ ^ 2))
    fun t _ => res_pt (hcr s hs t) _ (αz ζ s) μ η (hSη t) hη).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, integral_norm_sub_sq hSm hs hF]
  change 3 * (Real.sqrt (Fz ζ s))⁻¹ ^ 2 * (Fz ζ s * qz ζ s + ((αz ζ s - μ) ^ 2 + η ^ 2) * Fz ζ s) = _
  rw [hc2]
  field_simp
  ring

end HCL

namespace FiniteEnergyPlane

open HCL

theorem halfCyl_exists_subseq_tendsto_eigen_L2_aux {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ : ℝ, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
          Tendsto (fun k : ℕ => ∫ t in (0:ℝ)..1,
            ‖(Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t) - e t‖ ^ 2)
            atTop (𝓝 0) := by
  obtain ⟨μ, hμ, s₀, hs₀, hFpos, hα, hwin⟩ := halfCyl_exists_tendsto_rayleigh S hS hSper Sinf
    hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth
  refine ⟨μ, hμ, s₀, hFpos, fun σ hσ => ?_⟩
  have hSm : Sm ζ := hζ.1
  have hF : ∀ s ≥ s₀, 0 < Fz ζ s := hFpos
  have hα' : Tendsto (αz ζ) atTop (𝓝 μ) := hα
  have hwin' : Tendsto (fun s => ∫ x in s..s + 1, qz ζ x) atTop (𝓝 0) := hwin
  -- good points in the windows `[τ k, τ k + 1]`
  set τ : ℕ → ℝ := fun k => max (σ k) s₀ with hτdef
  have hτ : Tendsto τ atTop atTop := tendsto_atTop_mono (fun k => le_max_left _ _) hσ
  have hgood : ∀ k, ∃ c ∈ Icc (τ k) (τ k + 1), qz ζ c ≤ ∫ x in τ k..τ k + 1, qz ζ x :=
    fun k => exists_le_integral ((qz_cont hSm hs₀ hF).mono fun x hx =>
      le_trans (le_max_right _ _) (show τ k ≤ x from hx.1))
  choose s' hs'mem hs'q using hgood
  have hs'0 : ∀ k, s₀ ≤ s' k := fun k => le_trans (le_max_right _ _) (hs'mem k).1
  have hs'pos : ∀ k, 0 < s' k := fun k => lt_of_lt_of_le hs₀ (hs'0 k)
  have hs'top : Tendsto s' atTop atTop := tendsto_atTop_mono (fun k => (hs'mem k).1) hτ
  have hI : Tendsto (fun k => ∫ x in τ k..τ k + 1, qz ζ x) atTop (𝓝 0) := hwin'.comp hτ
  have hqk : Tendsto (fun k => qz ζ (s' k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => qz_nonneg hSm (hs'pos k) (hF _ (hs'0 k))) hs'q hI
  have hαk : Tendsto (fun k => αz ζ (s' k)) atTop (𝓝 μ) := hα'.comp hs'top
  -- the normalized slices at the good points
  set f : ℕ → ℝ → Vec n := fun k t => vz ζ (s' k) t with hfdef
  set f' : ℕ → ℝ → Vec n := fun k t => (Real.sqrt (Fz ζ (s' k)))⁻¹ • pT ζ (s' k, t) with hf'def
  have hf : ∀ k t, HasDerivAt (f k) (f' k t) t := fun k t => by
    show HasDerivAt (fun τ => (Real.sqrt (Fz ζ (s' k)))⁻¹ • ζ (s' k, τ))
      ((Real.sqrt (Fz ζ (s' k)))⁻¹ • pT ζ (s' k, t)) t
    exact (hSm.hasDerivAt_t (t := t) (hs'pos k)).const_smul ((Real.sqrt (Fz ζ (s' k)))⁻¹)
  have hf' : ∀ k, Continuous (f' k) := fun k =>
    (continuous_const (y := (Real.sqrt (Fz ζ (s' k)))⁻¹)).smul (cont_slice hSm.dT.cont (hs'pos k))
  have hper : ∀ k, Function.Periodic (f k) 1 := fun k t => by
    simp only [hfdef, vz, hζ.2.1]
  have hnorm : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 = 1 := fun k =>
    integral_norm_vz_sq (hF _ (hs'0 k))
  -- the residuals tend to zero
  have hres : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      ‖-(Matrix.toEuclideanLin (J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2) atTop (𝓝 0) := by
    have hB : Tendsto (fun k => 3 * (qz ζ (s' k) + (αz ζ (s' k) - μ) ^ 2)) atTop (𝓝 0) := by
      have := (hqk.add ((hαk.sub_const μ).pow 2)).const_mul 3
      simpa using this
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨s₁, hs₁⟩ := op_tendsto hSas (Real.sqrt (ε / 6)) (Real.sqrt_pos.2 (by linarith))
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hB) (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hs'top.eventually_ge_atTop s₁)
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    have hb := res_bound hSm hSinf.1 hζ.2.2 (hs'pos k) (hF _ (hs'0 k)) μ (Real.sqrt (ε / 6))
      (Real.sqrt_nonneg _) (hs₁ (s' k) (hN₂ k (le_of_max_le_right hk)))
    have hB' := hN₁ k (le_of_max_le_left hk)
    rw [Real.dist_eq, sub_zero] at hB' ⊢
    have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity
    rw [abs_of_nonneg h0]
    have hsq : Real.sqrt (ε / 6) ^ 2 = ε / 6 := Real.sq_sqrt (by linarith)
    have habs := le_abs_self (3 * (qz ζ (s' k) + (αz ζ (s' k) - μ) ^ 2))
    have hb' : ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2 ≤
        3 * (qz ζ (s' k) + (αz ζ (s' k) - μ) ^ 2 + Real.sqrt (ε / 6) ^ 2) := hb
    rw [hsq] at hb'
    linarith
  -- compactness
  obtain ⟨φ, hφ, e, he, hunif⟩ := exists_subseq_tendstoUniformly_isLoopEigen Sinf hSinf hSinf' μ
    f f' hf hf' hper hnorm hres
  refine ⟨φ, hφ, e, he, ?_⟩
  have hU : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f (φ k) t - e t‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_sq_of_tendstoUniformly (fun k => vz_slice_cont hSm (hs'pos (φ k)))
      he.1.continuous hunif
  have hIφ := hI.comp hφ.tendsto_atTop
  have hB : Tendsto (fun k => 2 * (∫ x in τ (φ k)..τ (φ k) + 1, qz ζ x) +
      2 * ∫ t in (0:ℝ)..1, ‖f (φ k) t - e t‖ ^ 2) atTop (𝓝 0) := by
    have := (hIφ.const_mul 2).add (hU.const_mul 2)
    simpa using this
  have hev : ∀ᶠ k in atTop, s₀ ≤ σ (φ k) :=
    (hσ.comp hφ.tendsto_atTop).eventually_ge_atTop s₀
  refine squeeze_zero' (Eventually.of_forall fun k =>
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity) ?_ hB
  filter_upwards [hev] with k hk
  -- here `τ (φ k) = σ (φ k)`
  have hτk : τ (φ k) = σ (φ k) := max_eq_left hk
  set a := σ (φ k)
  set b := s' (φ k)
  have hab : a ≤ b := hτk ▸ (hs'mem (φ k)).1
  have hb1 : b ≤ a + 1 := hτk ▸ (hs'mem (φ k)).2
  have hapos : 0 < a := lt_of_lt_of_le hs₀ hk
  have hd := disp hSm hs₀ hF hk hab
  -- `∫ₐᵇ q ≤ ∫ₐ^{a+1} q`
  have hq0 : ∀ x ≥ s₀, 0 ≤ qz ζ x := fun x hx => qz_nonneg hSm (lt_of_lt_of_le hs₀ hx) (hF x hx)
  have hqi : IntervalIntegrable (qz ζ) volume a (a + 1) :=
    ((qz_cont hSm hs₀ hF).mono fun x hx => le_trans hk
      (show a ≤ x by rw [uIcc_of_le (by linarith)] at hx; exact hx.1)).intervalIntegrable
  have hmono : ∫ x in a..b, qz ζ x ≤ ∫ x in a..a + 1, qz ζ x :=
    intervalIntegral.integral_mono_interval le_rfl hab hb1
      ((ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun x hx => hq0 x (le_trans hk (le_of_lt hx.1))))
      hqi
  have hab0 : 0 ≤ ∫ x in a..b, qz ζ x :=
    intervalIntegral.integral_nonneg hab fun x hx => hq0 x (le_trans hk hx.1)
  have hdisp : ∫ t in (0:ℝ)..1, ‖vz ζ b t - vz ζ a t‖ ^ 2 ≤ ∫ x in a..a + 1, qz ζ x := by
    refine hd.trans ?_
    nlinarith
  -- triangle inequality in `L²`
  have hva := vz_slice_cont hSm hapos
  have hvb := vz_slice_cont hSm (hs'pos (φ k))
  have hec := he.1.continuous
  have hpt : ∀ t, ‖vz ζ a t - e t‖ ^ 2 ≤
      2 * ‖vz ζ b t - vz ζ a t‖ ^ 2 + 2 * ‖f (φ k) t - e t‖ ^ 2 := by
    intro t
    have h1 : ‖vz ζ a t - e t‖ ≤ ‖vz ζ b t - vz ζ a t‖ + ‖f (φ k) t - e t‖ := by
      calc ‖vz ζ a t - e t‖ = ‖(vz ζ a t - vz ζ b t) + (vz ζ b t - e t)‖ := by abel_nf
        _ ≤ ‖vz ζ a t - vz ζ b t‖ + ‖vz ζ b t - e t‖ := norm_add_le _ _
        _ = ‖vz ζ b t - vz ζ a t‖ + ‖f (φ k) t - e t‖ := by rw [norm_sub_rev]
    have h0 := norm_nonneg (vz ζ a t - e t)
    nlinarith [sq_nonneg (‖vz ζ b t - vz ζ a t‖ - ‖f (φ k) t - e t‖),
      norm_nonneg (vz ζ b t - vz ζ a t), norm_nonneg (f (φ k) t - e t)]
  have i1 : IntervalIntegrable (fun t => ‖vz ζ b t - vz ζ a t‖ ^ 2) volume 0 1 :=
    ((hvb.sub hva).norm.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => ‖f (φ k) t - e t‖ ^ 2) volume 0 1 :=
    ((hvb.sub hec).norm.pow 2).intervalIntegrable _ _
  have hint : ∫ t in (0:ℝ)..1, ‖vz ζ a t - e t‖ ^ 2 ≤
      ∫ t in (0:ℝ)..1, (2 * ‖vz ζ b t - vz ζ a t‖ ^ 2 + 2 * ‖f (φ k) t - e t‖ ^ 2) :=
    intervalIntegral.integral_mono_on zero_le_one
      (((hva.sub hec).norm.pow 2).intervalIntegrable _ _) ((i1.const_mul 2).add (i2.const_mul 2))
      fun t _ => hpt t
  have hsplit : ∫ t in (0:ℝ)..1, (2 * ‖vz ζ b t - vz ζ a t‖ ^ 2 + 2 * ‖f (φ k) t - e t‖ ^ 2) =
      2 * (∫ t in (0:ℝ)..1, ‖vz ζ b t - vz ζ a t‖ ^ 2) +
        2 * (∫ t in (0:ℝ)..1, ‖f (φ k) t - e t‖ ^ 2) := by
    rw [intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have : ∫ t in (0:ℝ)..1,
      ‖(Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t) - e t‖ ^ 2 =
      ∫ t in (0:ℝ)..1, ‖vz ζ a t - e t‖ ^ 2 := rfl
  rw [this, hτk]
  rw [hsplit] at hint
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ : ℝ, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
          Tendsto (fun k : ℕ => ∫ t in (0:ℝ)..1,
            ‖(Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t) - e t‖ ^ 2)
            atTop (𝓝 0) :=
  FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen_L2_aux S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth
