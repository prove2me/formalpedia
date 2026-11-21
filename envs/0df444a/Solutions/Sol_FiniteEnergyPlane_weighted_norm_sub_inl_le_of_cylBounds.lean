-- Prove2me | solution 1 for FiniteEnergyPlane.weighted_norm_sub_inl_le_of_cylBounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T09:26:16.759779+00:00
-- url     : https://prove2.me/submissions/037f2be9-f71f-4dd8-bd9e-07b0da2a8bc8

import Mathlib



/-!
# A1, abstract part: a two-point lower bound on a thin tube from cylindrical bounds

`F : ℂ × ℂ → E` smooth on `ℂ × ball 0 ρ₀`, with first and second derivatives bounded in the
cylindrical weight `‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖` on `ℂ × closedBall 0 ρ'`, a weighted lower bound
of `F(·, 0)` and of `DF(·, 0)`. Then `F` satisfies a weighted two-point lower bound on
`ℂ × ball 0 ρ` for some `ρ > 0`.
-/

namespace FiniteEnergyPlane

namespace DGA1

open Metric Set Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma taylor_01 {φ φ' φ'' : ℝ → E} {K : ℝ}
    (h1 : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' τ) τ)
    (h2 : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ' (φ'' τ) τ)
    (hK : ∀ τ ∈ Icc (0 : ℝ) 1, ‖φ'' τ‖ ≤ K) :
    ‖φ 1 - φ 0 - φ' 0‖ ≤ K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  have hd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖φ' τ - φ' 0‖ ≤ K := by
    intro τ hτ
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ') (a := 0) (b := 1)
      (fun x hx => (h2 x hx).hasDerivWithinAt) (fun x hx => hK x (Ico_subset_Icc_self hx)) τ hτ
    calc ‖φ' τ - φ' 0‖ ≤ K * (τ - 0) := this
      _ ≤ K * 1 := by apply mul_le_mul_of_nonneg_left _ hK0; linarith [hτ.2]
      _ = K := mul_one K
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun τ => φ τ - τ • φ' 0)
    (f' := fun τ => φ' τ - φ' 0) (C := K)
    (fun x hx => (((h1 x hx).sub ((hasDerivAt_id x).smul_const (φ' 0))).congr_deriv
      (by simp)).hasDerivWithinAt)
    (fun x hx => hd x (Ico_subset_Icc_self hx))
  have e : (φ 1 - (1 : ℝ) • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0) = φ 1 - φ 0 - φ' 0 := by
    simp only [one_smul, zero_smul, sub_zero]
    abel
  simpa only [e] using key

/-- Weights along a short segment are comparable. -/
lemma wt_seg {z z' : ℂ} {θ : ℝ} (hθ : θ ≤ 1 / 4) (hX : ‖z - z'‖ ≤ θ * (1 + ‖z‖ + ‖z'‖))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    1 + ‖z‖ + ‖z'‖ ≤ 4 * (1 + ‖z + τ • (z' - z)‖) := by
  have h1 : ‖z‖ - ‖z - z'‖ ≤ ‖z + τ • (z' - z)‖ := by
    have : ‖τ • (z' - z)‖ ≤ ‖z - z'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
    have := norm_sub_norm_le z (-(τ • (z' - z)))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have h2 : ‖z'‖ - ‖z - z'‖ ≤ ‖z + τ • (z' - z)‖ := by
    have e : z + τ • (z' - z) = z' + (1 - τ) • (z - z') := by
      rw [sub_smul, one_smul, smul_sub, smul_sub]; abel
    have : ‖(1 - τ) • (z - z')‖ ≤ ‖z - z'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2])]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hτ.1])
    have := norm_sub_norm_le z' (-((1 - τ) • (z - z')))
    rw [sub_neg_eq_add, norm_neg] at this
    rw [e]
    linarith
  have hS : 0 ≤ 1 + ‖z‖ + ‖z'‖ := by positivity
  have h3 : θ * (1 + ‖z‖ + ‖z'‖) ≤ 1 / 4 * (1 + ‖z‖ + ‖z'‖) := mul_le_mul_of_nonneg_right hθ hS
  linarith

section tube

variable {F : ℂ × ℂ → E} {ρ₀ : ℝ}

lemma isOpen_tube (ρ : ℝ) : IsOpen ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
  isOpen_univ.prod isOpen_ball

lemma hasFDerivAt_of_mem (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) {x : ℂ × ℂ}
    (hx : x ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀) : HasFDerivAt F (fderiv ℝ F x) x :=
  ((hF.contDiffAt ((isOpen_tube ρ₀).mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt

lemma hasFDerivAt_fderiv_of_mem (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    {x : ℂ × ℂ} (hx : x ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀) :
    HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
  (((hF.contDiffAt ((isOpen_tube ρ₀).mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt

lemma hasDerivAt_path (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (p v : ℂ × ℂ)
    {τ : ℝ} (hm : p + τ • v ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀) :
    HasDerivAt (fun τ : ℝ => F (p + τ • v)) (fderiv ℝ F (p + τ • v) v) τ := by
  have hγ : HasDerivAt (fun τ : ℝ => p + τ • v) v τ := by
    simpa using ((hasDerivAt_id τ).smul_const v).const_add p
  exact (hasFDerivAt_of_mem hF hm).comp_hasDerivAt τ hγ

lemma hasDerivAt_path_d (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (p v k : ℂ × ℂ)
    {τ : ℝ} (hm : p + τ • v ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀) :
    HasDerivAt (fun τ : ℝ => fderiv ℝ F (p + τ • v) k)
      (fderiv ℝ (fderiv ℝ F) (p + τ • v) v k) τ := by
  have hγ : HasDerivAt (fun τ : ℝ => p + τ • v) v τ := by
    simpa using ((hasDerivAt_id τ).smul_const v).const_add p
  have h := (hasFDerivAt_fderiv_of_mem hF hm).comp_hasDerivAt τ hγ
  exact (h.clm_apply (hasDerivAt_const τ k)).congr_deriv (by simp)

lemma mem_vert {ρ' : ℝ} (hρ : ρ' < ρ₀) {ζ w : ℂ} (hw : ‖w‖ ≤ ρ') {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ((ζ, 0) + τ • ((0 : ℂ), w)) ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀ ∧
      ((ζ, 0) + τ • ((0 : ℂ), w)) = (ζ, τ • w) ∧ ‖τ • w‖ ≤ ρ' := by
  have e : ((ζ, 0) + τ • ((0 : ℂ), w)) = (ζ, τ • w) := by ext <;> simp
  have hn : ‖τ • w‖ ≤ ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
  refine ⟨?_, e, hn.trans hw⟩
  rw [e]
  exact ⟨Set.mem_univ _, mem_ball_zero_iff.2 (lt_of_le_of_lt (hn.trans hw) hρ)⟩

variable {ρ' C : ℝ}

/-- `F` is Lipschitz in `w` with the cylindrical constant. -/
lemma norm_sub_vert_le (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (hρ : ρ' < ρ₀)
    (hC1 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h : ℂ × ℂ,
      ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖))
    (ζ w : ℂ) (hw : ‖w‖ ≤ ρ') : ‖F (ζ, w) - F (ζ, 0)‖ ≤ C * ‖w‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun τ : ℝ => F ((ζ, 0) + τ • ((0 : ℂ), w)))
    (f' := fun τ => fderiv ℝ F ((ζ, 0) + τ • ((0 : ℂ), w)) ((0 : ℂ), w)) (C := C * ‖w‖)
    (fun x hx => (hasDerivAt_path hF _ _ (mem_vert hρ hw hx).1).hasDerivWithinAt)
    (fun x hx => by
      obtain ⟨-, e, hn⟩ := mem_vert (ζ := ζ) hρ hw (Ico_subset_Icc_self hx)
      simp only [e]
      have := hC1 ζ (x • w) (mem_closedBall_zero_iff.2 hn) ((0 : ℂ), w)
      simpa using this)
  have e1 : ((ζ, 0) + (1 : ℝ) • ((0 : ℂ), w)) = (ζ, w) := by ext <;> simp
  have e0 : ((ζ, 0) + (0 : ℝ) • ((0 : ℂ), w)) = (ζ, 0) := by ext <;> simp
  simpa only [e1, e0] using key

/-- The derivative moves by at most `C ‖w‖` in the weighted norm. -/
lemma norm_fderiv_sub_vert_le (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    (hρ : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (ζ w : ℂ) (hw : ‖w‖ ≤ ρ') (h : ℂ × ℂ) :
    ‖fderiv ℝ F (ζ, w) h - fderiv ℝ F (ζ, 0) h‖ ≤ C * ‖w‖ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun τ : ℝ => fderiv ℝ F ((ζ, 0) + τ • ((0 : ℂ), w)) h)
    (f' := fun τ => fderiv ℝ (fderiv ℝ F) ((ζ, 0) + τ • ((0 : ℂ), w)) ((0 : ℂ), w) h)
    (C := C * ‖w‖ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖))
    (fun x hx => (hasDerivAt_path_d hF _ _ h (mem_vert hρ hw hx).1).hasDerivWithinAt)
    (fun x hx => by
      obtain ⟨-, e, hn⟩ := mem_vert (ζ := ζ) hρ hw (Ico_subset_Icc_self hx)
      simp only [e]
      have := hC2 ζ (x • w) (mem_closedBall_zero_iff.2 hn) ((0 : ℂ), w) h
      simpa using this)
  have e1 : ((ζ, 0) + (1 : ℝ) • ((0 : ℂ), w)) = (ζ, w) := by ext <;> simp
  have e0 : ((ζ, 0) + (0 : ℝ) • ((0 : ℂ), w)) = (ζ, 0) := by ext <;> simp
  simpa only [e1, e0] using key

/-- Second-order Taylor remainder along a short segment in the tube. -/
lemma taylor_seg (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (hρ : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (hC : 0 ≤ C) {θ : ℝ} (hθ : θ ≤ 1 / 4) {ρ : ℝ} (hρρ : ρ ≤ ρ')
    {p q : ℂ × ℂ} (hp : p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) (hq : q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ)
    (hX : ‖p.1 - q.1‖ ≤ θ * (1 + ‖p.1‖ + ‖q.1‖)) :
    ‖F q - F p - fderiv ℝ F p (q - p)‖ ≤
      C * (4 * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖)) + ‖p.2 - q.2‖) ^ 2 := by
  have hconv : Convex ℝ ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
    (convex_univ (𝕜 := ℝ) (E := ℂ)).prod (convex_ball (0 : ℂ) ρ)
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, p + τ • (q - p) ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ :=
    fun τ hτ => hconv.add_smul_sub_mem hp hq hτ
  have hsub : (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ ⊆ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀ :=
    Set.prod_mono le_rfl (ball_subset_ball (hρρ.trans hρ.le))
  set X := ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖)
  set Y := ‖p.2 - q.2‖
  have hbd : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ F) (p + τ • (q - p)) (q - p) (q - p)‖ ≤ C * (4 * X + Y) ^ 2 := by
    intro τ hτ
    have hm := hseg τ hτ
    set ζ := (p + τ • (q - p)).1
    have hw : (p + τ • (q - p)).2 ∈ closedBall (0 : ℂ) ρ' :=
      ball_subset_closedBall (ball_subset_ball hρρ hm.2)
    have h := hC2 ζ (p + τ • (q - p)).2 hw (q - p) (q - p)
    have hpe : ((ζ, (p + τ • (q - p)).2) : ℂ × ℂ) = p + τ • (q - p) := rfl
    rw [hpe] at h
    have hζ : ζ = p.1 + τ • (q.1 - p.1) := by simp [ζ]
    have hwt : ‖(q - p).1‖ / (1 + ‖ζ‖) + ‖(q - p).2‖ ≤ 4 * X + Y := by
      have hS := wt_seg hθ hX hτ
      rw [← hζ] at hS
      have hpos : 0 < 1 + ‖ζ‖ := by positivity
      have hpos' : 0 < 1 + ‖p.1‖ + ‖q.1‖ := by positivity
      have e1 : ‖(q - p).1‖ = ‖p.1 - q.1‖ := by simp [norm_sub_rev]
      have e2 : ‖(q - p).2‖ = Y := by simp [Y, norm_sub_rev]
      rw [e1, e2]
      have : ‖p.1 - q.1‖ / (1 + ‖ζ‖) ≤ 4 * X := by
        rw [div_le_iff₀ hpos]
        have hX' : 4 * X * (1 + ‖ζ‖) = 4 * (1 + ‖ζ‖) / (1 + ‖p.1‖ + ‖q.1‖) * ‖p.1 - q.1‖ := by
          simp only [X]; field_simp
        rw [hX']
        have : 1 ≤ 4 * (1 + ‖ζ‖) / (1 + ‖p.1‖ + ‖q.1‖) := (one_le_div hpos').2 hS
        nlinarith [norm_nonneg (p.1 - q.1)]
      linarith
    have hw0 : 0 ≤ ‖(q - p).1‖ / (1 + ‖ζ‖) + ‖(q - p).2‖ := by positivity
    calc _ ≤ C * (‖(q - p).1‖ / (1 + ‖ζ‖) + ‖(q - p).2‖) *
          (‖(q - p).1‖ / (1 + ‖ζ‖) + ‖(q - p).2‖) := h
      _ = C * (‖(q - p).1‖ / (1 + ‖ζ‖) + ‖(q - p).2‖) ^ 2 := by ring
      _ ≤ C * (4 * X + Y) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact pow_le_pow_left₀ hw0 hwt 2
  have key := taylor_01 (φ := fun τ : ℝ => F (p + τ • (q - p)))
    (φ' := fun τ => fderiv ℝ F (p + τ • (q - p)) (q - p))
    (φ'' := fun τ => fderiv ℝ (fderiv ℝ F) (p + τ • (q - p)) (q - p) (q - p))
    (fun τ hτ => hasDerivAt_path hF p (q - p) (hsub (hseg τ hτ)))
    (fun τ hτ => hasDerivAt_path_d hF p (q - p) (q - p) (hsub (hseg τ hτ))) hbd
  have e1 : p + (1 : ℝ) • (q - p) = q := by simp
  have e0 : p + (0 : ℝ) • (q - p) = p := by simp
  simpa only [e1, e0] using key

end tube

/-! ### Arithmetic -/

lemma arith_near {N A R X Y C c₁ θ ρ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXθ : X ≤ θ)
    (hYρ : Y ≤ 2 * ρ) (hC : 0 < C) (hθρ : θ + 2 * ρ ≤ c₁ / (64 * C))
    (hA : c₁ / 2 * (X + Y) ≤ A) (hR : R ≤ C * (4 * X + Y) ^ 2) (hN : A - R ≤ N) :
    c₁ / 4 * (X + Y) ≤ N := by
  have h1 : (4 * X + Y) ^ 2 ≤ 16 * (X + Y) * (X + Y) := by nlinarith
  have h2 : X + Y ≤ c₁ / (64 * C) := by linarith
  have h3 : 16 * C * (X + Y) ≤ c₁ / 4 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * C)
    rw [show 16 * C * (c₁ / (64 * C)) = c₁ / 4 by field_simp; ring] at this
    exact this
  have h4 : C * (4 * X + Y) ^ 2 ≤ c₁ / 4 * (X + Y) := by
    have := mul_le_mul_of_nonneg_left h1 hC.le
    have h5 : C * (16 * (X + Y) * (X + Y)) = 16 * C * (X + Y) * (X + Y) := by ring
    rw [h5] at this
    have h6 := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ X + Y)
    linarith
  linarith

lemma arith_far {N X Y C c₀ θ ρ : ℝ} (hY : Y ≤ 2 * ρ) (hXθ : θ < X) (hC : 0 < C)
    (hc₀ : 0 < c₀) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c₀ * θ / (4 * (C + c₀)))
    (hN : c₀ * X - 2 * C * ρ ≤ N) : c₀ / 4 * (X + Y) ≤ N := by
  have h1 : (C + c₀) * ρ ≤ c₀ * θ / 4 := by
    have := mul_le_mul_of_nonneg_left hρ (by positivity : (0 : ℝ) ≤ C + c₀)
    rw [show (C + c₀) * (c₀ * θ / (4 * (C + c₀))) = c₀ * θ / 4 by field_simp] at this
    exact this
  have h2 : c₀ * θ < c₀ * X := mul_lt_mul_of_pos_left hXθ hc₀
  nlinarith

end DGA1

end FiniteEnergyPlane

/-!
# A2, abstract part 2: a weighted bound on the derivative of a lift through a thin tube

`F : ℂ × ℂ → E` smooth on `ℂ × ball 0 ρ₀`, with second derivatives bounded in the cylindrical
weight on `ℂ × closedBall 0 ρ'` and a weighted lower bound of `DF(·, 0)`. If a linear map `L`
satisfies `DF(ζ, w) ∘ L ≈ DF(z, 0) ∘ (·, 0)`, then `L ≈ (·, 0)` in the weight at `ζ`.
-/

namespace FiniteEnergyPlane

namespace DGA1

open Metric Set Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℂ × ℂ → E} {ρ₀ ρ' C : ℝ}

lemma dga2_ratio {z ζ : ℂ} (hX : ‖ζ - z‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖)) :
    1 + ‖z‖ ≤ 2 * (1 + ‖ζ‖) := by
  have := norm_sub_norm_le z ζ
  rw [norm_sub_rev] at this
  nlinarith [norm_nonneg z, norm_nonneg ζ]

/-- Horizontal first-order bound of `DF` along `(z, 0) → (ζ, 0)`. -/
lemma norm_fderiv_sub_horiz_le (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    (hρ : 0 ≤ ρ') (hρ' : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (hC : 0 ≤ C) {z ζ : ℂ} (hX : ‖z - ζ‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖)) (h : ℂ) :
    ‖fderiv ℝ F (ζ, 0) (h, 0) - fderiv ℝ F (z, 0) (h, 0)‖ ≤
      16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) * (‖h‖ / (1 + ‖z‖)) := by
  set D := 1 + ‖z‖ + ‖ζ‖ with hD
  have hDpos : 0 < D := by positivity
  set v : ℂ × ℂ := (ζ - z, 0)
  have hmem : ∀ τ : ℝ, (z, (0 : ℂ)) + τ • v ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀ := by
    intro τ
    refine ⟨Set.mem_univ _, ?_⟩
    simp [v, lt_of_le_of_lt hρ hρ']
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ F) ((z, (0 : ℂ)) + τ • v) v (h, 0)‖ ≤
        16 * C * (‖z - ζ‖ / D) * (‖h‖ / D) := by
    intro τ hτ
    have e : (z, (0 : ℂ)) + τ • v = (z + τ • (ζ - z), 0) := by ext <;> simp [v]
    rw [e]
    have hb := hC2 (z + τ • (ζ - z)) 0 (by simp [hρ]) v (h, 0)
    have hw := wt_seg (z := z) (z' := ζ) (θ := 1 / 4) le_rfl hX (Ico_subset_Icc_self hτ)
    set q := 1 + ‖z + τ • (ζ - z)‖
    have hq : 0 < q := by positivity
    have hqD : 1 / q ≤ 4 / D := by
      rw [div_le_div_iff₀ hq hDpos]; linarith
    have hmul : ∀ a : ℝ, 0 ≤ a → a / q ≤ 4 * (a / D) := by
      intro a ha
      calc a / q = a * (1 / q) := by ring
        _ ≤ a * (4 / D) := mul_le_mul_of_nonneg_left hqD ha
        _ = 4 * (a / D) := by ring
    have h1 : ‖ζ - z‖ / q ≤ 4 * (‖z - ζ‖ / D) := by
      rw [norm_sub_rev]; exact hmul _ (norm_nonneg _)
    have h2 : ‖h‖ / q ≤ 4 * (‖h‖ / D) := hmul _ (norm_nonneg _)
    simp only [v, norm_zero, add_zero] at hb
    calc _ ≤ C * (‖ζ - z‖ / q) * (‖h‖ / q) := hb
      _ ≤ C * (4 * (‖z - ζ‖ / D)) * (4 * (‖h‖ / D)) := by gcongr
      _ = _ := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun τ : ℝ => fderiv ℝ F ((z, (0 : ℂ)) + τ • v) (h, 0))
    (f' := fun τ => fderiv ℝ (fderiv ℝ F) ((z, (0 : ℂ)) + τ • v) v (h, 0))
    (fun x _ => (hasDerivAt_path_d hF _ _ (h, 0) (hmem x)).hasDerivWithinAt) hbound
  have e1 : (z, (0 : ℂ)) + (1 : ℝ) • v = (ζ, 0) := by ext <;> simp [v]
  have e0 : (z, (0 : ℂ)) + (0 : ℝ) • v = (z, 0) := by ext <;> simp [v]
  simp only [e1, e0] at key
  refine key.trans ?_
  have hD' : ‖h‖ / D ≤ ‖h‖ / (1 + ‖z‖) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by simp [hD])
  have : 0 ≤ 16 * C * (‖z - ζ‖ / D) := by positivity
  exact mul_le_mul_of_nonneg_left hD' this

/-- If `DF(ζ, w) ∘ L` is close to `DF(z, 0) ∘ (·, 0)`, then `L` is close to `(·, 0)` in the
cylindrical weight at `ζ`. -/
lemma weighted_sub_inl_le (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    (hρ : 0 ≤ ρ') (hρ' : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (hC : 0 ≤ C) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (k : ℂ × ℂ), c₁ * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) ≤ ‖fderiv ℝ F (ζ, 0) k‖)
    {z ζ w : ℂ} (hX : ‖z - ζ‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖)) (hw : ‖w‖ ≤ ρ')
    (hwc : C * ‖w‖ ≤ c₁ / 2) (L : ℂ →L[ℝ] ℂ × ℂ) {η : ℝ}
    (hL : ∀ h : ℂ, ‖fderiv ℝ F (ζ, w) (L h) - fderiv ℝ F (z, 0) (h, 0)‖ ≤ η * (‖h‖ / (1 + ‖z‖)))
    (h : ℂ) :
    ‖(L h).1 - h‖ / (1 + ‖ζ‖) + ‖(L h).2‖ ≤
      2 / c₁ * (η + 16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) + 2 * C * ‖w‖) * (‖h‖ / (1 + ‖z‖)) := by
  set k : ℂ × ℂ := L h - (h, 0) with hk
  have hk1 : k.1 = (L h).1 - h := by simp [k]
  have hk2 : k.2 = (L h).2 := by simp [k]
  rw [← hk1, ← hk2]
  set W := ‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖
  -- lower bound at (ζ, w)
  have hv := norm_fderiv_sub_vert_le hF hρ' hC2 ζ w hw k
  have hl := hlow ζ k
  have hlw : c₁ / 2 * W ≤ ‖fderiv ℝ F (ζ, w) k‖ := by
    have h1 := norm_sub_norm_le (fderiv ℝ F (ζ, 0) k) (fderiv ℝ F (ζ, 0) k - fderiv ℝ F (ζ, w) k)
    rw [sub_sub_cancel, norm_sub_rev] at h1
    have hW : 0 ≤ W := by positivity
    have : C * ‖w‖ * W ≤ c₁ / 2 * W := mul_le_mul_of_nonneg_right hwc hW
    nlinarith
  -- upper bound of DF(ζ, w) k
  have hX' : ‖ζ - z‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖) := by
    rw [norm_sub_rev]; exact hX
  have hr := dga2_ratio hX'
  have hho := norm_fderiv_sub_horiz_le hF hρ hρ' hC2 hC hX h
  have hv0 := norm_fderiv_sub_vert_le hF hρ' hC2 ζ w hw (h, 0)
  have hv0' : ‖fderiv ℝ F (ζ, w) (h, 0) - fderiv ℝ F (ζ, 0) (h, 0)‖ ≤
      2 * C * ‖w‖ * (‖h‖ / (1 + ‖z‖)) := by
    refine hv0.trans ?_
    simp only [norm_zero, add_zero]
    have h1 : ‖h‖ / (1 + ‖ζ‖) ≤ 2 * (‖h‖ / (1 + ‖z‖)) := by
      have hz : (0 : ℝ) < 1 + ‖z‖ := by positivity
      have hζ : (0 : ℝ) < 1 + ‖ζ‖ := by positivity
      have hinv : 1 / (1 + ‖ζ‖) ≤ 2 / (1 + ‖z‖) := by
        rw [div_le_div_iff₀ hζ hz]; linarith
      calc ‖h‖ / (1 + ‖ζ‖) = ‖h‖ * (1 / (1 + ‖ζ‖)) := by ring
        _ ≤ ‖h‖ * (2 / (1 + ‖z‖)) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = _ := by ring
    calc C * ‖w‖ * (‖h‖ / (1 + ‖ζ‖)) ≤ C * ‖w‖ * (2 * (‖h‖ / (1 + ‖z‖))) := by gcongr
      _ = _ := by ring
  have hsplit : fderiv ℝ F (ζ, w) k =
      (fderiv ℝ F (ζ, w) (L h) - fderiv ℝ F (z, 0) (h, 0)) -
        (fderiv ℝ F (ζ, 0) (h, 0) - fderiv ℝ F (z, 0) (h, 0)) -
        (fderiv ℝ F (ζ, w) (h, 0) - fderiv ℝ F (ζ, 0) (h, 0)) := by
    simp only [k, map_sub]; abel
  have hup : ‖fderiv ℝ F (ζ, w) k‖ ≤
      (η + 16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) + 2 * C * ‖w‖) * (‖h‖ / (1 + ‖z‖)) := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    have := hL h
    nlinarith
  have hW : W ≤ 2 / c₁ * ‖fderiv ℝ F (ζ, w) k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]; linarith
  calc W ≤ 2 / c₁ * ‖fderiv ℝ F (ζ, w) k‖ := hW
    _ ≤ 2 / c₁ * ((η + 16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) + 2 * C * ‖w‖) *
        (‖h‖ / (1 + ‖z‖))) := by gcongr
    _ = _ := by ring

end DGA1

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℂ × ℂ → E} {ρ₀ ρ' C : ℝ}
    (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    (hρ : 0 ≤ ρ') (hρ' : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (hC : 0 ≤ C) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (k : ℂ × ℂ), c₁ * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) ≤ ‖fderiv ℝ F (ζ, 0) k‖)
    {z ζ w : ℂ} (hX : ‖z - ζ‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖)) (hw : ‖w‖ ≤ ρ')
    (hwc : C * ‖w‖ ≤ c₁ / 2) (L : ℂ →L[ℝ] ℂ × ℂ) {η : ℝ}
    (hL : ∀ h : ℂ, ‖fderiv ℝ F (ζ, w) (L h) - fderiv ℝ F (z, 0) (h, 0)‖ ≤ η * (‖h‖ / (1 + ‖z‖)))
    (h : ℂ) :
    ‖(L h).1 - h‖ / (1 + ‖ζ‖) + ‖(L h).2‖ ≤
      2 / c₁ * (η + 16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) + 2 * C * ‖w‖) * (‖h‖ / (1 + ‖z‖)) :=
  DGA1.weighted_sub_inl_le hF hρ hρ' hC2 hC hc₁ hlow hX hw hwc L hL h
