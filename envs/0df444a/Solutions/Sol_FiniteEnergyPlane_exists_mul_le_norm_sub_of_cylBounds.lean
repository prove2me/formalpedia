-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_le_norm_sub_of_cylBounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T23:15:20.632988+00:00
-- url     : https://prove2.me/submissions/8e454565-526e-44a7-9e4c-a26f5b53b6b9

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
# A1, abstract part: the two-point lower bound
-/

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

/-- A map on a thin tube `ℂ × ball 0 ρ₀` with cylindrical `C²` bounds, whose restriction to
`w = 0` and whose derivative along `w = 0` satisfy weighted lower bounds, satisfies a weighted
two-point lower bound on a thinner tube. -/
theorem exists_mul_le_norm_sub_of_cylBounds_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℂ × ℂ → E) (ρ₀ ρ' : ℝ) (hρ' : 0 < ρ') (hρ : ρ' < ρ₀)
    (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (C : ℝ)
    (hC1 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h : ℂ × ℂ,
      ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖))
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * (‖z - z'‖ / (1 + ‖z‖ + ‖z'‖)) ≤ ‖F (z, 0) - F (z', 0)‖)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (h : ℂ × ℂ),
      c₁ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) ≤ ‖fderiv ℝ F (ζ, 0) h‖) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
      ∀ q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
        c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤ ‖F p - F q‖ := by
  obtain ⟨C', hC', hCC⟩ : ∃ C' : ℝ, 0 < C' ∧ C ≤ C' :=
    ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  have hC1' : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h : ℂ × ℂ,
      ‖fderiv ℝ F (ζ, w) h‖ ≤ C' * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := fun ζ w hw h =>
    (hC1 ζ w hw h).trans (mul_le_mul_of_nonneg_right hCC (by positivity))
  have hC2' : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C' * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := fun ζ w hw h k =>
    (hC2 ζ w hw h k).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (by positivity)) (by positivity))
  clear hC1 hC2 hCC
  obtain ⟨θ, hθ0, hθ4, hθc⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ θ ≤ c₁ / (128 * C') :=
    ⟨min (1 / 4) (c₁ / (128 * C')), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨ρ, hρpos, hρ1, hρ2, hρ3, hρ4⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ' ∧ ρ ≤ c₁ / (2 * C') ∧
      ρ ≤ c₁ / (256 * C') ∧ ρ ≤ c₀ * θ / (4 * (C' + c₀)) :=
    ⟨min (min ρ' (c₁ / (2 * C'))) (min (c₁ / (256 * C')) (c₀ * θ / (4 * (C' + c₀)))),
      lt_min (lt_min hρ' (by positivity)) (lt_min (by positivity) (by positivity)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hθρ : θ + 2 * ρ ≤ c₁ / (64 * C') := by
    have e : c₁ / (64 * C') = c₁ / (128 * C') + 2 * (c₁ / (256 * C')) := by ring
    rw [e]
    linarith
  refine ⟨ρ, hρpos, min (c₁ / 4) (c₀ / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro p hp q hq
  set X := ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) with hXdef
  set Y := ‖p.2 - q.2‖ with hYdef
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hpw : ‖p.2‖ < ρ := mem_ball_zero_iff.1 hp.2
  have hqw : ‖q.2‖ < ρ := mem_ball_zero_iff.1 hq.2
  have hY : Y ≤ 2 * ρ := by
    have := norm_sub_le p.2 q.2
    linarith
  have hpw' : ‖p.2‖ ≤ ρ' := (hpw.le.trans hρ1)
  have hqw' : ‖q.2‖ ≤ ρ' := (hqw.le.trans hρ1)
  have hpe : ((p.1, p.2) : ℂ × ℂ) = p := rfl
  have hqe : ((q.1, q.2) : ℂ × ℂ) = q := rfl
  by_cases hnear : X ≤ θ
  · have hS : 0 < 1 + ‖p.1‖ + ‖q.1‖ := by positivity
    have hXθ' : ‖p.1 - q.1‖ ≤ θ * (1 + ‖p.1‖ + ‖q.1‖) := by
      rw [hXdef, div_le_iff₀ hS] at hnear
      exact hnear
    have hT := DGA1.taylor_seg hF hρ hC2' hC'.le hθ4 hρ1 hp hq hXθ'
    have hA : c₁ / 2 * (X + Y) ≤ ‖fderiv ℝ F p (q - p)‖ := by
      have h1 := hlow p.1 (q - p)
      have h2 := DGA1.norm_fderiv_sub_vert_le hF hρ hC2' p.1 p.2 hpw' (q - p)
      rw [hpe] at h2
      set W := ‖(q - p).1‖ / (1 + ‖p.1‖) + ‖(q - p).2‖ with hW
      have hW0 : 0 ≤ W := by positivity
      have hwt : X + Y ≤ W := by
        have e1 : ‖(q - p).1‖ = ‖p.1 - q.1‖ := by simp [norm_sub_rev]
        have e2 : ‖(q - p).2‖ = Y := by simp [hYdef, norm_sub_rev]
        rw [hW, e1, e2]
        have : X ≤ ‖p.1 - q.1‖ / (1 + ‖p.1‖) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith [norm_nonneg q.1])
        linarith
      have hCp : C' * ‖p.2‖ ≤ c₁ / 2 := by
        have := mul_le_mul_of_nonneg_left (hpw.le.trans hρ2) hC'.le
        rwa [show C' * (c₁ / (2 * C')) = c₁ / 2 by field_simp] at this
      have h3 : ‖fderiv ℝ F (p.1, 0) (q - p)‖ ≤
          ‖fderiv ℝ F p (q - p)‖ + ‖fderiv ℝ F p (q - p) - fderiv ℝ F (p.1, 0) (q - p)‖ := by
        have := norm_sub_le (fderiv ℝ F p (q - p))
          (fderiv ℝ F p (q - p) - fderiv ℝ F (p.1, 0) (q - p))
        simpa using this
      have h4 : C' * ‖p.2‖ * W ≤ c₁ / 2 * W := mul_le_mul_of_nonneg_right hCp hW0
      nlinarith
    have hN : ‖fderiv ℝ F p (q - p)‖ - C' * (4 * X + Y) ^ 2 ≤ ‖F p - F q‖ := by
      have h1 : ‖fderiv ℝ F p (q - p)‖ ≤ ‖F q - F p‖ + ‖F q - F p - fderiv ℝ F p (q - p)‖ := by
        have := norm_sub_le (F q - F p) (F q - F p - fderiv ℝ F p (q - p))
        simpa using this
      rw [norm_sub_rev (F p)]
      linarith
    have := DGA1.arith_near hX0 hY0 hnear hY hC' hθρ hA le_rfl hN
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans this
  · have hfar : c₀ * X - 2 * C' * ρ ≤ ‖F p - F q‖ := by
      have hs := hslice p.1 q.1
      have hv1 := DGA1.norm_sub_vert_le hF hρ hC1' p.1 p.2 hpw'
      have hv2 := DGA1.norm_sub_vert_le hF hρ hC1' q.1 q.2 hqw'
      rw [hpe] at hv1
      rw [hqe] at hv2
      have e : F (p.1, 0) - F (q.1, 0) = -(F p - F (p.1, 0)) + (F p - F q) + (F q - F (q.1, 0)) := by
        abel
      have htri : ‖F (p.1, 0) - F (q.1, 0)‖ ≤
          ‖F p - F (p.1, 0)‖ + ‖F p - F q‖ + ‖F q - F (q.1, 0)‖ := by
        rw [e]
        have := norm_add₃_le (a := -(F p - F (p.1, 0))) (b := F p - F q) (c := F q - F (q.1, 0))
        rwa [norm_neg] at this
      have k1 : C' * ‖p.2‖ ≤ C' * ρ := mul_le_mul_of_nonneg_left hpw.le hC'.le
      have k2 : C' * ‖q.2‖ ≤ C' * ρ := mul_le_mul_of_nonneg_left hqw.le hC'.le
      linarith
    have := DGA1.arith_far hY (lt_of_not_ge hnear) hC' hc₀ hρpos.le hρ4 hfar
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans this

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℂ × ℂ → E) (ρ₀ ρ' : ℝ) (hρ' : 0 < ρ') (hρ : ρ' < ρ₀)
    (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (C : ℝ)
    (hC1 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h : ℂ × ℂ,
      ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖))
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * (‖z - z'‖ / (1 + ‖z‖ + ‖z'‖)) ≤ ‖F (z, 0) - F (z', 0)‖)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (h : ℂ × ℂ),
      c₁ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) ≤ ‖fderiv ℝ F (ζ, 0) h‖) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
      ∀ q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
        c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤ ‖F p - F q‖ :=
  exists_mul_le_norm_sub_of_cylBounds_aux F ρ₀ ρ' hρ' hρ hF C hC1 hC2 c₀ hc₀ hslice c₁ hc₁ hlow
