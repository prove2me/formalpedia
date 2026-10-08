-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.thm_3_19_telescoped
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:51:00.71412+00:00
-- url     : https://prove2.me/submissions/706f248f-45a6-442b-b038-d004b2ec6df8

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs

set_option autoImplicit false

open scoped InnerProductSpace

theorem nd3f_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (a b : EuclideanSpace ℝ (Fin n)) :
    f b ≤ f a + inner ℝ (g a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let p : ℝ → EuclideanSpace ℝ (Fin n) := fun s => a + s • v
  let G : ℝ → ℝ := fun s => f (p s) - f a - s * inner ℝ (g a) v - β / 2 * s ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ s : ℝ, HasDerivAt G
      (inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2) s := by
    intro s
    have hpd : HasDerivAt p v s := by
      have := ((hasDerivAt_id s).smul_const v).const_add a
      simpa [p] using this
    have hfg : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (g (p s))) (p s) :=
      hasGradientAt_iff_hasFDerivAt.mp (hgrad (p s))
    have h1 := hfg.comp_hasDerivAt s hpd
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g a) v) (inner ℝ (g a) v) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (g a) v)
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h1' : HasDerivAt (fun s => f (p s)) (inner ℝ (g (p s)) v) s := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
    exact ((h1'.sub_const (f a)).sub h2).sub h3
  have hnonpos : ∀ s ∈ Set.Icc (0:ℝ) 1,
      inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2 ≤ 0 := by
    intro s hs
    have hle := hlip (p s) a
    have hps : p s - a = s • v := by simp [p]
    rw [hps, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hle
    have hcs := real_inner_le_norm (g (p s) - g a) v
    rw [inner_sub_left] at hcs
    have : ‖g (p s) - g a‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    nlinarith
  have hanti : AntitoneOn G (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s _; exact (hderiv s).continuousAt.continuousWithinAt
    · intro s _
      exact (hderiv s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s).deriv]
      exact hnonpos s (interior_subset hs)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = b := by simp [p, v]
  simp only [G, hp0, hp1] at h01
  nlinarith

theorem nd3f_convex_fo {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hXcv : Convex ℝ X)
    (hc : ConvexOn ℝ X f) (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ X) (hb : b ∈ X) :
    f a + inner ℝ (g a) (b - a) ≤ f b := by
  set w := b - a
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + s • w)) (inner ℝ (g (a + t • w)) w) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => a + s • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add a
    have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hgrad (a + t • w))).comp_hasDerivAt t hl
    rw [InnerProductSpace.toDual_apply_apply] at h1
    exact h1
  have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => f (a + t • w)) := by
    have h0 := hc.comp_affineMap (AffineMap.lineMap a b)
    have e : (fun t : ℝ => f (a + t • w)) = f ∘ AffineMap.lineMap a b := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]
    refine h0.subset ?_ (convex_Icc 0 1)
    intro t ht
    simp only [Set.mem_preimage]
    have := hXcv.add_smul_sub_mem ha hb ht
    simpa [AffineMap.lineMap_apply, add_comm] using this
  have h := hφ.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one (by simpa using hline 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : a + w = b := by simp [w]
  rw [hw] at h
  linarith


/-- One step of the Lyapunov decrease for Nesterov's method (smooth convex case). -/
theorem nd3f_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (β L : ℝ) (hβ : 0 < β) (hL1 : 1 ≤ L)
    (x y xs g y2 : E) (fx fy fy2 fs : ℝ)
    (hy2 : y2 = x - (1 / β) • g)
    (h1 : fy2 ≤ fx + ⟪g, y2 - x⟫_ℝ + β / 2 * ‖y2 - x‖ ^ 2)
    (h2 : fx + ⟪g, y - x⟫_ℝ ≤ fy)
    (h3 : fx + ⟪g, xs - x⟫_ℝ ≤ fs) :
    L ^ 2 * (fy2 - fs) + β / 2 * ‖(L • y2 - (L - 1) • y) - xs‖ ^ 2 ≤
      (L ^ 2 - L) * (fy - fs) + β / 2 * ‖(L • x - (L - 1) • y) - xs‖ ^ 2 := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hL : 0 ≤ L := by linarith
  set w := (L • x - (L - 1) • y) - xs with hw
  have e1 : y2 - x = -(1 / β) • g := by rw [hy2]; simp [neg_smul, sub_eq_add_neg]
  have e2 : (L • y2 - (L - 1) • y) - xs = w - (L / β) • g := by
    rw [hw, hy2]; match_scalars <;> (try field_simp) <;> ring
  have e3 : -(L - 1) • (y - x) - (xs - x) = w := by rw [hw]; module
  rw [e1] at h1
  rw [e2]
  have hcomb : L * fy2 - (L - 1) * fy - fs ≤ ⟪g, w⟫_ℝ - L / (2 * β) * ‖g‖ ^ 2 := by
    have hG : fy2 ≤ fx - 1 / (2 * β) * ‖g‖ ^ 2 := by
      rw [inner_smul_right, norm_smul, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
        abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / β)] at h1
      have : -(1 / β) * ‖g‖ ^ 2 + β / 2 * (1 / β * ‖g‖) ^ 2 = -(1 / (2 * β)) * ‖g‖ ^ 2 := by
        field_simp; ring
      linarith
    rw [← e3, inner_sub_right, inner_smul_right]
    have k := mul_le_mul_of_nonneg_left (sub_nonneg.2 h2) (by linarith : (0:ℝ) ≤ L - 1)
    have : L / (2 * β) * ‖g‖ ^ 2 = L * (1 / (2 * β) * ‖g‖ ^ 2) := by ring
    nlinarith
  have hkey := mul_le_mul_of_nonneg_left hcomb hL
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ L / β)]
  have : β / 2 * (‖w‖ ^ 2 - 2 * (L / β * ⟪w, g⟫_ℝ) + (L / β * ‖g‖) ^ 2)
      = β / 2 * ‖w‖ ^ 2 - L * ⟪g, w⟫_ℝ + L * (L / (2 * β) * ‖g‖ ^ 2) := by
    rw [real_inner_comm]; field_simp; try ring
  rw [this]
  nlinarith

namespace Nd3f
open ConvexOptAlg.NesterovSmooth

theorem lam_succ (k : ℕ) : lam (k + 1) = (1 + Real.sqrt (1 + 4 * lam k ^ 2)) / 2 := rfl

theorem lam_one : lam 1 = 1 := by
  rw [lam_succ]; simp [lam]

theorem lam_succ_ge (k : ℕ) : lam k + 1 / 2 ≤ lam (k + 1) := by
  rw [lam_succ]
  have : |2 * lam k| ≤ Real.sqrt (1 + 4 * lam k ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; nlinarith
  have := le_abs_self (2 * lam k)
  linarith

theorem lam_ge (k : ℕ) : ((k : ℝ) + 2) / 2 ≤ lam (k + 1) := by
  induction k with
  | zero => rw [lam_one]; norm_num
  | succ k ih =>
    have := lam_succ_ge (k + 1)
    push_cast; linarith

theorem lam_pos (k : ℕ) : 0 < lam (k + 1) := by
  have := lam_ge k; have : (0:ℝ) ≤ k := k.cast_nonneg; linarith

theorem lam_sq (k : ℕ) : lam k ^ 2 = lam (k + 1) ^ 2 - lam (k + 1) := by
  rw [lam_succ]
  have h := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + 4 * lam k ^ 2)
  nlinarith

end Nd3f

open ConvexOptAlg.NesterovSmooth in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (t : ℕ) (ht : 2 ≤ t) :
    f (y t) - f xstar ≤
      β / (2 * lam (t - 1) ^ 2) * ‖lam 1 • x 1 - (lam 1 - 1) • y 1 - xstar‖ ^ 2 := by
  have hdesc := nd3f_descent f g β hf.1 hf.2
  have hlow : ∀ a b, f a + ⟪g a, b - a⟫_ℝ ≤ f b := fun a b =>
    nd3f_convex_fo Set.univ f g hf.1 convex_univ hconv a b (Set.mem_univ _) (Set.mem_univ _)
  set Φ : ℕ → ℝ := fun s => lam (s - 1) ^ 2 * (f (y s) - f xstar) +
      β / 2 * ‖(lam s • x s - (lam s - 1) • y s) - xstar‖ ^ 2 with hΦ
  have hstep : ∀ s, 1 ≤ s → Φ (s + 1) ≤ Φ s := by
    intro s hs
    obtain ⟨hy, hx⟩ := hrun.2 s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    have hL0 : 1 ≤ lam (k + 1) := by
      have := Nd3f.lam_ge k; have : (0:ℝ) ≤ k := k.cast_nonneg; linarith
    have hu : lam (k + 1 + 1) • x (k + 1 + 1) - (lam (k + 1 + 1) - 1) • y (k + 1 + 1)
        = lam (k + 1) • y (k + 1 + 1) - (lam (k + 1) - 1) • y (k + 1) := by
      rw [hx]
      have hp := (Nd3f.lam_pos (k + 1)).ne'
      unfold gam
      match_scalars <;> field_simp <;> ring
    have h1 := hdesc (x (k + 1)) (y (k + 1 + 1))
    have h2 := hlow (x (k + 1)) (y (k + 1))
    have h3 := hlow (x (k + 1)) xstar
    have := nd3f_step β (lam (k + 1)) hβ hL0 (x (k + 1)) (y (k + 1)) xstar (g (x (k + 1)))
      (y (k + 1 + 1)) (f (x (k + 1))) (f (y (k + 1))) (f (y (k + 1 + 1))) (f xstar) hy h1 h2 h3
    simp only [hΦ, hu, Nat.add_sub_cancel]
    rw [Nd3f.lam_sq k]
    linarith
  have hiter : ∀ k : ℕ, Φ (k + 1) ≤ Φ 1 := by
    intro k
    induction k with
    | zero => exact le_refl _
    | succ k ih => exact (hstep (k + 1) (by omega)).trans ih
  have hl0 : lam 0 = 0 := by simp [lam]
  have hΦ1 : Φ 1 = β / 2 * ‖lam 1 • x 1 - (lam 1 - 1) • y 1 - xstar‖ ^ 2 := by
    simp only [hΦ, Nat.sub_self, hl0]
    ring
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 2 := ⟨t - 2, by omega⟩
  have hP := hiter (j + 1)
  rw [hΦ1] at hP
  simp only [hΦ, Nat.add_sub_cancel] at hP
  have hsq := sq_nonneg ‖(lam (j + 1 + 1) • x (j + 1 + 1) - (lam (j + 1 + 1) - 1) • y (j + 1 + 1)) - xstar‖
  have hkey : lam (j + 1) ^ 2 * (f (y (j + 1 + 1)) - f xstar) ≤
      β / 2 * ‖lam 1 • x 1 - (lam 1 - 1) • y 1 - xstar‖ ^ 2 := by
    nlinarith
  have hpos : 0 < lam (j + 1) := Nd3f.lam_pos j
  have e : j + 2 - 1 = j + 1 := by omega
  rw [e, show j + 2 = j + 1 + 1 by omega]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith
