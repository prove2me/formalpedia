-- Prove2me | solution 1 for CubicNewton.Nonconvex.step_mem_and_accept
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:43:42.729278+00:00
-- url     : https://prove2.me/submissions/e5895866-3616-48a5-aa83-c4c667b706d1

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

open Set

theorem aux_cnsma_taylor {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hy : y ∈ F) :
    f y ≤ f x + ⟪g x, y - x⟫ + (1 / 2) * ⟪H x (y - x), y - x⟫ + L / 6 * ‖y - x‖ ^ 3 := by
  set h := y - x with hh
  set a := ⟪g x, h⟫ with ha
  set b := ⟪H x h, h⟫ with hb
  set r := ‖h‖ with hr
  have hγ : ∀ s ∈ Icc (0:ℝ) 1, x + s • h ∈ F := fun s hs =>
    hF_convex.add_smul_mem hx (by simpa [hh] using hy) hs
  have hγd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • h) h s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const h).const_add x
  have hd1 : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => f (x + s • h) - f x - s * a - s ^ 2 / 2 * b - L / 6 * s ^ 3 * r ^ 3)
      (⟪g (x + s • h), h⟫ - a - s * b - L / 2 * s ^ 2 * r ^ 3) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => f (x + s • h)) ⟪g (x + s • h), h⟫ s := by
      have hF : HasFDerivAt f
          (innerSL ℝ (g (x + s • h)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (x + s • h) :=
        (hf _ (hγ s hs)).hasFDerivAt
      have := hF.comp_hasDerivAt s (hγd s)
      rw [innerSL_apply_apply] at this
      exact this
    have := ((((h1.sub_const (f x)).sub ((hasDerivAt_id s).mul_const a)).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const b)).sub
      (((hasDerivAt_pow 3 s).const_mul (L/6)).mul_const (r^3)))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl]
    simp only [id, Nat.cast_ofNat, pow_one]
    ring
  have hd2 : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => ⟪g (x + s • h), h⟫ - a - s * b - L / 2 * s ^ 2 * r ^ 3)
      (⟪H (x + s • h) h, h⟫ - b - L * s * r ^ 3) s := by
    intro s hs
    have hc := (hg _ (hγ s hs)).comp_hasDerivAt s (hγd s)
    have h2 := hc.inner ℝ (hasDerivAt_const s h)
    have := (((h2.sub_const a).sub ((hasDerivAt_id s).mul_const b)).sub
      (((hasDerivAt_pow 2 s).const_mul (L/2)).mul_const (r^3)))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl]
    simp only [id, Nat.cast_ofNat, pow_one, inner_zero_right, zero_add]
    ring
  have hχ : AntitoneOn
      (fun s : ℝ => ⟪g (x + s • h), h⟫ - a - s * b - L / 2 * s ^ 2 * r ^ 3) (Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro s hs
      exact (hd2 s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd2 s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hs
      have e1 : ⟪H (x + s • h) h, h⟫ - b = ⟪(H (x + s • h) - H x) h, h⟫ := by
        simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, inner_sub_left, hb]
      have e2 : ⟪(H (x + s • h) - H x) h, h⟫ ≤ ‖H (x + s • h) - H x‖ * r * r := by
        calc ⟪(H (x + s • h) - H x) h, h⟫ ≤ ‖(H (x + s • h) - H x) h‖ * ‖h‖ :=
              real_inner_le_norm _ _
          _ ≤ ‖H (x + s • h) - H x‖ * ‖h‖ * ‖h‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
      have e3 : ‖H (x + s • h) - H x‖ ≤ L * (s * r) := by
        have := hLip _ (hγ s hs') x hx
        simpa [norm_smul, Real.norm_of_nonneg hs'.1] using this
      have hr0 : 0 ≤ r := norm_nonneg _
      have : ‖H (x + s • h) - H x‖ * r * r ≤ L * (s * r) * r * r := by
        gcongr
      nlinarith
  have hχ0 : ∀ s ∈ Icc (0:ℝ) 1,
      ⟪g (x + s • h), h⟫ - a - s * b - L / 2 * s ^ 2 * r ^ 3 ≤ 0 := by
    intro s hs
    have := hχ (left_mem_Icc.2 zero_le_one) hs hs.1
    simpa [ha] using this
  have hψ : AntitoneOn
      (fun s : ℝ => f (x + s • h) - f x - s * a - s ^ 2 / 2 * b - L / 6 * s ^ 3 * r ^ 3)
      (Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro s hs
      exact (hd1 s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd1 s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact hχ0 s (Ioo_subset_Icc_self hs)
  have := hψ (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  have hxy : x + (1:ℝ) • h = y := by simp [hh]
  simp only [hxy, zero_smul, add_zero, sub_self, zero_mul, one_mul] at this
  norm_num at this
  linarith

theorem aux_cnsma_model_bound {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hLM : L ≤ M)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hy : y ∈ F) :
    f y ≤ f x + CubicNewton.Shared.cubicModel g H M x y := by
  have h1 := aux_cnsma_taylor F f g H L hF_convex hf hg hLip x y hx hy
  have h2 : L / 6 * ‖y - x‖ ^ 3 ≤ M / 6 * ‖y - x‖ ^ 3 := by
    have : 0 ≤ ‖y - x‖ ^ 3 := by positivity
    nlinarith
  unfold CubicNewton.Shared.cubicModel
  linarith

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex
open Set
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hLM : L ≤ M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior F)
    (hfx : f x ≤ f x₀) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    T ∈ F ∧ f T ≤ f x + CubicNewton.Shared.cubicModel g H M x T := by
  have hxF : x ∈ F := interior_subset hx
  set h := T - x with hh
  have hM : 0 ≤ M := le_trans hL.le hLM
  have hmodel : ∀ t : ℝ, 0 ≤ t → CubicNewton.Shared.cubicModel g H M x (x + t • h) =
      t * ⟪g x, h⟫ + t ^ 2 / 2 * ⟪H x h, h⟫ + M / 6 * t ^ 3 * ‖h‖ ^ 3 := by
    intro t ht
    simp only [CubicNewton.Shared.cubicModel, add_sub_cancel_left, inner_smul_left,
      inner_smul_right, map_smul, norm_smul, Real.norm_of_nonneg ht]
    simp only [RCLike.conj_to_real]
    ring
  have hTeq : x + (1:ℝ) • h = T := by simp [hh]
  have hm1 : ⟪g x, h⟫ + 1 / 2 * ⟪H x h, h⟫ + M / 6 * ‖h‖ ^ 3 ≤ 0 := by
    have := hT x
    have e0 : CubicNewton.Shared.cubicModel g H M x x = 0 := by
      simp [CubicNewton.Shared.cubicModel]
    have e1 := hmodel 1 zero_le_one
    rw [hTeq] at e1
    rw [e0, e1] at this
    linarith
  have ha : ⟪g x, h⟫ ≤ 0 := by
    have := hT (x - h)
    have e1 := hmodel 1 zero_le_one
    rw [hTeq] at e1
    have e2 : CubicNewton.Shared.cubicModel g H M x (x - h) =
        -⟪g x, h⟫ + 1 / 2 * ⟪H x h, h⟫ + M / 6 * ‖h‖ ^ 3 := by
      simp only [CubicNewton.Shared.cubicModel, sub_sub_cancel_left, inner_neg_right,
        map_neg, inner_neg_left, norm_neg, neg_neg]
    rw [e1, e2] at this
    linarith
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, CubicNewton.Shared.cubicModel g H M x (x + t • h) ≤ 0 := by
    intro t ht
    rw [hmodel t ht.1]
    have hc : 0 ≤ M / 6 * ‖h‖ ^ 3 := by positivity
    have key : t * ⟪g x, h⟫ + t ^ 2 / 2 * ⟪H x h, h⟫ + M / 6 * t ^ 3 * ‖h‖ ^ 3 =
        t * (1 - t) * ⟪g x, h⟫ + t ^ 2 * (⟪g x, h⟫ + 1 / 2 * ⟪H x h, h⟫ + M / 6 * ‖h‖ ^ 3)
        + (M / 6 * ‖h‖ ^ 3) * t ^ 2 * (t - 1) := by ring
    rw [key]
    have t1 : t * (1 - t) * ⟪g x, h⟫ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.1 (by linarith [ht.2])) ha
    have t2 : t ^ 2 * (⟪g x, h⟫ + 1 / 2 * ⟪H x h, h⟫ + M / 6 * ‖h‖ ^ 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hm1
    have t3 : (M / 6 * ‖h‖ ^ 3) * t ^ 2 * (t - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [ht.2])
    linarith
  have hcont : Continuous (fun s : ℝ => x + s • h) := by fun_prop
  have hS : Icc (0:ℝ) 1 ⊆ {t : ℝ | x + t • h ∈ F} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · exact (hF_closed.preimage hcont).inter isClosed_Icc
    · simpa using hxF
    · rintro t ⟨htS, ht0, ht1⟩
      have hyF : x + t • h ∈ F := htS
      have hb := aux_cnsma_model_bound F f g H L hF_convex hf hg hLip M hLM x (x + t • h)
        hxF hyF
      have hle : f (x + t • h) ≤ f x₀ := by
        have := hseg t ⟨ht0, ht1.le⟩
        linarith
      have hint : x + t • h ∈ interior F := hlevel hle
      apply mem_nhdsWithin_of_mem_nhds
      exact Filter.mem_of_superset
        (hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
        (fun s (hs : x + s • h ∈ interior F) => (interior_subset hs : x + s • h ∈ F))
  have hTF : T ∈ F := by
    have h1 : x + (1:ℝ) • h ∈ F := hS (right_mem_Icc.2 zero_le_one)
    rwa [hTeq] at h1
  exact ⟨hTF, aux_cnsma_model_bound F f g H L hF_convex hf hg hLip M hLM x T hxF hTF⟩
