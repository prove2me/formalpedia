-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_form_bound_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:13.389814+00:00
-- url     : https://prove2.me/submissions/9a53a322-2c66-4bbd-bdde-3df57a7ee4a3

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gsK
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_bmatK
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_herm_real
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_besselK
import Theorems.Thm_Formalism_HadamardInequality_P_hadamard_inequality_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.DetBBoundK := by
  intro K U _ _ _ _ σ h η hσ herm hpos hη s u w
  have hnn : ∀ x : U, 0 ≤ (σ (h x x)).re := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have haniso : ∀ x : U, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    have := hpos x h0
    rw [hx] at this
    simp at this
  obtain ⟨g, Lu, hLu, hu, hgo⟩ := gsK h herm haniso s u
  obtain ⟨g', Lw, hLw, hw, hgo'⟩ := gsK h herm haniso s w
  let β : U →ₗ[K] U →ₗ⋆[K] K := h.compl₂ (LinearMap.id - η)
  have hβ : ∀ x y, β x y = bEta h η x y := by intro x y; simp [β, bEta]
  have e1 : (Matrix.of fun a b => bEta h η (u a) (w b)).det =
      (Matrix.of fun a b => bEta h η (g a) (g' b)).det := by
    have := bmatK β g g' Lu Lw u w hu hw
    simp only [hβ] at this
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hLu, hLw]; simp
  have e2 : ∀ (v gg : Fin s → U) (L : Matrix (Fin s) (Fin s) K), L.det = 1 →
      (∀ i, v i = ∑ k, L i k • gg k) → (∀ a b, a ≠ b → h (gg a) (gg b) = 0) →
      (Matrix.of fun a b => h (v a) (v b)).det = ∏ a, h (gg a) (gg a) := by
    intro v gg L hL hv ho
    rw [bmatK h gg gg L L v v hv hv, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hL]
    have : (Matrix.of fun k l => h (gg k) (gg l)) = Matrix.diagonal (fun a => h (gg a) (gg a)) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, ho a b hab]
    rw [this, Matrix.det_diagonal]; simp
  rw [e1, e2 u g Lu hLu hu hgo, e2 w g' Lw hLw hw hgo']
  have hn : ∀ gg : Fin s → U, ‖σ (∏ a, h (gg a) (gg a))‖ = ∏ a, (σ (h (gg a) (gg a))).re := by
    intro gg
    rw [map_prod, norm_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [herm_real σ h hσ herm (gg a), Complex.norm_real, Real.norm_of_nonneg (by simpa using hnn (gg a))]
    simp
  rw [hn, hn]
  set N : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun a b => σ (bEta h η (g a) (g' b)) with hN
  have hdetN : σ (Matrix.of fun a b => bEta h η (g a) (g' b)).det = N.det := by
    rw [RingHom.map_det]; rfl
  rw [hdetN]
  have hP : 0 ≤ ∏ a, (σ (h (g a) (g a))).re := Finset.prod_nonneg (fun a _ => hnn _)
  have hP' : 0 ≤ ∏ a, (σ (h (g' a) (g' a))).re := Finset.prod_nonneg (fun a _ => hnn _)
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hP, Real.sq_sqrt hP']
  by_cases hz : ∃ a, g a = 0
  · obtain ⟨a, ha⟩ := hz
    have : N.det = 0 := Matrix.det_eq_zero_of_row_eq_zero a (by intro b; simp [hN, ha, bEta])
    rw [this]; simp; positivity
  · have hz : ∀ a, g a ≠ 0 := fun a ha => hz ⟨a, ha⟩
    have hdpos : ∀ a, 0 < (σ (h (g a) (g a))).re := fun a => hpos _ (hz a)
    have hd0 : ∀ a, h (g a) (g a) ≠ 0 := fun a h0 => hz a (haniso _ h0)
    set N' : Matrix (Fin s) (Fin s) ℂ :=
      Matrix.diagonal (fun a => (((Real.sqrt (σ (h (g a) (g a))).re)⁻¹ : ℝ) : ℂ)) * N with hN'
    have hNN : ‖N.det‖ ^ 2 = ‖N'.det‖ ^ 2 * ∏ a, (σ (h (g a) (g a))).re := by
      rw [hN', Matrix.det_mul, Matrix.det_diagonal, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
      have : (∏ a, ‖(((Real.sqrt (σ (h (g a) (g a))).re)⁻¹ : ℝ) : ℂ)‖ ^ 2) * ∏ a, (σ (h (g a) (g a))).re = 1 := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro a _
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (hdpos a).le,
          inv_mul_cancel₀ (hdpos a).ne']
      calc ‖N.det‖ ^ 2 = ‖N.det‖ ^ 2 * 1 := by ring
        _ = _ := by rw [← this]; ring
    have hpar : ∀ x : U, (σ (h (x - η x) (x - η x))).re ≤ 4 * (σ (h x x)).re := by
      intro x
      have e : h (x - η x) (x - η x) + h (x + η x) (x + η x) = 4 * h x x := by
        simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hη]
        ring
      have h1 : (σ (h (x - η x) (x - η x) + h (x + η x) (x + η x))).re = (σ (4 * h x x)).re := by rw [e]
      rw [σ.map_add, σ.map_mul, Complex.add_re] at h1
      have h2 : (σ 4 * σ (h x x)).re = 4 * (σ (h x x)).re := by
        have : σ 4 = ((4:ℝ) : ℂ) := by
          rw [map_ofNat]; norm_num
        rw [this, Complex.re_ofReal_mul]
      rw [h2] at h1
      have := hnn (x + η x)
      linarith
    have hH := Formalism.HadamardInequality.P.hadamard_inequality_holds s N'ᵀ
    rw [Matrix.det_transpose] at hH
    have hrow : ∀ b, ∑ a, ‖N'ᵀ b a‖ ^ 2 ≤ 4 * (σ (h (g' b) (g' b))).re := by
      intro b
      refine le_trans (le_of_eq ?_) (le_trans
        (besselK σ h hσ herm hnn g hgo hd0 (g' b - η (g' b))) (hpar (g' b)))
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.transpose_apply, hN', Matrix.diagonal_mul, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (hdpos a).le, hN]
      simp only [Matrix.of_apply, bEta]
      rw [inv_mul_eq_div]
    have hfin : ‖N'.det‖ ^ 2 ≤ (2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re := by
      refine le_trans hH ?_
      calc ∏ b, ∑ a, ‖N'ᵀ b a‖ ^ 2 ≤ ∏ b, (4 * (σ (h (g' b) (g' b))).re) :=
            Finset.prod_le_prod (fun b _ => Finset.sum_nonneg (fun a _ => by positivity)) (fun b _ => hrow b)
        _ = (2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
              mul_comm s 2, pow_mul]
            norm_num
    rw [hNN]
    calc ‖N'.det‖ ^ 2 * ∏ a, (σ (h (g a) (g a))).re
        ≤ ((2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re) * ∏ a, (σ (h (g a) (g a))).re :=
          mul_le_mul_of_nonneg_right hfin hP
      _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
