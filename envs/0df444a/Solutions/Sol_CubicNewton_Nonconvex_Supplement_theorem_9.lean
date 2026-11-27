-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:06.321036+00:00
-- url     : https://prove2.me/submissions/f8dbf643-78ec-4ef9-aa3d-39d208412736

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_Supplement_TransformedConvexSetting

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 9, pp. 196–197. Assumptions of Theorem 8, and `φ` strongly
convex with parameter `γ > 0` (normalization (4.8), `γ/2` in front of the square). Let
`ω̌ = (1/L²)(γ/(2σ²))³` and `Δ_k = f(x_k) − f(x*)` with `x* = v(u*)`. There is a first index
`k₀` with `Δ_{k₀} ≤ (4/9) ω̌` (`k₀ = 0` when already `Δ₀ ≤ (4/9) ω̌`); if `Δ₀ ≥ (4/9) ω̌`,
then (4.20) holds for every `k ≤ k₀`; and (4.21) holds for every `k ≥ k₀`. -/
theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientWithinAt f (g x) F x) (hg : ∀ x ∈ F, HasFDerivWithinAt g (H x) F x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ustar : EuclideanSpace ℝ (Fin n)) (σ D : ℝ)
    (hT : TransformedConvexSetting f x₀ φ u v v' ustar σ D)
    (γ : ℝ) (hγ : 0 < γ) (hsc : StrongConvexOn Set.univ γ φ)
    (ω : ℝ) (hω : ω = 1 / L ^ 2 * (γ / (2 * σ ^ 2)) ^ 3) :
    ∃ k₀ : ℕ, f (x k₀) - f (v ustar) ≤ 4 / 9 * ω ∧
      (∀ j < k₀, 4 / 9 * ω < f (x j) - f (v ustar)) ∧
      (4 / 9 * ω ≤ f x₀ - f (v ustar) →
        ∀ k ≤ k₀, f (x k) - f (v ustar) ≤
          ((f x₀ - f (v ustar)) ^ (1 / 4 : ℝ) - (k : ℝ) / 6 * Real.sqrt (2 / 3) * ω ^ (1 / 4 : ℝ)) ^ 4) ∧
      ∀ k ≥ k₀, f (x (k + 1)) - f (v ustar) ≤
        1 / 2 * (f (x k) - f (v ustar)) * Real.sqrt ((f (x k) - f (v ustar)) / ω) := by
          classical
          let E := EuclideanSpace ℝ (Fin n)
          have hmono {p p' : ℝ → ℝ}
              (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt p (p' t) (Set.Icc 0 1) t)
              (hn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p' t) :
              ∀ t ∈ Set.Icc (0 : ℝ) 1, p 0 ≤ p t := by
            have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
              (fun t ht => (hd t ht).continuousWithinAt)
              (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
              (fun t ht => hn t (interior_subset ht))
            exact fun t ht => hm (by constructor <;> norm_num) ht ht.1
          have htaylor (a b : E) (ha : a ∈ F) (hb : b ∈ F) :
              f a + inner ℝ (g a) (b - a) + 1 / 2 * inner ℝ (H a (b - a)) (b - a) ≤
                f b + L / 6 * ‖b - a‖ ^ 3 := by
            clear * - a b ha hb hF_convex hf hg hLip hmono
            let d := b - a
            let z : ℝ → E := fun t => a + t • d
            have hz : Set.MapsTo z (Set.Icc 0 1) F := by
              intro t ht
              have h := hF_convex ha hb (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring)
              convert h using 1 <;> simp [z, d, sub_smul, smul_sub] <;> module
            have hdz (t : ℝ) : HasDerivAt z d t := by
              exact HasDerivAt.const_add a
                (by simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const d)
            let A := inner ℝ (g a) d
            let B := inner ℝ (H a d) d
            let C := L * ‖d‖ ^ 3
            have hdg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
                HasDerivWithinAt (fun t => inner ℝ (g (z t)) d)
                  (inner ℝ (H (z t) d) d) (Set.Icc 0 1) t := by
              simpa [Function.comp_def] using
                ((hg (z t) (hz ht)).comp_hasDerivWithinAt t (hdz t).hasDerivWithinAt hz).inner ℝ
                  (hasDerivWithinAt_const t (Set.Icc 0 1) d)
            have hdf (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
                HasDerivWithinAt (fun t => f (z t)) (inner ℝ (g (z t)) d) (Set.Icc 0 1) t := by
              simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
                (hf (z t) (hz ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
                  (hdz t).hasDerivWithinAt hz
            have hB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
                0 ≤ inner ℝ (H (z t) d) d - B + C * t := by
              have h1 := hLip (z t) (hz ht) a ha
              have h2 := (H (z t) - H a).le_opNorm d
              have h3 := norm_inner_le_norm (𝕜 := ℝ) ((H (z t) - H a) d) d
              have h4 := neg_le_abs (inner ℝ ((H (z t) - H a) d) d)
              have he : ‖z t - a‖ = t * ‖d‖ := by
                simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
              rw [he] at h1
              have h5 : ‖(H (z t) - H a) d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
                h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
              have h6 := h3.trans (mul_le_mul_of_nonneg_right h5 (norm_nonneg d))
              simp only [ContinuousLinearMap.sub_apply, inner_sub_left, Real.norm_eq_abs] at h4 h6
              dsimp [B, C]
              nlinarith only [h4, h6]
            have hq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
                0 ≤ inner ℝ (g (z t)) d - A - t * B + C / 2 * t ^ 2 := by
              have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  HasDerivWithinAt (fun t => inner ℝ (g (z t)) d - A - t * B + C / 2 * t ^ 2)
                    (inner ℝ (H (z t) d) d - B + C * t) (Set.Icc 0 1) t := by
                intro t ht
                convert (((hdg t ht).sub_const A).sub ((hasDerivAt_id t).mul_const B).hasDerivWithinAt).add
                  (((hasDerivAt_id t).pow 2).const_mul (C / 2)).hasDerivWithinAt using 1 <;> (try ext t) <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring
              have hh := hmono hd hB t ht
              simpa [z, A] using hh
            have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt
                  (fun t => f (z t) - f a - t * A - t ^ 2 / 2 * B + C / 6 * t ^ 3)
                  (inner ℝ (g (z t)) d - A - t * B + C / 2 * t ^ 2) (Set.Icc 0 1) t := by
              intro t ht
              convert ((((hdf t ht).sub_const (f a)).sub ((hasDerivAt_id t).mul_const A).hasDerivWithinAt).sub
                ((((hasDerivAt_id t).pow 2).div_const 2).mul_const B).hasDerivWithinAt).add
                (((hasDerivAt_id t).pow 3).const_mul (C / 6)).hasDerivWithinAt using 1 <;> (try ext t) <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring
            have hh := hmono hd hq 1 (by constructor <;> norm_num)
            have hz1 : z 1 = b := by simp [z, d]
            simp only [hz1, z, zero_smul, add_zero, sub_self, zero_mul, zero_pow,
              Nat.succ_ne_zero, ne_eq, not_false_eq_true, zero_div, mul_zero, sub_zero,
              one_pow, one_mul, div_one, add_zero] at hh
            dsimp [A, B, C, d] at hh
            linarith
          have hdec (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
            have hs := hrun.step k (x k)
            have ha := hrun.accept k
            have he : CubicNewton.Shared.cubicModel g H (M k) (x k) (x k) = 0 := by
              simp [CubicNewton.Shared.cubicModel]
            rw [he] at hs
            linarith
          have hxlevel (k : ℕ) : f (x k) ≤ f x₀ := by
            induction k with
            | zero => simp [hrun.init]
            | succ k ih => exact (hdec k).trans ih
          have hxF (k : ℕ) : x k ∈ F := interior_subset (hlevel (hxlevel k))
          have hmodel (k : ℕ) (b : E) (hb : b ∈ F) :
              f (x (k + 1)) ≤ f b + L / 2 * ‖b - x k‖ ^ 3 := by
            have ht := htaylor (x k) b (hxF k) hb
            have hs := hrun.step k b
            have ha := hrun.accept k
            have hm := (hrun.param_mem k).2
            dsimp [CubicNewton.Shared.cubicModel] at hs ha
            have hn : 0 ≤ ‖b - x k‖ ^ 3 := by positivity
            have hmul := mul_le_mul_of_nonneg_right hm hn
            linarith
          have hfstar : f (v ustar) = φ ustar := by rw [hT.comp, hT.right_inv]
          have hmin (a : E) : f (v ustar) ≤ f a := by
            rw [hfstar, hT.comp]
            exact hT.isMin _
          have hstarlevel : φ ustar ≤ f x₀ := by simpa [hfstar] using hmin x₀
          have hsigma : 0 ≤ σ := (norm_nonneg (v' ustar)).trans (hT.sigma_bound _ hstarlevel)
          have hvlip (a b : E) (ha : φ a ≤ f x₀) (hb : φ b ≤ f x₀) :
              ‖v b - v a‖ ≤ σ * ‖b - a‖ := by
            have hc : Convex ℝ {z | φ z ≤ f x₀} := by
              simpa using hT.convex.convex_le (f x₀)
            exact hc.norm_image_sub_le_of_norm_hasFDerivWithin_le
              (fun z hz => (hT.hasDeriv_inv z hz).hasFDerivWithinAt)
              (fun z hz => hT.sigma_bound z hz) ha hb
          by_cases hσ : σ = 0
          · have hv := hvlip ustar (u x₀) hstarlevel (by rw [← hT.comp])
            rw [hT.left_inv, hσ, zero_mul, norm_le_zero_iff, sub_eq_zero] at hv
            have hgap (k : ℕ) : f (x k) - f (v ustar) = 0 := by
              have := hxlevel k
              rw [hv] at this
              exact sub_eq_zero.mpr (le_antisymm this (hmin _))
            have hw : ω = 0 := by simp [hω, hσ]
            refine ⟨0, ?_, ?_, ?_, ?_⟩
            · simp [hgap, hw]
            · simp
            · intro _ k hk
              have : k = 0 := Nat.eq_zero_of_le_zero hk
              simp [this, hgap, hrun.init, ← hv]
            · intro k _
              simp [hgap]
          have hσpos : 0 < σ := lt_of_le_of_ne hsigma (Ne.symm hσ)
          have hωpos : 0 < ω := by rw [hω]; positivity
          have hquad (z : E) : γ / 2 * ‖z - ustar‖ ^ 2 ≤ φ z - φ ustar := by
            let C := γ / 2 * ‖z - ustar‖ ^ 2
            let d := φ z - φ ustar
            have hd : 0 ≤ d := sub_nonneg.mpr (hT.isMin z)
            change C ≤ d
            by_contra! hh
            have hC : 0 < C := lt_of_le_of_lt hd hh
            let t := (C - d) / (2 * C)
            have ht : 0 < t := by dsimp [t]; positivity
            have ht1 : t ≤ 1 := by
              dsimp [t]
              apply (div_le_one (by positivity)).mpr
              linarith
            have he : t * (2 * C) = C - d := by dsimp [t]; field_simp
            have hs := hsc.2 (x := z) (Set.mem_univ _) (y := ustar) (Set.mem_univ _)
              ht.le (show 0 ≤ 1 - t by linarith) (show t + (1 - t) = 1 by ring)
            have hm := hT.isMin (t • z + (1 - t) • ustar)
            simp only [smul_eq_mul] at hs
            have hi : t * ((1 - t) * C - d) ≤ 0 := by dsimp [C, d]; nlinarith
            have hi' : (1 - t) * C - d ≤ 0 := by
              by_contra! hp
              exact (not_lt_of_ge hi) (mul_pos ht hp)
            nlinarith
          have hpath (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
              f (x (k + 1)) - f (v ustar) ≤
                (1 - a) * (f (x k) - f (v ustar)) +
                  L / 2 * (σ * a * Real.sqrt (2 * (f (x k) - f (v ustar)) / γ)) ^ 3 := by
            let z := (1 - a) • u (x k) + a • ustar
            have hcv : φ z ≤ (1 - a) * φ (u (x k)) + a * φ ustar :=
              hT.convex.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) ha (by ring)
            have hzlev : φ z ≤ f x₀ := by
              rw [← hT.comp (x k), ← hfstar] at hcv
              have hm := hmin (x k)
              have hl := hxlevel k
              nlinarith
            have hbval : f (v z) = φ z := by rw [hT.comp, hT.right_inv]
            have hbF : v z ∈ F := interior_subset (hlevel (by simpa [hbval] using hzlev))
            have hd := hvlip (u (x k)) z (by rw [← hT.comp]; exact hxlevel k) hzlev
            rw [hT.left_inv] at hd
            have he : ‖z - u (x k)‖ = a * ‖u (x k) - ustar‖ := by
              have hz : z - u (x k) = a • (ustar - u (x k)) := by dsimp [z]; module
              rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, norm_sub_rev]
            rw [he] at hd
            have hq := hquad (u (x k))
            rw [← hT.comp, ← hfstar] at hq
            have hnn : 0 ≤ f (x k) - f (v ustar) := sub_nonneg.mpr (hmin _)
            have hsqr : ‖u (x k) - ustar‖ ≤ Real.sqrt (2 * (f (x k) - f (v ustar)) / γ) := by
              apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
              apply (le_div_iff₀ hγ).mpr
              nlinarith
            have hdb : ‖v z - x k‖ ≤ σ * a * Real.sqrt (2 * (f (x k) - f (v ustar)) / γ) :=
              hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hsqr (mul_nonneg hsigma ha)])
            have hm := hmodel k (v z) hbF
            have hp := pow_le_pow_left₀ (norm_nonneg (v z - x k)) hdb 3
            rw [hbval] at hm
            rw [← hT.comp, ← hfstar] at hcv
            have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ L / 2 by positivity)
            nlinarith
          have hcoef (d : ℝ) (hd : 0 ≤ d) :
              L * (σ * Real.sqrt (2 * d / γ)) ^ 3 = d * Real.sqrt (d / ω) := by
            clear * - L σ γ ω hL hσpos hγ hω d hd
            have hωpos : 0 < ω := by rw [hω]; positivity
            have hωeq : ω * (8 * L ^ 2 * σ ^ 6) = γ ^ 3 := by
              rw [hω]
              field_simp
              <;> ring
            have hr := Real.sq_sqrt (show 0 ≤ 2 * d / γ by positivity)
            have hq := Real.sq_sqrt (show 0 ≤ d / ω by positivity)
            apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
            calc
              (L * (σ * Real.sqrt (2 * d / γ)) ^ 3) ^ 2 = L ^ 2 * σ ^ 6 * (Real.sqrt (2 * d / γ) ^ 2) ^ 3 := by ring
              _ = L ^ 2 * σ ^ 6 * (2 * d / γ) ^ 3 := by rw [hr]
              _ = d ^ 3 / ω := by
                apply (eq_div_iff (ne_of_gt hωpos)).mpr
                field_simp
                linear_combination d ^ 3 * hωeq
              _ = (d * Real.sqrt (d / ω)) ^ 2 := by rw [mul_pow, hq]; ring
          let δ : ℕ → ℝ := fun k => f (x k) - f (v ustar)
          have hδ (k : ℕ) : 0 ≤ δ k := sub_nonneg.mpr (hmin _)
          have hrec (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
              δ (k + 1) ≤ (1 - a) * δ k + 1 / 2 * a ^ 3 * δ k * Real.sqrt (δ k / ω) := by
            have hh := hpath k a ha ha1
            change δ (k + 1) ≤ (1 - a) * δ k +
              L / 2 * (σ * a * Real.sqrt (2 * δ k / γ)) ^ 3 at hh
            have he : L / 2 * (σ * a * Real.sqrt (2 * δ k / γ)) ^ 3 =
                1 / 2 * a ^ 3 * δ k * Real.sqrt (δ k / ω) := by
              calc
                _ = 1 / 2 * a ^ 3 * (L * (σ * Real.sqrt (2 * δ k / γ)) ^ 3) := by ring
                _ = _ := by rw [hcoef (δ k) (hδ k)]; ring
            rwa [he] at hh
          have hscalar (d e : ℝ) (hd : 4 / 9 * ω ≤ d) (he : 0 ≤ e)
              (hrc : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
                e ≤ (1 - a) * d + 1 / 2 * a ^ 3 * d * Real.sqrt (d / ω)) :
              e ^ (1 / 4 : ℝ) ≤ d ^ (1 / 4 : ℝ) -
                1 / 6 * Real.sqrt (2 / 3) * ω ^ (1 / 4 : ℝ) := by
            clear * - ω hωpos d e hd he hrc
            have hfour (z : ℝ) (hz : 0 ≤ z) : (z ^ (1 / 4 : ℝ)) ^ 4 = z := by
              rw [← Real.rpow_mul_natCast hz]
              norm_num
            have hdpos : 0 < d := by linarith
            let r := d ^ (1 / 4 : ℝ)
            let s := ω ^ (1 / 4 : ℝ)
            let q := Real.sqrt (2 / 3)
            have hr : 0 < r := Real.rpow_pos_of_pos hdpos _
            have hs : 0 < s := Real.rpow_pos_of_pos hωpos _
            have hq : 0 < q := Real.sqrt_pos.mpr (by norm_num)
            have hr4 : r ^ 4 = d := hfour d hdpos.le
            have hs4 : s ^ 4 = ω := hfour ω hωpos.le
            have hq2 : q ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
            have hqr : q * s ≤ r := by
              apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ q * s) hr.le (by decide : 4 ≠ 0)).mp
              calc
                (q * s) ^ 4 = (q ^ 2) ^ 2 * s ^ 4 := by ring
                _ = 4 / 9 * ω := by rw [hq2, hs4]; ring
                _ ≤ r ^ 4 := by rw [hr4]; exact hd
            have hsqrt : Real.sqrt (d / ω) = r ^ 2 / s ^ 2 := by
              apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
              rw [Real.sq_sqrt (by positivity)]
              calc
                d / ω = r ^ 4 / s ^ 4 := by rw [hr4, hs4]
                _ = (r ^ 2 / s ^ 2) ^ 2 := by ring
            let a := q * s / r
            have ha : 0 ≤ a := by dsimp [a]; positivity
            have ha1 : a ≤ 1 := (div_le_one hr).mpr hqr
            have haD : a * d = q * s * r ^ 3 := by
              rw [← hr4]
              dsimp [a]
              field_simp
              <;> ring
            have haC : a ^ 3 * d * Real.sqrt (d / ω) = (2 / 3) * q * s * r ^ 3 := by
              have hq3 : q ^ 3 = (2 / 3) * q := by nlinarith [hq2]
              calc
                _ = q ^ 3 * s * r ^ 3 := by
                  rw [hsqrt, ← hr4]
                  dsimp [a]
                  field_simp
                  <;> ring
                _ = _ := by rw [hq3]
            have hbound : e ≤ r ^ 4 - 2 / 3 * q * s * r ^ 3 := by
              have hh := hrc a ha ha1
              rw [show (1 - a) * d = d - a * d by ring, haD] at hh
              have heq : 1 / 2 * a ^ 3 * d * Real.sqrt (d / ω) = 1 / 2 * ((2 / 3) * q * s * r ^ 3) := by
                rw [← haC]; ring
              rw [heq, ← hr4] at hh
              linarith
            let c := 1 / 6 * q * s
            have hc : 0 ≤ c := by dsimp [c]; positivity
            have hrc : 0 ≤ r - c := by dsimp [c]; linarith
            have hber : r ^ 4 - 2 / 3 * q * s * r ^ 3 ≤ (r - c) ^ 4 := by
              have hh : 0 ≤ c ^ 2 * ((c - 2 * r) ^ 2 + 2 * r ^ 2) := by positivity
              dsimp only [c] at hh ⊢
              nlinarith only [hh]
            apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg he _) hrc (by decide : 4 ≠ 0)).mp
            rw [hfour e he]
            exact hbound.trans hber
          let c : ℝ := 1 / 6 * Real.sqrt (2 / 3) * ω ^ (1 / 4 : ℝ)
          have hc : 0 < c := by dsimp [c]; positivity
          have hstep (k : ℕ) (hk : 4 / 9 * ω ≤ δ k) :
              (δ (k + 1)) ^ (1 / 4 : ℝ) ≤ (δ k) ^ (1 / 4 : ℝ) - c :=
            hscalar (δ k) (δ (k + 1)) hk (hδ _) (hrec k)
          have hex : ∃ k : ℕ, δ k ≤ 4 / 9 * ω := by
            by_contra! hno
            have hb (k : ℕ) : (δ k) ^ (1 / 4 : ℝ) ≤ (δ 0) ^ (1 / 4 : ℝ) - (k : ℝ) * c := by
              induction k with
              | zero => simp
              | succ k ih =>
                have hh := hstep k (hno k).le
                rw [Nat.cast_succ]
                linarith
            obtain ⟨k, hk⟩ := exists_nat_gt ((δ 0) ^ (1 / 4 : ℝ) / c)
            have hh := hb k
            have hn := Real.rpow_nonneg (hδ k) (1 / 4 : ℝ)
            have hmul : (δ 0) ^ (1 / 4 : ℝ) < (k : ℝ) * c := (div_lt_iff₀ hc).mp hk
            linarith
          let k₀ := Nat.find hex
          have hk₀ : δ k₀ ≤ 4 / 9 * ω := Nat.find_spec hex
          have hbefore (j : ℕ) (hj : j < k₀) : 4 / 9 * ω < δ j :=
            lt_of_not_ge (Nat.find_min hex hj)
          have hrate (k : ℕ) (hk : k ≤ k₀) :
              (δ k) ^ (1 / 4 : ℝ) ≤ (δ 0) ^ (1 / 4 : ℝ) - (k : ℝ) * c := by
            induction k with
            | zero => simp
            | succ k ih =>
              have hi := ih (by omega)
              have hh := hstep k (hbefore k (by omega)).le
              rw [Nat.cast_succ]
              linarith
          refine ⟨k₀, hk₀, hbefore, ?_, ?_⟩
          · intro _ k hk
            have hh := pow_le_pow_left₀ (Real.rpow_nonneg (hδ k) _) (hrate k hk) 4
            have he : ((δ k) ^ (1 / 4 : ℝ)) ^ 4 = δ k := by
              rw [← Real.rpow_mul_natCast (hδ k)]
              norm_num
            rw [he] at hh
            have hz : δ 0 = f x₀ - f (v ustar) := by dsimp [δ]; rw [hrun.init]
            rw [hz] at hh
            simpa only [δ, c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hh
          · intro k _
            have hh := hrec k 1 (by norm_num) (by norm_num)
            simpa [δ] using hh
