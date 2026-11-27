-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:45.295026+00:00
-- url     : https://prove2.me/submissions/c8c4805e-76fa-499a-8fbe-631c29f521e5

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_Supplement_TransformedConvexSetting

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 8, p. 196. Standing assumptions of Section 2 with Assumption 1
on `F ⊇ L(f(x₀))`, a run of method (3.3) with `0 < L₀ ≤ L`, and the setting of Section 4.3
(`f = φ ∘ u`, `x* = v(u*)`, `σ` and `D` as there). With `f* = f(x*)`:
1. if `f(x₀) − f* ≥ (3/2) L (σD)³`, then `f(x₁) − f* ≤ (1/2) L (σD)³`;
2. if `f(x₀) − f* ≤ (3/2) L (σD)³`, then for all `k ≥ 0`, (4.19)
   `f(x_k) − f(x*) ≤ 3 L (σD)³ / (2 (1 + k/3)²)`. -/
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
    (hT : TransformedConvexSetting f x₀ φ u v v' ustar σ D) :
    (3 / 2 * L * (σ * D) ^ 3 ≤ f x₀ - f (v ustar) →
      f (x 1) - f (v ustar) ≤ 1 / 2 * L * (σ * D) ^ 3) ∧
    (f x₀ - f (v ustar) ≤ 3 / 2 * L * (σ * D) ^ 3 →
      ∀ k : ℕ, f (x k) - f (v ustar) ≤
        3 * L * (σ * D) ^ 3 / (2 * (1 + (k : ℝ) / 3) ^ 2)) := by
          classical
          let E := EuclideanSpace ℝ (Fin n)
          have htaylor : ∀ a ∈ F, ∀ b ∈ F,
              f a + inner ℝ (g a) (b - a) + (1 / 2 : ℝ) * inner ℝ (H a (b - a)) (b - a) ≤
                f b + L / 6 * ‖b - a‖ ^ 3 := by
            intro a ha b hb
            let p : ℝ → E := AffineMap.lineMap a b
            let d := b - a
            let A : ℝ := inner ℝ (g a) d
            let B : ℝ := inner ℝ (H a d) d
            let C : ℝ := L * ‖d‖ ^ 3
            have hp : Set.MapsTo p (Set.Icc 0 1) F := hF_convex.mapsTo_lineMap ha hb
            have hfd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt (fun t => f (p t)) (inner ℝ (g (p t)) d) (Set.Icc 0 1) t := by
              intro t ht
              simpa [p, d, Function.comp_def] using
                ((hf (p t) (hp ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
                  AffineMap.hasDerivWithinAt_lineMap hp)
            have hgd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt (fun t => inner ℝ (g (p t)) d) (inner ℝ (H (p t) d) d)
                  (Set.Icc 0 1) t := by
              intro t ht
              have hh := (hg (p t) (hp ht)).comp_hasDerivWithinAt t
                AffineMap.hasDerivWithinAt_lineMap hp
              simpa [d, Function.comp_def] using
                hh.inner ℝ (hasDerivWithinAt_const t (Set.Icc 0 1) d)
            have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                B - C * t ≤ inner ℝ (H (p t) d) d := by
              intro t ht
              have hn : ‖p t - a‖ = t * ‖d‖ := by
                simp [p, AffineMap.lineMap_apply_module', d, norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg ht.1]
              have hl := hLip a ha (p t) (hp ht)
              rw [norm_sub_rev a (p t), hn] at hl
              have hi := real_inner_le_norm ((H a - H (p t)) d) d
              have hop := ContinuousLinearMap.le_opNorm (H a - H (p t)) d
              have hmul := mul_le_mul_of_nonneg_right hop (norm_nonneg d)
              have hmul' := mul_le_mul_of_nonneg_right hl (mul_nonneg (norm_nonneg d) (norm_nonneg d))
              simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hi
              simp only [ContinuousLinearMap.sub_apply] at hmul
              dsimp [B, C]
              nlinarith
            let Q : ℝ → ℝ := fun t => inner ℝ (g (p t)) d - A - B * t + C / 2 * t ^ 2
            have hQ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt Q (inner ℝ (H (p t) d) d - B + C * t) (Set.Icc 0 1) t := by
              intro t ht
              convert (((hgd t ht).sub_const A).sub ((hasDerivWithinAt_id t _).const_mul B)).add
                (((hasDerivWithinAt_id t _).pow 2).const_mul (C / 2)) using 1 <;> (try dsimp [Q]) <;> first | rfl | (funext s; ring) | ring
            have hQmono : MonotoneOn Q (Set.Icc (0 : ℝ) 1) := by
              apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
                (fun t ht => (hQ t ht).continuousWithinAt)
              · intro t ht
                exact (hQ t (interior_subset ht)).mono interior_subset
              · intro t ht
                have hh := hbound t (interior_subset ht)
                linarith
            have hQnonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Q t := by
              intro t ht
              have hh := hQmono (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) ht ht.1
              simpa [Q, p, A] using hh
            let R : ℝ → ℝ := fun t => f (p t) - f a - A * t - B / 2 * t ^ 2 + C / 6 * t ^ 3
            have hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt R (Q t) (Set.Icc 0 1) t := by
              intro t ht
              convert ((((hfd t ht).sub_const (f a)).sub ((hasDerivWithinAt_id t _).const_mul A)).sub
                (((hasDerivWithinAt_id t _).pow 2).const_mul (B / 2))).add
                (((hasDerivWithinAt_id t _).pow 3).const_mul (C / 6)) using 1 <;>
                (try dsimp [R, Q]) <;> first | rfl | (funext s; ring) | ring
            have hRmono : MonotoneOn R (Set.Icc (0 : ℝ) 1) := by
              apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
                (fun t ht => (hR t ht).continuousWithinAt)
              · intro t ht
                exact (hR t (interior_subset ht)).mono interior_subset
              · intro t ht
                exact hQnonneg t (interior_subset ht)
            have hh := hRmono (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
              (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) (by norm_num)
            simp only [R, p, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
              zero_pow, one_pow, mul_zero, mul_one, sub_self, sub_zero, add_zero] at hh
            dsimp [A, B, C, d] at hh
            linarith
          have hcomp : ∀ z, f (v z) = φ z := by
            intro z
            rw [hT.comp, hT.right_inv]
          have hmin : ∀ y, f (v ustar) ≤ f y := by
            intro y
            rw [hcomp, hT.comp]
            exact hT.isMin _
          have hs0 : φ (u x₀) ≤ f x₀ := (hT.comp x₀).ge
          have hσ : 0 ≤ σ := (norm_nonneg _).trans (hT.sigma_bound _ hs0)
          have hD : 0 ≤ D := (norm_nonneg _).trans (hT.radius_bound _ hs0)
          have hS : Convex ℝ {z | φ z ≤ f x₀} := by
            simpa only [Set.mem_univ, true_and] using hT.convex.convex_le (f x₀)
          have hvlip : ∀ z w, φ z ≤ f x₀ → φ w ≤ f x₀ →
              ‖v z - v w‖ ≤ σ * ‖z - w‖ := by
            intro z w hz hw
            exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
              (fun t ht => (hT.hasDeriv_inv t ht).hasFDerivWithinAt)
              (fun t ht => hT.sigma_bound t ht) hS hw hz
          have hdecrease : ∀ k, f (x (k + 1)) ≤ f (x k) := by
            intro k
            have hh := (hrun.step k) (x k)
            have ha := hrun.accept k
            have hzero : CubicNewton.Shared.cubicModel g H (M k) (x k) (x k) = 0 := by
              simp [CubicNewton.Shared.cubicModel]
            rw [hzero] at hh
            linarith
          have hxlevel : ∀ k, f (x k) ≤ f x₀ := by
            intro k
            induction k with
            | zero => rw [hrun.init]
            | succ k ih => exact (hdecrease k).trans ih
          have hrec : ∀ (k : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
              f (x (k + 1)) - f (v ustar) ≤
                (1 - α) * (f (x k) - f (v ustar)) +
                  (L * (σ * D) ^ 3) / 2 * α ^ 3 := by
            intro k α hα hα1
            let z := (1 - α) • u (x k) + α • ustar
            have hφ : φ z ≤ (1 - α) * f (x k) + α * f (v ustar) := by
              have hh := hT.convex.2 (Set.mem_univ (u (x k))) (Set.mem_univ ustar)
                (sub_nonneg.mpr hα1) hα (sub_add_cancel 1 α)
              simpa [z, ← hT.comp, ← hcomp] using hh
            have hz : φ z ≤ f x₀ := by
              have hh := hmin (x k)
              have hh' := hxlevel k
              nlinarith
            have hy : f (v z) ≤ f x₀ := (hcomp z).le.trans hz
            have haF : x k ∈ F := interior_subset (hlevel (hxlevel k))
            have hbF : v z ∈ F := interior_subset (hlevel hy)
            have hdist : ‖v z - x k‖ ≤ α * (σ * D) := by
              have hh := hvlip z (u (x k)) hz (by rw [← hT.comp]; exact hxlevel k)
              rw [hT.left_inv] at hh
              have heq : z - u (x k) = α • (ustar - u (x k)) := by
                dsimp [z]
                module
              rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, norm_sub_rev ustar (u (x k))] at hh
              have hr := hT.radius_bound (u (x k)) (by rw [← hT.comp]; exact hxlevel k)
              calc
                ‖v z - x k‖ ≤ σ * (α * ‖u (x k) - ustar‖) := hh
                _ ≤ σ * (α * D) := mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hr hα) hσ
                _ = α * (σ * D) := by ring
            have ht := htaylor (x k) haF (v z) hbF
            have hm := (hrun.step k) (v z)
            have hac := hrun.accept k
            have hmodel : f (x (k + 1)) ≤ f (v z) + (L + M k) / 6 * ‖v z - x k‖ ^ 3 := by
              dsimp [CubicNewton.Shared.cubicModel] at hm hac
              linarith
            have hcube : ‖v z - x k‖ ^ 3 ≤ (α * (σ * D)) ^ 3 :=
              pow_le_pow_left₀ (norm_nonneg _) hdist 3
            have hcoef : (L + M k) / 6 ≤ L / 2 := by
              have hh := (hrun.param_mem k).2
              linarith
            have herr : (L + M k) / 6 * ‖v z - x k‖ ^ 3 ≤
                (L * (σ * D) ^ 3) / 2 * α ^ 3 := by
              calc
                _ ≤ L / 2 * ‖v z - x k‖ ^ 3 := mul_le_mul_of_nonneg_right hcoef (by positivity)
                _ ≤ L / 2 * (α * (σ * D)) ^ 3 := mul_le_mul_of_nonneg_left hcube (by positivity)
                _ = _ := by ring
            rw [hcomp] at hmodel
            linarith
          constructor
          · intro _
            have hh := hrec 0 1 (by norm_num) (by norm_num)
            norm_num at hh
            linarith
          · intro hinit k
            let C : ℝ := L * (σ * D) ^ 3
            have hC : 0 ≤ C := by dsimp [C]; positivity
            have hind : ∀ j : ℕ, f (x j) - f (v ustar) ≤ (27 / 2 : ℝ) * C / ((j : ℝ) + 3) ^ 2 := by
              intro j
              induction j with
              | zero =>
                rw [hrun.init]
                norm_num
                dsimp [C]
                linarith
              | succ j ih =>
                have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                have hp : 0 < (j : ℝ) + 3 := by positivity
                have hp' : 0 < (j : ℝ) + 4 := by positivity
                let α : ℝ := 3 / ((j : ℝ) + 3)
                have hα : 0 ≤ α := by dsimp [α]; positivity
                have hα1 : α ≤ 1 := by dsimp [α]; apply (div_le_one hp).2; linarith
                have hr := hrec j α hα hα1
                have hmul := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hα1)
                have hrat : (1 - α) * ((27 / 2 : ℝ) * C / ((j : ℝ) + 3) ^ 2) + C / 2 * α ^ 3 ≤
                    (27 / 2 : ℝ) * C / ((j : ℝ) + 4) ^ 2 := by
                  dsimp [α]
                  field_simp
                  nlinarith [mul_nonneg hC hj]
                have hh : f (x (j + 1)) - f (v ustar) ≤
                    (27 / 2 : ℝ) * C / ((j : ℝ) + 4) ^ 2 := by
                  dsimp [C] at hrat
                  linarith
                simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
                  show (1 : ℝ) + 3 = 4 by norm_num] using hh
            have hh := hind k
            have heq : (27 / 2 : ℝ) * C / ((k : ℝ) + 3) ^ 2 =
                3 * L * (σ * D) ^ 3 / (2 * (1 + (k : ℝ) / 3) ^ 2) := by
              dsimp [C]
              field_simp <;> ring
            exact heq ▸ hh
