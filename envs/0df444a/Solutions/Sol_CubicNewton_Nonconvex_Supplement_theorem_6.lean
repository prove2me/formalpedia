-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:05.304145+00:00
-- url     : https://prove2.me/submissions/0a9dc429-a04f-4f64-baa6-4d2da30a8208

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_Supplement_IsGradDominated1

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 6, p. 193. Standing assumptions of Section 2, Assumption 1, a
run of method (3.3) with `0 < L₀ ≤ L`, and `f` gradient dominated of degree `p = 1` with
constant `τ` and global minimizer `xs` (Definition 3). Let
`ω̂ = (18/L₀²) τ³ (L + L₀)³`.
1. If `f(x₀) − f(x*) ≥ ω̂`, then (4.11)
   `ln((f(x_k) − f(x*))/ω̂) ≤ (2/3)^k ln((f(x₀) − f(x*))/ω̂)` holds at every `k` with a positive
   gap, and from some index on `f(x_k) − f(x*) ≤ ω̂` (the process reaches `L(ω̂)`).
2. If `f(x₀) − f(x*) ≤ γ² ω̂` for some `γ > 1`, then for every `k ≥ 0`, (4.12)
   `f(x_k) − f(x*) ≤ ω̂ γ² (2 + (3/2)γ)² / (2 + (k + 3/2)γ)²`. -/
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
    (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) (hgd : IsGradDominated1 F f g τ xs)
    (ω : ℝ) (hω : ω = 18 / L₀ ^ 2 * τ ^ 3 * (L + L₀) ^ 3) :
    (ω ≤ f x₀ - f xs →
      (∀ k : ℕ, 0 < f (x k) - f xs →
        Real.log (1 / ω * (f (x k) - f xs)) ≤ (2 / 3 : ℝ) ^ k * Real.log (1 / ω * (f x₀ - f xs))) ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀, f (x k) - f xs ≤ ω) ∧
    ∀ γ : ℝ, 1 < γ → f x₀ - f xs ≤ γ ^ 2 * ω →
      ∀ k : ℕ, f (x k) - f xs ≤
        ω * (γ ^ 2 * (2 + 3 / 2 * γ) ^ 2 / (2 + ((k : ℝ) + 3 / 2) * γ) ^ 2) := by
          set_option maxHeartbeats 1000000 in
          classical
          obtain ⟨hxsF, hmin, hτ, hdomF⟩ := hgd
          have hωpos : 0 < ω := by rw [hω]; positivity
          have hmodel0 : ∀ (m : ℝ) (y : EuclideanSpace ℝ (Fin n)),
              CubicNewton.Shared.cubicModel g H m y y = 0 := by
            intro m y; simp [CubicNewton.Shared.cubicModel]
          have hdec : ∀ k, f (x (k+1)) ≤ f (x k) := by
            intro k
            have h1 := hrun.accept k
            have h2 := hrun.step k (x k)
            rw [hmodel0] at h2
            linarith
          have hle0 : ∀ k, f (x k) ≤ f x₀ := by
            intro k
            induction k with
            | zero => rw [hrun.init]
            | succ k ih => exact (hdec k).trans ih
          have hint : ∀ k, x k ∈ interior F := fun k => hlevel (hle0 k)
          have hFn : ∀ y ∈ interior F, F ∈ nhds y := fun y hy => mem_interior_iff_mem_nhds.mp hy
          have hgA : ∀ y ∈ interior F,
              HasFDerivAt f (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g y)) y := by
            intro y hy
            exact (hasGradientWithinAt_iff_hasFDerivWithinAt.mp (hf y (interior_subset hy))).hasFDerivAt (hFn y hy)
          have hHA : ∀ y ∈ interior F, HasFDerivAt g (H y) y := fun y hy =>
            (hg y (interior_subset hy)).hasFDerivAt (hFn y hy)
          have hsymm : ∀ y ∈ interior F, ∀ v w,
              inner ℝ (H y v) w = inner ℝ (H y w) v := by
            intro y hy v w
            let I : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
            have hev : ∀ᶠ z in nhds y, HasFDerivAt f (I (g z)) z := by
              filter_upwards [isOpen_interior.mem_nhds hy] with z hz
              have e : I (g z) = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g z) := by
                ext u; simp only [I, InnerProductSpace.toDual_apply_apply]; rfl
              rw [e]; exact hgA z hz
            have hd : HasFDerivAt (fun z => I (g z)) (I.comp (H y)) y :=
              I.hasFDerivAt.comp y (hHA y hy)
            have := second_derivative_symmetric_of_eventually hev hd v w
            simp only [I, ContinuousLinearMap.comp_apply] at this
            exact this
          have htaylor : ∀ y ∈ interior F, ∀ z ∈ interior F,
              ‖g z - g y - H y (z - y)‖ ≤ L / 2 * ‖z - y‖ ^ 2 := by
            intro y hy z hz
            have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, y + t • (z - y) ∈ interior F := fun t ht =>
              hF_convex.interior.add_smul_sub_mem hy hz ht
            have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
                HasDerivAt (fun t : ℝ => g (y + t • (z - y)) - g y - t • H y (z - y))
                  (H (y + t • (z - y)) (z - y) - H y (z - y)) t := by
              intro t ht
              have h1 : HasDerivAt (fun t : ℝ => y + t • (z - y)) (z - y) t := by
                simpa using ((hasDerivAt_id t).smul_const (z - y)).const_add y
              have h2 := (hHA _ (hseg t ht)).comp_hasDerivAt t h1
              have h3 : HasDerivAt (fun t : ℝ => t • H y (z - y)) (H y (z - y)) t := by
                simpa using (hasDerivAt_id t).smul_const (H y (z - y))
              exact (h2.sub_const (g y)).sub h3
            have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
              (f := fun t : ℝ => g (y + t • (z - y)) - g y - t • H y (z - y)) (a := 0) (b := 1)
              (f' := fun t => H (y + t • (z - y)) (z - y) - H y (z - y))
              (B := fun t => L / 2 * t ^ 2 * ‖z - y‖ ^ 2) (B' := fun t => L * t * ‖z - y‖ ^ 2)
              (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
              (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
              (by simp)
              (fun t => by
                have := ((hasDerivAt_pow 2 t).const_mul (L/2)).mul_const (‖z - y‖^2)
                exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring))
              (fun t ht => by
                have ht' := Set.Ico_subset_Icc_self ht
                calc ‖H (y + t • (z - y)) (z - y) - H y (z - y)‖
                    = ‖(H (y + t • (z - y)) - H y) (z - y)‖ := rfl
                  _ ≤ ‖H (y + t • (z - y)) - H y‖ * ‖z - y‖ := ContinuousLinearMap.le_opNorm _ _
                  _ ≤ (L * ‖t • (z - y)‖) * ‖z - y‖ := by
                      gcongr
                      have := hLip _ (interior_subset (hseg t ht')) _ (interior_subset hy)
                      simpa using this
                  _ = L * t * ‖z - y‖ ^ 2 := by rw [norm_smul, Real.norm_of_nonneg ht.1]; ring)
              (Set.right_mem_Icc.2 zero_le_one)
            simpa using key
          have hcube : ∀ w : EuclideanSpace ℝ (Fin n), (‖w‖ ^ 2) ^ (3/2 : ℝ) = ‖w‖ ^ 3 := by
            intro w
            rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
            norm_num
          have hhalf : ∀ w : EuclideanSpace ℝ (Fin n), (‖w‖ ^ 2) ^ ((3/2 : ℝ) - 1) = ‖w‖ := by
            intro w
            rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
            norm_num
          have hfoc : ∀ k, g (x k) + H (x k) (x (k+1) - x k)
              + ((M k / 2) * ‖x (k+1) - x k‖) • (x (k+1) - x k) = 0 := by
            intro k
            have hst := hrun.step k
            have hd : ∀ d, inner ℝ (g (x k)) d
                + 1/2 * (inner ℝ (H (x k) (x (k+1) - x k)) d + inner ℝ (H (x k) d) (x (k+1) - x k))
                + M k / 6 * (2 * inner ℝ (x (k+1) - x k) d * (3/2) * ‖x (k+1) - x k‖) = 0 := by
              intro d
              have hu : HasDerivAt (fun ε : ℝ => x (k+1) + ε • d - x k) d 0 := by
                simpa using (((hasDerivAt_id (0:ℝ)).smul_const d).const_add (x (k+1))).sub_const (x k)
              have hHu : HasDerivAt (fun ε : ℝ => H (x k) (x (k+1) + ε • d - x k)) (H (x k) d) 0 :=
                (H (x k)).hasFDerivAt.comp_hasDerivAt 0 hu
              have hsq := hu.norm_sq
              have hcb := hsq.rpow_const (p := 3/2) (Or.inr (by norm_num))
              have hphi := (((hasDerivAt_const (0:ℝ) (g (x k))).inner ℝ hu).add
                ((hHu.inner ℝ hu).const_mul (1/2))).add (hcb.const_mul (M k / 6))
              have hmn : IsLocalMin (fun ε : ℝ => inner ℝ (g (x k)) (x (k+1) + ε • d - x k)
                  + 1/2 * inner ℝ (H (x k) (x (k+1) + ε • d - x k)) (x (k+1) + ε • d - x k)
                  + M k / 6 * (‖x (k+1) + ε • d - x k‖ ^ 2) ^ (3/2 : ℝ)) 0 := by
                refine Filter.Eventually.of_forall (fun ε => ?_)
                have h := hst (x (k+1) + ε • d)
                simp only [CubicNewton.Shared.cubicModel] at h
                simp only [zero_smul, add_zero, hcube]
                exact h
              have := hmn.hasDerivAt_eq_zero hphi
              simp only [zero_smul, add_zero, hhalf, inner_zero_left] at this
              linarith [real_inner_comm (H (x k) (x (k+1) - x k)) (x (k+1) - x k)]
            set r := x (k+1) - x k with hr
            set w := g (x k) + H (x k) r + ((M k / 2) * ‖r‖) • r with hw
            have h1 := hd w
            rw [hsymm _ (hint k) w r] at h1
            have h2 : inner ℝ w w = 0 := by
              have e : inner ℝ w w = inner ℝ (g (x k)) w + inner ℝ (H (x k) r) w
                  + (M k / 2 * ‖r‖) * inner ℝ r w := by
                nth_rewrite 1 [hw]
                rw [inner_add_left, inner_add_left, real_inner_smul_left]
              rw [e]; linarith
            exact inner_self_eq_zero.mp h2
          have hstepA : ∀ k, M k / 12 * ‖x (k+1) - x k‖ ^ 3 ≤ f (x k) - f (x (k+1)) := by
            intro k
            have hfoc' := hfoc k
            have hacc := hrun.accept k
            have hneg := hrun.step k (x k - (x (k+1) - x k))
            simp only [CubicNewton.Shared.cubicModel] at hacc hneg
            have e1 : x k - (x (k+1) - x k) - x k = -(x (k+1) - x k) := by abel
            rw [e1] at hneg
            simp only [map_neg, inner_neg_left, inner_neg_right, norm_neg, neg_neg] at hneg
            have hr := congrArg (fun w => inner ℝ w (x (k+1) - x k)) hfoc'
            simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
              real_inner_self_eq_norm_sq] at hr
            have hM0 : 0 ≤ M k := hL₀.le.trans (hrun.param_mem k).1
            nlinarith [norm_nonneg (x (k+1) - x k)]
          have hstepB : ∀ k, ‖g (x (k+1))‖ ≤ (L + M k) / 2 * ‖x (k+1) - x k‖ ^ 2 := by
            intro k
            have ht := htaylor _ (hint k) _ (hint (k+1))
            have hw : g (x k) + H (x k) (x (k+1) - x k)
                = -(((M k / 2) * ‖x (k+1) - x k‖) • (x (k+1) - x k)) :=
              eq_neg_of_add_eq_zero_left (hfoc k)
            have hM0 : 0 ≤ M k := hL₀.le.trans (hrun.param_mem k).1
            have hn : ‖g (x k) + H (x k) (x (k+1) - x k)‖ = M k / 2 * ‖x (k+1) - x k‖ ^ 2 := by
              rw [hw, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]; ring
            calc ‖g (x (k+1))‖ = ‖(g (x (k+1)) - g (x k) - H (x k) (x (k+1) - x k))
                  + (g (x k) + H (x k) (x (k+1) - x k))‖ := by congr 1; abel
              _ ≤ ‖g (x (k+1)) - g (x k) - H (x k) (x (k+1) - x k)‖
                  + ‖g (x k) + H (x k) (x (k+1) - x k)‖ := norm_add_le _ _
              _ ≤ L / 2 * ‖x (k+1) - x k‖ ^ 2 + M k / 2 * ‖x (k+1) - x k‖ ^ 2 := by
                  rw [hn]; linarith
              _ = _ := by ring
          have hΔnn : ∀ k, 0 ≤ f (x k) - f xs := fun k => sub_nonneg.2 (hmin _)
          have hrec : ∀ k, (f (x (k+1)) - f xs) ^ 3 ≤ ω * (f (x k) - f (x (k+1))) ^ 2 := by
            intro k
            have hA := hstepA k
            have hB := hstepB k
            have hD := hdomF _ (interior_subset (hint (k+1)))
            have hm1 : L₀ ≤ M k := (hrun.param_mem k).1
            have hm2 : M k ≤ 2 * L := (hrun.param_mem k).2
            have hM0 : 0 ≤ M k := hL₀.le.trans hm1
            have hpoly : L₀ ^ 2 * (L + M k) ^ 3 ≤ M k ^ 2 * (L + L₀) ^ 3 := by
              have key : M k ^ 2 * (L + L₀) ^ 3 - L₀ ^ 2 * (L + M k) ^ 3 = (M k - L₀) *
                  (L₀ ^ 2 * (M k - L₀) * (2 * L - M k) + (2 * L - M k) * L₀ * (L + L₀) ^ 2
                    + (M k - L₀) * L ^ 2 * (L + 4 * L₀)) := by ring
              have h1 : 0 ≤ M k - L₀ := sub_nonneg.2 hm1
              have h2 : 0 ≤ 2 * L - M k := sub_nonneg.2 hm2
              have : 0 ≤ (M k - L₀) *
                  (L₀ ^ 2 * (M k - L₀) * (2 * L - M k) + (2 * L - M k) * L₀ * (L + L₀) ^ 2
                    + (M k - L₀) * L ^ 2 * (L + 4 * L₀)) := by positivity
              linarith
            set ρ := ‖x (k+1) - x k‖ with hρ
            have hρ0 : 0 ≤ ρ := norm_nonneg _
            have h1 : (f (x (k+1)) - f xs) ^ 3 ≤ (τ * ‖g (x (k+1))‖) ^ 3 :=
              pow_le_pow_left₀ (hΔnn _) hD 3
            have h2 : (τ * ‖g (x (k+1))‖) ^ 3 ≤ (τ * ((L + M k) / 2 * ρ ^ 2)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hB hτ.le) 3
            have h3 : (M k / 12 * ρ ^ 3) ^ 2 ≤ (f (x k) - f (x (k+1))) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hA 2
            have hq : (L + M k) ^ 3 ≤ M k ^ 2 * (L + L₀) ^ 3 / L₀ ^ 2 := by
              rw [le_div_iff₀ (by positivity)]; linarith
            have h4 : (τ * ((L + M k) / 2 * ρ ^ 2)) ^ 3 ≤ ω * (M k / 12 * ρ ^ 3) ^ 2 := by
              calc (τ * ((L + M k) / 2 * ρ ^ 2)) ^ 3 = τ ^ 3 * ρ ^ 6 / 8 * (L + M k) ^ 3 := by ring
                _ ≤ τ ^ 3 * ρ ^ 6 / 8 * (M k ^ 2 * (L + L₀) ^ 3 / L₀ ^ 2) := by gcongr
                _ = ω * (M k / 12 * ρ ^ 3) ^ 2 := by rw [hω]; field_simp; ring
            have h5 : ω * (M k / 12 * ρ ^ 3) ^ 2 ≤ ω * (f (x k) - f (x (k+1))) ^ 2 :=
              mul_le_mul_of_nonneg_left h3 hωpos.le
            linarith
          obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ k, δ k = 1 / ω * (f (x k) - f xs) := ⟨_, fun k => rfl⟩
          have hδnn : ∀ k, 0 ≤ δ k := fun k => by
            rw [hδ]; exact mul_nonneg (by positivity) (hΔnn k)
          have hδmono : ∀ k, δ (k+1) ≤ δ k := fun k => by
            rw [hδ, hδ]; exact mul_le_mul_of_nonneg_left (by linarith [hdec k]) (by positivity)
          have hδrec : ∀ k, δ (k+1) ^ 3 ≤ (δ k - δ (k+1)) ^ 2 := by
            intro k
            have h := hrec k
            rw [hδ, hδ]
            have e1 : (1 / ω * (f (x (k+1)) - f xs)) ^ 3 = (f (x (k+1)) - f xs) ^ 3 / ω ^ 3 := by
              field_simp
            have e2 : (1 / ω * (f (x k) - f xs) - 1 / ω * (f (x (k+1)) - f xs)) ^ 2
                = ω * (f (x k) - f (x (k+1))) ^ 2 / ω ^ 3 := by
              field_simp; ring
            rw [e1, e2]; exact div_le_div_of_nonneg_right h (by positivity)
          have hδanti : Antitone δ := antitone_nat_of_succ_le hδmono
          have hδ0 : δ 0 = 1 / ω * (f x₀ - f xs) := by rw [hδ, hrun.init]
          refine ⟨fun _ => ⟨?_, ?_⟩, ?_⟩
          · have hlog : ∀ k, 0 < δ k → Real.log (δ k) ≤ (2/3:ℝ)^k * Real.log (δ 0) := by
              intro k
              induction k with
              | zero => intro _; simp
              | succ k ih =>
                intro hpos
                have hk : 0 < δ k := lt_of_lt_of_le hpos (hδmono k)
                have h1 : δ (k+1) ^ 3 ≤ δ k ^ 2 := by
                  have := hδrec k
                  have h0 : 0 ≤ δ k - δ (k+1) := by linarith [hδmono k]
                  have : (δ k - δ (k+1)) ^ 2 ≤ δ k ^ 2 :=
                    pow_le_pow_left₀ h0 (by linarith [hδnn (k+1)]) 2
                  linarith
                have h2 := Real.log_le_log (by positivity) h1
                rw [Real.log_pow, Real.log_pow] at h2
                have := ih hk
                push_cast at h2
                calc Real.log (δ (k+1)) ≤ 2/3 * Real.log (δ k) := by linarith
                  _ ≤ 2/3 * ((2/3)^k * Real.log (δ 0)) := by
                      exact mul_le_mul_of_nonneg_left this (by norm_num)
                  _ = (2/3)^(k+1) * Real.log (δ 0) := by ring
            intro k hk
            rw [← hδ, ← hδ0]
            apply hlog k
            rw [hδ]; positivity
          · have hex : ∃ k, δ k ≤ 1 := by
              by_contra hcon
              push Not at hcon
              have hstep : ∀ k, δ (k+1) ≤ δ k - 1 := by
                intro k
                have h1 := hcon (k+1)
                have h2 := hδrec k
                have h3 : 1 < δ (k+1) ^ 3 := one_lt_pow₀ h1 (by norm_num)
                have h0 : 0 ≤ δ k - δ (k+1) := by linarith [hδmono k]
                nlinarith
              have hlin : ∀ k : ℕ, δ k ≤ δ 0 - k := by
                intro k; induction k with
                | zero => simp
                | succ k ih => push_cast; linarith [hstep k]
              obtain ⟨N, hN⟩ := exists_nat_gt (δ 0)
              linarith [hlin N, hδnn N]
            obtain ⟨k₀, hk₀⟩ := hex
            refine ⟨k₀, fun k hk => ?_⟩
            have h1 := (hδanti hk).trans hk₀
            rw [hδ, one_div, inv_mul_le_iff₀ hωpos] at h1
            linarith
          · intro γ hγ hγ0 k
            have hγpos : 0 < γ := by linarith
            have hδ0γ : δ 0 ≤ γ ^ 2 := by
              rw [hδ0, one_div, inv_mul_le_iff₀ hωpos]; linarith
            have hcpos : 0 < 2 + 3/2 * γ := by positivity
            set c := 2 + 3/2 * γ with hc
            have hclaim : ∀ k : ℕ, δ k ≤ (γ * c / (2 + ((k:ℝ) + 3/2) * γ)) ^ 2 := by
              intro k
              induction k with
              | zero =>
                have e : (2 + (((0:ℕ):ℝ) + 3/2) * γ) = c := by rw [hc]; push_cast; ring
                rw [e, mul_div_assoc, div_self hcpos.ne', mul_one]; exact hδ0γ
              | succ k ih =>
                have hApos : 0 < 2 + ((k:ℝ) + 3/2) * γ := by positivity
                set A := 2 + ((k:ℝ) + 3/2) * γ with hA
                have hs : 0 ≤ Real.sqrt (δ (k+1)) := Real.sqrt_nonneg _
                set s := Real.sqrt (δ (k+1)) with hs_def
                have hss : δ (k+1) = s ^ 2 := (Real.sq_sqrt (hδnn _)).symm
                have hsγ : s ≤ γ := by
                  calc s ≤ Real.sqrt (γ ^ 2) :=
                        Real.sqrt_le_sqrt (le_trans (hδanti (Nat.zero_le _)) hδ0γ)
                    _ = γ := Real.sqrt_sq hγpos.le
                have hcube : s ^ 3 ≤ δ k - s ^ 2 := by
                  have h := hδrec k
                  rw [hss] at h
                  have h0 : 0 ≤ δ k - s ^ 2 := by linarith [hδmono k]
                  have : (s ^ 3) ^ 2 ≤ (δ k - s ^ 2) ^ 2 := by nlinarith
                  exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp this
                have hk : s ^ 2 * (1 + s) ≤ (γ * c / A) ^ 2 := by nlinarith [ih]
                have hk' : s ^ 2 * (1 + s) * A ^ 2 ≤ (γ * c) ^ 2 := by
                  rw [div_pow, le_div_iff₀ (by positivity)] at hk; exact hk
                have htarget : s * (A + γ) ≤ γ * c := by
                  by_contra hcon
                  push Not at hcon
                  have hcs : 0 < c - s := by rw [hc]; linarith
                  have hlt : γ * (c - s) < s * A := by linarith
                  have hsq : (γ * (c - s)) ^ 2 < (s * A) ^ 2 :=
                    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
                  have hpoly : c ^ 2 ≤ (1 + s) * (c - s) ^ 2 := by
                    have e : (1 + s) * (c - s) ^ 2 - c ^ 2 = s * ((c - s - 1) ^ 2 - 1 - s) := by ring
                    have hge : 1 + s / 2 ≤ c - s - 1 := by rw [hc]; linarith
                    have h7 : (1 + s / 2) ^ 2 ≤ (c - s - 1) ^ 2 := pow_le_pow_left₀ (by positivity) hge 2
                    have e7 : (1 + s / 2) ^ 2 = 1 + s + s ^ 2 / 4 := by ring
                    have : 0 ≤ s * ((c - s - 1) ^ 2 - 1 - s) :=
                      mul_nonneg hs (by linarith [sq_nonneg s])
                    linarith
                  have h8 : (γ * (c - s)) ^ 2 * (1 + s) < (s * A) ^ 2 * (1 + s) :=
                    mul_lt_mul_of_pos_right hsq (by positivity)
                  have h9 : γ ^ 2 * c ^ 2 ≤ γ ^ 2 * ((1 + s) * (c - s) ^ 2) :=
                    mul_le_mul_of_nonneg_left hpoly (sq_nonneg γ)
                  have e1 : (γ * (c - s)) ^ 2 * (1 + s) = γ ^ 2 * ((1 + s) * (c - s) ^ 2) := by ring
                  have e2 : (s * A) ^ 2 * (1 + s) = s ^ 2 * (1 + s) * A ^ 2 := by ring
                  have e3 : (γ * c) ^ 2 = γ ^ 2 * c ^ 2 := by ring
                  linarith
                rw [hss]
                have hA1 : (2 + (((k+1:ℕ):ℝ) + 3/2) * γ) = A + γ := by rw [hA]; push_cast; ring
                rw [hA1]
                have : s ≤ γ * c / (A + γ) := by rw [le_div_iff₀ (by positivity)]; exact htarget
                exact pow_le_pow_left₀ hs this 2
            have h := hclaim k
            rw [hδ, one_div, inv_mul_le_iff₀ hωpos] at h
            have e : (γ * c / (2 + ((k:ℝ) + 3/2) * γ)) ^ 2
                = γ ^ 2 * c ^ 2 / (2 + ((k:ℝ) + 3/2) * γ) ^ 2 := by rw [div_pow, mul_pow]
            rw [e] at h
            exact h
