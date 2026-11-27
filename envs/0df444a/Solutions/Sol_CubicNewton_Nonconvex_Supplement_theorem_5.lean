-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:39.919351+00:00
-- url     : https://prove2.me/submissions/ee1b70a4-f3f3-45ea-b288-362065b084a9

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_StarConvex_IsStarConvexFn
import Definitions.Def_CubicNewton_Nonconvex_Supplement_IsGloballyNondegenerate

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Theorem 5, p. 190, with `ω̄ = (1/L²)(γ/2)³`. Standing assumptions of
Section 2, Assumption 1, a run of method (3.3) with `0 < L₀ ≤ L`; `f` is star-convex
(Definition 1) and its optimal set is globally non-degenerate with constant `γ` (Definition 2);
`xs` is a global minimizer. Writing `Δ_k = f(x_k) − f(x*)`, there is a first index `k₀` with
`Δ_{k₀} ≤ (4/9) ω̄` (end of the first phase; `k₀ = 0` when already `Δ₀ ≤ (4/9) ω̄`);
if `Δ₀ ≥ (4/9) ω̄`, then (4.4) holds for every `k ≤ k₀`; and (4.5) holds for every `k ≥ k₀`. -/
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
    (hstar : CubicNewton.StarConvex.IsStarConvexFn F f)
    (γ : ℝ) (hnd : IsGloballyNondegenerate F f γ)
    (ω : ℝ) (hω : ω = 1 / L ^ 2 * (γ / 2) ^ 3)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : ∀ y, f xs ≤ f y) :
    ∃ k₀ : ℕ, f (x k₀) - f xs ≤ 4 / 9 * ω ∧ (∀ j < k₀, 4 / 9 * ω < f (x j) - f xs) ∧
      (4 / 9 * ω ≤ f x₀ - f xs →
        ∀ k ≤ k₀, f (x k) - f xs ≤
          ((f x₀ - f xs) ^ (1 / 4 : ℝ) - (k : ℝ) / 6 * Real.sqrt (2 / 3) * ω ^ (1 / 4 : ℝ)) ^ 4) ∧
      ∀ k ≥ k₀, f (x (k + 1)) - f xs ≤
        1 / 2 * (f (x k) - f xs) * Real.sqrt ((f (x k) - f xs) / ω) := by
          classical
          have hγ : 0 < γ := hnd.2.1
          have hωpos : 0 < ω := by rw [hω]; positivity
          have htaylor : ∀ a ∈ interior F, ∀ b ∈ interior F,
              f a + inner ℝ (g a) (b - a) + 1/2 * inner ℝ (H a (b - a)) (b - a) ≤ f b + L/6 * ‖b - a‖^3 := by
              intro a ha b hb
              have hfA : ∀ z ∈ interior F, HasFDerivAt f (InnerProductSpace.toDual ℝ _ (g z)) z := fun z hz =>
                HasFDerivWithinAt.hasFDerivAt (hf z (interior_subset hz)) (mem_interior_iff_mem_nhds.mp hz)
              have hgA : ∀ z ∈ interior F, HasFDerivAt g (H z) z := fun z hz =>
                (hg z (interior_subset hz)).hasFDerivAt (mem_interior_iff_mem_nhds.mp hz)
              set d := b - a with hd
              have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, a + t • d ∈ interior F := by
                intro t ht
                have := hF_convex.interior ha hb (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring)
                convert this using 1
                rw [hd, smul_sub, sub_smul, one_smul]; abel
              have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a + t • d) d t := by
                intro t; simpa using ((hasDerivAt_id t).smul_const d).const_add a
              set K := L * ‖d‖^3 with hK
              set φ1 : ℝ → ℝ := fun t => f (a + t • d) - f a - t * (inner ℝ (g a) (d)) - t^2/2 * (inner ℝ (H a d) (d)) + K * t^3/6
                with hφ1
              set φ2 : ℝ → ℝ := fun t => (inner ℝ (g (a + t • d)) (d)) - (inner ℝ (g a) (d)) - t * (inner ℝ (H a d) (d)) + K * t^2/2
                with hφ2
              have h1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ1 (φ2 t) t := by
                intro t ht
                have e1 : HasDerivAt (fun t : ℝ => f (a + t • d)) (inner ℝ (g (a + t • d)) (d)) t := by
                  have := (hfA _ (hseg t ht)).comp_hasDerivAt t (hl t)
                  exact this.congr_deriv (by simp)
                have := ((((e1.sub_const (f a)).sub ((hasDerivAt_id t).mul_const (inner ℝ (g a) (d)))).sub
                  (((hasDerivAt_pow 2 t).div_const 2).mul_const (inner ℝ (H a d) (d)))).add
                  (((hasDerivAt_pow 3 t).const_mul K).div_const 6))
                exact this.congr_deriv (by simp only [hφ2]; push_cast; ring)
              have h2 : ∀ t ∈ Set.Icc (0:ℝ) 1,
                  HasDerivAt φ2 ((inner ℝ (H (a + t • d) d) (d)) - (inner ℝ (H a d) (d)) + K * t) t := by
                intro t ht
                have e1 : HasDerivAt (fun t : ℝ => g (a + t • d)) (H (a + t • d) d) t := by
                  have := (hgA _ (hseg t ht)).comp_hasDerivAt t (hl t)
                  exact this
                have e2 := e1.inner ℝ (hasDerivAt_const t d)
                have := (((e2.sub_const (inner ℝ (g a) (d))).sub ((hasDerivAt_id t).mul_const (inner ℝ (H a d) (d)))).add
                  (((hasDerivAt_pow 2 t).const_mul K).div_const 2))
                exact this.congr_deriv (by simp; ring)
              have h3 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ (inner ℝ (H (a + t • d) d) (d)) - (inner ℝ (H a d) (d)) + K * t := by
                intro t ht
                have hLt := hLip _ (interior_subset (hseg t ht)) a (interior_subset ha)
                have hnorm : ‖a + t • d - a‖ = t * ‖d‖ := by
                  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
                rw [hnorm] at hLt
                have e : (inner ℝ (H (a + t • d) d) (d)) - (inner ℝ (H a d) (d)) = (inner ℝ ((H (a + t • d) - H a) d) (d)) := by
                  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
                have hc := real_inner_le_norm ((H (a + t • d) - H a) d) d
                have hc' := abs_real_inner_le_norm ((H (a + t • d) - H a) d) d
                have hop := ContinuousLinearMap.le_opNorm (H (a + t • d) - H a) d
                have hdn := norm_nonneg d
                have : ‖(H (a + t • d) - H a) d‖ * ‖d‖ ≤ L * t * ‖d‖ ^ 3 := by
                  calc ‖(H (a + t • d) - H a) d‖ * ‖d‖ ≤ (‖H (a + t • d) - H a‖ * ‖d‖) * ‖d‖ := by gcongr
                    _ ≤ (L * (t * ‖d‖) * ‖d‖) * ‖d‖ := by gcongr
                    _ = L * t * ‖d‖ ^ 3 := by ring
                rw [e, hK]
                have := neg_abs_le (inner ℝ ((H (a + t • d) - H a) d) (d))
                nlinarith
              have hint : interior (Set.Icc (0:ℝ) 1) ⊆ Set.Icc 0 1 := interior_subset
              have hm2 : MonotoneOn φ2 (Set.Icc 0 1) :=
                monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
                  (fun t ht => (h2 t ht).continuousAt.continuousWithinAt)
                  (fun t ht => (h2 t (hint ht)).hasDerivWithinAt) (fun t ht => h3 t (hint ht))
              have hφ2nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ φ2 t := by
                intro t ht
                have := hm2 (Set.left_mem_Icc.mpr zero_le_one) ht ht.1
                simpa [hφ2] using this
              have hm1 : MonotoneOn φ1 (Set.Icc 0 1) :=
                monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
                  (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
                  (fun t ht => (h1 t (hint ht)).hasDerivWithinAt) (fun t ht => hφ2nn t (hint ht))
              have := hm1 (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
              simp only [hφ1] at this
              simp at this
              have hb' : a + d = b := by rw [hd]; abel
              rw [hb'] at this
              rw [hK] at this
              linarith
          have hmono : ∀ k, f (x (k+1)) ≤ f (x k) := by
            intro k
            have h1 := hrun.accept k
            have h2 := hrun.step k (x k)
            have h0 : CubicNewton.Shared.cubicModel g H (M k) (x k) (x k) = 0 := by
              simp [CubicNewton.Shared.cubicModel]
            linarith
          have hlev : ∀ k, f (x k) ≤ f x₀ := by
            intro k
            induction k with
            | zero => rw [hrun.init]
            | succ k ih => exact (hmono k).trans ih
          have hxint : ∀ k, x k ∈ interior F := fun k => hlevel (hlev k)
          have hXsint : ∀ z ∈ {z | ∀ y, f z ≤ f y}, z ∈ interior F :=
            fun z hz => hlevel (show f z ≤ f x₀ from hz x₀)
          have hXs_eq : {z | ∀ y, f z ≤ f y} = F ∩ f ⁻¹' Set.Iic (f xs) := by
            ext z; constructor
            · intro hz; exact ⟨interior_subset (hXsint z hz), hz xs⟩
            · rintro ⟨_, hz⟩ y; exact le_trans hz (hxs y)
          have hcont : ContinuousOn f F := fun z hz => HasFDerivWithinAt.continuousWithinAt (hf z hz)
          have hXs_closed : IsClosed {z | ∀ y, f z ≤ f y} := by
            rw [hXs_eq]; exact hcont.preimage_isClosed_of_isClosed hF_closed isClosed_Iic
          have hmodel : ∀ k, ∀ y ∈ interior F, f (x (k+1)) ≤ f y + L/2 * ‖y - x k‖^3 := by
            intro k y hy
            have h1 := hrun.accept k
            have h2 := hrun.step k y
            have h3 := htaylor (x k) (hxint k) y hy
            have hM := hrun.param_mem k
            unfold CubicNewton.Shared.cubicModel at h1 h2
            have hn := pow_nonneg (norm_nonneg (y - x k)) 3
            have : M k / 6 * ‖y - x k‖^3 ≤ 2 * L / 6 * ‖y - x k‖^3 := by
              apply mul_le_mul_of_nonneg_right _ hn; linarith [hM.2]
            linarith
          have hrec : ∀ k, ∀ α ∈ Set.Icc (0:ℝ) 1,
              f (x (k+1)) - f xs ≤ (1 - α) * (f (x k) - f xs)
                + L/2 * α^3 * Metric.infDist (x k) {z | ∀ y, f z ≤ f y} ^ 3 := by
            intro k α hα
            obtain ⟨z, hz, hzd⟩ := hXs_closed.exists_infDist_eq_dist ⟨xs, hxs⟩ (x k)
            have hzeq : f z = f xs := le_antisymm (hz xs) (hxs z)
            have hy : α • z + (1 - α) • x k ∈ interior F :=
              hF_convex.interior (hXsint z hz) (hxint k) hα.1 (by linarith [hα.2]) (by ring)
            have hs := hstar.2 z hz (x k) (interior_subset (hxint k)) α hα
            have hm := hmodel k _ hy
            have hnorm : ‖α • z + (1 - α) • x k - x k‖ = α * Metric.infDist (x k) {z | ∀ y, f z ≤ f y} := by
              rw [hzd, dist_eq_norm, show α • z + (1 - α) • x k - x k = α • (z - x k) by
                rw [smul_sub, sub_smul, one_smul]; abel, norm_smul, Real.norm_of_nonneg hα.1, norm_sub_rev]
            rw [hnorm, mul_pow] at hm
            rw [hzeq] at hs
            nlinarith
          have hcube : ∀ k, L * Metric.infDist (x k) {z | ∀ y, f z ≤ f y} ^ 3 ≤
              (f (x k) - f xs) * Real.sqrt ((f (x k) - f xs) / ω) := by
            intro k
            have hρ0 : 0 ≤ Metric.infDist (x k) {z | ∀ y, f z ≤ f y} := Metric.infDist_nonneg
            have hnd' := hnd.2.2 (x k) (interior_subset (hxint k)) xs hxs
            set ρ := Metric.infDist (x k) {z | ∀ y, f z ≤ f y} with hρ
            set D := f (x k) - f xs with hD
            have hD0 : 0 ≤ D := by rw [hD]; linarith [hxs (x k)]
            have hs0 := Real.sqrt_nonneg (D/ω)
            have hs2 : Real.sqrt (D/ω) ^ 2 = D/ω := Real.sq_sqrt (div_nonneg hD0 hωpos.le)
            apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hD0 hs0)
            rw [mul_pow, mul_pow, hs2]
            have e : D^2 * (D/ω) = D^3 * L^2 / (γ/2)^3 := by rw [hω]; field_simp
            rw [e, le_div_iff₀ (by positivity)]
            calc L^2 * (ρ^3)^2 * (γ/2)^3 = L^2 * (γ/2*ρ^2)^3 := by ring
              _ ≤ L^2 * D^3 := by gcongr
              _ = D^3 * L^2 := by ring
          have h45 : ∀ k, f (x (k + 1)) - f xs ≤
              1 / 2 * (f (x k) - f xs) * Real.sqrt ((f (x k) - f xs) / ω) := by
            intro k
            have h1 := hrec k 1 ⟨zero_le_one, le_refl 1⟩
            have h2 := hcube k
            norm_num at h1
            linarith
          have q4 : ∀ y : ℝ, 0 ≤ y → (y ^ (1/4:ℝ))^4 = y := fun y hy => by
            rw [show (1/4:ℝ) = ((4:ℕ):ℝ)⁻¹ by norm_num]; exact Real.rpow_inv_natCast_pow hy (by norm_num)
          have hdec : ∀ k, 4/9*ω < f (x k) - f xs →
              (f (x (k+1)) - f xs)^(1/4:ℝ) ≤ (f (x k) - f xs)^(1/4:ℝ) - 1/6 * Real.sqrt (2/3) * ω^(1/4:ℝ) := by
            intro k hk
            have hC := hcube k
            have hD'0 : 0 ≤ f (x (k+1)) - f xs := by linarith [hxs (x (k+1))]
            set D := f (x k) - f xs with hD
            set D' := f (x (k+1)) - f xs with hD'
            set u := D ^ (1/4:ℝ) with hu
            set w := ω ^ (1/4:ℝ) with hw
            set v := D' ^ (1/4:ℝ) with hv
            set r := Real.sqrt (2/3) with hr
            have hD0 : 0 < D := by linarith
            have hu4 : u^4 = D := q4 D hD0.le
            have hw4 : w^4 = ω := q4 ω hωpos.le
            have hv4 : v^4 = D' := q4 D' hD'0
            have hu0 : 0 < u := Real.rpow_pos_of_pos hD0 _
            have hw0 : 0 < w := Real.rpow_pos_of_pos hωpos _
            have hv0 : 0 ≤ v := Real.rpow_nonneg hD'0 _
            have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
            have hr2 : r^2 = 2/3 := Real.sq_sqrt (by norm_num)
            have hsq : Real.sqrt (D/ω) = u^2/w^2 := by
              rw [← hu4, ← hw4, show u^4/w^4 = (u^2/w^2)^2 by ring]; exact Real.sqrt_sq (by positivity)
            have hu2 : 2/3 * w^2 < u^2 := by
              have : (2/3*w^2)^2 < (u^2)^2 := by
                rw [show (2/3*w^2)^2 = 4/9*w^4 by ring, show (u^2)^2 = u^4 by ring, hu4, hw4]; exact hk
              exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
            have hrw : r * w < u := by
              apply lt_of_pow_lt_pow_left₀ 2 hu0.le; rw [mul_pow, hr2]; exact hu2
            set α := r * w / u with hα
            have hα0 : 0 ≤ α := by positivity
            have hα1 : α ≤ 1 := by rw [hα, div_le_one hu0]; exact hrw.le
            have hR := hrec k α ⟨hα0, hα1⟩
            rw [hsq] at hC
            have hα3 := pow_nonneg hα0 3
            have hstep : D' ≤ (1-α)*D + 1/2*α^3*(D*(u^2/w^2)) := by
              nlinarith [mul_le_mul_of_nonneg_left hC hα3]
            have r3 : r^3 = 2/3*r := by rw [pow_succ, hr2]
            have hval : (1-α)*D + 1/2*α^3*(D*(u^2/w^2)) = u^4 - r*w*u^3 + 1/2*r^3*w*u^3 := by
              rw [hα, ← hu4]; field_simp
            rw [hval, r3] at hstep
            by_contra hcon
            push Not at hcon
            have hc0 : 0 < r * w / 6 := by positivity
            have hlt : (u - r*w/6)^4 < v^4 := by
              have : u - r*w/6 < v := by linarith
              exact pow_lt_pow_left₀ this (by linarith) (by norm_num)
            have hb := mul_nonneg (sq_nonneg (r*w/6))
              (add_nonneg (mul_nonneg zero_le_two (sq_nonneg u)) (sq_nonneg (2*u - r*w/6)))
            have hid : (u - r*w/6)^4 - (u^4 - 4*(r*w/6)*u^3) =
                (r*w/6)^2 * (2*u^2 + (2*u - r*w/6)^2) := by ring
            have hbern : u^4 - 4*(r*w/6)*u^3 ≤ (u - r*w/6)^4 := by
              have : 0 ≤ (r*w/6)^2 * (2*u^2 + (2*u - r*w/6)^2) := by positivity
              linarith
            have e4 : 4*(r*w/6)*u^3 = r*w*u^3 - 1/2*(2/3*r)*w*u^3 := by ring
            rw [e4] at hbern
            linarith
          have hphase : ∀ k : ℕ, (∀ j < k, 4/9*ω < f (x j) - f xs) →
              (f (x k) - f xs)^(1/4:ℝ) ≤
                (f x₀ - f xs)^(1/4:ℝ) - (k:ℝ)/6 * Real.sqrt (2/3) * ω^(1/4:ℝ) := by
            intro k
            induction k with
            | zero => intro _; simp [hrun.init]
            | succ k ih =>
              intro h
              have h1 := hdec k (h k (lt_add_one k))
              have h2 := ih (fun j hj => h j (by omega))
              push_cast
              linarith
          have hrw0 : 0 < Real.sqrt (2/3) * ω^(1/4:ℝ) :=
            mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.rpow_pos_of_pos hωpos _)
          have hex : ∃ k, f (x k) - f xs ≤ 4/9*ω := by
            by_contra hne
            push Not at hne
            obtain ⟨N, hN⟩ := exists_nat_gt (6 * (f x₀ - f xs)^(1/4:ℝ) / (Real.sqrt (2/3) * ω^(1/4:ℝ)))
            have h1 := hphase N (fun j _ => hne j)
            have h0 : 0 ≤ (f (x N) - f xs)^(1/4:ℝ) := Real.rpow_nonneg (by linarith [hxs (x N)]) _
            rw [div_lt_iff₀ hrw0] at hN
            nlinarith
          refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj),
            fun _ k hk => ?_, fun k _ => h45 k⟩
          have h1 := hphase k (fun j hj => not_le.mp (Nat.find_min hex (lt_of_lt_of_le hj hk)))
          have hD0 : 0 ≤ f (x k) - f xs := by linarith [hxs (x k)]
          calc f (x k) - f xs = ((f (x k) - f xs)^(1/4:ℝ))^4 := (q4 _ hD0).symm
            _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hD0 _) h1 4
