-- Prove2me | solution 1 for BregmanPPA.EqMult.Supplement.theorem5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:13.830987+00:00
-- url     : https://prove2.me/submissions/2da59cd1-38e2-4244-874e-66885c7c0cbd

import Mathlib
import Definitions.Def_BregmanPPA_EqMult_Supplement_PrimalRun

open BregmanPPA.Convergence InertialFB.IFB Filter Topology

open BregmanPPA
open BregmanPPA.EqMult
open BregmanPPA.EqMult.Supplement

/-- Theorem 5: convergence, existence under (i), divergence under (i), and a concrete
refutation of the printed existence claim (ii). The last printed `on h` is read `on X`.
No premise is added to repair (ii): the explicit counterexample replaces that false clause. -/
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (S : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℕ → ℝ) (hP : BregmanPPA.EqMult.IsEqProgram X f)
    (hh : IsBregmanFunction S h)
    (hri : intrinsicInterior ℝ (effectiveFeasible X f) ⊆ S)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k) :
    (∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsPrimalRun S X h f c x →
      (∃ z, IsMinimizer X f z) →
      ∃ z, IsMinimizer X f z ∧ Tendsto x atTop (𝓝 z)) ∧
    (AlternativeI S X h f → ∀ x₀ ∈ S,
      ∃ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x₀ ∧ IsPrimalRun S X h f c x) ∧
    (∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsPrimalRun S X h f c x →
      AlternativeI S X h f → (¬ ∃ z, IsMinimizer X f z) →
      ¬ Bornology.IsBounded (Set.range x)) ∧
    (IsBregmanFunction (Set.Ioi (0 : ℝ)) (fun t : ℝ => t ^ 2 / 2) ∧
      IsProperFn (fun t : ℝ => (t : EReal)) ∧
      IsConvexFn (fun t : ℝ => (t : EReal)) ∧
      LowerSemicontinuous (fun t : ℝ => (t : EReal)) ∧
      IsClosed (Set.Ici (0 : ℝ)) ∧ Convex ℝ (Set.Ici (0 : ℝ)) ∧
      (∃ z ∈ Set.Ici (0 : ℝ), (z : EReal) ≠ ⊤) ∧
      intrinsicInterior ℝ (effectiveFeasible (Set.Ici (0 : ℝ)) (fun t : ℝ => (t : EReal))) ⊆
        Set.Ioi (0 : ℝ) ∧
      AlternativeII (Set.Ici (0 : ℝ)) (fun t : ℝ => (t : EReal)) ∧
      (∀ k : ℕ, 0 < (fun _ : ℕ => (1 : ℝ)) k) ∧
      (∃ ε > 0, ∀ k : ℕ, ε ≤ (fun _ : ℕ => (1 : ℝ)) k) ∧
      (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) ∧
      ¬ ∃ x : ℕ → ℝ, x 0 = 1 / 2 ∧
        IsPrimalRun (Set.Ioi 0) (Set.Ici 0) (fun t : ℝ => t ^ 2 / 2)
          (fun t : ℝ => (t : EReal)) (fun _ => 1) x) := by
            have key : (∀ z ∈ closure S, ∀ y ∈ S, 0 ≤ bregmanD h z y) ∧ (∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsPrimalRun S X h f c x → ∀ k, ∀ z ∈ X, z ∈ closure S → f z ≠ ⊤ → bregmanD h z (x (k+1)) + c k * ((f (x (k+1))).toReal - (f z).toReal) ≤ bregmanD h z (x k)) := by
              have slope_le : ∀ (φ : ℝ → ℝ) (d a : ℝ), HasDerivAt φ d 0 →
                  (∀ t ∈ Set.Ioc (0:ℝ) 1, a * t ≤ φ t - φ 0) → a ≤ d := by
                intro φ d a hd hle
                have h1 := hd.tendsto_slope_zero_right
                apply ge_of_tendsto h1
                filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
                have := hle t ⟨ht.1, ht.2.le⟩
                simp only [zero_add, smul_eq_mul]
                rw [inv_mul_eq_div, le_div_iff₀ ht.1]
                linarith
              have hline : ∀ y ∈ S, ∀ v : EuclideanSpace ℝ (Fin n),
                  HasDerivAt (fun t : ℝ => h (y + t • v)) (inner ℝ (gradient h y) v) 0 := by
                intro y hy v
                have hd : DifferentiableAt ℝ h y :=
                  (hh.contDiffOn.differentiableOn one_ne_zero y hy).differentiableAt (hh.isOpen.mem_nhds hy)
                have hg : HasFDerivAt h (fderiv ℝ h y) (y + (0:ℝ) • v) := by
                  simpa using hd.hasFDerivAt
                have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
                  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
                have := hg.comp_hasDerivAt (0:ℝ) hl
                have e : (fderiv ℝ h y) v = inner ℝ (gradient h y) v := by
                  rw [hd.hasGradientAt.hasFDerivAt.fderiv]; simp
                rw [e] at this
                exact this
              have hcvx : Convex ℝ (closure S) := hh.strictConvexOn.1
              have part1 : ∀ z ∈ closure S, ∀ y ∈ S, 0 ≤ bregmanD h z y := by
                intro z hz y hy
                have hd := (hline y hy (z - y)).neg
                have := slope_le _ _ (h y - h z) hd (by
                  intro t ht
                  have hmem := hh.strictConvexOn.convexOn.2 (subset_closure hy) hz
                    (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring)
                  have heq : y + t • (z - y) = (1 - t) • y + t • z := by module
                  simp only [Pi.neg_apply, zero_smul, add_zero]
                  rw [heq]
                  simp only [smul_eq_mul] at hmem
                  linarith)
                unfold bregmanD
                linarith
              refine ⟨part1, ?_⟩
              intro x hx k z hzX hzS hzf
              set x1 := x (k+1) with hx1def
              set xk := x k with hxkdef
              have hx1S : x1 ∈ S := hx.1 (k+1)
              have hxkS : xk ∈ S := hx.1 k
              obtain ⟨hx1X, hx1f, hmin⟩ := hx.2 k
              rw [← hx1def] at hx1X hx1f hmin
              rw [← hxkdef] at hmin
              set v := z - x1 with hv
              set a1 := (f x1).toReal with ha1
              set b := (f z).toReal with hb
              have hfa1 : f x1 = (a1 : EReal) := (EReal.coe_toReal hx1f (hP.ne_bot _)).symm
              have hfb : f z = (b : EReal) := (EReal.coe_toReal hzf (hP.ne_bot _)).symm
              have hck := hc k
              set φ : ℝ → ℝ := fun t => h (x1 + t • v) - h xk - inner ℝ (gradient h xk) (x1 - xk)
                - t * inner ℝ (gradient h xk) v with hφ
              have hφD : ∀ t : ℝ, φ t = bregmanD h (x1 + t • v) xk := by
                intro t
                simp only [hφ, bregmanD]
                rw [show x1 + t • v - xk = (x1 - xk) + t • v by abel, inner_add_right, inner_smul_right]
                ring
              have hφd : HasDerivAt φ (inner ℝ (gradient h x1) v - inner ℝ (gradient h xk) v) 0 := by
                have := (((hline x1 hx1S v).sub_const (h xk)).sub_const
                  (inner ℝ (gradient h xk) (x1 - xk))).sub (hasDerivAt_mul_const (inner ℝ (gradient h xk) v))
                exact this
              have hslope := slope_le φ _ (c k * (a1 - b)) hφd (by
                intro t ht
                have heq : x1 + t • v = (1 - t) • x1 + t • z := by rw [hv]; module
                have hzt_X : x1 + t • v ∈ X := by
                  rw [heq]; exact hP.convex hx1X hzX (by linarith [ht.2]) ht.1.le (by ring)
                have hzt_S : x1 + t • v ∈ closure S := by
                  rw [heq]; exact hcvx (subset_closure hx1S) hzS (by linarith [ht.2]) ht.1.le (by ring)
                have hm := hmin _ hzt_X
                simp only [primalObjective, if_pos hzt_S, if_pos (subset_closure hx1S)] at hm
                have hepi := hP.convexFn (show ((x1, a1) : _ × ℝ) ∈ {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ (p.2 : EReal)} by
                    simp [hfa1])
                  (show ((z, b) : _ × ℝ) ∈ {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ (p.2 : EReal)} by
                    simp [hfb]) (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring)
                simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
                  smul_eq_mul] at hepi
                rw [← heq] at hepi
                have h2 : f x1 + (((c k)⁻¹ * bregmanD h x1 xk : ℝ) : EReal) ≤
                    (((1 - t) * a1 + t * b : ℝ) : EReal) + (((c k)⁻¹ * bregmanD h (x1 + t • v) xk : ℝ) : EReal) :=
                  hm.trans (add_le_add_left hepi _)
                rw [hfa1, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
                have h0 : φ 0 = bregmanD h x1 xk := by rw [hφD]; simp
                rw [hφD t, h0]
                have h3 : t * (a1 - b) ≤ (c k)⁻¹ * (bregmanD h (x1 + t • v) xk - bregmanD h x1 xk) := by
                  nlinarith
                have h4 := mul_le_mul_of_nonneg_left h3 hck.le
                rw [mul_inv_cancel_left₀ hck.ne'] at h4
                linarith [mul_assoc (c k) t (a1 - b), mul_right_comm (c k) t (a1 - b)])
              have h3pt : bregmanD h z xk = bregmanD h z x1 + bregmanD h x1 xk +
                  inner ℝ (gradient h x1 - gradient h xk) v := by
                simp only [bregmanD]
                rw [show z - xk = v + (x1 - xk) by rw [hv]; abel, inner_add_right, inner_sub_left]
                ring
              have hD0 := part1 x1 (subset_closure hx1S) xk hxkS
              rw [h3pt, inner_sub_left]
              linarith
            obtain ⟨hD0, hKEY⟩ := key
            have hclos : effectiveFeasible X f ⊆ closure S := by
              have hCconv : Convex ℝ (effectiveFeasible X f) := by
                intro x hx y hy a b ha hb hab
                refine ⟨hP.convex hx.1 hy.1 ha hb hab, ?_⟩
                have hxe : ((x, (f x).toReal) : EuclideanSpace ℝ (Fin n) × ℝ) ∈
                    {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
                  show f x ≤ (((f x).toReal : ℝ) : EReal)
                  rw [EReal.coe_toReal hx.2 (hP.ne_bot x)]
                have hye : ((y, (f y).toReal) : EuclideanSpace ℝ (Fin n) × ℝ) ∈
                    {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
                  show f y ≤ (((f y).toReal : ℝ) : EReal)
                  rw [EReal.coe_toReal hy.2 (hP.ne_bot y)]
                have := hP.convexFn hxe hye ha hb hab
                simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
                  Prod.smul_snd] at this
                exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this
              obtain ⟨z0, hz0X, hz0f⟩ := hP.finite_on_X
              have hCne : (effectiveFeasible X f).Nonempty := ⟨z0, hz0X, hz0f⟩
              obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior hCconv hCne
              obtain ⟨y0, hy0, hyp⟩ := mem_intrinsicInterior.1 hp
              rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy0
              obtain ⟨ε, hε, hball⟩ := hy0
              have hpA : p ∈ affineSpan ℝ (effectiveFeasible X f) := hyp ▸ y0.2
              intro z hz
              have hzA : z ∈ affineSpan ℝ (effectiveFeasible X f) := subset_affineSpan ℝ _ hz
              have hw : ∀ t : ℝ, 0 < t → t ≤ 1 → z + t • (p - z) ∈ S := by
                intro t ht ht1
                apply hri
                have hwA : z + t • (p - z) ∈ affineSpan ℝ (effectiveFeasible X f) := by
                  have := AffineSubspace.smul_vsub_vadd_mem _ t hpA hzA hzA
                  simpa [vsub_eq_sub, vadd_eq_add, add_comm] using this
                refine mem_intrinsicInterior.2 ⟨⟨_, hwA⟩, ?_, rfl⟩
                rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
                refine ⟨t * ε, mul_pos ht hε, ?_⟩
                intro q hq
                rw [Metric.mem_ball, Subtype.dist_eq] at hq
                simp only [Set.mem_preimage]
                have hq'A : z + t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - z) ∈
                    affineSpan ℝ (effectiveFeasible X f) := by
                  have := AffineSubspace.smul_vsub_vadd_mem _ t⁻¹ q.2 hzA hzA
                  simpa [vsub_eq_sub, vadd_eq_add, add_comm] using this
                have hq'C : z + t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - z) ∈ effectiveFeasible X f := by
                  have : (⟨_, hq'A⟩ : affineSpan ℝ (effectiveFeasible X f)) ∈ Metric.ball y0 ε := by
                    rw [Metric.mem_ball, Subtype.dist_eq, hyp]
                    have heq : z + t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - z) - p
                        = t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - (z + t • (p - z))) := by
                      rw [smul_sub (t⁻¹) (q : EuclideanSpace ℝ (Fin n)) (z + t • (p - z)), smul_add,
                        smul_smul, inv_mul_cancel₀ ht.ne', one_smul, smul_sub]
                      abel
                    show dist (z + t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - z)) p < ε
                    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht),
                      ← dist_eq_norm, inv_mul_lt_iff₀ ht]
                    exact hq
                  exact hball this
                have hqeq : (q : EuclideanSpace ℝ (Fin n)) =
                    z + t • ((z + t⁻¹ • ((q : EuclideanSpace ℝ (Fin n)) - z)) - z) := by
                  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
                  abel
                rw [hqeq]
                exact hCconv.add_smul_sub_mem hz hq'C ⟨ht.le, ht1⟩
              have htend : Tendsto (fun t : ℝ => z + t • (p - z)) (𝓝[>] 0) (𝓝 z) := by
                apply tendsto_nhdsWithin_of_tendsto_nhds
                have : Continuous (fun t : ℝ => z + t • (p - z)) := by continuity
                simpa using this.tendsto 0
              apply mem_closure_of_tendsto htend
              filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
              exact hw t ht.1 ht.2
            refine ⟨?p1, ?p2, ?p3, ?p4⟩
            case p1 =>
              intro x hx ⟨zs, hzs⟩
              obtain ⟨ε, hε, hεc⟩ := hcinf
              set a : ℕ → ℝ := fun k => (f (x (k+1))).toReal with ha_def
              have hfin : ∀ k, f (x (k+1)) = ((a k : ℝ) : EReal) := by
                intro k
                simp only [ha_def]
                exact (EReal.coe_toReal (hx.2 k).2.1 (hP.ne_bot _)).symm
              -- minimizers: D(z, x ·) antitone
              have hminanti : ∀ z, IsMinimizer X f z → z ∈ closure S →
                  ∀ k, bregmanD h z (x (k+1)) ≤ bregmanD h z (x k) := by
                intro z hz hzc k
                have h1 := hKEY x hx k z hz.1 hzc hz.2.1
                have h2 : f z ≤ f (x (k+1)) := hz.2.2 _ (hx.2 k).1
                have e2 : f z = (((f z).toReal : ℝ) : EReal) :=
                  (EReal.coe_toReal hz.2.1 (hP.ne_bot _)).symm
                rw [hfin k, e2] at h2
                have h3 := EReal.coe_le_coe_iff.mp h2
                have : 0 ≤ c k * ((f (x (k+1))).toReal - (f z).toReal) :=
                  mul_nonneg (le_of_lt (hc k)) (by simp only [ha_def] at h3; linarith)
                linarith
              have hzscl : zs ∈ closure S := hclos ⟨hzs.1, hzs.2.1⟩
              set fstar := (f zs).toReal with hfstar
              have ezs : f zs = (fstar : EReal) := (EReal.coe_toReal hzs.2.1 (hP.ne_bot _)).symm
              have hage : ∀ k, fstar ≤ a k := by
                intro k
                have h2 : f zs ≤ f (x (k+1)) := hzs.2.2 _ (hx.2 k).1
                rw [hfin k, ezs] at h2
                exact EReal.coe_le_coe_iff.mp h2
              -- bounded
              have hbdd : Bornology.IsBounded (Set.range x) := by
                apply (hh.bounded_L₂ (bregmanD h zs (x 0)) zs hzscl).subset
                rintro _ ⟨k, rfl⟩
                refine ⟨hx.1 k, ?_⟩
                have : Antitone (fun k => bregmanD h zs (x k)) :=
                  antitone_nat_of_succ_le (hminanti zs hzs hzscl)
                exact this (Nat.zero_le k)
              have hDself : ∀ y, bregmanD h y y = 0 := by
                intro y; simp [bregmanD]
              have hstep : ∀ k, a (k+1) ≤ a k := by
                intro k
                have h1 := hKEY x hx (k+1) (x (k+1)) (hx.2 k).1 (subset_closure (hx.1 (k+1))) (hx.2 k).2.1
                rw [hDself] at h1
                have h2 := hD0 (x (k+1)) (subset_closure (hx.1 (k+1))) (x (k+1+1)) (hx.1 _)
                have h3 : c (k+1) * (a (k+1) - a k) ≤ 0 := by simp only [ha_def]; linarith
                have hc1 := hc (k+1)
                by_contra hcon
                have : 0 < c (k+1) * (a (k+1) - a k) := mul_pos hc1 (by linarith)
                linarith
              have hanti : Antitone a := antitone_nat_of_succ_le hstep
              have hsum : ∀ k : ℕ, ((k:ℝ)+1) * ε * (a k - fstar) + bregmanD h zs (x (k+1))
                  ≤ bregmanD h zs (x 0) := by
                intro k
                induction k with
                | zero =>
                  have h1 := hKEY x hx 0 zs hzs.1 hzscl hzs.2.1
                  have h2 : ε * (a 0 - fstar) ≤ c 0 * (a 0 - fstar) :=
                    mul_le_mul_of_nonneg_right (hεc 0) (by linarith [hage 0])
                  simp only [ha_def] at h1 h2 ⊢
                  push_cast
                  linarith
                | succ k ih =>
                  have h1 := hKEY x hx (k+1) zs hzs.1 hzscl hzs.2.1
                  have h2 : ε * (a (k+1) - fstar) ≤ c (k+1) * (a (k+1) - fstar) :=
                    mul_le_mul_of_nonneg_right (hεc (k+1)) (by linarith [hage (k+1)])
                  have h3 : ((k:ℝ)+1) * ε * (a (k+1) - fstar) ≤ ((k:ℝ)+1) * ε * (a k - fstar) := by
                    apply mul_le_mul_of_nonneg_left (by linarith [hstep k])
                    positivity
                  simp only [ha_def] at h1 h2 h3 ih ⊢
                  push_cast
                  nlinarith
              -- subsequence
              obtain ⟨xbar, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd
                (x := fun k => x (k+1)) (fun k => ⟨k+1, rfl⟩)
              have hxbarX : xbar ∈ X := by
                apply hP.closed.mem_of_tendsto hlim
                exact Eventually.of_forall (fun j => (hx.2 (φ j)).1)
              have hfle : f xbar ≤ (fstar : EReal) := by
                by_contra hcon
                push_neg at hcon
                obtain ⟨y, hy1, hy2⟩ := exists_between hcon
                have hyt : y ≠ ⊤ := ne_top_of_lt hy2
                have hyb : y ≠ ⊥ := ne_bot_of_gt hy1
                have ey : y = ((y.toReal : ℝ) : EReal) := (EReal.coe_toReal hyt hyb).symm
                set r := y.toReal
                have hr : fstar < r := by rw [ey] at hy1; exact EReal.coe_lt_coe_iff.mp hy1
                have hev := hP.lsc xbar y hy2
                have hev2 := hlim.eventually hev
                have hD0' := hD0 zs hzscl
                obtain ⟨K, hK⟩ := exists_nat_gt (bregmanD h zs (x 0) / (ε * (r - fstar)))
                obtain ⟨j, hj⟩ := (hev2.and (eventually_ge_atTop K)).exists
                have hle : a (φ j) ≤ a K := hanti (le_trans hj.2 (hφ.id_le j))
                have := hj.1
                simp only [Function.comp, hfin] at this
                rw [ey] at this
                have hlt := EReal.coe_lt_coe_iff.mp this
                have hs := hsum K
                have hD := hD0' (x (K+1)) (hx.1 _)
                have hpos : 0 < ε * (r - fstar) := mul_pos hε (by linarith)
                rw [div_lt_iff₀ hpos] at hK
                have : ((K:ℝ)+1) * ε * (r - fstar) ≤ ((K:ℝ)+1) * ε * (a K - fstar) := by
                  apply mul_le_mul_of_nonneg_left (by linarith)
                  positivity
                nlinarith
              have hxbarTop : f xbar ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hfle
              have hxbarmin : IsMinimizer X f xbar := by
                refine ⟨hxbarX, hxbarTop, fun y hy => ?_⟩
                calc f xbar ≤ (fstar : EReal) := hfle
                  _ = f zs := ezs.symm
                  _ ≤ f y := hzs.2.2 y hy
              have hxbarcl : xbar ∈ closure S := hclos ⟨hxbarX, hxbarTop⟩
              -- D(xbar, x k) → 0
              set g : ℕ → ℝ := fun k => bregmanD h xbar (x k) with hg
              have hganti : Antitone g := antitone_nat_of_succ_le (hminanti xbar hxbarmin hxbarcl)
              have hgbdd : BddBelow (Set.range g) :=
                ⟨0, by rintro _ ⟨k, rfl⟩; exact hD0 xbar hxbarcl (x k) (hx.1 k)⟩
              have hginf := tendsto_atTop_ciInf hganti hgbdd
              have hψ : Tendsto (fun j => φ j + 1) atTop atTop :=
                tendsto_atTop_atTop.mpr fun b => ⟨b, fun j hj => by have : j ≤ φ j := hφ.id_le j; omega⟩
              have hgsub : Tendsto (fun j => g (φ j + 1)) atTop (𝓝 0) :=
                hh.tendsto_zero (fun j => x (φ j + 1)) xbar (fun j => hx.1 _) hlim
              have hg0 : Tendsto g atTop (𝓝 0) := by
                have h2 := hginf.comp hψ
                have := tendsto_nhds_unique h2 hgsub
                rw [← this]; exact hginf
              refine ⟨xbar, hxbarmin, ?_⟩
              apply tendsto_of_subseq_tendsto
              intro ns hns
              have hbdd2 : Bornology.IsBounded (Set.range x) := hbdd
              obtain ⟨xh, -, ψ, hψm, hlim2⟩ := tendsto_subseq_of_bounded hbdd2
                (x := fun k => x (ns k)) (fun k => ⟨ns k, rfl⟩)
              refine ⟨ψ, ?_⟩
              have hnsψ : Tendsto (fun j => ns (ψ j)) atTop atTop := hns.comp hψm.tendsto_atTop
              have hxhcl : xh ∈ closure S :=
                isClosed_closure.mem_of_tendsto hlim2
                  (Eventually.of_forall (fun j => subset_closure (hx.1 _)))
              have hconst := hh.tendsto_of_zero (fun _ => xbar) (fun j => x (ns (ψ j))) xh
                (fun _ => hxbarcl) (fun j => hx.1 _) hlim2 hxhcl
                (by
                  refine (Metric.isBounded_iff_subset_closedBall xbar).mpr ⟨0, ?_⟩
                  rintro _ ⟨k, rfl⟩
                  simp)
                (hg0.comp hnsψ)
              have heq : xbar = xh := tendsto_const_nhds_iff.mp hconst
              rw [heq]
              exact hlim2
            case p2 =>
              intro hAI x₀ hx₀
              have hmin : ∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, f x ≠ ⊤ →
                  inner ℝ a x + b ≤ (f x).toReal := by
                obtain ⟨z0, hz0X, hz0⟩ := hP.finite_on_X
                set A : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | f p.1 ≤ (p.2 : EReal)} with hA
                have hAc : Convex ℝ A := hP.convexFn
                have hAcl : IsClosed A := by
                  have h1 := hP.lsc.isClosed_epigraph
                  exact h1.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
                have hz0r : f z0 = ((f z0).toReal : EReal) := (EReal.coe_toReal hz0 (hP.ne_bot z0)).symm
                have hnot : (z0, (f z0).toReal - 1) ∉ A := by
                  intro hm
                  simp only [hA, Set.mem_ofPred_eq] at hm
                  rw [hz0r] at hm
                  have := EReal.coe_le_coe_iff.mp hm
                  simp only [EReal.toReal_coe] at this
                  linarith
                obtain ⟨L, u, hLA, hLu⟩ := geometric_hahn_banach_closed_point hAc hAcl hnot
                set ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ _ ℝ) with hℓ
                set β : ℝ := L (0, 1) with hβdef
                have hL : ∀ x r, L (x, r) = ℓ x + r * β := by
                  intro x r
                  have : ((x, r) : EuclideanSpace ℝ (Fin n) × ℝ) =
                      (x, 0) + r • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
                    ext <;> simp
                  rw [this, map_add, map_smul]
                  simp [ℓ, β, smul_eq_mul]
                have hz0A : (z0, (f z0).toReal) ∈ A := by
                  show f z0 ≤ _
                  rw [← hz0r]
                have h1 := hLA _ hz0A
                rw [hL] at h1 hLu
                have hβ : β < 0 := by nlinarith
                refine ⟨(-β⁻¹) • (InnerProductSpace.toDual ℝ _).symm ℓ, u / β, ?_⟩
                intro x hx
                have hxA : (x, (f x).toReal) ∈ A := by
                  show f x ≤ _
                  rw [EReal.coe_toReal hx (hP.ne_bot x)]
                have h2 := hLA _ hxA
                rw [hL] at h2
                rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
                have hb : (u - ℓ x) / β ≤ (f x).toReal := by
                  rw [div_le_iff_of_neg hβ]; linarith
                calc -β⁻¹ * ℓ x + u / β = (u - ℓ x) / β := by ring
                  _ ≤ _ := hb
              obtain ⟨a, b, hab⟩ := hmin
              have step : ∀ y ∈ S, ∀ c' : ℝ, 0 < c' → ∃ z, z ∈ S ∧ z ∈ X ∧ f z ≠ ⊤ ∧
                  ∀ w ∈ X, primalObjective S h f c' y z ≤ primalObjective S h f c' y w := by
                intro y hy c' hc'
                obtain ⟨z0, hz0X, hz0⟩ := hP.finite_on_X
                have hFS : ∀ z, z ∈ X → f z ≠ ⊤ → z ∈ S := fun z hzX hz =>
                  hAI.1 (subset_closure ⟨hzX, hz⟩)
                have hz0S : z0 ∈ closure S := subset_closure (hFS z0 hz0X hz0)
                set g : EuclideanSpace ℝ (Fin n) → EReal :=
                  fun z => f z + ((c'⁻¹ * bregmanD h z y : ℝ) : EReal) with hg
                have hobj : ∀ z ∈ closure S, primalObjective S h f c' y z = g z := by
                  intro z hz; simp [primalObjective, hz, g]
                set M : ℝ := (f z0).toReal + c'⁻¹ * bregmanD h z0 y with hM
                have hgz0 : g z0 = (M : EReal) := by
                  simp only [g, M, EReal.coe_add]
                  rw [EReal.coe_toReal hz0 (hP.ne_bot z0)]
                have hfin : ∀ z, g z ≤ (M : EReal) → f z ≠ ⊤ := by
                  intro z hz htop
                  have : g z = ⊤ := by simp only [hg, htop, EReal.top_add_coe]
                  rw [this, top_le_iff] at hz
                  exact EReal.coe_ne_top M hz
                obtain ⟨y', hy'S, hy'⟩ : ∃ y' ∈ S, gradient h y' = gradient h y - c' • a := by
                  have : gradient h y - c' • a ∈ gradient h '' S := by rw [hAI.2]; trivial
                  exact this
                set α : ℝ := c' * (M - b) + (h y - h y' + inner ℝ (gradient h y) y' -
                  inner ℝ (gradient h y) y - c' * inner ℝ a y') with hα
                set K := (X ∩ closure S) ∩ g ⁻¹' Set.Iic (g z0) with hK
                have hKsub : K ⊆ {x | x ∈ closure S ∧ bregmanD h x y' ≤ α} := by
                  rintro z ⟨⟨hzX, hzS⟩, hzg⟩
                  refine ⟨hzS, ?_⟩
                  simp only [Set.mem_preimage, Set.mem_Iic, hgz0] at hzg
                  have hfz : f z ≠ ⊤ := hfin z hzg
                  have hzr := EReal.coe_toReal hfz (hP.ne_bot z)
                  have hle : (f z).toReal + c'⁻¹ * bregmanD h z y ≤ M := by
                    have : g z = (((f z).toReal + c'⁻¹ * bregmanD h z y : ℝ) : EReal) := by
                      simp only [g, EReal.coe_add, hzr]
                    rw [this] at hzg; exact_mod_cast hzg
                  have hab' := hab z hfz
                  have h3 : bregmanD h z y + c' * inner ℝ a z ≤ c' * (M - b) := by
                    have : c'⁻¹ * bregmanD h z y + inner ℝ a z ≤ M - b := by linarith
                    have := mul_le_mul_of_nonneg_left this hc'.le
                    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul] at this
                    exact this
                  have h4 : bregmanD h z y' = bregmanD h z y + c' * inner ℝ a z +
                      (h y - h y' + inner ℝ (gradient h y) y' - inner ℝ (gradient h y) y -
                        c' * inner ℝ a y') := by
                    simp only [bregmanD, hy', inner_sub_left, inner_sub_right, real_inner_smul_left]
                    ring
                  rw [hα]; linarith
                have hKb : Bornology.IsBounded K := (hh.bounded_L₁ α y' hy'S).subset hKsub
                have hXS : IsClosed (X ∩ closure S) := hP.closed.inter isClosed_closure
                have hDcont : ContinuousOn (fun z => c'⁻¹ * bregmanD h z y) (closure S) := by
                  unfold bregmanD
                  exact continuousOn_const.mul ((hh.continuousOn.sub continuousOn_const).sub (by fun_prop))
                have hglsc : LowerSemicontinuousOn g (X ∩ closure S) := by
                  apply LowerSemicontinuousOn.add'
                  · exact hP.lsc.lowerSemicontinuousOn _
                  · exact (continuous_coe_real_ereal.comp_continuousOn
                      (hDcont.mono Set.inter_subset_right)).lowerSemicontinuousOn
                  · intro z _
                    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
                have hKc : IsClosed K := by
                  obtain ⟨v, hv, hve⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hglsc (g z0)
                  rw [hK, hve]; exact hXS.inter hv
                have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
                have hKne : K.Nonempty := ⟨z0, ⟨hz0X, hz0S⟩, (show g z0 ≤ g z0 from le_rfl)⟩
                obtain ⟨zs, hzsK, hzsmin⟩ :=
                  (hglsc.mono Set.inter_subset_left).exists_isMinOn hKne hKcpt
                obtain ⟨⟨hzsX, hzsS⟩, hzsg⟩ := hzsK
                have hzsg' : g zs ≤ (M : EReal) := by
                  simpa only [Set.mem_preimage, Set.mem_Iic, hgz0] using hzsg
                have hfzs : f zs ≠ ⊤ := hfin zs hzsg'
                refine ⟨zs, hFS zs hzsX hfzs, hzsX, hfzs, ?_⟩
                intro w hwX
                by_cases hw : w ∈ closure S
                · rw [hobj w hw, hobj zs hzsS]
                  by_cases hwK : g w ≤ g z0
                  · exact isMinOn_iff.mp hzsmin w ⟨⟨hwX, hw⟩, hwK⟩
                  · exact le_trans hzsg (le_of_lt (not_le.mp hwK))
                · simp [primalObjective, hw]
              choose F hF using step
              let seq : ℕ → {y // y ∈ S} := fun k =>
                Nat.rec (motive := fun _ => {y // y ∈ S}) ⟨x₀, hx₀⟩
                  (fun k p => ⟨F p.1 p.2 (c k) (hc k), (hF p.1 p.2 (c k) (hc k)).1⟩) k
              refine ⟨fun k => (seq k).1, rfl, fun k => (seq k).2, fun k => ?_⟩
              obtain ⟨_, h1, h2, h3⟩ := hF (seq k).1 (seq k).2 (c k) (hc k)
              exact ⟨h1, h2, h3⟩
            case p3 =>
              intro x hx hA hnm hbdd
              obtain ⟨ε, hε, hεc⟩ := hcinf
              set a : ℕ → ℝ := fun k => (f (x (k+1))).toReal with ha_def
              have hfin : ∀ k, f (x (k+1)) = ((a k : ℝ) : EReal) := by
                intro k
                simp only [ha_def]
                exact (EReal.coe_toReal (hx.2 k).2.1 (hP.ne_bot _)).symm
              have hDself : ∀ y, bregmanD h y y = 0 := by
                intro y; simp [bregmanD]
              have hstep : ∀ k, a (k+1) ≤ a k := by
                intro k
                have h1 := hKEY x hx (k+1) (x (k+1)) (hx.2 k).1 (subset_closure (hx.1 (k+1))) (hx.2 k).2.1
                rw [hDself] at h1
                have h2 := hD0 (x (k+1)) (subset_closure (hx.1 (k+1))) (x (k+1+1)) (hx.1 _)
                have h3 : c (k+1) * (a (k+1) - a k) ≤ 0 := by simp only [ha_def]; linarith
                have hc1 := hc (k+1)
                by_contra hcon
                push_neg at hcon
                have : 0 < c (k+1) * (a (k+1) - a k) := mul_pos hc1 (by linarith)
                linarith
              have hanti : Antitone a := antitone_nat_of_succ_le hstep
              obtain ⟨xbar, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd
                (x := fun k => x (k+1)) (fun k => ⟨k+1, rfl⟩)
              have hxbarX : xbar ∈ X := by
                apply hP.closed.mem_of_tendsto hlim
                exact Eventually.of_forall (fun j => (hx.2 (φ j)).1)
              have hfle : ∀ k, f xbar ≤ ((a k : ℝ) : EReal) := by
                intro k
                by_contra hcon
                push_neg at hcon
                have hev := hP.lsc xbar _ hcon
                have hev2 := hlim.eventually hev
                obtain ⟨j, hj⟩ := (hev2.and (eventually_ge_atTop k)).exists
                have hle : a (φ j) ≤ a k := hanti (le_trans hj.2 (hφ.id_le j))
                have := hj.1
                simp only [Function.comp, hfin] at this
                have := EReal.coe_lt_coe_iff.mp this
                linarith
              have hxbarTop : f xbar ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hfle 0)
              have hxbarBot : f xbar ≠ ⊥ := hP.ne_bot _
              have : ¬ IsMinimizer X f xbar := fun hm => hnm ⟨xbar, hm⟩
              simp only [IsMinimizer, not_and, not_forall, not_le] at this
              obtain ⟨z, hzX, hz⟩ := this hxbarX hxbarTop
              have hzTop : f z ≠ ⊤ := ne_top_of_lt hz
              have hzS : z ∈ S := hA.1 (subset_closure ⟨hzX, hzTop⟩)
              have hzcl : z ∈ closure S := subset_closure hzS
              set t1 := (f xbar).toReal
              set t2 := (f z).toReal
              have e1 : f xbar = (t1 : EReal) := (EReal.coe_toReal hxbarTop hxbarBot).symm
              have e2 : f z = (t2 : EReal) := (EReal.coe_toReal hzTop (hP.ne_bot _)).symm
              have hδ : t2 < t1 := by
                rw [e1, e2] at hz; exact EReal.coe_lt_coe_iff.mp hz
              have hak : ∀ k, t1 ≤ a k := by
                intro k; have := hfle k; rw [e1] at this; exact EReal.coe_le_coe_iff.mp this
              have hdec : ∀ k, bregmanD h z (x (k+1)) ≤ bregmanD h z (x k) - ε * (t1 - t2) := by
                intro k
                have h1 := hKEY x hx k z hzX hzcl hzTop
                have h2 : ε * (t1 - t2) ≤ c k * (a k - t2) :=
                  mul_le_mul (hεc k) (by linarith [hak k]) (by linarith) (le_of_lt (hc k))
                simp only [ha_def] at h2
                linarith
              have hind : ∀ k : ℕ, bregmanD h z (x k) ≤ bregmanD h z (x 0) - k * (ε * (t1 - t2)) := by
                intro k
                induction k with
                | zero => simp
                | succ k ih =>
                  have := hdec k
                  push_cast
                  linarith
              have hpos : 0 < ε * (t1 - t2) := mul_pos hε (by linarith)
              obtain ⟨N, hN⟩ := exists_nat_gt (bregmanD h z (x 0) / (ε * (t1 - t2)))
              have hN' : bregmanD h z (x 0) < N * (ε * (t1 - t2)) := by
                rwa [div_lt_iff₀ hpos] at hN
              have := hind N
              have := hD0 z hzcl (x N) (hx.1 N)
              linarith
            case p4 =>
              have hgrad : ∀ y : ℝ, gradient (fun t : ℝ => t ^ 2 / 2) y = y := by
                intro y
                rw [gradient_eq_deriv]
                have : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
                  have := (hasDerivAt_pow 2 y).div_const 2
                  rw [show ((2:ℕ) : ℝ) * y ^ (2 - 1) / 2 = y by norm_num] at this
                  exact this
                rw [this.deriv]
                simp
              have hD : ∀ x y : ℝ, bregmanD (fun t : ℝ => t ^ 2 / 2) x y = (x - y) ^ 2 / 2 := by
                intro x y
                simp only [bregmanD, hgrad]
                rw [Real.inner_apply]
                ring
              have hcl : closure (Set.Ioi (0 : ℝ)) = Set.Ici 0 := closure_Ioi 0
              have habs : ∀ d : ℝ, |d| ≤ d ^ 2 + 1 := by
                intro d
                rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> nlinarith [sq_nonneg (d - 1/2), sq_nonneg (d + 1/2)]
              have hEF : effectiveFeasible (Set.Ici (0 : ℝ)) (fun t : ℝ => (t : EReal)) = Set.Ici 0 := by
                ext z; simp [effectiveFeasible]
              refine ⟨?_, ?_, ?_, ?_, isClosed_Ici, convex_Ici 0, ⟨0, Set.mem_Ici.mpr le_rfl, EReal.coe_ne_top _⟩, ?_, ?_,
                fun _ => one_pos, ⟨1, one_pos, fun _ => le_refl _⟩, by norm_num, ?_⟩
              · refine ⟨isOpen_Ioi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · exact (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => t ^ 2 / 2)).contDiffOn
                · rw [hcl]
                  refine ⟨convex_Ici 0, ?_⟩
                  intro u _ v _ huv a b ha hb hab
                  simp only [smul_eq_mul]
                  have hne : 0 < (u - v) ^ 2 := by
                    have : u - v ≠ 0 := sub_ne_zero.mpr huv
                    positivity
                  have hb' : b = 1 - a := by linarith
                  subst hb'
                  nlinarith [mul_pos (mul_pos ha hb) hne]
                · exact (by fun_prop : Continuous (fun t : ℝ => t ^ 2 / 2)).continuousOn
                · intro α y _
                  rw [Metric.isBounded_iff_subset_closedBall y]
                  refine ⟨2 * α + 1, fun x hx => ?_⟩
                  obtain ⟨_, hx⟩ := hx
                  rw [hD] at hx
                  rw [Metric.mem_closedBall, Real.dist_eq]
                  have := habs (x - y)
                  linarith
                · intro α x _
                  rw [Metric.isBounded_iff_subset_closedBall x]
                  refine ⟨2 * α + 1, fun y hy => ?_⟩
                  obtain ⟨_, hy⟩ := hy
                  rw [hD] at hy
                  rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
                  have := habs (x - y)
                  linarith
                · intro y y' _ hy
                  simp only [hD]
                  have : Tendsto (fun k => (y' - y k) ^ 2 / 2) atTop (𝓝 ((y' - y') ^ 2 / 2)) :=
                    ((tendsto_const_nhds.sub hy).pow 2).div_const 2
                  simpa using this
                · intro x y y' _ _ hy _ _ hxy
                  simp only [hD] at hxy
                  have h1 : Tendsto (fun k => |x k - y k|) atTop (𝓝 0) := by
                    have := (hxy.const_mul 2).sqrt
                    simp only [mul_zero, Real.sqrt_zero] at this
                    refine this.congr fun k => ?_
                    rw [show 2 * ((x k - y k) ^ 2 / 2) = (x k - y k) ^ 2 by ring, Real.sqrt_sq_eq_abs]
                  have h2 : Tendsto (fun k => x k - y k) atTop (𝓝 0) := by
                    rw [tendsto_zero_iff_abs_tendsto_zero]; exact h1
                  have := h2.add hy
                  simpa using this
              · exact ⟨fun x => EReal.coe_ne_bot x, 0, EReal.coe_ne_top 0⟩
              · intro p hp q hq a b ha hb hab
                simp only [Set.mem_ofPred_eq, EReal.coe_le_coe_iff] at hp hq ⊢
                simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
                nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb]
              · exact continuous_coe_real_ereal.lowerSemicontinuous
              · rw [hEF]
                intro z hz
                rw [mem_intrinsicInterior] at hz
                obtain ⟨y, hy, rfl⟩ := hz
                have hz0 : (0 : ℝ) ≤ (y : ℝ) := by
                  have := interior_subset hy
                  simpa using this
                by_contra hneg
                have hy0 : (y : ℝ) = 0 := le_antisymm (not_lt.mp hneg) hz0
                obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
                have htop : affineSpan ℝ (Set.Ici (0 : ℝ)) = ⊤ :=
                  affineSpan_eq_top_of_nonempty_interior
                    ⟨1, interior_mono (subset_convexHull ℝ _) (by rw [interior_Ici]; norm_num)⟩
                have hmem : (-(ε / 2) : ℝ) ∈ affineSpan ℝ (Set.Ici (0 : ℝ)) := by
                  rw [htop]; exact AffineSubspace.mem_top _ _ _
                have := hball (show (⟨-(ε / 2), hmem⟩ : affineSpan ℝ (Set.Ici (0 : ℝ))) ∈ Metric.ball y ε by
                  rw [Metric.mem_ball, Subtype.dist_eq, hy0, Real.dist_eq]
                  rw [abs_of_neg (by linarith)]; linarith)
                simp only [Set.mem_preimage, Set.mem_Ici] at this
                linarith
              · refine ⟨fun z _ => ⟨EReal.coe_ne_top z, EReal.coe_ne_bot z⟩, ?_, 0, fun z hz => ?_⟩
                · simp only [EReal.toReal_coe]; exact continuousOn_id
                · exact EReal.coe_le_coe_iff.mpr hz
              · rintro ⟨x, hx0, hS, hrun⟩
                have h1pos : 0 < x 1 := hS 1
                obtain ⟨_, _, hmin⟩ := hrun 0
                have := hmin 0 (Set.mem_Ici.mpr (le_refl _))
                simp only [primalObjective, hcl, Set.mem_Ici, le_refl, if_true, hD, hx0, zero_add] at this
                rw [if_pos h1pos.le] at this
                have h' : x 1 + 1⁻¹ * ((x 1 - 1 / 2) ^ 2 / 2) ≤ 0 + 1⁻¹ * ((0 - 1 / 2) ^ 2 / 2) := by
                  exact_mod_cast this
                nlinarith
