-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.theorem_4_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:07.256459+00:00
-- url     : https://prove2.me/submissions/6d28bb70-a3cc-4368-857b-cfc0b1c7dc0c

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvex : FixedConvexLower D) (habnormal : abnormalCondition D z)
    (hexclude : ∀ d lam κ μ, variationalSystem D z d lam κ μ → d = 0) :
    StrictLocalMin D.F (feasSet D) z := by
      refine ⟨hfeas, ?_⟩
      by_contra hcon
      push_neg at hcon
      have hseq : ∀ k : ℕ, ∃ a ∈ feasSet D, a ≠ z ∧ D.F a ≤ D.F z ∧ ‖a - z‖ < 1 / (k + 1) := by
        intro k
        obtain ⟨a, ⟨ha, hU⟩, hne, hle⟩ := hcon (Metric.ball z (1 / (k+1))) (Metric.ball_mem_nhds _ (by positivity))
        exact ⟨a, ha, hne, hle, by simpa [dist_eq_norm] using hU⟩
      choose zk hzk hne hle hdist using hseq
      have hzk_tend : Filter.Tendsto zk Filter.atTop (𝓝 z) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hdist k).le) ?_
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      have hsph : ∀ k, ‖zk k - z‖⁻¹ • (zk k - z) ∈ Metric.sphere (0 : E n × Y m) 1 := by
        intro k
        have : zk k - z ≠ 0 := sub_ne_zero.mpr (hne k)
        simp [norm_smul, this]
      obtain ⟨d, hdS, φ, hφ, hdlim⟩ := (isCompact_sphere (0 : E n × Y m) 1).tendsto_subseq hsph
      have hdnorm : ‖d‖ = 1 := by simpa using hdS
      have hseqD : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
          [NormedSpace ℝ W] (h : V → W) (h' : V →L[ℝ] W) (z d : V) (zs : ℕ → V),
          HasFDerivAt h h' z → Filter.Tendsto zs Filter.atTop (𝓝 z) →
          Filter.Tendsto (fun k => ‖zs k - z‖⁻¹ • (zs k - z)) Filter.atTop (𝓝 d) →
          Filter.Tendsto (fun k => ‖zs k - z‖⁻¹ • (h (zs k) - h z)) Filter.atTop (𝓝 (h' d)) := by
        intro V W _ _ _ _ h h' z d zs hh hz hd
        have h1 : Filter.Tendsto (fun k => h' (‖zs k - z‖⁻¹ • (zs k - z))) Filter.atTop (𝓝 (h' d)) :=
          (h'.continuous.tendsto d).comp hd
        have h2 : Filter.Tendsto (fun k => ‖zs k - z‖⁻¹ • (h (zs k) - h z - h' (zs k - z)))
            Filter.atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have := (hasFDerivAt_iff_tendsto.mp hh).comp hz
          refine this.congr fun k => ?_
          simp only [Function.comp, norm_smul, norm_inv, norm_norm]
        have h3 := h1.add h2
        rw [add_zero] at h3
        refine h3.congr fun k => ?_
        simp only [map_smul, ← smul_add, map_sub]
        congr 1
        abel
      have key : ∀ (h : E n × Y m → ℝ), DifferentiableAt ℝ h z →
          (∀ k, h (zk (φ k)) ≤ h z) → fderiv ℝ h z d ≤ 0 := fun h hh hle' =>
        le_of_tendsto' (hseqD _ ℝ h _ z d (fun k => zk (φ k)) hh.hasFDerivAt
          (hzk_tend.comp hφ.tendsto_atTop) hdlim) fun k =>
            mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) (sub_nonpos.2 (hle' k))
      have hFd : DifferentiableAt ℝ D.F z :=
        (hStanding.1.differentiable (by norm_num)).differentiableAt
      have hfd : ∀ w, DifferentiableAt ℝ D.f w := fun w =>
        (hStanding.2.1.differentiable (by norm_num)).differentiableAt
      have hGd : ∀ i, DifferentiableAt ℝ (D.G i) z := fun i =>
        ((hStanding.2.2.1 i).differentiable (by norm_num)).differentiableAt
      have hgd : ∀ i w, DifferentiableAt ℝ (D.g i) w := fun i w =>
        ((hStanding.2.2.2 i).differentiable (by norm_num)).differentiableAt
      have c1 : fderiv ℝ D.F z d ≤ 0 := key D.F hFd (fun k => hle _)
      have c2 : ∀ i ∈ actG D z, fderiv ℝ (D.G i) z d ≤ 0 := by
        intro i hi
        refine key _ (hGd i) (fun k => ?_)
        have := (hzk (φ k)).1 i
        simp only [actG, Set.mem_setOf_eq] at hi
        linarith
      have hlineG : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : V → ℝ) (w v : V)
          (t : ℝ), DifferentiableAt ℝ h (w + t • v) →
          HasDerivAt (fun s : ℝ => h (w + s • v)) (fderiv ℝ h (w + t • v) v) t := by
        intro V _ _ h w v t hh
        exact hh.hasFDerivAt.comp_hasDerivAt t
          ((((hasDerivAt_id' t).smul_const v).const_add w).congr_deriv (one_smul ℝ v))
      have hline2G : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : V → (V →L[ℝ] ℝ))
          (w v : V), DifferentiableAt ℝ k w →
          HasDerivAt (fun s : ℝ => k (w + s • v) v) (fderiv ℝ k w v v) 0 := by
        intro V _ _ k w v hk
        have hl := (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add w).congr_deriv (one_smul ℝ v)
        have hA : HasFDerivAt k (fderiv ℝ k w) (w + (0:ℝ) • v) := by
          rw [zero_smul, add_zero]; exact hk.hasFDerivAt
        exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt (0:ℝ)
          (hA.comp_hasDerivAt (0:ℝ) hl)
      have hgx : ∀ i (v : E n), fderiv ℝ (D.g i) z (v, 0) = 0 := by
        intro i v
        have h1 := hlineG _ (D.g i) z ((v, 0) : E n × Y m) 0 (hgd i _)
        rw [zero_smul, add_zero] at h1
        have h2 : (fun t : ℝ => D.g i (z + t • ((v, 0) : E n × Y m))) = fun _ => D.g i z := by
          funext t
          rw [hconvex.2.1 i, hconvex.2.1 i z.1 z.2]
          simp
        rw [h2] at h1
        exact h1.unique (hasDerivAt_const _ _)
      have hgsplit : ∀ i, fderiv ℝ (D.g i) z (0, d.2) = fderiv ℝ (D.g i) z d := by
        intro i
        have : d = (d.1, 0) + (0, d.2) := by ext <;> simp
        conv_rhs => rw [this, map_add, hgx]
        simp
      have c10 : d.2 ∈ lowerLinCone D z := by
        intro i hi
        rw [hgsplit]
        refine key _ (hgd i z) (fun k => ?_)
        have := (hzk (φ k)).2.1 i
        simp only [actg, Set.mem_setOf_eq] at hi
        rw [hi]; simpa using this
      have hK : ∀ x x' (y : Y m), y ∈ lowerFeas D x → y ∈ lowerFeas D x' := by
        intro x x' y hy j
        have := hy j
        rw [hconvex.2.1 j] at this ⊢; exact this
      have hsplitG : ∀ (V1 V2 : Type) [NormedAddCommGroup V1] [NormedSpace ℝ V1]
          [NormedAddCommGroup V2] [NormedSpace ℝ V2] (f : V1 × V2 → ℝ) (z : V1 × V2),
          DifferentiableAt ℝ f z → DifferentiableAt ℝ (fun w => f w - f (w.1, z.2)) z ∧
            ∀ v : V1 × V2, fderiv ℝ (fun w => f w - f (w.1, z.2)) z v = fderiv ℝ f z (0, v.2) := by
        intro V1 V2 _ _ _ _ f z hf
        have hA : HasFDerivAt (fun w : V1 × V2 => (w.1, z.2))
            ((ContinuousLinearMap.fst ℝ V1 V2).prod 0) z :=
          hasFDerivAt_fst.prodMk (hasFDerivAt_const _ _)
        have hB : HasFDerivAt (fun w : V1 × V2 => f (w.1, z.2))
            ((fderiv ℝ f z).comp ((ContinuousLinearMap.fst ℝ V1 V2).prod 0)) z :=
          hf.hasFDerivAt.comp z hA
        have hC : HasFDerivAt (fun w => f w - f (w.1, z.2))
            (fderiv ℝ f z - (fderiv ℝ f z).comp ((ContinuousLinearMap.fst ℝ V1 V2).prod 0)) z :=
          hf.hasFDerivAt.sub hB
        refine ⟨hC.differentiableAt, fun v => ?_⟩
        rw [hC.fderiv]
        show fderiv ℝ f z v - fderiv ℝ f z (v.1, 0) = fderiv ℝ f z (0, v.2)
        rw [← map_sub]
        congr 1
        ext
        · exact sub_self v.1
        · exact sub_zero v.2
      have c11le : fderiv ℝ D.f z (0, d.2) ≤ 0 := by
        obtain ⟨hCd, hCv⟩ := hsplitG _ _ D.f z (hfd z)
        have := key (fun w => D.f w - D.f (w.1, z.2)) hCd (fun k => ?_)
        · rw [hCv] at this; exact this
        · simp only [sub_self, sub_nonpos]
          exact (hzk (φ k)).2.2 z.2 (hK _ _ _ hfeas.2.1)
      have hdir : ∀ k, 0 ≤ fderiv ℝ D.f z (0, (zk k).2 - z.2) := by
        intro k
        set v : E n × Y m := (0, (zk k).2 - z.2) with hv
        have h1 := hlineG _ D.f z v 0 (hfd _)
        rw [zero_smul, add_zero] at h1
        have h2 := (hasDerivAt_iff_tendsto_slope.mp h1).mono_left
          (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
        refine ge_of_tendsto h2 ?_
        have hI : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
        filter_upwards [hI] with t ht
        rw [slope_def_field]
        apply div_nonneg _ (by linarith [ht.1])
        simp only [zero_smul, add_zero, sub_nonneg]
        have hzt : z + t • v = (z.1, (z + t • v).2) := by ext <;> simp [hv]
        rw [hzt]
        apply hfeas.2.2
        intro j
        have hy := (hzk k).2.1 j
        have hz := hfeas.2.1 j
        rw [hconvex.2.1 j] at hy hz ⊢
        have hc := (hconvex.2.2 j).2 (Set.mem_univ z.2) (Set.mem_univ (zk k).2)
          (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) (le_of_lt ht.1) (by ring)
        have heq : (z + t • v).2 = (1 - t) • z.2 + t • (zk k).2 := by
          simp [hv, smul_sub, sub_smul]; abel
        rw [heq]
        refine hc.trans ?_
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith only [ht.2]) hz)
          (mul_nonpos_of_nonneg_of_nonpos ht.1.le hy)
      have c11ge : 0 ≤ fderiv ℝ D.f z (0, d.2) := by
        have hcl : Continuous fun u : E n × Y m => fderiv ℝ D.f z (0, u.2) :=
          (fderiv ℝ D.f z).continuous.comp (continuous_const.prodMk continuous_snd)
        have h2 := (hcl.tendsto d).comp hdlim
        refine ge_of_tendsto h2 (Filter.Eventually.of_forall fun k => ?_)
        simp only [Function.comp, Prod.smul_snd, Prod.snd_sub]
        have : ((0 : E n), ‖zk (φ k) - z‖⁻¹ • ((zk (φ k)).2 - z.2)) =
            ‖zk (φ k) - z‖⁻¹ • ((0 : E n), (zk (φ k)).2 - z.2) := by simp
        rw [this, map_smul, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hdir _)
      have c11 : fderiv ℝ D.f z (0, d.2) = 0 := le_antisymm c11le c11ge
      have hpsdG : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
          [NormedSpace ℝ W] (h : V × W → ℝ) (w : V × W) (u : W), ContDiff ℝ 2 h →
          ConvexOn ℝ Set.univ (fun y => h (w.1, y)) → 0 ≤ fderiv ℝ (fderiv ℝ h) w (0, u) (0, u) := by
        intro V W _ _ _ _ h w u hh hcv
        have hd1 : Differentiable ℝ h := hh.differentiable (by norm_num)
        have hd2 : Differentiable ℝ (fderiv ℝ h) :=
          (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
        have hφd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => h (w + s • ((0:V), u)))
            (fderiv ℝ h (w + t • ((0:V), u)) ((0:V), u)) t :=
          fun t => hlineG _ h w ((0:V), u) t (hd1 _)
        have hconv : ConvexOn ℝ Set.univ (fun s : ℝ => h (w + s • ((0:V), u))) := by
          have hc := hcv.comp_affineMap (AffineMap.lineMap w.2 (w.2 + u))
          have heq : (fun s : ℝ => h (w + s • ((0:V), u))) =
              (fun y => h (w.1, y)) ∘ (AffineMap.lineMap w.2 (w.2 + u) : ℝ →ᵃ[ℝ] W) := by
            funext s
            rw [Function.comp_apply, AffineMap.lineMap_apply]
            congr 1
            ext
            · simp
            · simp [add_comm]
          rw [heq]; rw [Set.preimage_univ] at hc; exact hc
        have hmono := hconv.monotoneOn_deriv (fun t _ => (hφd t).differentiableAt)
        have hψd : HasDerivAt (fun s : ℝ => fderiv ℝ h (w + s • ((0:V), u)) ((0:V), u))
            (fderiv ℝ (fderiv ℝ h) w ((0:V), u) ((0:V), u)) 0 :=
          hline2G _ (fderiv ℝ h) w ((0:V), u) (hd2 w)
        refine ge_of_tendsto ((hasDerivAt_iff_tendsto_slope.mp hψd).mono_left
          (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))) ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (0:ℝ) < t := ht
        rw [slope_def_field]
        refine div_nonneg ?_ (by linarith)
        have := hmono (Set.mem_univ 0) (Set.mem_univ t) ht'.le
        rw [(hφd 0).deriv, (hφd t).deriv] at this
        exact sub_nonneg.mpr this
      have hpsd : ∀ i (u : Y m), 0 ≤ fderiv ℝ (fderiv ℝ (D.g i)) z ((0 : E n), u) ((0 : E n), u) :=
        fun i u => hpsdG _ _ (D.g i) z u (hStanding.2.2.2 i) (by
          have : (fun y => D.g i (z.1, y)) = fun y => D.g i (0, y) :=
            funext fun y => hconvex.2.1 i z.1 y
          rw [this]; exact hconvex.2.2 i)
      have hnoabn : d.2 ≠ 0 → ∀ lam : Fin q → ℝ, (∑ i, lam i • yGrad (D.g i) z) = 0 →
          (∀ i, 0 ≤ lam i) → (∑ i, lam i * D.g i z) = 0 → lam = 0 := by
        intro hd2 lam h1 h2 h3
        refine habnormal d.2 c10 hd2 lam h1 h2 h3 ?_
        exact Finset.sum_nonneg fun i _ => mul_nonneg (h2 i) (hpsd i d.2)
      have hcrux : ∃ (lam : Fin q → ℝ) (κ : ℝ) (μ : Fin q → ℝ),
          yHess D.f z d + κ • yGrad D.f z +
            (∑ i, (lam i • yHess (D.g i) z (0, d.2) + μ i • yGrad (D.g i) z)) = 0 ∧
          yGrad D.f z + (∑ i, lam i • yGrad (D.g i) z) = 0 ∧
          (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i * D.g i z) = 0 ∧
          (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i * D.g i z) = 0 ∧
          (∑ i, μ i * fderiv ℝ (D.g i) z (0, d.2)) = 0 := by
        have hclosed : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (k : ℕ) (v : Fin k → F),
            IsClosed {w : F | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ w = ∑ i, c i • v i} := by
          intro F _ _ k
          induction k with
          | zero =>
            intro v
            convert (isClosed_singleton : IsClosed ({0} : Set F)) using 1
            ext w
            simp only [Finset.univ_eq_empty, Finset.sum_empty, Set.mem_setOf_eq, Set.mem_singleton_iff]
            exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, fun i => i.elim0, h⟩⟩
          | succ k ih =>
            intro v
            have key : ∀ (a : F) (v' : Fin k → F), IsClosed {w | ∃ t : ℝ, 0 ≤ t ∧
                ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ w - t • a = ∑ i, c i • v' i} := by
              intro a v'
              have hcl := ih v'
              by_cases hneg : ∃ e : Fin k → ℝ, (∀ i, 0 ≤ e i) ∧ -a = ∑ i, e i • v' i
              · obtain ⟨e, he, hae⟩ := hneg
                obtain ⟨P, hP⟩ : ∃ P : F →L[ℝ] F, ∀ x, P x = x - (inner ℝ a x * (inner ℝ a a)⁻¹) • a :=
                  ⟨ContinuousLinearMap.id ℝ F - (innerSL ℝ a).smulRight ((inner ℝ a a)⁻¹ • a),
                    fun x => by rw [mul_smul]; rfl⟩
                have hPw : ∀ x, x = P x + (inner ℝ a x * (inner ℝ a a)⁻¹) • a := fun x => by
                  rw [hP, sub_add_cancel]
                have hPa : P a = 0 := by
                  rw [hP]
                  rcases eq_or_ne (inner ℝ a a) (0:ℝ) with h | h
                  · rw [inner_self_eq_zero.mp h, smul_zero, sub_zero]
                  · rw [mul_inv_cancel₀ h, one_smul, sub_self]
                have hsum : ∀ c : Fin k → ℝ, P (∑ i, c i • v' i) = ∑ i, c i • P (v' i) := fun c =>
                  (map_sum P _ _).trans (Finset.sum_congr rfl fun i _ => P.map_smul _ _)
                convert (ih (fun i => P (v' i))).preimage P.continuous using 1
                ext w
                constructor
                · rintro ⟨t, ht, c, hc, hw⟩
                  refine ⟨c, hc, ?_⟩
                  rw [← hsum, ← hw, P.map_sub, P.map_smul, hPa, smul_zero, sub_zero]
                · rintro ⟨c, hc, hw⟩
                  have hx : P (w - ∑ i, c i • v' i) = 0 := by
                    rw [P.map_sub, hsum]; exact sub_eq_zero.mpr hw
                  obtain ⟨s, hs⟩ : ∃ s : ℝ, w - ∑ i, c i • v' i = s • a :=
                    ⟨_, (hPw _).trans (by rw [hx, zero_add])⟩
                  rcases le_or_gt 0 s with h0 | h0
                  · exact ⟨s, h0, c, hc, by rw [← hs, sub_sub_cancel]⟩
                  · refine ⟨0, le_refl _, fun i => c i + (-s) * e i,
                      fun i => add_nonneg (hc i) (mul_nonneg (by linarith) (he i)), ?_⟩
                    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, ← hae,
                      zero_smul, sub_zero]
                    rw [smul_neg, neg_smul, neg_neg, ← hs, add_sub_cancel]
              · apply IsSeqClosed.isClosed
                intro wn w hmem hlim
                choose t ht c hc hwn using hmem
                have hpos : ∀ j, 0 < 1 + t j := fun j => by linarith [ht j]
                have hrI : ∀ j, (1 + t j)⁻¹ ∈ Set.Icc (0:ℝ) 1 := fun j =>
                  ⟨inv_nonneg.mpr (hpos j).le, inv_le_one_of_one_le₀ (by linarith [ht j])⟩
                obtain ⟨r, hr, φ, hφ, hrlim⟩ := isCompact_Icc.tendsto_subseq hrI
                have hmemr : ∀ j, (1 + t j)⁻¹ • wn j - (1 - (1 + t j)⁻¹) • a ∈
                    {u | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ u = ∑ i, c i • v' i} := by
                  intro j
                  refine ⟨fun i => (1 + t j)⁻¹ * c j i,
                    fun i => mul_nonneg (inv_nonneg.mpr (hpos j).le) (hc j i), ?_⟩
                  have h1 : 1 - (1 + t j)⁻¹ = (1 + t j)⁻¹ * t j := by
                    have := mul_inv_cancel₀ (hpos j).ne'
                    linear_combination (-1 : ℝ) * this
                  rw [h1, mul_smul, ← smul_sub, hwn j, Finset.smul_sum]
                  simp only [smul_smul]
                obtain ⟨e, he, hee⟩ := hcl.mem_of_tendsto
                  ((hrlim.smul (hlim.comp hφ.tendsto_atTop)).sub
                    ((tendsto_const_nhds (x := (1:ℝ))).sub hrlim |>.smul_const a))
                  (Filter.Eventually.of_forall fun j => hmemr (φ j))
                rcases eq_or_lt_of_le hr.1 with h0 | h0
                · exfalso
                  refine hneg ⟨e, he, ?_⟩
                  rw [← hee, ← h0, zero_smul, sub_zero, one_smul, zero_sub]
                · refine ⟨r⁻¹ * (1 - r), mul_nonneg (inv_nonneg.mpr h0.le) (by linarith [hr.2]),
                    fun i => r⁻¹ * e i, fun i => mul_nonneg (inv_nonneg.mpr h0.le) (he i), ?_⟩
                  have hw' : w - (r⁻¹ * (1 - r)) • a = r⁻¹ • (r • w - (1 - r) • a) := by
                    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h0.ne', one_smul]
                  rw [hw', hee, Finset.smul_sum]
                  simp only [smul_smul]
            convert key (v (Fin.last k)) (fun i => v i.castSucc) using 1
            ext w
            constructor
            · rintro ⟨c, hc, rfl⟩
              refine ⟨c (Fin.last k), hc _, fun i => c i.castSucc, fun i => hc _, ?_⟩
              rw [Fin.sum_univ_castSucc, add_sub_cancel_right]
            · rintro ⟨t, ht, c, hc, hw⟩
              refine ⟨Fin.lastCases t c, fun i => ?_, ?_⟩
              · induction i using Fin.lastCases with
                | last => simp only [Fin.lastCases_last]; exact ht
                | cast j => simp only [Fin.lastCases_castSucc]; exact hc j
              · simp only [Fin.sum_univ_castSucc, Fin.lastCases_last, Fin.lastCases_castSucc]
                rw [← hw, sub_add_cancel]
        have hfarkas : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
            (k : ℕ) (v : Fin k → F) (w : F),
            (∀ u : F, (∀ i, inner ℝ (v i) u ≤ 0) → inner ℝ w u ≤ 0) →
            ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ w = ∑ i, c i • v i := by
          intro F _ _ _ k v w hw
          by_contra hnot
          set C := {w : F | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ w = ∑ i, c i • v i} with hCdef
          have hconv : Convex ℝ C := by
            rintro x ⟨c, hc, rfl⟩ y ⟨e, he, rfl⟩ a b ha hb _
            refine ⟨fun i => a * c i + b * e i,
              fun i => add_nonneg (mul_nonneg ha (hc i)) (mul_nonneg hb (he i)), ?_⟩
            simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
          obtain ⟨f, u, hf, hfw⟩ := geometric_hahn_banach_closed_point hconv (hclosed F k v) hnot
          have h0 : (0 : F) ∈ C := ⟨0, fun _ => le_refl _, by simp⟩
          have hu : 0 < u := by simpa using hf 0 h0
          have hsc : ∀ x ∈ C, f x ≤ 0 := by
            rintro x ⟨c, hc, rfl⟩
            by_contra hx
            push_neg at hx
            have hmem : (u / f (∑ i, c i • v i)) • (∑ i, c i • v i) ∈ C :=
              ⟨fun i => (u / f (∑ i, c i • v i)) * c i,
                fun i => mul_nonneg (div_nonneg hu.le hx.le) (hc i), by simp [Finset.smul_sum, mul_smul]⟩
            have := hf _ hmem
            rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx.ne'] at this
            exact lt_irrefl _ this
          have hvi : ∀ i, inner ℝ (v i) ((InnerProductSpace.toDual ℝ (F)).symm f) ≤ 0 := by
            intro i
            rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
            refine hsc _ ⟨Pi.single i 1, fun j => ?_, ?_⟩
            · by_cases h : j = i
              · subst h; simp
              · simp [h]
            · simp [Pi.single_apply]
          have := hw _ hvi
          rw [real_inner_comm, InnerProductSpace.toDual_symm_apply] at this
          linarith
        have hkktG : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
            (q : ℕ) (φ0 : F → ℝ) (gs : Fin q → F → ℝ) (y u0 : F),
            (∀ y', (∀ i, gs i y' ≤ 0) → φ0 y ≤ φ0 y') → (∀ i, gs i y ≤ 0) →
            DifferentiableAt ℝ φ0 y → (∀ i, DifferentiableAt ℝ (gs i) y) →
            (∀ i, gs i y = 0 → inner ℝ (gradient (gs i) y) u0 < 0) →
            ∃ c : Fin q → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, gs i y ≠ 0 → c i = 0) ∧
              gradient φ0 y + ∑ i, c i • gradient (gs i) y = 0 := by
          classical
          intro F _ _ _ q φ0 gs y u0 hopt hfeas hφd hgd hu0
          have hline : ∀ (h : F → ℝ) (v : F), DifferentiableAt ℝ h y →
              HasDerivAt (fun s : ℝ => h (y + s • v)) (inner ℝ (gradient h y) v) 0 := by
            intro h v hh
            have hl := (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y).congr_deriv (one_smul ℝ v)
            have hA : HasFDerivAt h (fderiv ℝ h y) (y + (0:ℝ) • v) := by
              rw [zero_smul, add_zero]; exact hh.hasFDerivAt
            have := hA.comp_hasDerivAt (0:ℝ) hl
            rwa [gradient, InnerProductSpace.toDual_symm_apply]
          have hpolar : ∀ u : F, (∀ i, inner ℝ ((fun i => if gs i y = 0 then gradient (gs i) y else 0) i) u ≤ 0) →
              inner ℝ (-gradient φ0 y) u ≤ 0 := by
            intro u hu
            simp only at hu
            rw [inner_neg_left, neg_nonpos]
            have hstrict : ∀ ε : ℝ, 0 < ε → 0 ≤ inner ℝ (gradient φ0 y) (u + ε • u0) := by
              intro ε hε
              have hv : ∀ i, gs i y = 0 → inner ℝ (gradient (gs i) y) (u + ε • u0) < 0 := by
                intro i hi
                have h1 := hu i
                rw [if_pos hi] at h1
                rw [inner_add_right, real_inner_smul_right]
                linarith only [h1, mul_neg_of_pos_of_neg hε (hu0 i hi)]
              have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, gs i (y + t • (u + ε • u0)) ≤ 0 := by
                rw [Filter.eventually_all]
                intro i
                have hd := hline (gs i) (u + ε • u0) (hgd i)
                by_cases hi : gs i y = 0
                · have h2 := ((hasDerivAt_iff_tendsto_slope.mp hd).mono_left
                    (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))).eventually_lt_const
                    (hv i hi)
                  filter_upwards [h2, self_mem_nhdsWithin] with t ht ht0
                  have ht0' : (0:ℝ) < t := ht0
                  rw [slope_def_field, div_lt_iff₀ (by linarith), zero_mul] at ht
                  simp only [zero_smul, add_zero, hi, sub_zero] at ht
                  exact ht.le
                · have hneg : gs i y < 0 := lt_of_le_of_ne (hfeas i) hi
                  have hc := hd.continuousAt.tendsto
                  simp only [zero_smul, add_zero] at hc
                  exact nhdsWithin_le_nhds ((hc.eventually_lt_const hneg).mono fun t ht => ht.le)
              have hd := hline φ0 (u + ε • u0) hφd
              refine ge_of_tendsto ((hasDerivAt_iff_tendsto_slope.mp hd).mono_left
                (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))) ?_
              filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
              have ht0' : (0:ℝ) < t := ht0
              rw [slope_def_field]
              refine div_nonneg ?_ (by linarith)
              simp only [zero_smul, add_zero, sub_nonneg]
              exact hopt _ ht
            have hlim : Filter.Tendsto (fun ε : ℝ => inner ℝ (gradient φ0 y) (u + ε • u0))
                (𝓝[>] (0:ℝ)) (𝓝 (inner ℝ (gradient φ0 y) u)) := by
              have : Continuous (fun ε : ℝ => inner ℝ (gradient φ0 y) (u + ε • u0)) := by fun_prop
              have h := this.tendsto 0
              simp only [zero_smul, add_zero] at h
              exact h.mono_left nhdsWithin_le_nhds
            exact ge_of_tendsto hlim (by
              filter_upwards [self_mem_nhdsWithin] with ε hε
              exact hstrict ε hε)
          obtain ⟨c, hc, hw⟩ := hfarkas F q (fun i => if gs i y = 0 then gradient (gs i) y else 0)
            (-gradient φ0 y) hpolar
          · refine ⟨fun i => if gs i y = 0 then c i else 0, fun i => ?_, fun i hi => if_neg hi, ?_⟩
            · show 0 ≤ ite _ _ _
              split_ifs
              · exact hc i
              · exact le_refl _
            · have : ∑ i, (if gs i y = 0 then c i else 0) • gradient (gs i) y =
                  ∑ i, c i • (if gs i y = 0 then gradient (gs i) y else 0) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                by_cases h : gs i y = 0
                · simp only [if_pos h]
                · simp only [if_neg h, smul_zero, zero_smul]
              rw [this, ← hw]; exact add_neg_cancel _
        have hgradG : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
            [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] (h : V × W → ℝ)
            (w : V × W), DifferentiableAt ℝ h w →
            ∀ v : W, fderiv ℝ h w ((0 : V), v) = inner ℝ (gradient (fun y => h (w.1, y)) w.2) v := by
          intro V W _ _ _ _ _ h w hh v
          have hc : HasFDerivAt (fun y : W => h (w.1, y))
              ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ V W)) w.2 :=
            hh.hasFDerivAt.comp w.2 (hasFDerivAt_prodMk_right w.1 w.2)
          rw [gradient, hc.fderiv, InnerProductSpace.toDual_symm_apply]
          rfl
        have hgradeq : ∀ (h : E n × Y m → ℝ) (w : E n × Y m), DifferentiableAt ℝ h w →
            ∀ v : Y m, fderiv ℝ h w ((0 : E n), v) = inner ℝ (yGrad h w) v :=
          fun h w hh v => hgradG _ _ h w hh v
        have hlg : ∀ lam : Fin q → ℝ, (∀ i, 0 ≤ lam i) → (∑ i, lam i * D.g i z) = 0 →
            ∀ i, lam i * D.g i z = 0 := by
          intro lam h2 h3 i
          have hnp : ∀ j ∈ Finset.univ, lam j * D.g j z ≤ 0 := fun j _ =>
            mul_nonpos_of_nonneg_of_nonpos (h2 j) (hfeas.2.1 j)
          exact (Finset.sum_eq_zero_iff_of_nonpos hnp).mp h3 i (Finset.mem_univ _)
        have hfinal : ∀ lam : Fin q → ℝ, yGrad D.f z + (∑ i, lam i • yGrad (D.g i) z) = 0 →
            (∀ i, 0 ≤ lam i) → (∑ i, lam i * D.g i z) = 0 →
            ∀ c e : Fin q → ℝ, (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ e i) →
            (∀ i, c i ≠ 0 → i ∈ actg D z ∧ inner ℝ (yGrad (D.g i) z) d.2 = 0) →
            (∀ i, lam i = 0 → e i = 0) →
            -(yHess D.f z d + ∑ i, lam i • yHess (D.g i) z (0, d.2)) =
              ∑ i, (c i - e i) • yGrad (D.g i) z →
            ∃ (lam : Fin q → ℝ) (κ : ℝ) (μ : Fin q → ℝ),
              yHess D.f z d + κ • yGrad D.f z +
                (∑ i, (lam i • yHess (D.g i) z (0, d.2) + μ i • yGrad (D.g i) z)) = 0 ∧
              yGrad D.f z + (∑ i, lam i • yGrad (D.g i) z) = 0 ∧
              (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i * D.g i z) = 0 ∧
              (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i * D.g i z) = 0 ∧
              (∑ i, μ i * fderiv ℝ (D.g i) z (0, d.2)) = 0 := by
          intro lam h1 h2 h3 c e hc he hc0 he0 hw
          have hlg' := hlg lam h2 h3
          have hfeq : fderiv ℝ D.f z (0, d.2) = - ∑ i, lam i * inner ℝ (yGrad (D.g i) z) d.2 := by
            rw [hgradeq _ _ (hfd z), eq_neg_of_add_eq_zero_left h1, inner_neg_left, sum_inner]
            simp only [real_inner_smul_left]
          have hld : ∀ i, lam i * inner ℝ (yGrad (D.g i) z) d.2 = 0 := by
            intro i
            have hnp : ∀ j ∈ Finset.univ, lam j * inner ℝ (yGrad (D.g j) z) d.2 ≤ 0 := by
              intro j _
              by_cases hj : j ∈ actg D z
              · have := c10 j hj
                rw [hgradeq _ _ (hgd j z)] at this
                exact mul_nonpos_of_nonneg_of_nonpos (h2 j) this
              · have : lam j = 0 := by
                  rcases mul_eq_zero.mp (hlg' j) with h | h
                  · exact h
                  · exact absurd h hj
                rw [this, zero_mul]
            have hs : ∑ j, lam j * inner ℝ (yGrad (D.g j) z) d.2 = 0 := by
              have := c11; rw [hfeq] at this; linarith
            exact (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hs i (Finset.mem_univ _)
          set κ : ℝ := ∑ i, e i / lam i with hκ
          refine ⟨lam, κ, fun i => c i - e i + κ * lam i, ?_, h1, h2, h3, ?_, ?_, ?_⟩
          · have hSl : ∑ i, lam i • yGrad (D.g i) z = - yGrad D.f z := eq_neg_of_add_eq_zero_right h1
            have hμ : ∑ i, (c i - e i + κ * lam i) • yGrad (D.g i) z =
                ∑ i, (c i - e i) • yGrad (D.g i) z + κ • ∑ i, lam i • yGrad (D.g i) z := by
              rw [Finset.smul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [add_smul, mul_smul]
            rw [Finset.sum_add_distrib, hμ, hSl, ← hw]
            module
          · intro i
            by_cases hl : lam i = 0
            · simp only [hl, he0 i hl, mul_zero, add_zero, sub_zero]; exact hc i
            · have hlp : 0 < lam i := lt_of_le_of_ne (h2 i) (Ne.symm hl)
              have hk : e i / lam i ≤ κ :=
                Finset.single_le_sum (f := fun j => e j / lam j)
                  (fun j _ => div_nonneg (he j) (h2 j)) (Finset.mem_univ i)
              have : e i ≤ κ * lam i := by
                rwa [div_le_iff₀ hlp] at hk
              linarith [hc i]
          · refine Finset.sum_eq_zero fun i _ => ?_
            have hA : c i * D.g i z = 0 := by
              by_cases h : c i = 0
              · rw [h, zero_mul]
              · have := (hc0 i h).1; simp only [actg, Set.mem_setOf_eq] at this; rw [this, mul_zero]
            have hB : e i * D.g i z = 0 := by
              by_cases h : lam i = 0
              · rw [he0 i h, zero_mul]
              · rcases mul_eq_zero.mp (hlg' i) with h' | h'
                · exact absurd h' h
                · rw [h', mul_zero]
            have hC : κ * lam i * D.g i z = 0 := by rw [mul_assoc, hlg' i, mul_zero]
            linear_combination hA - hB + hC
          · refine Finset.sum_eq_zero fun i _ => ?_
            rw [hgradeq _ _ (hgd i z)]
            have hA : c i * inner ℝ (yGrad (D.g i) z) d.2 = 0 := by
              by_cases h : c i = 0
              · rw [h, zero_mul]
              · rw [(hc0 i h).2, mul_zero]
            have hB : e i * inner ℝ (yGrad (D.g i) z) d.2 = 0 := by
              by_cases h : lam i = 0
              · rw [he0 i h, zero_mul]
              · rcases mul_eq_zero.mp (hld i) with h' | h'
                · exact absurd h' h
                · rw [h', mul_zero]
            have hC : κ * lam i * inner ℝ (yGrad (D.g i) z) d.2 = 0 := by rw [mul_assoc, hld i, mul_zero]
            linear_combination hA - hB + hC
        have hgordanG : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
            (q : ℕ) (a : Fin q → F) (A : Set (Fin q)),
            (¬ ∃ u0 : F, ∀ i ∈ A, inner ℝ (a i) u0 < 0) →
            ∃ c ∈ stdSimplex ℝ (Fin q), (∀ i, i ∉ A → c i = 0) ∧ ∑ i, c i • a i = 0 := by
          classical
          intro F _ _ _ q a A hM
          by_contra h0
          have hTcl : IsClosed {c : Fin q → ℝ | ∀ i, i ∉ A → c i = 0} := by
            rw [Set.setOf_forall]
            refine isClosed_iInter fun i => ?_
            by_cases hi : i ∈ A
            · simp only [hi, not_true_eq_false, IsEmpty.forall_iff, Set.setOf_true]; exact isClosed_univ
            · simp only [hi, not_false_eq_true, forall_const]
              exact isClosed_eq (continuous_apply i) continuous_const
          have hTc : IsCompact (stdSimplex ℝ (Fin q) ∩ {c | ∀ i, i ∉ A → c i = 0}) :=
            (isCompact_stdSimplex ℝ (Fin q)).inter_right hTcl
          have hLc : Continuous fun c : Fin q → ℝ => ∑ i, c i • a i :=
            continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
          have hSc := (hTc.image hLc).isClosed
          have hSconv : Convex ℝ ((fun c : Fin q → ℝ => ∑ i, c i • a i) ''
              (stdSimplex ℝ (Fin q) ∩ {c | ∀ i, i ∉ A → c i = 0})) := by
            rintro _ ⟨c, hc, rfl⟩ _ ⟨e, he, rfl⟩ x y hx hy hxy
            refine ⟨x • c + y • e, ⟨convex_stdSimplex ℝ (Fin q) hc.1 he.1 hx hy hxy, fun i hi => ?_⟩, ?_⟩
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc.2 i hi, he.2 i hi, mul_zero,
                add_zero]
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
                Finset.sum_add_distrib, Finset.smul_sum]
          obtain ⟨f, r, hf, hfr⟩ := geometric_hahn_banach_closed_point hSconv hSc
            (by rintro ⟨c, hc, hc0⟩; exact h0 ⟨c, hc.1, hc.2, hc0⟩)
          apply hM
          refine ⟨(InnerProductSpace.toDual ℝ F).symm f, fun i hi => ?_⟩
          rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
          have := hf (a i) ⟨Pi.single i 1, ⟨single_mem_stdSimplex ℝ i, fun j hj => by
            rw [Pi.single_apply, if_neg (by rintro rfl; exact hj hi)]⟩, by
            simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
              Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩
          rw [map_zero] at hfr
          linarith
        have hgordan : (¬ ∃ u0 : Y m, ∀ i ∈ actg D z, inner ℝ (yGrad (D.g i) z) u0 < 0) →
            ∀ u ∈ lowerLinCone D z, u = 0 := by
          intro hM u hu
          by_contra hu0
          obtain ⟨c, hc, hcA, hc0⟩ := hgordanG (Y m) q (fun i => yGrad (D.g i) z) (actg D z) hM
          have hcs : (∑ i, c i * D.g i z) = 0 := Finset.sum_eq_zero fun i _ => by
            by_cases hi : i ∈ actg D z
            · rw [show D.g i z = 0 from hi, mul_zero]
            · rw [hcA i hi, zero_mul]
          have := habnormal u hu hu0 c hc0 (fun i => hc.1 i) hcs
            (Finset.sum_nonneg fun i _ => mul_nonneg (hc.1 i) (hpsd i u))
          have h1 := hc.2
          rw [this] at h1
          simp at h1
        have hfeasdir : ∀ y : Y m, (∀ j, D.g j (0, y) ≤ 0) → (y - z.2) ∈ lowerLinCone D z := by
          intro y hy i hi
          have h1 := hlineG _ (D.g i) z ((0:E n), y - z.2) 0 (hgd i _)
          rw [zero_smul, add_zero] at h1
          have h2 := (hasDerivAt_iff_tendsto_slope.mp h1).mono_left
            (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
          refine le_of_tendsto h2 ?_
          filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
          rw [slope_def_field]
          refine div_nonpos_of_nonpos_of_nonneg ?_ (by linarith [ht.1])
          have hz0 : D.g i z = 0 := hi
          have hzg : D.g i (0, z.2) = 0 := by rw [← hconvex.2.1 i z.1 z.2]; exact hi
          have hc := (hconvex.2.2 i).2 (Set.mem_univ z.2) (Set.mem_univ y)
            (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) (le_of_lt ht.1) (by ring)
          have heq : (z + t • ((0:E n), y - z.2)).2 = (1 - t) • z.2 + t • y := by
            rw [Prod.snd_add, Prod.smul_snd]; module
          show D.g i (z + t • ((0:E n), y - z.2)) - D.g i (z + (0:ℝ) • ((0:E n), y - z.2)) ≤ 0
          rw [zero_smul, add_zero, hz0, sub_zero, hconvex.2.1 i, heq]
          refine hc.trans ?_
          rw [smul_eq_mul, smul_eq_mul]
          show (1 - t) * D.g i (0, z.2) + t * D.g i (0, y) ≤ 0
          rw [hzg, mul_zero, zero_add]
          exact mul_nonpos_of_nonneg_of_nonpos ht.1.le (hy i)
        classical
        have hyG : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
            [InnerProductSpace ℝ W] [CompleteSpace W] (h : V × W → ℝ), ContDiff ℝ 2 h →
            Differentiable ℝ (fun w : V × W => gradient (fun y => h (w.1, y)) w.2) := by
          intro V W _ _ _ _ _ h hh
          have hd1 : Differentiable ℝ h := hh.differentiable (by norm_num)
          have hd2 : Differentiable ℝ (fderiv ℝ h) :=
            (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
          have heq : (fun w : V × W => gradient (fun y => h (w.1, y)) w.2) = fun w =>
              (InnerProductSpace.toDual ℝ W).symm
                ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ V W)) := by
            funext w
            have hc : HasFDerivAt (fun y : W => h (w.1, y))
                ((fderiv ℝ h w).comp (ContinuousLinearMap.inr ℝ V W)) w.2 :=
              (hd1 w).hasFDerivAt.comp w.2 (hasFDerivAt_prodMk_right w.1 w.2)
            rw [gradient, hc.fderiv]
          rw [heq]
          exact (InnerProductSpace.toDual ℝ W).symm.toContinuousLinearEquiv.differentiable.comp
            (hd2.clm_comp (differentiable_const _))
        have hsplitX : ∀ (V1 V2 W : Type) [NormedAddCommGroup V1] [NormedSpace ℝ V1]
            [NormedAddCommGroup V2] [NormedSpace ℝ V2] [NormedAddCommGroup W] [NormedSpace ℝ W]
            (h : V1 × V2 → W) (w d : V1 × V2), DifferentiableAt ℝ h w →
            (∀ a b, h (a, b) = h (w.1, b)) → fderiv ℝ h w (0, d.2) = fderiv ℝ h w d := by
          intro V1 V2 W _ _ _ _ _ _ h w d hh hx
          have hl := (((hasDerivAt_id' (0:ℝ)).smul_const ((d.1, 0) : V1 × V2)).const_add w).congr_deriv
            (one_smul ℝ _)
          have hA : HasFDerivAt h (fderiv ℝ h w) (w + (0:ℝ) • ((d.1, 0) : V1 × V2)) := by
            rw [zero_smul, add_zero]; exact hh.hasFDerivAt
          have h1 := hA.comp_hasDerivAt (0:ℝ) hl
          have h2 : (h ∘ fun s : ℝ => w + s • ((d.1, 0) : V1 × V2)) = fun _ => h w := by
            funext s
            have : w + s • ((d.1, 0) : V1 × V2) = (w.1 + s • d.1, w.2) := by ext <;> simp
            rw [Function.comp_apply, this, hx]
          rw [h2] at h1
          have h3 := h1.unique (hasDerivAt_const _ _)
          have : d = (d.1, 0) + (0, d.2) := by ext <;> simp
          conv_rhs => rw [this, map_add, h3, zero_add]
        have hkktB : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
            [InnerProductSpace ℝ W] [CompleteSpace W] (q : ℕ) (f : V × W → ℝ) (g : Fin q → V × W → ℝ)
            (x : V) (y u0 : W) (e : Fin q → ℝ) (A : ℝ),
            (∀ y', (∀ i, g i (x, y') ≤ 0) → f (x, y) ≤ f (x, y')) → (∀ i, g i (x, y) ≤ 0) →
            Differentiable ℝ f → (∀ i, Differentiable ℝ (g i)) →
            (∀ i, g i (x, y) = 0 → 0 < e i ∧ inner ℝ (gradient (fun y => g i (x, y)) y) u0 ≤ -e i) →
            inner ℝ (gradient (fun y => f (x, y)) y) u0 ≤ A →
            ∃ l : Fin q → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ i, g i (x, y) ≠ 0 → l i = 0) ∧
              gradient (fun y => f (x, y)) y + ∑ i, l i • gradient (fun y => g i (x, y)) y = 0 ∧
              ∀ i, l i * e i ≤ A := by
          intro V W _ _ _ _ _ q f g x y u0 e A hopt hfe hf hg he hA
          have hsl : ∀ h : V × W → ℝ, Differentiable ℝ h → DifferentiableAt ℝ (fun y => h (x, y)) y :=
            fun h hh => (hh (x, y)).comp y ((differentiableAt_const x).prodMk differentiableAt_id)
          obtain ⟨c, hc, hcs, hsum⟩ := hkktG W q (fun y => f (x, y)) (fun i y => g i (x, y)) y u0
            hopt hfe (hsl f hf) (fun i => hsl (g i) (hg i))
            (fun i hi => by linarith [(he i hi).1, (he i hi).2])
          refine ⟨c, hc, hcs, hsum, fun i => ?_⟩
          have hK := congrArg (fun v => inner ℝ v u0) hsum
          simp only [inner_add_left, sum_inner, real_inner_smul_left, inner_zero_left] at hK
          have hce : ∀ j, 0 ≤ c j * e j ∧
              c j * inner ℝ (gradient (fun y => g j (x, y)) y) u0 ≤ -(c j * e j) := by
            intro j
            by_cases h0 : g j (x, y) = 0
            · have := he j h0
              exact ⟨mul_nonneg (hc j) this.1.le, by
                have := mul_le_mul_of_nonneg_left this.2 (hc j); linarith⟩
            · rw [hcs j h0]; simp
          have h1 : c i * e i ≤ ∑ j, c j * e j :=
            Finset.single_le_sum (f := fun j => c j * e j) (fun j _ => (hce j).1) (Finset.mem_univ i)
          have h2 : ∑ j, c j * inner ℝ (gradient (fun y => g j (x, y)) y) u0 ≤ -∑ j, c j * e j := by
            rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum fun j _ => (hce j).2
          linarith
        have hmain : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
            [InnerProductSpace ℝ W] [CompleteSpace W] (q : ℕ) (Gf : V → W) (Gg : Fin q → V → W)
            (z d : V) (zs : ℕ → V) (lk : ℕ → Fin q → ℝ) (lam : Fin q → ℝ) (P : Fin q → Prop) [DecidablePred P],
            DifferentiableAt ℝ Gf z → (∀ i, DifferentiableAt ℝ (Gg i) z) →
            Filter.Tendsto zs Filter.atTop (𝓝 z) →
            Filter.Tendsto (fun k => ‖zs k - z‖⁻¹ • (zs k - z)) Filter.atTop (𝓝 d) →
            Filter.Tendsto lk Filter.atTop (𝓝 lam) →
            (∀ k, Gf (zs k) + ∑ i, lk k i • Gg i (zs k) = 0) →
            (∀ k i, 0 ≤ lk k i) →
            (∀ i, ¬ P i → ∀ᶠ k in Filter.atTop, lk k i = 0) →
            ∃ c0 : ℝ, 0 ≤ c0 ∧ ∃ c : Fin q → ℝ, (∀ i, 0 ≤ c i) ∧
              -(fderiv ℝ Gf z d + ∑ i, lam i • fderiv ℝ (Gg i) z d) =
                c0 • Gf z + ∑ i, c i • (if P i then Gg i z else 0) := by

          intro V W _ _ _ _ _ q Gf Gg z d zs lk lam P _ hGf hGg hz hd hl hkkt hl0 hP
          have hR : Filter.Tendsto (fun k => -(‖zs k - z‖⁻¹ • (Gf (zs k) - Gf z)) -
              ∑ i, lk k i • (‖zs k - z‖⁻¹ • (Gg i (zs k) - Gg i z))) Filter.atTop
              (𝓝 (-(fderiv ℝ Gf z d) - ∑ i, lam i • fderiv ℝ (Gg i) z d)) :=
            (hseqD V W Gf _ z d zs hGf.hasFDerivAt hz hd).neg.sub
              (tendsto_finsetSum _ fun i _ => (((continuous_apply i).tendsto lam).comp hl).smul
                (hseqD V W (Gg i) _ z d zs (hGg i).hasFDerivAt hz hd))
          obtain ⟨c, hc, hw⟩ := hfarkas W (q+1)
            (Fin.cons (Gf z) (fun i => if P i then Gg i z else 0) : Fin (q+1) → W)
            (-(fderiv ℝ Gf z d + ∑ i, lam i • fderiv ℝ (Gg i) z d)) (by
              intro u hu
              have hu0 : inner ℝ (Gf z) u ≤ 0 := hu 0
              have hui : ∀ i, P i → inner ℝ (Gg i z) u ≤ 0 := fun i hi => by
                have := hu i.succ
                rwa [Fin.cons_succ, if_pos hi] at this
              have hev : ∀ᶠ k in Filter.atTop, ∀ i, ¬ P i → lk k i = 0 := by
                rw [Filter.eventually_all]
                intro i
                by_cases hi : P i
                · exact Filter.Eventually.of_forall fun k h => absurd hi h
                · exact (hP i hi).mono fun k hk _ => hk
              rw [neg_add']
              refine le_of_tendsto (hR.inner tendsto_const_nhds) ?_
              filter_upwards [hev] with k hk
              have hK := congrArg (fun x => inner ℝ x u) (hkkt k)
              simp only [inner_add_left, sum_inner, real_inner_smul_left, inner_zero_left] at hK
              simp only [inner_sub_left, inner_neg_left, sum_inner, real_inner_smul_left]
              have hSd : ∑ i, lk k i * inner ℝ (Gg i z) u ≤ 0 := Finset.sum_nonpos fun i _ => by
                by_cases hi : P i
                · exact mul_nonpos_of_nonneg_of_nonpos (hl0 k i) (hui i hi)
                · rw [hk i hi, zero_mul]
              have e1 : ∑ i, lk k i * (‖zs k - z‖⁻¹ * (inner ℝ (Gg i (zs k)) u - inner ℝ (Gg i z) u)) =
                  ‖zs k - z‖⁻¹ * ∑ i, lk k i * inner ℝ (Gg i (zs k)) u -
                    ‖zs k - z‖⁻¹ * ∑ i, lk k i * inner ℝ (Gg i z) u := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by ring
              rw [e1]
              have h2 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (zs k - z)))
                (add_nonpos hu0 hSd)
              linear_combination h2 - ‖zs k - z‖⁻¹ * hK)
          refine ⟨c 0, hc 0, fun i => c i.succ, fun i => hc i.succ, ?_⟩
          rw [hw, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
        have hbr : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
            [InnerProductSpace ℝ W] [CompleteSpace W] (q : ℕ) (f : V × W → ℝ) (g : Fin q → V × W → ℝ)
            (Gf : V × W → W) (Gg : Fin q → V × W → W) (z d : V × W) (zs : ℕ → V × W) (u0 : W),
            (∀ w, Gf w = gradient (fun y => f (w.1, y)) w.2) →
            (∀ i w, Gg i w = gradient (fun y => g i (w.1, y)) w.2) →
            ContDiff ℝ 2 f → (∀ i, ContDiff ℝ 2 (g i)) → (∀ i a b, g i (a, b) = g i (z.1, b)) →
            (∀ k y', (∀ i, g i ((zs k).1, y') ≤ 0) → f ((zs k).1, (zs k).2) ≤ f ((zs k).1, y')) →
            (∀ k i, g i ((zs k).1, (zs k).2) ≤ 0) → (∀ i, g i z ≤ 0) →
            Filter.Tendsto zs Filter.atTop (𝓝 z) →
            Filter.Tendsto (fun k => ‖zs k - z‖⁻¹ • (zs k - z)) Filter.atTop (𝓝 d) →
            (∀ i ∈ {j | g j z = 0}, inner ℝ (Gg i z) u0 < 0) →
            (∀ i ∈ {j | g j z = 0}, fderiv ℝ (g i) z (0, d.2) ≤ 0) →
            ∃ (lam : Fin q → ℝ) (κ : ℝ) (μ : Fin q → ℝ),
              fderiv ℝ Gf z d + κ • Gf z +
                (∑ i, (lam i • fderiv ℝ (Gg i) z (0, d.2) + μ i • Gg i z)) = 0 ∧
              Gf z + (∑ i, lam i • Gg i z) = 0 ∧
              (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i * g i z) = 0 ∧
              (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i * g i z) = 0 ∧
              (∑ i, μ i * fderiv ℝ (g i) z (0, d.2)) = 0 := by
          intro V W _ _ _ _ _ q f g Gf Gg z d zs u0 hGf hGg hf2 hg2 hx hopt hfe hfz hzs hd hu0 hc10
          have hdf : Differentiable ℝ Gf := by
            rw [show Gf = _ from funext hGf]; exact hyG V W f hf2
          have hdg : ∀ i, Differentiable ℝ (Gg i) := fun i => by
            rw [show Gg i = _ from funext (hGg i)]; exact hyG V W (g i) (hg2 i)
          have hfD : Differentiable ℝ f := hf2.differentiable (by norm_num)
          have hgD : ∀ i, Differentiable ℝ (g i) := fun i => (hg2 i).differentiable (by norm_num)
          obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |inner ℝ (Gf z) u0| + 1 := ⟨_, rfl⟩
          have hev : ∀ᶠ k in Filter.atTop, inner ℝ (Gf (zs k)) u0 ≤ A ∧
              ∀ i, (g i (zs k) = 0 → 0 < -inner ℝ (Gg i z) u0 / 2 ∧
                inner ℝ (Gg i (zs k)) u0 ≤ -(-inner ℝ (Gg i z) u0 / 2)) := by
            refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun i => ?_)
            · have hlt : inner ℝ (Gf z) u0 < A := by
                rw [hA]; linarith [le_abs_self (inner ℝ (Gf z) u0)]
              exact ((((hdf z).continuousAt.tendsto.comp hzs).inner
                tendsto_const_nhds).eventually_lt_const hlt).mono fun k hk => hk.le
            · by_cases hi : g i z = 0
              · have hs : inner ℝ (Gg i z) u0 < 0 := hu0 i hi
                have hlt : inner ℝ (Gg i z) u0 < -(-inner ℝ (Gg i z) u0 / 2) := by linarith
                exact ((((hdg i z).continuousAt.tendsto.comp hzs).inner
                  tendsto_const_nhds).eventually_lt_const hlt).mono fun k hk _ => ⟨by linarith, hk.le⟩
              · have hneg : g i z < 0 := lt_of_le_of_ne (hfz i) hi
                exact ((((hgD i).continuous.tendsto z).comp hzs).eventually_lt_const hneg).mono
                  fun k hk h0 => absurd h0 hk.ne
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
          have hkkt : ∀ k, ∃ l : Fin q → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ i, g i (zs (k + N)) ≠ 0 → l i = 0) ∧
              Gf (zs (k + N)) + ∑ i, l i • Gg i (zs (k + N)) = 0 ∧
              l ∈ Set.Icc (0 : Fin q → ℝ) (fun i => |A / (-inner ℝ (Gg i z) u0 / 2)|) := by
            intro k
            obtain ⟨hA', he⟩ := hN (k + N) (Nat.le_add_left N k)
            rw [hGf] at hA'
            obtain ⟨l, hl0, hls, hlk, hlb⟩ := hkktB V W q f g (zs (k + N)).1 (zs (k + N)).2 u0
              (fun i => -inner ℝ (Gg i z) u0 / 2) A (hopt (k + N)) (hfe (k + N)) hfD hgD
              (fun i h0 => by rw [← hGg i (zs (k + N))]; exact he i h0) hA'
            refine ⟨l, hl0, hls, by simp only [hGf, hGg]; exact hlk, hl0, fun i => ?_⟩
            by_cases h0 : g i (zs (k + N)) = 0
            · exact ((le_div_iff₀ (he i h0).1).2 (hlb i)).trans (le_abs_self _)
            · rw [hls i h0]; exact abs_nonneg _
          choose lk hlk using hkkt
          obtain ⟨lam, hlamI, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq fun k => (hlk k).2.2.2
          have hρ : StrictMono fun k => ψ k + N := fun a b h => Nat.add_lt_add_right (hψ h) N
          have hzs' : Filter.Tendsto (fun k => zs (ψ k + N)) Filter.atTop (𝓝 z) :=
            hzs.comp hρ.tendsto_atTop
          have hPev : ∀ i, ¬ (g i z = 0 ∧ fderiv ℝ (g i) z (0, d.2) = 0) →
              ∀ᶠ k in Filter.atTop, g i (zs k) ≠ 0 := by
            intro i hi
            by_cases ha : g i z = 0
            · have hlt : fderiv ℝ (g i) z d < 0 := by
                rw [← hsplitX V W ℝ (g i) z d (hgD i z) (hx i)]
                exact lt_of_le_of_ne (hc10 i ha) fun h => hi ⟨ha, h⟩
              refine ((hseqD _ ℝ (g i) _ z d zs (hgD i z).hasFDerivAt hzs
                hd).eventually_lt_const hlt).mono fun k hk h0 => ?_
              rw [h0, ha, sub_zero, smul_zero] at hk
              exact lt_irrefl _ hk
            · have hneg : g i z < 0 := lt_of_le_of_ne (hfz i) ha
              exact ((((hgD i).continuous.tendsto z).comp hzs).eventually_lt_const hneg).mono
                fun k hk => hk.ne
          obtain ⟨c0, hc0, c, hc, hrep⟩ := hmain (V × W) W q Gf Gg z d
            (fun k => zs (ψ k + N)) (fun k => lk (ψ k)) lam
            (fun i => g i z = 0 ∧ fderiv ℝ (g i) z (0, d.2) = 0) (hdf z) (fun i => hdg i z)
            hzs' (hd.comp hρ.tendsto_atTop) hlim (fun k => (hlk (ψ k)).2.2.1)
            (fun k => (hlk (ψ k)).1) (fun i hi => ((hρ.tendsto_atTop.eventually (hPev i hi))).mono
              fun k hk => (hlk (ψ k)).2.1 i hk)
          have hK1 : Gf z + ∑ i, lam i • Gg i z = 0 := by
            have h : Filter.Tendsto (fun k => Gf (zs (ψ k + N)) +
                ∑ i, lk (ψ k) i • Gg i (zs (ψ k + N))) Filter.atTop
                (𝓝 (Gf z + ∑ i, lam i • Gg i z)) :=
              ((hdf z).continuousAt.tendsto.comp hzs').add (tendsto_finsetSum _ fun i _ =>
                (((continuous_apply i).tendsto lam).comp hlim).smul
                  ((hdg i z).continuousAt.tendsto.comp hzs'))
            exact tendsto_nhds_unique h ((tendsto_const_nhds (x := (0 : W))).congr
              fun k => ((hlk (ψ k)).2.2.1).symm)
          have hK3 : ∀ i, lam i * g i z = 0 := by
            intro i
            have h := (((continuous_apply i).tendsto lam).comp hlim).mul
              (((hgD i).continuous.tendsto z).comp hzs')
            refine tendsto_nhds_unique h ((tendsto_const_nhds (x := (0 : ℝ))).congr fun k => ?_)
            simp only [Function.comp_apply]
            by_cases h0 : g i (zs (ψ k + N)) = 0
            · rw [h0, mul_zero]
            · rw [(hlk (ψ k)).2.1 i h0, zero_mul]
          have hHg : ∀ i, fderiv ℝ (Gg i) z (0, d.2) = fderiv ℝ (Gg i) z d := by
            intro i
            refine hsplitX V W W (Gg i) z d (hdg i z) fun a b => ?_
            rw [hGg, hGg]
            show gradient (fun y => g i (a, y)) b = gradient (fun y => g i (z.1, y)) b
            congr 1
            funext y
            exact hx i a y
          refine ⟨lam, c0, fun i => if g i z = 0 ∧ fderiv ℝ (g i) z (0, d.2) = 0 then c i else 0,
            ?_, hK1, fun i => hlamI.1 i, Finset.sum_eq_zero fun i _ => hK3 i, fun i => ?_, ?_, ?_⟩
          · have hS : ∑ i, ((if g i z = 0 ∧ fderiv ℝ (g i) z (0, d.2) = 0 then c i else 0) •
                Gg i z) = ∑ i, c i • (if g i z = 0 ∧ fderiv ℝ (g i) z (0, d.2) = 0
                  then Gg i z else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs <;> simp
            simp only [hHg]
            rw [Finset.sum_add_distrib, hS]
            linear_combination (norm := module) -hrep
          · show 0 ≤ ite _ _ _
            split_ifs
            · exact hc i
            · exact le_refl _
          · refine Finset.sum_eq_zero fun i _ => ?_
            dsimp only
            split_ifs with h
            · rw [h.1, mul_zero]
            · rw [zero_mul]
          · refine Finset.sum_eq_zero fun i _ => ?_
            dsimp only
            split_ifs with h
            · rw [h.2, mul_zero]
            · rw [zero_mul]
        by_cases hM : ∃ u0 : Y m, ∀ i ∈ actg D z, inner ℝ (yGrad (D.g i) z) u0 < 0
        · obtain ⟨u0, hu0⟩ := hM
          exact hbr (E n) (Y m) q D.f D.g (yGrad D.f) (fun i => yGrad (D.g i)) z d (fun k => zk (φ k))
            u0 (fun w => rfl) (fun i w => rfl) hStanding.2.1 hStanding.2.2.2
            (fun i a b => by rw [hconvex.2.1 i a b, hconvex.2.1 i z.1 b])
            (fun k y' hy' => (hzk _).2.2 y' hy') (fun k i => (hzk _).2.1 i) (fun i => hfeas.2.1 i)
            (hzk_tend.comp hφ.tendsto_atTop) hdlim hu0 c10
        · have hy2 : ∀ k, (zk k).2 = z.2 := by
            intro k
            refine sub_eq_zero.mp (hgordan hM _ (hfeasdir _ fun j => ?_))
            have := (hzk k).2.1 j
            rwa [hconvex.2.1 j] at this
          have hd2 : d.2 = 0 := by
            have h1 := (continuous_snd.tendsto d).comp hdlim
            have h2 : (Prod.snd ∘ ((fun k => ‖zk k - z‖⁻¹ • (zk k - z)) ∘ φ)) = fun _ => (0 : Y m) := by
              funext k
              simp only [Function.comp, Prod.smul_snd, Prod.snd_sub, hy2 (φ k), sub_self, smul_zero]
            rw [h2] at h1
            exact tendsto_nhds_unique h1 tendsto_const_nhds
          classical
          have hall : ∀ w : Y m, ∃ c : Fin q → ℝ, (∀ i, 0 ≤ c i) ∧
              w = ∑ i, c i • (if i ∈ actg D z then yGrad (D.g i) z else 0) := by
            intro w
            refine hfarkas (Y m) q _ w fun u hu => ?_
            have hu0 : u = 0 := hgordan hM u (fun i hi => by
              have := hu i
              rw [if_pos hi] at this
              rw [hgradeq _ _ (hgd i z)]
              exact this)
            rw [hu0, inner_zero_right]
          have hrep : ∀ w : Y m, ∃ c : Fin q → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, c i ≠ 0 → i ∈ actg D z) ∧
              w = ∑ i, c i • yGrad (D.g i) z := by
            intro w
            obtain ⟨c, hc, hw⟩ := hall w
            refine ⟨fun i => if i ∈ actg D z then c i else 0, fun i => ?_, fun i hi => ?_, ?_⟩
            · show 0 ≤ ite _ _ _
              split_ifs
              · exact hc i
              · exact le_refl _
            · by_contra h; exact hi (if_neg h)
            · rw [hw]
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases h : i ∈ actg D z
              · simp only [if_pos h]
              · simp only [if_neg h, smul_zero, zero_smul]
          obtain ⟨lam, hl0, hlA, hlw⟩ := hrep (-yGrad D.f z)
          have h1 : yGrad D.f z + ∑ i, lam i • yGrad (D.g i) z = 0 := by
            rw [← hlw]; exact add_neg_cancel _
          have h3 : ∑ i, lam i * D.g i z = 0 := Finset.sum_eq_zero fun i _ => by
            by_cases h : lam i = 0
            · rw [h, zero_mul]
            · rw [show D.g i z = 0 from hlA i h, mul_zero]
          obtain ⟨c, hc0, hcA, hcw⟩ :=
            hrep (-(yHess D.f z d + ∑ i, lam i • yHess (D.g i) z (0, d.2)))
          refine hfinal lam h1 hl0 h3 c 0 hc0 (fun _ => le_refl _)
            (fun i hi => ⟨hcA i hi, by rw [hd2, inner_zero_right]⟩) (fun _ _ => rfl) ?_
          rw [hcw]
          simp only [Pi.zero_apply, sub_zero]
      obtain ⟨lam, κ, μ, h3, h4, h5, h6, h7, h8, h9⟩ := hcrux
      have hd0 := hexclude d lam κ μ ⟨c1, c2, h3, h4, h5, h6, h7, h8, h9, c10, c11⟩
      rw [hd0, norm_zero] at hdnorm
      exact zero_ne_one hdnorm
