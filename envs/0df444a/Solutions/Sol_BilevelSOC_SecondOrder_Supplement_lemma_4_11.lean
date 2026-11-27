-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:44.332261+00:00
-- url     : https://prove2.me/submissions/3b954d5a-89b7-44c3-abc9-4a46be1c3b88

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_NormalGraph
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hconvex : FixedConvexLower D)
    (hsol : z.2 ∈ solMap D z.1) :
    tangentCone (graph (solMap D)) z ⊆ normalTangentEstimate D z ∧
    (MetricSubregularAt (normalResidual D) z 0 →
      tangentCone (graph (solMap D)) z = normalTangentEstimate D z) := by
        obtain ⟨-, hf, -, -⟩ := hStanding
        obtain ⟨hfc, hgi, hgc⟩ := hconvex
        -- general limit along directions
        have hlim : ∀ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
            [NormedAddCommGroup W] [NormedSpace ℝ W] (φ : V → W) (φ' : V →L[ℝ] W) (x : V)
            (_ : HasFDerivAt φ φ' x) (t : ℕ → ℝ) (dk : ℕ → V) (d : V) (_ : ∀ k, 0 < t k)
            (_ : Filter.Tendsto t Filter.atTop (𝓝 0)) (_ : Filter.Tendsto dk Filter.atTop (𝓝 d)),
            Filter.Tendsto (fun k => (t k)⁻¹ • (φ (x + t k • dk k) - φ x)) Filter.atTop (𝓝 (φ' d)) := by
          intro V W _ _ _ _ φ φ' x hφ t dk d ht ht0 hdk
          have h := hφ.hasFDerivWithinAt (s := Set.univ)
          refine h.lim (c := fun k => (t k)⁻¹) (d := fun k => t k • dk k) (l := Filter.atTop) ?_ ?_ ?_
          · have h1 : Filter.Tendsto (fun k => t k • dk k) Filter.atTop (𝓝 ((0:ℝ) • d)) := ht0.smul hdk
            rw [zero_smul] at h1
            exact h1
          · exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
          · refine hdk.congr (fun k => ?_)
            rw [smul_smul, inv_mul_cancel₀ (ht k).ne', one_smul]
        have hfd : Differentiable ℝ D.f := hf.differentiable (by norm_num)
        have hpart : ∀ w : E n × Y m, HasFDerivAt (fun y => D.f (w.1, y))
            ((fderiv ℝ D.f w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) w.2 := by
          intro w
          have h1 : HasFDerivAt D.f (fderiv ℝ D.f w) (w.1, w.2) := (hfd w).hasFDerivAt
          exact h1.comp w.2 (hasFDerivAt_prodMk_right w.1 w.2)
        have hyG : yGrad D.f = fun w => (InnerProductSpace.toDual ℝ (Y m)).symm
            ((fderiv ℝ D.f w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) := by
          funext w
          simp only [yGrad, gradient]
          rw [(hpart w).fderiv]
        have hinner : ∀ (w : E n × Y m) (u : Y m),
            inner ℝ (yGrad D.f w) u = fderiv ℝ D.f w (0, u) := by
          intro w u
          rw [hyG]
          simp [InnerProductSpace.toDual_symm_apply]
        have hyGd : Differentiable ℝ (yGrad D.f) := by
          rw [hyG]
          have h1 : Differentiable ℝ (fderiv ℝ D.f) :=
            (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
          have h2 : Differentiable ℝ (fun w => (fderiv ℝ D.f w).comp
              (ContinuousLinearMap.inr ℝ (E n) (Y m))) := fun w =>
            (h1 w).clm_comp (differentiableAt_const _)
          intro w
          exact ((InnerProductSpace.toDual ℝ (Y m)).symm.toContinuousLinearEquiv.differentiableAt).comp w (h2 w)
        -- the map
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E n × Y m → Y m × Y m, Ψ = fun w => (w.2, - yGrad D.f w) := ⟨_, rfl⟩
        obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : E n × Y m →L[ℝ] Y m × Y m, Ψ' =
            (ContinuousLinearMap.snd ℝ (E n) (Y m)).prod (-(fderiv ℝ (yGrad D.f) z)) := ⟨_, rfl⟩
        have hΨd : HasFDerivAt Ψ Ψ' z := by
          rw [hΨ, hΨ']
          exact hasFDerivAt_snd.prodMk (hyGd z).hasFDerivAt.neg
        have hΨ'a : ∀ d, Ψ' d = (d.2, - yHess D.f z d) := by
          intro d; rw [hΨ']; simp [yHess]
        have hfeas : ∀ x, lowerFeas D x = lowerFeas D 0 := by
          intro x; ext y
          constructor
          · intro h j
            have := h j
            rwa [hgi] at this
          · intro h j
            rw [hgi]; exact h j
        have hKconv : Convex ℝ (lowerFeas D 0) := by
          intro a ha b hb s t hs ht hst j
          have := (hgc j).2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
          refine this.trans ?_
          have h1 := ha j
          have h2 := hb j
          simp only [smul_eq_mul]
          nlinarith
        -- characterization
        have hchar : ∀ w : E n × Y m, w ∈ graph (solMap D) ↔ Ψ w ∈ normalGraph D := by
          intro w
          have hτ0 : Filter.Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) Filter.atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have hτ : ∀ k : ℕ, 0 < 1 / ((k:ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
          have hτ1 : ∀ k : ℕ, 1 / ((k:ℝ) + 1) ≤ 1 := by
            intro k
            rw [div_le_one (by positivity)]
            have : (0:ℝ) ≤ k := Nat.cast_nonneg k
            linarith
          have hw : Ψ w ∈ normalGraph D ↔ w.2 ∈ lowerFeas D 0 ∧
              ∀ u ∈ tangentCone (lowerFeas D 0) w.2, 0 ≤ fderiv ℝ D.f w (0, u) := by
            rw [hΨ]
            show (w.2 ∈ lowerFeas D 0 ∧ ∀ u ∈ tangentCone (lowerFeas D 0) w.2,
              inner ℝ (-yGrad D.f w) u ≤ 0) ↔ _
            refine and_congr Iff.rfl (forall₂_congr fun u _ => ?_)
            rw [inner_neg_left, hinner]
            exact neg_nonpos
          rw [hw]
          show (w.2 ∈ lowerFeas D w.1 ∧ ∀ y' ∈ lowerFeas D w.1, D.f (w.1, w.2) ≤ D.f (w.1, y')) ↔ _
          rw [hfeas w.1]
          refine and_congr_right (fun hw2 => ?_)
          constructor
          · rintro hmin u ⟨t, dk, ht, ht0, hdk, hmem⟩
            have h := hlim _ _ _ (hpart w) t dk u ht ht0 hdk
            have h' : 0 ≤ ((fderiv ℝ D.f w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) u := by
              refine ge_of_tendsto' h (fun k => ?_)
              have := hmin _ (hmem k)
              exact smul_nonneg (inv_nonneg.2 (ht k).le) (sub_nonneg.2 this)
            simpa using h'
          · intro hn y' hy'
            have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → w.2 + s • (y' - w.2) = (1 - s) • w.2 + s • y' := by
              intro s _ _
              rw [smul_sub, sub_smul, one_smul]; abel
            have h1 := hn (y' - w.2) ⟨fun k => 1 / ((k:ℝ) + 1), fun _ => y' - w.2, hτ, hτ0,
              tendsto_const_nhds, fun k => by
                rw [hseg _ (hτ k).le (hτ1 k)]
                exact hKconv hw2 hy' (sub_nonneg.2 (hτ1 k)) (hτ k).le (by ring)⟩
            have h := hlim _ _ _ (hpart w) (fun k : ℕ => 1 / ((k:ℝ) + 1)) (fun _ => y' - w.2)
              (y' - w.2) hτ hτ0 tendsto_const_nhds
            have h2 : ((fderiv ℝ D.f w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) (y' - w.2)
                ≤ D.f (w.1, y') - D.f (w.1, w.2) := by
              refine le_of_tendsto' h (fun k => ?_)
              have hc := (hfc w.1).2 (Set.mem_univ w.2) (Set.mem_univ y')
                (sub_nonneg.2 (hτ1 k)) (hτ k).le (by ring)
              rw [← hseg _ (hτ k).le (hτ1 k)] at hc
              simp only [smul_eq_mul] at hc ⊢
              rw [inv_mul_le_iff₀ (hτ k)]
              linarith
            have h3 : ((fderiv ℝ D.f w).comp (ContinuousLinearMap.inr ℝ (E n) (Y m))) (y' - w.2)
                = fderiv ℝ D.f w (0, y' - w.2) := by simp
            rw [h3] at h2
            linarith
        have hest : ∀ d, d ∈ normalTangentEstimate D z ↔ Ψ' d ∈ tangentCone (normalGraph D) (Ψ z) := by
          intro d
          rw [hΨ'a, hΨ]; rfl
        have hsub : tangentCone (graph (solMap D)) z ⊆ normalTangentEstimate D z := by
          rintro d ⟨t, dk, ht, ht0, hdk, hmem⟩
          rw [hest]
          refine ⟨t, fun k => (t k)⁻¹ • (Ψ (z + t k • dk k) - Ψ z), ht, ht0,
            hlim _ _ _ hΨd t dk d ht ht0 hdk, fun k => ?_⟩
          rw [smul_smul, mul_inv_cancel₀ (ht k).ne', one_smul, add_sub_cancel]
          exact (hchar _).1 (hmem k)
        refine ⟨hsub, fun hms => Set.Subset.antisymm hsub ?_⟩
        obtain ⟨-, U, hU, κ, hκ, hreg⟩ := hms
        have hzero : {b | (0 : Y m × Y m) ∈ normalResidual D b} = graph (solMap D) := by
          ext b
          rw [hchar, hΨ]
          constructor
          · rintro ⟨w, hw, h⟩
            have : w = (b.2, - yGrad D.f b) := (sub_eq_zero.1 h.symm)
            rw [this] at hw; exact hw
          · intro h
            exact ⟨_, h, (sub_self _).symm⟩
        rw [hzero] at hreg
        intro d hd
        rw [hest] at hd
        obtain ⟨t, ek, ht, ht0, hek, hmem⟩ := hd
        have ha : Filter.Tendsto (fun k => z + t k • d) Filter.atTop (𝓝 z) := by
          have := (ht0.smul_const d).const_add z
          simpa using this
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ha.eventually hU)
        -- remainder
        have hΨlim := hlim _ _ _ hΨd t (fun _ => d) d ht ht0 tendsto_const_nhds
        obtain ⟨r, hr⟩ : ∃ r : ℕ → Y m × Y m,
            r = fun k => ek k - (t k)⁻¹ • (Ψ (z + t k • d) - Ψ z) := ⟨_, rfl⟩
        have hr0 : Filter.Tendsto r Filter.atTop (𝓝 0) := by
          rw [hr]; simpa using hek.sub hΨlim
        have hres : ∀ k, t k • r k ∈ normalResidual D (z + t k • d) := by
          intro k
          refine ⟨_, hmem k, ?_⟩
          have h1 : ((z + t k • d).2, - yGrad D.f (z + t k • d)) = Ψ (z + t k • d) := by rw [hΨ]
          rw [h1, hr]
          simp only [smul_sub, smul_smul]
          rw [mul_inv_cancel₀ (ht k).ne', one_smul, one_smul]
          abel
        have hb : ∀ k, N ≤ k → ∃ b ∈ graph (solMap D),
            dist (z + t k • d) b < t k * (κ * ‖r k‖ + t k) := by
          intro k hk
          have h1 := hreg _ (hN k hk)
          have h2 : Metric.infEDist (0 : Y m × Y m) (normalResidual D (z + t k • d)) ≤
              edist 0 (t k • r k) := Metric.infEDist_le_edist_of_mem (hres k)
          have h3 : Metric.infEDist (z + t k • d) (graph (solMap D)) <
              ENNReal.ofReal (t k * (κ * ‖r k‖ + t k)) := by
            refine (h1.trans (mul_le_mul_right h2 _)).trans_lt ?_
            rw [edist_dist, dist_zero_left, norm_smul, Real.norm_of_nonneg (ht k).le,
              ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg κ)]
            have hpos : 0 < t k * t k := mul_pos (ht k) (ht k)
            have hnn : 0 ≤ t k * (κ * ‖r k‖) := mul_nonneg (ht k).le (mul_nonneg κ.2 (norm_nonneg _))
            refine (ENNReal.ofReal_lt_ofReal_iff ?_).2 ?_ <;> nlinarith
          obtain ⟨b, hbm, hbd⟩ := Metric.infEDist_lt_iff.1 h3
          refine ⟨b, hbm, ?_⟩
          rw [edist_dist] at hbd
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 hbd
        choose! b hbm hbd using hb
        refine ⟨fun k => t (k + N), fun k => (t (k+N))⁻¹ • (b (k+N) - z), fun k => ht _,
          ht0.comp (Filter.tendsto_add_atTop_nat N), ?_, fun k => ?_⟩
        · rw [tendsto_iff_dist_tendsto_zero]
          have hlim2 : Filter.Tendsto (fun k => (κ:ℝ) * ‖r (k+N)‖ + t (k+N)) Filter.atTop (𝓝 0) := by
            have h0 := ((hr0.norm).const_mul (κ:ℝ)).add ht0
            have h1 := h0.comp (Filter.tendsto_add_atTop_nat N)
            rw [norm_zero, mul_zero, add_zero] at h1
            exact h1
          refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hlim2
          have hk := hbd (k+N) (Nat.le_add_left _ _)
          have hT := ht (k+N)
          have heq : (t (k+N))⁻¹ • (b (k+N) - z) - d
              = (t (k+N))⁻¹ • (b (k+N) - (z + t (k+N) • d)) := by
            simp only [smul_sub, smul_add, smul_smul]
            rw [inv_mul_cancel₀ hT.ne', one_smul]
            abel
          rw [dist_eq_norm, heq, norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_le_iff₀ hT,
            ← dist_eq_norm, dist_comm]
          exact hk.le
        · rw [smul_smul, mul_inv_cancel₀ (ht _).ne', one_smul, add_sub_cancel]
          exact hbm _ (Nat.le_add_left _ _)
