-- Prove2me | solution 1 for DROOptimal.Predictor.Supplement.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:34.634811+00:00
-- url     : https://prove2.me/submissions/1417e324-e597-4268-9636-b2006c8e14a2

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Supplement_Pairs

set_option autoImplicit false

open DROOptimal
open DROOptimal.Predictor
open DROOptimal.Predictor.Supplement

/-- Theorem 11, p. 26, both clauses, with standing assumptions of §2, p. 5,
and §5, p. 23. The selector is any quasi-continuous selector of the constructed
robust predictor, as in Definition 7 and §5, pp. 24–25.
Every positive constant shift is feasible for r ≥ 0. For r > 0 the unshifted
pair is preferred to every feasible pair; its feasibility is not asserted.
The proof's last sentence on p. 37 has ε > 0 where the statement has r > 0. -/
theorem solution {n d : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (Ξ : Set (EuclideanSpace ℝ (Fin d))) (hΞ : IsCompact Ξ)
    (γ : ↥X → ↥Ξ → ℝ) (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2))
    (r : ℝ) (hr : 0 ≤ r)
    (xhat_r : DROOptimal.Continuous.Dist Ξ → ↥X)
    (hquasi : QuasiContinuous xhat_r)
    (hargmin : IsArgminSelector (DROOptimal.Continuous.drPredictor γ r) xhat_r) :
    (∀ ε : ℝ, 0 < ε →
      Feasible6 γ r (fun x P' => DROOptimal.Continuous.drPredictor γ r x P' + ε) xhat_r) ∧
    (0 < r → ∀ (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
      (xhat : DROOptimal.Continuous.Dist Ξ → ↥X),
      Feasible6 γ r chat xhat →
        PairLE (DROOptimal.Continuous.drPredictor γ r) xhat_r chat xhat) := by
          -- Joint weak continuity of the model-based cost (x, ℙ) ↦ ∫ γ(x, ·) dℙ.
          have hcost : Continuous (fun q : ↥X × DROOptimal.Continuous.Dist Ξ =>
              DROOptimal.Continuous.cost γ q.1 q.2) := by
            have : CompactSpace ↥Ξ := isCompact_iff_compactSpace.mp hΞ
            let G : C(↥X, C(↥Ξ, ℝ)) := ContinuousMap.curry ⟨fun p : ↥X × ↥Ξ => γ p.1 p.2, hγ⟩
            have hint : ∀ (y : ↥X) (P : DROOptimal.Continuous.Dist Ξ),
                MeasureTheory.Integrable (fun ξ => γ y ξ) (P : MeasureTheory.Measure ↥Ξ) :=
              fun y P => (BoundedContinuousFunction.mkOfCompact (G y)).integrable _
            rw [continuous_iff_continuousAt]
            rintro ⟨x0, P0⟩
            rw [Metric.continuousAt_iff']
            intro ε hε
            have h1 : ∀ᶠ x in nhds x0, dist (G x) (G x0) < ε / 2 :=
              (G.continuous.tendsto x0) (Metric.ball_mem_nhds _ (half_pos hε))
            have h2 : ∀ᶠ P in nhds P0, dist (DROOptimal.Continuous.cost γ x0 P)
                (DROOptimal.Continuous.cost γ x0 P0) < ε / 2 := by
              let f : BoundedContinuousFunction ↥Ξ ℝ := BoundedContinuousFunction.mkOfCompact (G x0)
              have := (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
                f).continuousAt (x := P0)
              exact this (Metric.ball_mem_nhds _ (half_pos hε))
            rw [nhds_prod_eq]
            filter_upwards [h1.prod_mk h2]
            rintro ⟨x, P⟩ ⟨hx, hP⟩
            have h3 : dist (DROOptimal.Continuous.cost γ x P) (DROOptimal.Continuous.cost γ x0 P)
                ≤ dist (G x) (G x0) := by
              unfold DROOptimal.Continuous.cost
              rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x P) (hint x0 P)]
              refine (MeasureTheory.norm_integral_le_of_norm_le_const
                (C := dist (G x) (G x0)) (Filter.Eventually.of_forall fun ξ => ?_)).trans ?_
              · rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist (f := G x) (g := G x0) ξ
              · simp
            calc dist (DROOptimal.Continuous.cost γ x P) (DROOptimal.Continuous.cost γ x0 P0)
                ≤ dist (DROOptimal.Continuous.cost γ x P) (DROOptimal.Continuous.cost γ x0 P)
                  + dist (DROOptimal.Continuous.cost γ x0 P) (DROOptimal.Continuous.cost γ x0 P0) :=
                  dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h3.trans hx.le) hP
              _ = ε := add_halves ε
          rcases hr.eq_or_lt with h0 | hpos
          · -- r = 0: the robust predictor is the model-based cost and the rate condition is vacuous.
            subst h0
            have hdr : ∀ (x : ↥X) (P' : DROOptimal.Continuous.Dist Ξ),
                DROOptimal.Continuous.drPredictor γ 0 x P' = DROOptimal.Continuous.cost γ x P' := by
              intro x P'
              have hset : {P : DROOptimal.Continuous.Dist Ξ |
                  DROOptimal.Continuous.relEnt P' P ≤ ENNReal.ofReal 0} = {P'} := by
                ext P
                simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ENNReal.ofReal_zero,
                  nonpos_iff_eq_zero, DROOptimal.Continuous.relEnt, InformationTheory.klDiv_eq_zero_iff]
                constructor
                · intro h; exact (MeasureTheory.ProbabilityMeasure.toMeasure_injective h).symm
                · intro h; rw [h]
              unfold DROOptimal.Continuous.drPredictor
              rw [hset, Set.image_singleton, csSup_singleton]
            refine ⟨fun ε hε => ⟨⟨?_, hquasi, ?_⟩, fun P r' hr' => ?_⟩, fun h => absurd h (lt_irrefl 0)⟩
            · have : (fun q : ↥X × DROOptimal.Continuous.Dist Ξ =>
                  DROOptimal.Continuous.drPredictor γ 0 q.1 q.2 + ε) =
                  (fun q : ↥X × DROOptimal.Continuous.Dist Ξ =>
                  DROOptimal.Continuous.cost γ q.1 q.2 + ε) := by
                funext q; rw [hdr]
              show Continuous (fun q : ↥X × DROOptimal.Continuous.Dist Ξ =>
                  DROOptimal.Continuous.drPredictor γ 0 q.1 q.2 + ε)
              rw [this]; exact hcost.add continuous_const
            · intro P'
              refine ⟨Set.mem_univ _, fun y _ => ?_⟩
              have := (hargmin P').2 y (Set.mem_univ _)
              simpa using this
            · simp at hr'
          · -- r > 0
            -- Uniform bound on the cost, so the robust supremum is a genuine supremum.
            have hbound : ∃ C : ℝ, ∀ (x : ↥X) (P : DROOptimal.Continuous.Dist Ξ),
                |DROOptimal.Continuous.cost γ x P| ≤ C := by
              have : CompactSpace ↥X := isCompact_iff_compactSpace.mp hX
              have : CompactSpace ↥Ξ := isCompact_iff_compactSpace.mp hΞ
              obtain ⟨C, hC⟩ := (isCompact_univ (X := ↥X × ↥Ξ)).exists_bound_of_continuousOn
                hγ.continuousOn
              refine ⟨C, fun x P => ?_⟩
              have h := MeasureTheory.norm_integral_le_of_norm_le_const
                (μ := (P : MeasureTheory.Measure ↥Ξ)) (f := fun ξ => γ x ξ) (C := C)
                (Filter.Eventually.of_forall fun ξ => hC (x, ξ) (Set.mem_univ _))
              simpa [DROOptimal.Continuous.cost] using h
            obtain ⟨C, hC⟩ := hbound
            have hbdd : ∀ (x : ↥X) (P' : DROOptimal.Continuous.Dist Ξ),
                BddAbove (DROOptimal.Continuous.cost γ x '' {P : DROOptimal.Continuous.Dist Ξ |
                  DROOptimal.Continuous.relEnt P' P ≤ ENNReal.ofReal r}) := by
              intro x P'
              refine ⟨C, ?_⟩
              rintro _ ⟨P, _, rfl⟩
              exact (le_abs_self _).trans (hC x P)
            -- Every model in the relative-entropy ball is dominated by the robust predictor.
            have hle : ∀ (x : ↥X) (P' P : DROOptimal.Continuous.Dist Ξ),
                DROOptimal.Continuous.relEnt P' P ≤ ENNReal.ofReal r →
                DROOptimal.Continuous.cost γ x P ≤ DROOptimal.Continuous.drPredictor γ r x P' :=
              fun x P' P hP => le_csSup (hbdd x P') ⟨P, hP, rfl⟩
            have instX : CompactSpace ↥X := isCompact_iff_compactSpace.mp hX
            have instXi : CompactSpace ↥Ξ := isCompact_iff_compactSpace.mp hΞ
            obtain ⟨C0, hγC0⟩ := (isCompact_univ (X := ↥X × ↥Ξ)).exists_bound_of_continuousOn
              hγ.continuousOn
            have hγC : ∀ x ξ, |γ x ξ| ≤ C0 := fun x ξ => hγC0 (x, ξ) (Set.mem_univ _)
            have hjoint : ∀ (Y : Type) [TopologicalSpace Y] (g : Y → ↥Ξ → ℝ),
                Continuous (fun p : Y × ↥Ξ => g p.1 p.2) →
                Continuous (fun q : Y × DROOptimal.Continuous.Dist Ξ =>
                  ∫ ξ, g q.1 ξ ∂(q.2 : MeasureTheory.Measure ↥Ξ)) := by
              intro Y _ g hg
              let G : C(Y, C(↥Ξ, ℝ)) := ContinuousMap.curry ⟨fun p : Y × ↥Ξ => g p.1 p.2, hg⟩
              have hint : ∀ (y : Y) (P : DROOptimal.Continuous.Dist Ξ),
                  MeasureTheory.Integrable (fun ξ => g y ξ) (P : MeasureTheory.Measure ↥Ξ) :=
                fun y P => (BoundedContinuousFunction.mkOfCompact (G y)).integrable _
              rw [continuous_iff_continuousAt]
              rintro ⟨x0, P0⟩
              rw [Metric.continuousAt_iff']
              intro ε hε
              have h1 : ∀ᶠ x in nhds x0, dist (G x) (G x0) < ε / 2 :=
                (G.continuous.tendsto x0) (Metric.ball_mem_nhds _ (half_pos hε))
              have h2 : ∀ᶠ P in nhds P0, dist (∫ ξ, g x0 ξ ∂((P : DROOptimal.Continuous.Dist Ξ) : MeasureTheory.Measure ↥Ξ))
                  (∫ ξ, g x0 ξ ∂(P0 : MeasureTheory.Measure ↥Ξ)) < ε / 2 := by
                let f : BoundedContinuousFunction ↥Ξ ℝ := BoundedContinuousFunction.mkOfCompact (G x0)
                have := (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
                  f).continuousAt (x := P0)
                exact this (Metric.ball_mem_nhds _ (half_pos hε))
              rw [nhds_prod_eq]
              filter_upwards [h1.prod_mk h2]
              rintro ⟨x, P⟩ ⟨hx, hP⟩
              have h3 : dist (∫ ξ, g x ξ ∂(P : MeasureTheory.Measure ↥Ξ)) (∫ ξ, g x0 ξ ∂(P : MeasureTheory.Measure ↥Ξ))
                  ≤ dist (G x) (G x0) := by
                rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x P) (hint x0 P)]
                refine (MeasureTheory.norm_integral_le_of_norm_le_const
                  (C := dist (G x) (G x0)) (Filter.Eventually.of_forall fun ξ => ?_)).trans ?_
                · rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist (f := G x) (g := G x0) ξ
                · simp
              exact (dist_triangle _ _ _).trans_lt ((add_lt_add_of_le_of_lt (h3.trans hx.le) hP).trans_eq (add_halves ε))
            have hintg : ∀ (f : ↥Ξ → ℝ), Continuous f → ∀ P : DROOptimal.Continuous.Dist Ξ,
                MeasureTheory.Integrable f (P : MeasureTheory.Measure ↥Ξ) := fun f hf P =>
              (BoundedContinuousFunction.mkOfCompact (⟨f, hf⟩ : C(↥Ξ, ℝ))).integrable _
            have hDV : ∀ (f : ↥Ξ → ℝ), Continuous f → ∀ (r0 : ℝ), 0 ≤ r0 → ∀ q P : DROOptimal.Continuous.Dist Ξ,
                DROOptimal.Continuous.relEnt q P ≤ ENNReal.ofReal r0 →
                ∫ ξ, f ξ ∂(q : MeasureTheory.Measure ↥Ξ) -
                  Real.log (∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ)) ≤ r0 := by
              intro f hf r0 hr0 q P h
              have hne : InformationTheory.klDiv (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) ≠ ⊤ :=
                ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
              obtain ⟨hac, hllr⟩ := InformationTheory.klDiv_ne_top_iff.mp hne
              have h1 := InformationTheory.toReal_klDiv hac hllr
              have hexp : MeasureTheory.Integrable (fun ξ => Real.exp (f ξ)) (P : MeasureTheory.Measure ↥Ξ) :=
                hintg _ (Real.continuous_exp.comp hf) P
              have hprob : MeasureTheory.IsProbabilityMeasure ((P : MeasureTheory.Measure ↥Ξ).tilted f) :=
                MeasureTheory.isProbabilityMeasure_tilted hexp
              have h2 := MeasureTheory.integral_llr_tilted_right hac (hintg f hf q) hexp hllr
              have h3 := InformationTheory.integral_llr_add_sub_measure_univ_nonneg
                (hac.trans (MeasureTheory.absolutelyContinuous_tilted hexp))
                (MeasureTheory.integrable_llr_tilted_right hac (hintg f hf q) hllr hexp)
              rw [h2] at h3
              have h4 : (InformationTheory.klDiv (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ)).toReal ≤ r0 :=
                ENNReal.toReal_le_of_le_ofReal hr0 h
              rw [h1] at h4
              simp only [MeasureTheory.probReal_univ] at h3 h4
              linarith
            have hKL : ∀ (q P : DROOptimal.Continuous.Dist Ξ) (k : ↥Ξ → ℝ), Continuous k → (∀ ξ, 0 < k ξ) →
                (q : MeasureTheory.Measure ↥Ξ).withDensity (fun ξ => ENNReal.ofReal (k ξ)) ≤ (P : MeasureTheory.Measure ↥Ξ) →
                DROOptimal.Continuous.relEnt q P ≤
                  ENNReal.ofReal (∫ ξ, - Real.log (k ξ) ∂(q : MeasureTheory.Measure ↥Ξ)) := by
              intro q P k hk hkpos hle
              have hkm : Measurable (fun ξ => ENNReal.ofReal (k ξ)) := hk.measurable.ennreal_ofReal
              have hac : MeasureTheory.Measure.AbsolutelyContinuous (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) :=
                (MeasureTheory.withDensity_absolutelyContinuous' hkm.aemeasurable
                  (Filter.Eventually.of_forall fun ξ => by simpa using hkpos ξ)).trans
                  (MeasureTheory.Measure.absolutelyContinuous_of_le hle)
              have hLD : (q : MeasureTheory.Measure ↥Ξ).HaveLebesgueDecomposition (P : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
              set ρ := (q : MeasureTheory.Measure ↥Ξ).rnDeriv (P : MeasureTheory.Measure ↥Ξ) with hρ
              have hρm : Measurable ρ := MeasureTheory.Measure.measurable_rnDeriv _ _
              have hq : (P : MeasureTheory.Measure ↥Ξ).withDensity ρ = (q : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.Measure.withDensity_rnDeriv_eq (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) hac
              have hae : (fun ξ => ρ ξ * ENNReal.ofReal (k ξ)) ≤ᵐ[(P : MeasureTheory.Measure ↥Ξ)] (fun _ => 1) := by
                refine MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite (hρm.mul hkm) ?_
                intro s hs _
                have e1 : ∫⁻ ξ in s, ρ ξ * ENNReal.ofReal (k ξ) ∂(P : MeasureTheory.Measure ↥Ξ) =
                    (q : MeasureTheory.Measure ↥Ξ).withDensity (fun ξ => ENNReal.ofReal (k ξ)) s := by
                  conv_rhs => rw [← hq]
                  rw [← MeasureTheory.withDensity_mul _ hρm hkm, MeasureTheory.withDensity_apply _ hs]
                  rfl
                rw [e1]
                simpa using hle s
              -- lower bound of k
              obtain ⟨c, hc, hck⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ξ, c ≤ k ξ := by
                rcases isEmpty_or_nonempty ↥Ξ with he | hne
                · exact ⟨1, one_pos, fun ξ => (he.false ξ).elim⟩
                · obtain ⟨ξ0, _, h0⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := ↥Ξ)) hk.continuousOn
                  exact ⟨k ξ0, hkpos ξ0, fun ξ => h0 (Set.mem_univ ξ)⟩
              have hub : ∀ᵐ ξ ∂(P : MeasureTheory.Measure ↥Ξ), (ρ ξ).toReal * k ξ ≤ 1 := by
                filter_upwards [hae] with ξ hξ
                have := ENNReal.toReal_mono ENNReal.one_ne_top hξ
                rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hkpos ξ).le, ENNReal.toReal_one] at this
              have hllrint : MeasureTheory.Integrable (MeasureTheory.llr (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ)) (q : MeasureTheory.Measure ↥Ξ) := by
                rw [← InformationTheory.integrable_klFun_rnDeriv_iff hac]
                obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := c⁻¹)).exists_bound_of_continuousOn
                  InformationTheory.continuous_klFun.continuousOn
                refine MeasureTheory.Integrable.of_bound (C := B) ?_ ?_
                · exact (InformationTheory.measurable_klFun.comp hρm.ennreal_toReal).aestronglyMeasurable
                · filter_upwards [hub] with ξ hξ
                  refine hB _ ⟨ENNReal.toReal_nonneg, ?_⟩
                  rw [← one_div, le_div_iff₀ hc]
                  exact (mul_le_mul_of_nonneg_left (hck ξ) ENNReal.toReal_nonneg).trans hξ
              unfold DROOptimal.Continuous.relEnt
              rw [InformationTheory.klDiv_of_ac_of_integrable hac hllrint]
              apply ENNReal.ofReal_le_ofReal
              simp only [MeasureTheory.probReal_univ, add_sub_cancel_right]
              have hlk : Continuous (fun ξ => - Real.log (k ξ)) := (hk.log fun ξ => (hkpos ξ).ne').neg
              refine MeasureTheory.integral_mono_ae hllrint (hintg _ hlk q) ?_
              filter_upwards [hac.ae_le hub, MeasureTheory.Measure.rnDeriv_pos hac, hac.ae_le (MeasureTheory.Measure.rnDeriv_lt_top (q : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ))] with ξ h1 h2' h2''
              have h2 : 0 < (ρ ξ).toReal := ENNReal.toReal_pos h2'.ne' h2''.ne
              show Real.log (ρ ξ).toReal ≤ _
              rw [← Real.log_inv]
              apply Real.log_le_log h2
              rw [← one_div, le_div_iff₀ (hkpos ξ)]
              exact h1
            have hemp : ∀ (T : ℕ) (hT : 0 < T) (ω : Fin T → ↥Ξ) (f : ↥Ξ → ℝ),
                Measurable f →
                ∫ ξ, f ξ ∂(DROOptimal.Continuous.empirical ω hT : MeasureTheory.Measure ↥Ξ) = (∑ t, f (ω t)) / T := by
              intro T hT ω f hf
              show ∫ ξ, f ξ ∂(DROOptimal.Continuous.empiricalMeasure ω) = _
              unfold DROOptimal.Continuous.empiricalMeasure
              rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_finsetSum_measure]
              · simp [MeasureTheory.integral_dirac, div_eq_inv_mul]
              · intro i _
                exact MeasureTheory.integrable_dirac (by simp)
            have hnbhd : ∀ (q0 : DROOptimal.Continuous.Dist Ξ) (V : Set (DROOptimal.Continuous.Dist Ξ)), V ∈ nhds q0 →
                ∃ (I : Finset (BoundedContinuousFunction ↥Ξ ℝ)) (δ : ℝ), 0 < δ ∧
                  ∀ q : DROOptimal.Continuous.Dist Ξ, (∀ f ∈ I, |∫ ξ, f ξ ∂(q : MeasureTheory.Measure ↥Ξ) -
                    ∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ)| < δ) → q ∈ V := by
              intro q0 V hV
              let F : Filter (DROOptimal.Continuous.Dist Ξ) := ⨅ f : BoundedContinuousFunction ↥Ξ ℝ,
                Filter.comap (fun q : DROOptimal.Continuous.Dist Ξ => ∫ ξ, f ξ ∂(q : MeasureTheory.Measure ↥Ξ))
                  (nhds (∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ)))
              have hF : Filter.Tendsto (fun q : DROOptimal.Continuous.Dist Ξ => q) F (nhds q0) := by
                rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
                intro f
                rw [Filter.tendsto_iff_comap]
                exact iInf_le _ f
              have hVF : V ∈ F := hF hV
              obtain ⟨I, hI, W, hW, hVW⟩ := Filter.mem_iInf.mp hVF
              have hW' : ∀ i : I, ∃ δ : ℝ, 0 < δ ∧ ∀ q : DROOptimal.Continuous.Dist Ξ,
                  |∫ ξ, i.1 ξ ∂(q : MeasureTheory.Measure ↥Ξ) -
                    ∫ ξ, i.1 ξ ∂(q0 : MeasureTheory.Measure ↥Ξ)| < δ → q ∈ W i := by
                intro i
                obtain ⟨t, ht, htW⟩ := Filter.mem_comap.mp (hW i)
                obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
                exact ⟨δ, hδ, fun q hq => htW (hball (by simpa [Metric.mem_ball, Real.dist_eq] using hq))⟩
              choose δ hδ hδW using hW'
              have : Finite I := hI
              obtain ⟨δ0, hδ0, hle⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ i, δ0 ≤ δ i := by
                rcases isEmpty_or_nonempty I with he | hne
                · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
                · obtain ⟨i0, hi0⟩ := Finite.exists_min δ
                  exact ⟨δ i0, hδ i0, hi0⟩
              refine ⟨hI.toFinset, δ0, hδ0, fun q hq => ?_⟩
              rw [hVW]
              refine Set.mem_iInter.mpr fun i => hδW i q ?_
              exact (hq i.1 (hI.mem_toFinset.mpr i.2)).trans_le (hle i)
            -- SLLN
            have hSLLN : ∀ (q0 : DROOptimal.Continuous.Dist Ξ) (f : ↥Ξ → ℝ), Measurable f →
                MeasureTheory.Integrable f (q0 : MeasureTheory.Measure ↥Ξ) →
                ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => (q0 : MeasureTheory.Measure ↥Ξ))),
                  Filter.Tendsto (fun T : ℕ => (∑ t : Fin T, f (ω t)) / T) Filter.atTop
                    (nhds (∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ))) := by
              intro q0 f hf hfi
              set μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => (q0 : MeasureTheory.Measure ↥Ξ)) with hμ
              have hmp : ∀ i : ℕ, MeasureTheory.MeasurePreserving (Function.eval i) μ (q0 : MeasureTheory.Measure ↥Ξ) :=
                fun i => _root_.measurePreserving_eval_infinitePi (fun _ : ℕ => (q0 : MeasureTheory.Measure ↥Ξ)) i
              have hind : ProbabilityTheory.iIndepFun (fun (i : ℕ) (ω : ℕ → ↥Ξ) => f (ω i)) μ :=
                ProbabilityTheory.iIndepFun_infinitePi (X := fun (_ : ℕ) => f) (fun _ => hf)
              have h := ProbabilityTheory.strong_law_ae_real (μ := μ) (fun (i : ℕ) (ω : ℕ → ↥Ξ) => f (ω i))
                ((hmp 0).integrable_comp_of_integrable hfi)
                (fun i j hij => hind.indepFun hij)
                (fun i => by
                  refine ⟨(hf.comp (measurable_pi_apply i)).aemeasurable, (hf.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
                  have e : ∀ j : ℕ, MeasureTheory.Measure.map (fun ω : ℕ → ↥Ξ => f (ω j)) μ = MeasureTheory.Measure.map f (q0 : MeasureTheory.Measure ↥Ξ) := by
                    intro j
                    rw [← (hmp j).map_eq, MeasureTheory.Measure.map_map hf (measurable_pi_apply j)]
                    rfl
                  rw [e i, e 0])
              have hmean : ∫ ω, f (ω 0) ∂μ = ∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ) := by
                rw [← (hmp 0).map_eq, MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
                  hf.aestronglyMeasurable]
              rw [hmean] at h
              filter_upwards [h] with ω hω
              refine hω.congr fun T => ?_
              rw [Finset.sum_range (fun i => f (ω i))]
            -- change of measure
            have hCOM : ∀ (q0 P : DROOptimal.Continuous.Dist Ξ), MeasureTheory.Measure.AbsolutelyContinuous (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) →
                ∀ (T : ℕ) (c : ℝ) (E : Set (Fin T → ↥Ξ)), MeasurableSet E →
                (∀ ω ∈ E, ∑ t, MeasureTheory.llr (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) (ω t) ≤ c) →
                MeasureTheory.Measure.pi (fun _ : Fin T => (q0 : MeasureTheory.Measure ↥Ξ)) E ≤
                  ENNReal.ofReal (Real.exp c) * MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) E := by
              intro q0 P hac T c E hE hc
              have hLD : (q0 : MeasureTheory.Measure ↥Ξ).HaveLebesgueDecomposition (P : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
              set ρ := (q0 : MeasureTheory.Measure ↥Ξ).rnDeriv (P : MeasureTheory.Measure ↥Ξ) with hρ
              have hρm : Measurable ρ := MeasureTheory.Measure.measurable_rnDeriv _ _
              have hq : (P : MeasureTheory.Measure ↥Ξ).withDensity ρ = (q0 : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.Measure.withDensity_rnDeriv_eq (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) hac
              have hprodm : Measurable (fun ω : Fin T → ↥Ξ => ∏ t, ρ (ω t)) :=
                Finset.measurable_prod _ fun t _ => hρm.comp (measurable_pi_apply t)
              have hpi : MeasureTheory.Measure.pi (fun _ : Fin T => (q0 : MeasureTheory.Measure ↥Ξ)) =
                  (MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))).withDensity
                    (fun ω => ∏ t, ρ (ω t)) := by
                refine MeasureTheory.Measure.pi_eq fun s hs => ?_
                rw [MeasureTheory.withDensity_apply _ (MeasurableSet.univ_pi hs), ← MeasureTheory.lintegral_indicator (MeasurableSet.univ_pi hs)]
                have e1 : ∀ ω : Fin T → ↥Ξ, (Set.univ.pi s).indicator (fun ω => ∏ t, ρ (ω t)) ω =
                    ∏ t, (s t).indicator ρ (ω t) := by
                  intro ω
                  by_cases hω : ω ∈ Set.univ.pi s
                  · rw [Set.indicator_of_mem hω]
                    exact Finset.prod_congr rfl fun t _ => (Set.indicator_of_mem (hω t (Set.mem_univ t)) _).symm
                  · rw [Set.indicator_of_notMem hω]
                    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hω
                    obtain ⟨t, ht⟩ := hω
                    exact (Finset.prod_eq_zero (Finset.mem_univ t) (Set.indicator_of_notMem ht _)).symm
                rw [MeasureTheory.lintegral_congr e1]
                have hind : ProbabilityTheory.iIndepFun (fun (t : Fin T) (ω : Fin T → ↥Ξ) => (s t).indicator ρ (ω t))
                    (MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))) := by
                  rw [← MeasureTheory.Measure.infinitePi_eq_pi]
                  exact ProbabilityTheory.iIndepFun_infinitePi (X := fun (t : Fin T) => (s t).indicator ρ) (fun t => hρm.indicator (hs t))
                rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
                  (fun t => (hρm.indicator (hs t)).comp (measurable_pi_apply t))]
                refine Finset.prod_congr rfl fun t _ => ?_
                have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) t
                rw [show ∫⁻ ω : Fin T → ↥Ξ, (s t).indicator ρ (ω t) ∂(MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))) =
                  ∫⁻ ξ, (s t).indicator ρ ξ ∂(P : MeasureTheory.Measure ↥Ξ) from
                    hmp.lintegral_comp (hρm.indicator (hs t))]
                rw [MeasureTheory.lintegral_indicator (hs t), ← MeasureTheory.withDensity_apply _ (hs t), hq]
              rw [hpi, MeasureTheory.withDensity_apply _ hE]
              have hfin : ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))), ∀ t, ρ (ω t) < ⊤ := by
                rw [MeasureTheory.ae_all_iff]
                intro t
                have h := MeasureTheory.Measure.rnDeriv_lt_top (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ)
                exact (MeasureTheory.measurePreserving_eval (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) t).quasiMeasurePreserving.ae h
              calc ∫⁻ ω in E, ∏ t, ρ (ω t) ∂(MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)))
                  ≤ ∫⁻ ω in E, ENNReal.ofReal (Real.exp c) ∂(MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))) := by
                    refine MeasureTheory.setLIntegral_mono_ae measurable_const.aemeasurable ?_
                    filter_upwards [hfin] with ω hω hωE
                    have e2 : ∏ t, ρ (ω t) = ENNReal.ofReal (∏ t, (ρ (ω t)).toReal) := by
                      rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
                      exact Finset.prod_congr rfl fun t _ => (ENNReal.ofReal_toReal (hω t).ne).symm
                    rw [e2]
                    apply ENNReal.ofReal_le_ofReal
                    by_cases hz : ∃ t, (ρ (ω t)).toReal = 0
                    · obtain ⟨t, ht⟩ := hz
                      rw [Finset.prod_eq_zero (Finset.mem_univ t) ht]
                      exact (Real.exp_pos c).le
                    · push Not at hz
                      have e3 : ∏ t, (ρ (ω t)).toReal = Real.exp (∑ t, Real.log (ρ (ω t)).toReal) := by
                        rw [Real.exp_sum]
                        exact Finset.prod_congr rfl fun t _ => (Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (hz t).symm)).symm
                      rw [e3]
                      exact Real.exp_le_exp.mpr (hc ω hωE)
                _ = _ := by
                    rw [MeasureTheory.setLIntegral_const]
            -- Sanov lower bound
            have hSanov : ∀ (q0 P : DROOptimal.Continuous.Dist Ξ) (V : Set (DROOptimal.Continuous.Dist Ξ)), V ∈ nhds q0 →
                ∀ (r0 s : ℝ), 0 ≤ r0 → r0 < s → DROOptimal.Continuous.relEnt q0 P ≤ ENNReal.ofReal r0 →
                ∀ᶠ T : ℕ in Filter.atTop, ENNReal.ofReal (Real.exp (-(s * T))) ≤
                  DROOptimal.Continuous.sampleProb P T (fun q => q ∈ V) := by
              intro q0 P V hV r0 s hr0 hs h
              have hne : InformationTheory.klDiv (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) ≠ ⊤ :=
                ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
              obtain ⟨hac, hllr⟩ := InformationTheory.klDiv_ne_top_iff.mp hne
              have h1 := InformationTheory.toReal_klDiv hac hllr
              have h4 : (InformationTheory.klDiv (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ)).toReal ≤ r0 :=
                ENNReal.toReal_le_of_le_ofReal hr0 h
              rw [h1] at h4
              simp only [MeasureTheory.probReal_univ, add_sub_cancel_right] at h4
              have hllrm := MeasureTheory.measurable_llr (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ)
              set ℓ := MeasureTheory.llr (q0 : MeasureTheory.Measure ↥Ξ) (P : MeasureTheory.Measure ↥Ξ) with hℓ
              obtain ⟨I, δ, hδ, hIV⟩ := hnbhd q0 V hV
              obtain ⟨s', hs1, hs2⟩ := exists_between hs
              let A : (T : ℕ) → Set (Fin T → ↥Ξ) := fun T =>
                {ω | (∑ t, ℓ (ω t)) / T < s'} ∩ ⋂ f ∈ I, {ω | |(∑ t, f (ω t)) / T - ∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ)| < δ}
              have hAm : ∀ T, MeasurableSet (A T) := by
                intro T
                refine MeasurableSet.inter ?_ ?_
                · refine measurableSet_lt ?_ measurable_const
                  exact (Finset.measurable_sum _ fun t _ => hllrm.comp (measurable_pi_apply t)).div_const _
                · refine Finset.measurableSet_biInter I fun f _ => ?_
                  refine measurableSet_lt ?_ measurable_const
                  refine Measurable.abs (Measurable.sub_const ((Finset.measurable_sum _ fun t _ => f.continuous.measurable.comp (measurable_pi_apply t)).div_const _) _)
              set μ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => (q0 : MeasureTheory.Measure ↥Ξ)) with hμ
              have hrm : ∀ T : ℕ, Measurable (fun (ω : ℕ → ↥Ξ) (t : Fin T) => ω t) := fun T =>
                measurable_pi_lambda _ fun t => measurable_pi_apply _
              have hmap : ∀ T : ℕ, MeasureTheory.Measure.pi (fun _ : Fin T => (q0 : MeasureTheory.Measure ↥Ξ)) (A T) =
                  μ ((fun (ω : ℕ → ↥Ξ) (t : Fin T) => ω t) ⁻¹' (A T)) := by
                intro T
                rw [← MeasureTheory.Measure.map_apply (hrm T) (hAm T), hμ,
                  MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj (f := fun t : Fin T => (t : ℕ)) Fin.val_injective,
                  MeasureTheory.Measure.infinitePi_eq_pi]
              have hlim : Filter.Tendsto (fun T : ℕ => μ ((fun (ω : ℕ → ↥Ξ) (t : Fin T) => ω t) ⁻¹' (A T))) Filter.atTop (nhds (μ Set.univ)) := by
                refine MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure _ MeasurableSet.univ
                  (fun T => hrm T (hAm T)) ?_
                have hfs : ∀ᵐ ω ∂μ, ∀ f ∈ I, Filter.Tendsto (fun T : ℕ => (∑ t : Fin T, f (ω t)) / T) Filter.atTop
                    (nhds (∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ))) := by
                  rw [Filter.eventually_all_finset]
                  intro f _
                  exact hSLLN q0 f f.continuous.measurable (f.integrable _)
                filter_upwards [hSLLN q0 ℓ hllrm hllr, hfs] with ω hω1 hω2
                have e1 : ∀ᶠ T : ℕ in Filter.atTop, (∑ t : Fin T, ℓ (ω t)) / T < s' :=
                  hω1.eventually (gt_mem_nhds (h4.trans_lt hs1))
                have e2 : ∀ᶠ T : ℕ in Filter.atTop, ∀ f ∈ I, |(∑ t : Fin T, f (ω t)) / T - ∫ ξ, f ξ ∂(q0 : MeasureTheory.Measure ↥Ξ)| < δ := by
                  rw [Filter.eventually_all_finset]
                  intro f hf
                  have := (hω2 f hf).eventually (Metric.ball_mem_nhds _ hδ)
                  filter_upwards [this] with T hT
                  simpa [Metric.mem_ball, Real.dist_eq] using hT
                filter_upwards [e1, e2] with T h1 h2
                simp only [Set.mem_univ, iff_true]
                refine ⟨h1, ?_⟩
                simp only [Set.mem_iInter]
                exact fun f hf => h2 f hf
              rw [MeasureTheory.measure_univ] at hlim
              have hhalf : ∀ᶠ T : ℕ in Filter.atTop, ENNReal.ofReal (1/2) < μ ((fun (ω : ℕ → ↥Ξ) (t : Fin T) => ω t) ⁻¹' (A T)) :=
                hlim.eventually (lt_mem_nhds (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)))
              have hexp : ∀ᶠ T : ℕ in Filter.atTop, Real.exp (s' * T) * Real.exp (-(s * T)) ≤ 1 / 2 := by
                have : Filter.Tendsto (fun T : ℕ => Real.exp (-((s - s') * T))) Filter.atTop (nhds 0) := by
                  refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
                  exact Filter.Tendsto.const_mul_atTop (sub_pos.mpr hs2) tendsto_natCast_atTop_atTop
                filter_upwards [this.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))] with T hT
                rw [← Real.exp_add]
                refine le_trans (le_of_eq ?_) hT.le
                congr 1; ring
              filter_upwards [hhalf, hexp, Filter.eventually_gt_atTop 0] with T hT1 hT2 hT0
              have hT0' : (0:ℝ) < T := by exact_mod_cast hT0
              have hcom := hCOM q0 P hac T (s' * T) (A T) (hAm T) (fun ω hω => by
                have := hω.1
                simp only [Set.mem_ofPred_eq] at this
                exact ((div_lt_iff₀ hT0').mp this).le)
              rw [hmap T] at hcom
              have hsub : MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) (A T) ≤
                  DROOptimal.Continuous.sampleProb P T (fun q => q ∈ V) := by
                unfold DROOptimal.Continuous.sampleProb
                rw [dif_pos hT0]
                apply MeasureTheory.measure_mono
                intro ω hω
                show DROOptimal.Continuous.empirical ω hT0 ∈ V
                apply hIV
                intro f hf
                rw [hemp T hT0 ω f f.continuous.measurable]
                have := hω.2
                simp only [Set.mem_iInter] at this
                exact this f hf
              have hpos : ENNReal.ofReal (Real.exp (s' * T)) ≠ 0 := by simpa using Real.exp_pos _
              have key : ENNReal.ofReal (Real.exp (s' * T)) * ENNReal.ofReal (Real.exp (-(s * T))) ≤
                  ENNReal.ofReal (Real.exp (s' * T)) * DROOptimal.Continuous.sampleProb P T (fun q => q ∈ V) := by
                rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
                calc _ ≤ ENNReal.ofReal (1/2) := ENNReal.ofReal_le_ofReal hT2
                  _ ≤ _ := hT1.le
                  _ ≤ _ := hcom
                  _ ≤ _ := by gcongr
              exact (ENNReal.mul_le_mul_iff_right hpos ENNReal.ofReal_ne_top).mp key
            have hChern : ∀ (f : ↥Ξ → ℝ), Continuous f → ∀ (P : DROOptimal.Continuous.Dist Ξ) (T : ℕ) (hT : 0 < T) (u : ℝ),
                MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))
                  {ω | u ≤ ∫ ξ, f ξ ∂(DROOptimal.Continuous.empirical ω hT : MeasureTheory.Measure ↥Ξ) -
                    Real.log (∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ))} ≤
                ENNReal.ofReal (Real.exp (-(u * T))) := by
              intro f hf P T hT u
              have hT' : (0:ℝ) < T := by exact_mod_cast hT
              set Z := ∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ) with hZ
              have hZpos : 0 < Z := MeasureTheory.integral_exp_pos (hintg _ (Real.continuous_exp.comp hf) P)
              set μ := MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) with hμ
              have hpint : ∫ ω : Fin T → ↥Ξ, ∏ t, Real.exp (f (ω t)) ∂μ = Z ^ T := by
                rw [hμ, MeasureTheory.integral_fintype_prod_eq_pow (fun ξ => Real.exp (f ξ)), Fintype.card_fin]
              have hpintg : MeasureTheory.Integrable (fun ω : Fin T → ↥Ξ => ∏ t, Real.exp (f (ω t))) μ :=
                MeasureTheory.Integrable.fintype_prod (f := fun _ : Fin T => fun ξ => Real.exp (f ξ))
                  (fun _ => hintg _ (Real.continuous_exp.comp hf) P)
              have hmk := MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := μ)
                (f := fun ω : Fin T → ↥Ξ => ∏ t, Real.exp (f (ω t)))
                (Filter.Eventually.of_forall fun ω => Finset.prod_nonneg fun t _ => (Real.exp_pos _).le) hpintg
                (Real.exp (u * T) * Z ^ T)
              rw [hpint] at hmk
              have hsub : {ω : Fin T → ↥Ξ | u ≤ ∫ ξ, f ξ ∂(DROOptimal.Continuous.empirical ω hT : MeasureTheory.Measure ↥Ξ) -
                    Real.log Z} ⊆ {ω | Real.exp (u * T) * Z ^ T ≤ ∏ t, Real.exp (f (ω t))} := by
                intro ω hω
                simp only [Set.mem_ofPred_eq] at hω ⊢
                rw [hemp T hT ω f hf.measurable] at hω
                rw [← Real.exp_sum]
                have e : Z ^ T = Real.exp (T * Real.log Z) := by
                  rw [mul_comm, ← Real.rpow_def_of_pos hZpos, Real.rpow_natCast]
                rw [e, ← Real.exp_add]
                apply Real.exp_le_exp.mpr
                have h2 : (u + Real.log Z) ≤ (∑ t, f (ω t)) / T := by linarith
                rw [le_div_iff₀ hT'] at h2
                linarith
              refine (MeasureTheory.measure_mono hsub).trans ?_
              rw [← MeasureTheory.ofReal_measureReal]
              apply ENNReal.ofReal_le_ofReal
              have hZT : 0 < Z ^ T := pow_pos hZpos T
              rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
              have : μ.real {ω | Real.exp (u * T) * Z ^ T ≤ ∏ t, Real.exp (f (ω t))} * Real.exp (u * T) * Z ^ T ≤ 1 * Z ^ T := by
                rw [one_mul]; refine le_trans (le_of_eq ?_) hmk; ring
              exact le_of_mul_le_mul_right this hZT
            -- Worst-case cost and the dual integrand.
            have hne : ∀ q : DROOptimal.Continuous.Dist Ξ, Nonempty ↥Ξ := by
              intro q
              by_contra hcon
              rw [not_nonempty_iff] at hcon
              have h1 : (q : MeasureTheory.Measure ↥Ξ) Set.univ = 1 := MeasureTheory.measure_univ
              rw [Set.univ_eq_empty_iff.mpr hcon, MeasureTheory.measure_empty] at h1
              exact zero_ne_one h1
            have hγx : ∀ x : ↥X, Continuous (γ x) := fun x => hγ.comp (Continuous.prodMk_right x)
            obtain ⟨m, hmcont, hmle, hmatt⟩ : ∃ m : ↥X → ℝ, Continuous m ∧ (∀ x ξ, γ x ξ ≤ m x) ∧
                (Nonempty ↥Ξ → ∀ x, ∃ ξ, γ x ξ = m x) := by
              refine ⟨fun x => sSup (γ x '' Set.univ), IsCompact.continuous_sSup isCompact_univ hγ, ?_, ?_⟩
              · intro x ξ
                exact le_csSup (isCompact_univ.image (hγx x)).bddAbove ⟨ξ, Set.mem_univ _, rfl⟩
              · intro hN x
                obtain ⟨ξ, _, h⟩ := (isCompact_univ.image (hγx x)).sSup_mem (Set.univ_nonempty.image _)
                exact ⟨ξ, h⟩
            have hmC : Nonempty ↥Ξ → ∀ x, m x ≤ C0 := by
              intro hN x
              obtain ⟨ξ, h⟩ := hmatt hN x
              rw [← h]
              exact (le_abs_self _).trans (hγC x ξ)
            obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ → ↥X → ↥Ξ → ℝ, ∀ η s x ξ, b η s x ξ = |s| + η + (m x - γ x ξ) :=
              ⟨_, fun _ _ _ _ => rfl⟩
            have hbpos : ∀ η s x ξ, 0 < η → |s| + η ≤ b η s x ξ := by
              intro η s x ξ _
              rw [hb]; linarith [hmle x ξ]
            have hbpos' : ∀ η s x ξ, 0 < η → 0 < b η s x ξ := by
              intro η s x ξ hη
              linarith [hbpos η s x ξ hη, abs_nonneg s]
            have hbub : ∀ η s x ξ, b η s x ξ ≤ |s| + η + 2 * C0 := by
              intro η s x ξ
              rw [hb]
              linarith [hmC ⟨ξ⟩ x, (abs_le.mp (hγC x ξ)).1]
            have hbc : ∀ η, Continuous (fun p : (ℝ × ↥X) × ↥Ξ => b η p.1.1 p.1.2 p.2) := by
              intro η
              simp only [hb]
              have h1 : Continuous (fun p : (ℝ × ↥X) × ↥Ξ => γ p.1.2 p.2) :=
                hγ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
              have h2 : Continuous (fun p : (ℝ × ↥X) × ↥Ξ => m p.1.2) :=
                hmcont.comp (continuous_snd.comp continuous_fst)
              have h3 : Continuous (fun p : (ℝ × ↥X) × ↥Ξ => |p.1.1|) :=
                (continuous_fst.comp continuous_fst).abs
              exact (h3.add continuous_const).add (h2.sub h1)
            have hlogbc : ∀ η, 0 < η → Continuous (fun p : (ℝ × ↥X) × ↥Ξ => Real.log (b η p.1.1 p.1.2 p.2)) :=
              fun η hη => (hbc η).log fun p => (hbpos' _ _ _ _ hη).ne'
            have hbinvc : ∀ η, 0 < η → Continuous (fun p : (ℝ × ↥X) × ↥Ξ => (b η p.1.1 p.1.2 p.2)⁻¹) :=
              fun η hη => (hbc η).inv₀ fun p => (hbpos' _ _ _ _ hη).ne'
            have hbx : ∀ η s x, Continuous (fun ξ => b η s x ξ) := fun η s x =>
              (hbc η).comp (Continuous.prodMk_right ((s, x) : ℝ × ↥X))
            have hlogbx : ∀ η s x, 0 < η → Continuous (fun ξ => Real.log (b η s x ξ)) := fun η s x hη =>
              (hlogbc η hη).comp (Continuous.prodMk_right ((s, x) : ℝ × ↥X))
            have hbinvx : ∀ η s x, 0 < η → Continuous (fun ξ => (b η s x ξ)⁻¹) := fun η s x hη =>
              (hbinvc η hη).comp (Continuous.prodMk_right ((s, x) : ℝ × ↥X))
            obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ → ↥X → DROOptimal.Continuous.Dist Ξ → ℝ, ∀ η s x q,
                L η s x q = ∫ ξ, Real.log (b η s x ξ) ∂(q : MeasureTheory.Measure ↥Ξ) := ⟨_, fun _ _ _ _ => rfl⟩
            obtain ⟨Z, hZ⟩ : ∃ Z : ℝ → ℝ → ↥X → DROOptimal.Continuous.Dist Ξ → ℝ, ∀ η s x q,
                Z η s x q = ∫ ξ, (b η s x ξ)⁻¹ ∂(q : MeasureTheory.Measure ↥Ξ) := ⟨_, fun _ _ _ _ => rfl⟩
            have hLc : ∀ η, 0 < η → Continuous (fun p : (ℝ × ↥X) × DROOptimal.Continuous.Dist Ξ => L η p.1.1 p.1.2 p.2) := by
              intro η hη
              simp only [hL]
              exact hjoint (ℝ × ↥X) (fun y ξ => Real.log (b η y.1 y.2 ξ)) (hlogbc η hη)
            have hZc : ∀ η, 0 < η → Continuous (fun p : (ℝ × ↥X) × DROOptimal.Continuous.Dist Ξ => Z η p.1.1 p.1.2 p.2) := by
              intro η hη
              simp only [hZ]
              exact hjoint (ℝ × ↥X) (fun y ξ => (b η y.1 y.2 ξ)⁻¹) (hbinvc η hη)
            have hcostb : ∀ η s x (P : DROOptimal.Continuous.Dist Ξ),
                ∫ ξ, b η s x ξ ∂(P : MeasureTheory.Measure ↥Ξ) = |s| + η + m x - DROOptimal.Continuous.cost γ x P := by
              intro η s x P
              have e : ∀ ξ, b η s x ξ = (|s| + η + m x) - γ x ξ := fun ξ => by rw [hb]; ring
              simp only [e]
              rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const _) (hintg _ (hγx x) P)]
              simp [DROOptimal.Continuous.cost]
            have hexplog : ∀ η s x ξ, 0 < η → Real.exp (Real.log (b η s x ξ)) = b η s x ξ :=
              fun η s x ξ hη => Real.exp_log (hbpos' η s x ξ hη)
            have hcostlt : ∀ η s x (P : DROOptimal.Continuous.Dist Ξ), 0 < η →
                0 < |s| + η + m x - DROOptimal.Continuous.cost γ x P := by
              intro η s x P hη
              rw [← hcostb η s x P]
              have h1 : ∫ _ξ, η ∂(P : MeasureTheory.Measure ↥Ξ) ≤ ∫ ξ, b η s x ξ ∂(P : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.integral_mono (MeasureTheory.integrable_const _) (hintg _ (hbx η s x) P)
                  (fun ξ => by show η ≤ b η s x ξ; linarith [hbpos η s x ξ hη, abs_nonneg s])
              have h2 : ∫ _ξ, η ∂(P : MeasureTheory.Measure ↥Ξ) = η := by simp
              linarith
            have hLub : ∀ η s x (q : DROOptimal.Continuous.Dist Ξ), 0 < η →
                Real.exp (L η s x q) ≤ |s| + η + 2 * C0 := by
              intro η s x q hη
              obtain ⟨ξ0⟩ := hne q
              have hB : 0 < |s| + η + 2 * C0 := (hbpos' η s x ξ0 hη).trans_le (hbub η s x ξ0)
              rw [← Real.le_log_iff_exp_le hB, hL]
              have h1 : ∫ ξ, Real.log (b η s x ξ) ∂(q : MeasureTheory.Measure ↥Ξ) ≤
                  ∫ _ξ, Real.log (|s| + η + 2 * C0) ∂(q : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.integral_mono (hintg _ (hlogbx η s x hη) q) (MeasureTheory.integrable_const _)
                  (fun ξ => Real.log_le_log (hbpos' η s x ξ hη) (hbub η s x ξ))
              simpa using h1
            have hZub : ∀ η s x (q : DROOptimal.Continuous.Dist Ξ), 0 < η →
                Z η s x q ≤ (|s| + η)⁻¹ := by
              intro η s x q hη
              have hs : 0 < |s| + η := by linarith [abs_nonneg s]
              rw [hZ]
              have h1 : ∫ ξ, (b η s x ξ)⁻¹ ∂(q : MeasureTheory.Measure ↥Ξ) ≤
                  ∫ _ξ, (|s| + η)⁻¹ ∂(q : MeasureTheory.Measure ↥Ξ) :=
                MeasureTheory.integral_mono (hintg _ (hbinvx η s x hη) q) (MeasureTheory.integrable_const _)
                  (fun ξ => inv_anti₀ hs (hbpos η s x ξ hη))
              simpa using h1
            have hZnn : ∀ η s x (q : DROOptimal.Continuous.Dist Ξ), 0 < η → 0 ≤ Z η s x q := by
              intro η s x q hη
              rw [hZ]
              exact MeasureTheory.integral_nonneg fun ξ => (inv_pos.mpr (hbpos' η s x ξ hη)).le
            -- Weak duality.
            have hweak : ∀ η s x (r0 : ℝ) (q P : DROOptimal.Continuous.Dist Ξ), 0 < η → 0 ≤ r0 →
                DROOptimal.Continuous.relEnt q P ≤ ENNReal.ofReal r0 →
                DROOptimal.Continuous.cost γ x P ≤ |s| + η + m x - Real.exp (-r0) * Real.exp (L η s x q) := by
              intro η s x r0 q P hη hr0 h
              have h1 := hDV (fun ξ => Real.log (b η s x ξ)) (hlogbx η s x hη) r0 hr0 q P h
              simp only [hexplog η s x _ hη] at h1
              rw [hcostb, ← hL] at h1
              have h2 : L η s x q - r0 ≤ Real.log (|s| + η + m x - DROOptimal.Continuous.cost γ x P) := by linarith
              rw [Real.le_log_iff_exp_le (hcostlt η s x P hη)] at h2
              rw [← Real.exp_add, show -r0 + L η s x q = L η s x q - r0 by ring]
              linarith
            -- Primal construction.
            have hprimal : ∀ η s x (r0 : ℝ) (q : DROOptimal.Continuous.Dist Ξ), 0 < η → 0 ≤ r0 →
                Real.exp (-r0) * Real.exp (L η s x q) * Z η s x q ≤ 1 →
                ∃ P : DROOptimal.Continuous.Dist Ξ, DROOptimal.Continuous.relEnt q P ≤ ENNReal.ofReal r0 ∧
                  DROOptimal.Continuous.cost γ x P = m x +
                    (Real.exp (-r0) * Real.exp (L η s x q) * Z η s x q * (|s| + η) - Real.exp (-r0) * Real.exp (L η s x q)) := by
              intro η s x r0 q hη hr0 h1
              set lam := Real.exp (-r0) * Real.exp (L η s x q) with hlam
              have hlampos : 0 < lam := mul_pos (Real.exp_pos _) (Real.exp_pos _)
              obtain ⟨ξs, hξs⟩ := hmatt (hne q) x
              have hkc : Continuous (fun ξ => lam * (b η s x ξ)⁻¹) := continuous_const.mul (hbinvx η s x hη)
              have hkpos : ∀ ξ, 0 < lam * (b η s x ξ)⁻¹ := fun ξ => mul_pos hlampos (inv_pos.mpr (hbpos' η s x ξ hη))
              have hkm : Measurable (fun ξ => ENNReal.ofReal (lam * (b η s x ξ)⁻¹)) := hkc.measurable.ennreal_ofReal
              set μ1 := (q : MeasureTheory.Measure ↥Ξ).withDensity (fun ξ => ENNReal.ofReal (lam * (b η s x ξ)⁻¹)) with hμ1
              have hkint : ∫ ξ, lam * (b η s x ξ)⁻¹ ∂(q : MeasureTheory.Measure ↥Ξ) = lam * Z η s x q := by
                rw [MeasureTheory.integral_const_mul, hZ]
              have hmass : μ1 Set.univ = ENNReal.ofReal (lam * Z η s x q) := by
                rw [hμ1, MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ,
                  ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hintg _ hkc q)
                    (Filter.Eventually.of_forall fun ξ => (hkpos ξ).le), hkint]
              have hfin1 : MeasureTheory.IsFiniteMeasure μ1 := ⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩
              have hlZ : 0 ≤ lam * Z η s x q := mul_nonneg hlampos.le (hZnn η s x q hη)
              let Pm : MeasureTheory.Measure ↥Ξ := μ1 + ENNReal.ofReal (1 - lam * Z η s x q) • MeasureTheory.Measure.dirac ξs
              have hPm : MeasureTheory.IsProbabilityMeasure Pm := ⟨by
                show (μ1 + ENNReal.ofReal (1 - lam * Z η s x q) • MeasureTheory.Measure.dirac ξs) Set.univ = 1
                rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply, hmass, MeasureTheory.measure_univ,
                  smul_eq_mul, mul_one, ← ENNReal.ofReal_add hlZ (by linarith)]
                simp⟩
              refine ⟨⟨Pm, hPm⟩, ?_, ?_⟩
              · refine (hKL q ⟨Pm, hPm⟩ _ hkc hkpos ?_).trans ?_
                · show μ1 ≤ Pm
                  exact MeasureTheory.Measure.le_add_right le_rfl
                · apply ENNReal.ofReal_le_ofReal
                  have e : ∀ ξ, -Real.log (lam * (b η s x ξ)⁻¹) = Real.log (b η s x ξ) - Real.log lam := by
                    intro ξ
                    rw [Real.log_mul hlampos.ne' (inv_pos.mpr (hbpos' η s x ξ hη)).ne', Real.log_inv]
                    ring
                  simp only [e]
                  rw [MeasureTheory.integral_sub (hintg _ (hlogbx η s x hη) q) (MeasureTheory.integrable_const _), ← hL]
                  have e2 : Real.log lam = -r0 + L η s x q := by
                    rw [hlam, ← Real.exp_add, Real.log_exp]
                  simp [e2]
              · show ∫ ξ, γ x ξ ∂(μ1 + ENNReal.ofReal (1 - lam * Z η s x q) • MeasureTheory.Measure.dirac ξs) = _
                have hi1 : MeasureTheory.Integrable (fun ξ => γ x ξ) μ1 :=
                  (BoundedContinuousFunction.mkOfCompact (⟨γ x, hγx x⟩ : C(↥Ξ, ℝ))).integrable _
                have hi2 : MeasureTheory.Integrable (fun ξ => γ x ξ) (ENNReal.ofReal (1 - lam * Z η s x q) • MeasureTheory.Measure.dirac ξs) :=
                  (MeasureTheory.integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
                rw [MeasureTheory.integral_add_measure hi1 hi2, MeasureTheory.integral_smul_measure,
                  MeasureTheory.integral_dirac, hξs, ENNReal.toReal_ofReal (by linarith)]
                have e1 : ∫ ξ, γ x ξ ∂μ1 = lam * ((|s| + η + m x) * Z η s x q - 1) := by
                  rw [hμ1, integral_withDensity_eq_integral_toReal_smul hkm (Filter.Eventually.of_forall fun ξ => ENNReal.ofReal_lt_top)]
                  have e : ∀ ξ, (ENNReal.ofReal (lam * (b η s x ξ)⁻¹)).toReal • γ x ξ =
                      lam * ((|s| + η + m x) * (b η s x ξ)⁻¹ - 1) := by
                    intro ξ
                    rw [ENNReal.toReal_ofReal (hkpos ξ).le, smul_eq_mul]
                    have h3 : γ x ξ = (|s| + η + m x) - b η s x ξ := by rw [hb]; ring
                    have h4 : (b η s x ξ)⁻¹ * b η s x ξ = 1 := inv_mul_cancel₀ (hbpos' η s x ξ hη).ne'
                    rw [h3]
                    linear_combination (-lam) * h4
                  simp only [e]
                  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub
                    ((hintg _ (hbinvx η s x hη) q).const_mul _) (MeasureTheory.integrable_const _),
                    MeasureTheory.integral_const_mul, ← hZ]
                  simp
                rw [e1, smul_eq_mul]
                ring
            -- Strong duality, up to `η`, with a uniformly bounded dual variable.
            have hstrong : ∀ η r1 : ℝ, 0 < η → 0 < r1 → ∃ S : ℝ, 0 ≤ S ∧ ∀ r0 : ℝ, r1 ≤ r0 →
                ∀ (x : ↥X) (q : DROOptimal.Continuous.Dist Ξ), ∃ s ∈ Set.Icc 0 S,
                  ∃ P : DROOptimal.Continuous.Dist Ξ, DROOptimal.Continuous.relEnt q P ≤ ENNReal.ofReal r0 ∧
                    |s| + η + m x - Real.exp (-r0) * Real.exp (L η s x q) - η ≤ DROOptimal.Continuous.cost γ x P := by
              intro η r1 hη hr1
              have he1 : Real.exp (-r1) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
              refine ⟨2 * |C0| / (1 - Real.exp (-r1)), div_nonneg (by positivity) (by linarith), ?_⟩
              intro r0 hr0 x q
              set S := 2 * |C0| / (1 - Real.exp (-r1)) with hS
              have hS0 : 0 ≤ S := div_nonneg (by positivity) (by linarith)
              have hSe : S * (1 - Real.exp (-r1)) = 2 * |C0| := div_mul_cancel₀ _ (by linarith)
              have hr00 : 0 ≤ r0 := by linarith
              have hC0 : 0 ≤ C0 := by
                obtain ⟨ξ0⟩ := hne q
                exact (abs_nonneg _).trans (hγC x ξ0)
              rw [abs_of_nonneg hC0] at hSe
              have hsc : Continuous (fun s : ℝ => Real.exp (-r0) * Real.exp (L η s x q) * Z η s x q) := by
                have hp : Continuous (fun s : ℝ => ((s, x), q) : ℝ → (ℝ × ↥X) × DROOptimal.Continuous.Dist Ξ) := by fun_prop
                have c1 : Continuous (fun s : ℝ => L η s x q) := (hLc η hη).comp hp
                have c2 : Continuous (fun s : ℝ => Z η s x q) := (hZc η hη).comp hp
                exact (continuous_const.mul (Real.continuous_exp.comp c1)).mul c2
              by_cases h0 : Real.exp (-r0) * Real.exp (L η 0 x q) * Z η 0 x q ≤ 1
              · obtain ⟨P, hP, hcP⟩ := hprimal η 0 x r0 q hη hr00 h0
                refine ⟨0, ⟨le_rfl, hS0⟩, P, hP, ?_⟩
                rw [hcP, abs_zero]
                have : 0 ≤ Real.exp (-r0) * Real.exp (L η 0 x q) * Z η 0 x q * (0 + η) := by
                  have := hZnn η 0 x q hη
                  positivity
                linarith
              · have hSle : Real.exp (-r0) * Real.exp (L η S x q) * Z η S x q ≤ 1 := by
                  have a1 := hLub η S x q hη
                  have a2 := hZub η S x q hη
                  rw [abs_of_nonneg hS0] at a1 a2
                  have a3 : Real.exp (-r0) ≤ Real.exp (-r1) := Real.exp_le_exp.mpr (by linarith)
                  have hSη : 0 < S + η := by linarith
                  have a4 : Real.exp (-r0) * Real.exp (L η S x q) ≤ S + η := by
                    calc _ ≤ Real.exp (-r1) * (S + η + 2 * C0) := by gcongr
                      _ ≤ S + η := by
                        have : 0 ≤ η * (1 - Real.exp (-r1)) := mul_nonneg hη.le (by linarith)
                        have : 0 ≤ 2 * C0 * (1 - Real.exp (-r1)) := mul_nonneg (by linarith) (by linarith)
                        nlinarith
                  calc _ ≤ (S + η) * (S + η)⁻¹ := by
                        have := hZnn η S x q hη
                        gcongr
                    _ = 1 := mul_inv_cancel₀ hSη.ne'
                obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc' hS0 hsc.continuousOn ⟨hSle, (not_le.mp h0).le⟩
                simp only at hs1
                obtain ⟨P, hP, hcP⟩ := hprimal η s x r0 q hη hr00 hs1.le
                refine ⟨s, hs, P, hP, ?_⟩
                rw [hcP, hs1]
                linarith
            have hdrle : ∀ η s x (q : DROOptimal.Continuous.Dist Ξ), 0 < η →
                DROOptimal.Continuous.drPredictor γ r x q ≤ |s| + η + m x - Real.exp (-r) * Real.exp (L η s x q) := by
              intro η s x q hη
              unfold DROOptimal.Continuous.drPredictor
              refine csSup_le ⟨_, q, ?_, rfl⟩ ?_
              · show DROOptimal.Continuous.relEnt q q ≤ _
                unfold DROOptimal.Continuous.relEnt
                rw [InformationTheory.klDiv_self]
                exact bot_le
              · rintro _ ⟨P, hP, rfl⟩
                exact hweak η s x r q P hη hr hP
            -- Proposition 6.
            have hcont : DROOptimal.Continuous.IsPredictor (DROOptimal.Continuous.drPredictor γ r) := by
              unfold DROOptimal.Continuous.IsPredictor
              apply continuous_of_uniform_approx_of_continuous
              intro u hu
              obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
              obtain ⟨S, hS0, hS⟩ := hstrong (ε / 2) r (half_pos hε) hpos
              have hη := half_pos hε
              let H : (↥X × DROOptimal.Continuous.Dist Ξ) → ℝ → ℝ := fun p s =>
                |s| + ε / 2 + m p.1 - Real.exp (-r) * Real.exp (L (ε / 2) s p.1 p.2)
              have hHc : Continuous (fun p : (↥X × DROOptimal.Continuous.Dist Ξ) × ℝ => H p.1 p.2) := by
                have hp : Continuous (fun p : (↥X × DROOptimal.Continuous.Dist Ξ) × ℝ =>
                    (((p.2, p.1.1), p.1.2) : (ℝ × ↥X) × DROOptimal.Continuous.Dist Ξ)) := by fun_prop
                have c1 : Continuous (fun p : (↥X × DROOptimal.Continuous.Dist Ξ) × ℝ => L (ε / 2) p.2 p.1.1 p.1.2) :=
                  (hLc _ hη).comp hp
                have c2 : Continuous (fun p : (↥X × DROOptimal.Continuous.Dist Ξ) × ℝ => m p.1.1) :=
                  hmcont.comp (continuous_fst.comp continuous_fst)
                exact ((continuous_snd.abs.add continuous_const).add c2).sub
                  (continuous_const.mul (Real.continuous_exp.comp c1))
              refine ⟨fun p => sInf (H p '' Set.Icc 0 S), IsCompact.continuous_sInf isCompact_Icc hHc, ?_⟩
              rintro ⟨x, q⟩
              apply hεu
              have hlb : ∀ y ∈ H (x, q) '' Set.Icc 0 S, DROOptimal.Continuous.drPredictor γ r x q ≤ y := by
                rintro _ ⟨s, _, rfl⟩
                exact hdrle (ε / 2) s x q hη
              have h1 : DROOptimal.Continuous.drPredictor γ r x q ≤ sInf (H (x, q) '' Set.Icc 0 S) :=
                le_csInf ((Set.nonempty_Icc.mpr hS0).image _) hlb
              obtain ⟨s, hs, P, hP, hcP⟩ := hS r le_rfl x q
              have h2 : sInf (H (x, q) '' Set.Icc 0 S) ≤ H (x, q) s := csInf_le ⟨_, hlb⟩ ⟨s, hs, rfl⟩
              have h3 := hle x q P hP
              have h4 : H (x, q) s = |s| + ε / 2 + m x - Real.exp (-r) * Real.exp (L (ε / 2) s x q) := rfl
              rw [Real.dist_eq, abs_lt]
              constructor <;> dsimp only <;> linarith
            have hstrict : ∀ (x : ↥X) (q : DROOptimal.Continuous.Dist Ξ) (w : ℝ),
                w < DROOptimal.Continuous.drPredictor γ r x q → ∃ r0 : ℝ, 0 ≤ r0 ∧ r0 < r ∧
                  ∃ P : DROOptimal.Continuous.Dist Ξ, DROOptimal.Continuous.relEnt q P ≤ ENNReal.ofReal r0 ∧
                    w < DROOptimal.Continuous.cost γ x P := by
              intro x q w hw
              obtain ⟨η, hη, hηw⟩ : ∃ η : ℝ, 0 < η ∧ w + 3 * η = DROOptimal.Continuous.drPredictor γ r x q :=
                ⟨(DROOptimal.Continuous.drPredictor γ r x q - w) / 3, by linarith, by ring⟩
              obtain ⟨S, hS0, hS⟩ := hstrong η (r / 2) hη (half_pos hpos)
              have hlim : Filter.Tendsto (fun r0 : ℝ => (Real.exp (-r0) - Real.exp (-r)) * (S + η + 2 * C0)) (nhds r) (nhds 0) := by
                have : Continuous (fun r0 : ℝ => (Real.exp (-r0) - Real.exp (-r)) * (S + η + 2 * C0)) := by fun_prop
                have h := this.tendsto r
                simpa using h
              have hev : ∀ᶠ r0 in nhdsWithin r (Set.Iio r), (Real.exp (-r0) - Real.exp (-r)) * (S + η + 2 * C0) < η ∧ r / 2 < r0 ∧ r0 < r := by
                refine Filter.Eventually.and (nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds hη)))
                  (Filter.Eventually.and (nhdsWithin_le_nhds (lt_mem_nhds (by linarith))) self_mem_nhdsWithin)
              obtain ⟨r0, h1, h2, h3⟩ := hev.exists
              obtain ⟨s, hs, P, hP, hcP⟩ := hS r0 h2.le x q
              refine ⟨r0, by linarith, h3, P, hP, ?_⟩
              have a1 := hLub η s x q hη
              have a2 := hdrle η s x q hη
              rw [abs_of_nonneg hs.1] at a1
              have a3 : 0 ≤ Real.exp (-r0) - Real.exp (-r) := sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
              have a4 : (Real.exp (-r0) - Real.exp (-r)) * Real.exp (L η s x q) ≤
                  (Real.exp (-r0) - Real.exp (-r)) * (S + η + 2 * C0) :=
                mul_le_mul_of_nonneg_left (a1.trans (by linarith [hs.2])) a3
              rw [sub_mul] at a4
              linarith
            -- Uniform rate, via a finite cover of the dual functions and the Chernoff bound.
            have hdecay : ∀ ε : ℝ, 0 < ε → ∀ P : DROOptimal.Continuous.Dist Ξ,
                DROOptimal.Continuous.DecaysAtRate (ENNReal.ofReal r)
                  (fun T => DROOptimal.Continuous.sampleProb P T (fun P' => P' ∈ disappointSet γ
                    (fun x P' => DROOptimal.Continuous.drPredictor γ r x P' + ε) xhat_r P)) := by
              intro ε hε P r' hr'
              have hr'r : (r' : ℝ) < r := by
                have := ENNReal.toReal_lt_of_lt_ofReal hr'
                simpa using this
              have hη := half_pos hε
              obtain ⟨S, hS0, hS⟩ := hstrong (ε / 2) r hη hpos
              let G : C(ℝ × ↥X, C(↥Ξ, ℝ)) := ContinuousMap.curry ⟨fun p : (ℝ × ↥X) × ↥Ξ => Real.log (b (ε / 2) p.1.1 p.1.2 p.2), hlogbc _ hη⟩
              have hGap : ∀ s x ξ, G (s, x) ξ = Real.log (b (ε / 2) s x ξ) := fun _ _ _ => rfl
              have hK : IsCompact (G '' (Set.Icc 0 S ×ˢ Set.univ)) := (isCompact_Icc.prod isCompact_univ).image G.continuous
              obtain ⟨τ, hτ, hτr⟩ : ∃ τ : ℝ, 0 < τ ∧ (r' : ℝ) + 4 * τ = r := ⟨(r - r') / 4, by linarith, by ring⟩
              obtain ⟨t, _, htf, htc⟩ := hK.finite_cover_balls hτ
              have hD : ∀ q ∈ disappointSet γ (fun x P' => DROOptimal.Continuous.drPredictor γ r x P' + ε) xhat_r P,
                  ∃ f ∈ htf.toFinset, (r' : ℝ) + 2 * τ ≤ ∫ ξ, f ξ ∂(q : MeasureTheory.Measure ↥Ξ) -
                    Real.log (∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ)) := by
                intro q hq
                simp only [disappointSet, Set.mem_ofPred_eq] at hq
                obtain ⟨s, hs, P1, hP1, hcP⟩ := hS r le_rfl (xhat_r q) q
                have h1 := hle (xhat_r q) q P1 hP1
                have h2 : |s| + ε / 2 + m (xhat_r q) - DROOptimal.Continuous.cost γ (xhat_r q) P <
                    Real.exp (L (ε / 2) s (xhat_r q) q - r) := by
                  rw [show L (ε / 2) s (xhat_r q) q - r = -r + L (ε / 2) s (xhat_r q) q by ring, Real.exp_add]
                  linarith
                rw [← Real.log_lt_iff_lt_exp (hcostlt _ s _ P hη), ← hcostb, hL] at h2
                have hmem : G (s, xhat_r q) ∈ G '' (Set.Icc 0 S ×ˢ Set.univ) := ⟨(s, xhat_r q), ⟨hs, Set.mem_univ _⟩, rfl⟩
                obtain ⟨f, hft, hfb⟩ := Set.mem_iUnion₂.mp (htc hmem)
                have hfb' : ∀ ξ, |Real.log (b (ε / 2) s (xhat_r q) ξ) - f ξ| ≤ τ := by
                  intro ξ
                  rw [← hGap, ← Real.dist_eq]
                  exact (ContinuousMap.dist_apply_le_dist ξ).trans (Metric.mem_ball.mp hfb).le
                refine ⟨f, htf.mem_toFinset.mpr hft, ?_⟩
                have i1 : ∫ ξ, Real.log (b (ε / 2) s (xhat_r q) ξ) ∂(q : MeasureTheory.Measure ↥Ξ) ≤
                    ∫ ξ, f ξ ∂(q : MeasureTheory.Measure ↥Ξ) + τ := by
                  have := MeasureTheory.integral_mono (hintg _ (hlogbx _ s (xhat_r q) hη) q)
                    ((hintg _ f.continuous q).add (MeasureTheory.integrable_const τ))
                    (fun ξ => by show _ ≤ f ξ + τ; linarith [(abs_le.mp (hfb' ξ)).2])
                  rw [MeasureTheory.integral_add' (hintg _ f.continuous q) (MeasureTheory.integrable_const τ)] at this
                  simpa using this
                have i2 : ∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ) ≤
                    Real.exp τ * ∫ ξ, b (ε / 2) s (xhat_r q) ξ ∂(P : MeasureTheory.Measure ↥Ξ) := by
                  rw [← MeasureTheory.integral_const_mul]
                  refine MeasureTheory.integral_mono (hintg _ (Real.continuous_exp.comp f.continuous) P)
                    ((hintg _ (hbx _ s (xhat_r q)) P).const_mul _) (fun ξ => ?_)
                  show Real.exp (f ξ) ≤ Real.exp τ * b (ε / 2) s (xhat_r q) ξ
                  rw [← hexplog _ s (xhat_r q) ξ hη, ← Real.exp_add]
                  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hfb' ξ)).1])
                have hposf : 0 < ∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ) :=
                  MeasureTheory.integral_exp_pos (hintg _ (Real.continuous_exp.comp f.continuous) P)
                have hposb : 0 < ∫ ξ, b (ε / 2) s (xhat_r q) ξ ∂(P : MeasureTheory.Measure ↥Ξ) := by
                  rw [hcostb]; exact hcostlt _ s _ P hη
                have i3 := Real.log_le_log hposf i2
                rw [Real.log_mul (Real.exp_pos _).ne' hposb.ne', Real.log_exp] at i3
                linarith
              have hN : ∀ᶠ T : ℕ in Filter.atTop, (htf.toFinset.card : ℝ) * Real.exp (-(2 * τ * T)) ≤ 1 := by
                have : Filter.Tendsto (fun T : ℕ => (htf.toFinset.card : ℝ) * Real.exp (-(2 * τ * T))) Filter.atTop (nhds ((htf.toFinset.card : ℝ) * 0)) := by
                  refine Filter.Tendsto.const_mul _ (Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_)
                  exact Filter.Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
                rw [mul_zero] at this
                filter_upwards [this.eventually (gt_mem_nhds one_pos)] with T hT using hT.le
              filter_upwards [hN, Filter.eventually_gt_atTop 0] with T hT1 hT0
              unfold DROOptimal.Continuous.sampleProb
              rw [dif_pos hT0]
              calc MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) _
                  ≤ MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ)) (⋃ f ∈ htf.toFinset,
                    {ω | (r' : ℝ) + 2 * τ ≤ ∫ ξ, f ξ ∂(DROOptimal.Continuous.empirical ω hT0 : MeasureTheory.Measure ↥Ξ) -
                    Real.log (∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ))}) := by
                      apply MeasureTheory.measure_mono
                      intro ω hω
                      obtain ⟨f, hf, hfω⟩ := hD _ hω
                      exact Set.mem_iUnion₂.mpr ⟨f, hf, hfω⟩
                _ ≤ ∑ f ∈ htf.toFinset, MeasureTheory.Measure.pi (fun _ : Fin T => (P : MeasureTheory.Measure ↥Ξ))
                    {ω | (r' : ℝ) + 2 * τ ≤ ∫ ξ, f ξ ∂(DROOptimal.Continuous.empirical ω hT0 : MeasureTheory.Measure ↥Ξ) -
                    Real.log (∫ ξ, Real.exp (f ξ) ∂(P : MeasureTheory.Measure ↥Ξ))} := MeasureTheory.measure_biUnion_finset_le _ _
                _ ≤ ∑ f ∈ htf.toFinset, ENNReal.ofReal (Real.exp (-(((r' : ℝ) + 2 * τ) * T))) :=
                    Finset.sum_le_sum fun f _ => hChern f f.continuous P T hT0 _
                _ = ENNReal.ofReal ((htf.toFinset.card : ℝ) * Real.exp (-(((r' : ℝ) + 2 * τ) * T))) := by
                    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
                _ ≤ _ := by
                    apply ENNReal.ofReal_le_ofReal
                    rw [show -(((r' : ℝ) + 2 * τ) * T) = -(2 * τ * T) + -((r' : ℝ) * T) by ring, Real.exp_add, ← mul_assoc]
                    exact (mul_le_mul_of_nonneg_right hT1 (Real.exp_pos _).le).trans_eq (one_mul _)
            -- Optimality.
            have hopt : ∀ (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
                (xhat : DROOptimal.Continuous.Dist Ξ → ↥X), Feasible6 γ r chat xhat →
                ∀ P', DROOptimal.Continuous.drPredictor γ r (xhat P') P' ≤ chat (xhat P') P' := by
              intro chat xhat hF P'
              by_contra hcon
              rw [not_le] at hcon
              obtain ⟨⟨hcc, hqc, _⟩, hdec⟩ := hF
              set x0 := xhat P' with hx0
              obtain ⟨Δ, hΔ, hΔe⟩ : ∃ Δ : ℝ, 0 < Δ ∧ chat x0 P' + 4 * Δ = DROOptimal.Continuous.drPredictor γ r x0 P' :=
                ⟨(DROOptimal.Continuous.drPredictor γ r x0 P' - chat x0 P') / 4, by linarith, by ring⟩
              have e1 : ∀ᶠ p in nhds (x0, P'), chat p.1 p.2 < chat x0 P' + Δ :=
                (hcc.tendsto (x0, P')).eventually (gt_mem_nhds (by show chat x0 P' < _; linarith))
              have e2 : ∀ᶠ q in nhds P', chat x0 P' + 3 * Δ < DROOptimal.Continuous.drPredictor γ r x0 q := by
                have hc : Continuous (fun q : DROOptimal.Continuous.Dist Ξ => DROOptimal.Continuous.drPredictor γ r x0 q) :=
                  hcont.comp (Continuous.prodMk_right x0)
                exact (hc.tendsto P').eventually (lt_mem_nhds (by linarith))
              have e3 : ∀ᶠ x in nhds x0, ∀ P : DROOptimal.Continuous.Dist Ξ,
                  DROOptimal.Continuous.cost γ x0 P - Δ ≤ DROOptimal.Continuous.cost γ x P := by
                let G : C(↥X, C(↥Ξ, ℝ)) := ContinuousMap.curry ⟨fun p : ↥X × ↥Ξ => γ p.1 p.2, hγ⟩
                have h1 : ∀ᶠ x in nhds x0, dist (G x) (G x0) < Δ := (G.continuous.tendsto x0) (Metric.ball_mem_nhds _ hΔ)
                filter_upwards [h1] with x hx P
                have h2 : ∀ ξ, γ x0 ξ - Δ ≤ γ x ξ := by
                  intro ξ
                  have h3 : dist (γ x ξ) (γ x0 ξ) ≤ dist (G x) (G x0) := ContinuousMap.dist_apply_le_dist (f := G x) (g := G x0) ξ
                  rw [Real.dist_eq] at h3
                  linarith [(abs_le.mp (h3.trans hx.le)).1]
                have h4 := MeasureTheory.integral_mono ((hintg _ (hγx x0) P).sub (MeasureTheory.integrable_const Δ)) (hintg _ (hγx x) P) h2
                rw [MeasureTheory.integral_sub' (hintg _ (hγx x0) P) (MeasureTheory.integrable_const Δ)] at h4
                simpa [DROOptimal.Continuous.cost] using h4
              rw [nhds_prod_eq] at e1
              obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.mp e1
              obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hpa.and e3)
              obtain ⟨V, hVo, ⟨q0, hq0⟩, hVU, hVd⟩ := hqc P' (ρ / 2) (half_pos hρ) _ (hpb.and e2)
              obtain ⟨r0, hr00, hr0r, P, hP, hcP⟩ := hstrict x0 q0 _ (hVU hq0).2
              have hsub : ∀ q ∈ V, q ∈ disappointSet γ chat xhat P := by
                intro q hq
                have hxq : xhat q ∈ Metric.ball x0 ρ := by
                  rw [Metric.mem_ball, dist_comm]
                  exact (hVd q hq).trans_lt (half_lt_self hρ)
                have h1 := hball hxq
                have h2 := hpab h1.1 (hVU hq).1
                have h3 := h1.2 P
                show chat (xhat q) q < DROOptimal.Continuous.cost γ (xhat q) P
                simp only at h2
                linarith
              obtain ⟨s, hs1, hs2⟩ := exists_between hr0r
              obtain ⟨s', hs'1, hs'2⟩ := exists_between hs2
              have hs'0 : 0 ≤ s' := by linarith
              have hd := hdec P (Real.toNNReal s') (by
                exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hs'2)
              have hl := hSanov q0 P V (hVo.mem_nhds hq0) r0 s hr00 hs1 hP
              obtain ⟨T, hT1, hT2, hT0⟩ := (hd.and (hl.and (Filter.eventually_gt_atTop 0))).exists
              have hT0' : (0:ℝ) < T := by exact_mod_cast hT0
              have hmono : DROOptimal.Continuous.sampleProb P T (fun q => q ∈ V) ≤
                  DROOptimal.Continuous.sampleProb P T (fun P' => P' ∈ disappointSet γ chat xhat P) := by
                unfold DROOptimal.Continuous.sampleProb
                rw [dif_pos hT0, dif_pos hT0]
                exact MeasureTheory.measure_mono fun ω hω => hsub _ hω
              have hfinal := (hT2.trans hmono).trans hT1
              rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp] at hfinal
              have : (s:ℝ) * T < s' * T := mul_lt_mul_of_pos_right hs'1 hT0'
              rw [Real.coe_toNNReal s' hs'0] at hfinal
              linarith
            refine ⟨fun ε hε => ⟨⟨?_, hquasi, ?_⟩, hdecay ε hε⟩, fun _ chat xhat hF P' => ?_⟩
            · exact hcont.add continuous_const
            · intro P'
              refine ⟨Set.mem_univ _, fun y _ => ?_⟩
              have := (hargmin P').2 y (Set.mem_univ _)
              simpa using this
            · exact le_trans ((hargmin P').2 (xhat P') (Set.mem_univ _)) (hopt chat xhat hF P')
