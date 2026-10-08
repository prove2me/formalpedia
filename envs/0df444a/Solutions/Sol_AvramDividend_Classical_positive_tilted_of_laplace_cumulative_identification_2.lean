-- Prove2me | solution 2 for AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:26:07.12538+00:00
-- url     : https://prove2.me/submissions/f44f59ec-073c-40b5-bde6-35fa65534d34

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem solution
    (β : Measure ℝ) (φ b : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hatom : 0 < β {0})
    (W : ℝ → ℝ)
    (htiltcont : ContinuousOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (htiltnonneg : ∀ x : ℝ, 0 < x → 0 ≤ Real.exp (-φ * x) * W x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  set F : ℝ → ℝ := fun x => Real.exp (-φ * x) * W x with hF
  set G : ℝ → ℝ := fun x => (β (Iic x)).toReal with hG
  have hGmono : Monotone G := fun x y hxy =>
    ENNReal.toReal_mono (hfin y) (measure_mono (Iic_subset_Iic.mpr hxy))
  set θ0 : ℝ := b + 1 with hθ0
  have hθ0b : b < θ0 := by linarith
  have hS : MeasurableSet (Ioi (0:ℝ)) := measurableSet_Ioi
  set μS : Measure (Ioi (0:ℝ)) := Measure.comap Subtype.val volume with hμS
  -- functions on the subtype
  set f : Ioi (0:ℝ) → ℝ := fun y => Real.exp (-θ0 * y) * F y with hf
  set g : Ioi (0:ℝ) → ℝ := fun y => Real.exp (-θ0 * y) * G y with hg
  have hfint : Integrable f μS :=
    (integrableOn_iff_comap_subtypeVal hS).mp (hlap θ0 hθ0b).1
  have hgint : Integrable g μS :=
    (integrableOn_iff_comap_subtypeVal hS).mp (hlap θ0 hθ0b).2.1
  have hfmeas : Measurable f := by
    have : Continuous f := by
      refine ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val))).mul ?_
      exact htiltcont.domRestrict
    exact this.measurable
  have hgmeas : Measurable g :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val))).measurable.mul
      (hGmono.measurable.comp measurable_subtype_coe)
  have hf0 : ∀ y, 0 ≤ f y := fun y => mul_nonneg (Real.exp_pos _).le (htiltnonneg y y.2)
  have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  set P : Measure (Ioi (0:ℝ)) := μS.withDensity (fun y => ENNReal.ofReal (f y)) with hP
  set P' : Measure (Ioi (0:ℝ)) := μS.withDensity (fun y => ENNReal.ofReal (g y)) with hP'
  have : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hfint.2
  have : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hgint.2
  -- generator
  let e₁ : BoundedContinuousFunction (Ioi (0:ℝ)) ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y : Ioi (0:ℝ) => Real.exp (-(y:ℝ)))
    (Real.continuous_exp.comp (continuous_neg.comp continuous_subtype_val)) 1
    (fun y : Ioi (0:ℝ) => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith [y.2.out]))
  have he₁ : ∀ y, e₁ y = Real.exp (-(y:ℝ)) := fun y => rfl
  have hint : ∀ (Q : Measure (Ioi (0:ℝ))) (h : Ioi (0:ℝ) → ℝ), Measurable h → (∀ y, 0 ≤ h y) →
      ∀ u : BoundedContinuousFunction (Ioi (0:ℝ)) ℝ,
      ∫ y, u y ∂(Q.withDensity (fun y => ENNReal.ofReal (h y))) = ∫ y, h y * u y ∂Q := by
    intro Q h hm h0 u
    have := integral_withDensity_eq_integral_smul (μ := Q) (measurable_real_toNNReal.comp hm) u
    calc ∫ y, u y ∂(Q.withDensity (fun y => ENNReal.ofReal (h y)))
        = ∫ y, (h y).toNNReal • u y ∂Q := this
      _ = _ := by
        congr 1; ext y; rw [NNReal.smul_def, Real.coe_toNNReal _ (h0 y), smul_eq_mul]
  have hpow : ∀ n : ℕ, ∫ y, (e₁ ^ n) y ∂P = ∫ y, (e₁ ^ n) y ∂P' := by
    intro n
    rw [hP, hP', hint _ _ hfmeas hf0, hint _ _ hgmeas hg0]
    have key := (hlap (θ0 + n) (by have := n.cast_nonneg (α := ℝ); linarith)).2.2
    rw [← integral_subtype_comap hS, ← integral_subtype_comap hS] at key
    have hexp : ∀ x : ℝ, Real.exp (-(θ0 + n) * x) = Real.exp (-θ0 * x) * Real.exp (-x) ^ n := by
      intro x; rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    convert key using 2
    · funext y
      simp only [hf, BoundedContinuousFunction.coe_pow, Pi.pow_apply, he₁, hexp, hF]
      ring
    · funext y
      simp only [hg, BoundedContinuousFunction.coe_pow, Pi.pow_apply, he₁, hexp, hG]
      ring
  have hA : ∀ u ∈ StarAlgebra.adjoin ℝ {e₁}, ∫ y, u y ∂P = ∫ y, u y ∂P' := by
    intro u hu
    have hstar : star e₁ = e₁ := by ext y; simp
    have hu' : u ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ ({e₁} : Set _)) := by
      have := StarAlgebra.adjoin_toSubalgebra ℝ
        ({e₁} : Set (BoundedContinuousFunction (Ioi (0:ℝ)) ℝ))
      rw [Set.star_singleton, hstar, Set.union_self] at this
      rw [Subalgebra.mem_toSubmodule, ← this]; exact hu
    rw [Algebra.adjoin_eq_span] at hu'
    clear hu
    induction hu' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.mp hv
      exact hpow n
    | zero => simp
    | add v w _ _ hv hw =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (v.integrable _) (w.integrable _),
        integral_add (v.integrable _) (w.integrable _), hv, hw]
    | smul c v _ hv =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hv]
  have hsep : ((StarAlgebra.adjoin ℝ {e₁}).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    refine ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ e₁,
      ⟨e₁, StarAlgebra.subset_adjoin ℝ _ rfl, rfl⟩, rfl⟩, ?_⟩
    show e₁ x ≠ e₁ y
    rw [he₁, he₁]
    intro h
    exact hxy (Subtype.ext (neg_injective (Real.exp_injective h)))
  have : PolishSpace (Ioi (0:ℝ)) := isOpen_Ioi.polishSpace
  have hPP : P = P' := ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep hA
  have hae : (fun y => ENNReal.ofReal (f y)) =ᵐ[μS] (fun y => ENNReal.ofReal (g y)) :=
    (withDensity_eq_iff hfmeas.ennreal_ofReal.aemeasurable hgmeas.ennreal_ofReal.aemeasurable
      hfint.lintegral_lt_top.ne).mp hPP
  have hae' : ∀ᵐ y : Ioi (0:ℝ) ∂μS, F y = G y := by
    filter_upwards [hae] with y hy
    rw [ENNReal.ofReal_eq_ofReal_iff (hf0 y) (hg0 y)] at hy
    exact mul_left_cancel₀ (Real.exp_pos _).ne' hy
  have hae2 : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), F x = G x := by
    rw [← map_comap_subtype_coe hS]
    exact (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr hae'
  have hFG : ∀ x, 0 < x → F x = G x := by
    intro x hx
    by_contra hne
    have hFt : Tendsto F (𝓝[>] x) (𝓝 (F x)) :=
      (htiltcont.continuousAt (Ioi_mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
    have hGt : Tendsto G (𝓝[>] x) (𝓝 (G x)) := by
      have h1 := tendsto_measure_biInter_gt (μ := β) (s := fun r => Iic r) (a := x)
        (fun r _ => measurableSet_Iic.nullMeasurableSet) (fun i j _ hij => Iic_subset_Iic.mpr hij)
        ⟨x + 1, by linarith, hfin _⟩
      have h2 : (⋂ r, ⋂ (_ : r > x), Iic r) = Iic x := by
        ext z; simp only [mem_iInter, mem_Iic]; constructor
        · intro h
          by_contra hz
          push Not at hz
          have := h ((x + z) / 2) (by linarith)
          linarith
        · intro h r hr; linarith
      rw [h2] at h1
      exact (ENNReal.tendsto_toReal (hfin x)).comp h1
    have hev : ∀ᶠ y in 𝓝[>] x, F y - G y ≠ 0 :=
      (hFt.sub hGt).eventually_ne (sub_ne_zero.mpr hne)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    have hae3 : ∀ᵐ y ∂(volume.restrict (Ioo x u)), F y = G y :=
      ae_restrict_of_ae_restrict_of_subset (fun z hz => lt_trans hx hz.1) hae2
    have hfalse : ∀ᵐ y ∂(volume.restrict (Ioo x u)), False := by
      filter_upwards [hae3, ae_restrict_mem measurableSet_Ioo] with y h1 h2
      exact hsub h2 (sub_eq_zero.mpr h1)
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero,
      Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hfalse
    have : x < u := hu
    linarith
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : 0 < G x := by
      have : β {0} ≤ β (Iic x) := measure_mono (singleton_subset_iff.mpr (mem_Iic.mpr hx.le))
      exact ENNReal.toReal_pos (hatom.trans_le this).ne' (hfin x)
    rw [← hFG x hx] at h1
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h1
  · intro x hx y hy hxy
    show F x ≤ F y
    rw [hFG x hx, hFG y hy]
    exact hGmono hxy
