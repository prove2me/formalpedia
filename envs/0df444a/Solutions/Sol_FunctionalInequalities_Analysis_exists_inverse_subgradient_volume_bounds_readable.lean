-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:26.271409+00:00
-- url     : https://prove2.me/submissions/ae3cd721-77d8-48ea-9060-8c448e58e551

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11F4ReciprocalAlexandrovBounds
open MeasureTheory Set Metric
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section CompleteSpace
variable [CompleteSpace E]
private lemma FunctionalInequalities.Analysis.inverse_subgradient_gradient_support
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    {x : E} (hx : DifferentiableAt ℝ u x) (y : E) :
    u x + ⟪gradient u x, y - x⟫ ≤ u y := by
  have hd :
      HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u x))
        ((AffineMap.lineMap (k := ℝ) x y) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hx.hasGradientAt.hasFDerivAt
  have hl :
      HasDerivAt (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y))
        ⟪gradient u x, y - x⟫ (0 : ℝ) := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hcl :
      ConvexOn ℝ univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y)) := by
    simpa only [preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) x y) hc
  have hle : ⟪gradient u x, y - x⟫ ≤ u y - u x := by
    simpa only [slope_def_field, Function.comp_apply,
      AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
      hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
        (zero_lt_one : (0 : ℝ) < 1) hl
  linarith
private lemma FunctionalInequalities.Analysis.inverse_subgradient_eq_gradient
    {u : E → ℝ} {x p : E} (hx : DifferentiableAt ℝ u x)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    p = gradient u x := by
  have hm :
      IsLocalMin (fun y => u y - (InnerProductSpace.toDual ℝ E p) y) x := by
    apply Filter.Eventually.of_forall
    intro y
    change u x - (InnerProductSpace.toDual ℝ E p) x ≤
      u y - (InnerProductSpace.toDual ℝ E p) y
    simp only [InnerProductSpace.toDual_apply_apply]
    have h := hp y
    rw [inner_sub_right] at h
    linarith
  have hz := hm.hasFDerivAt_eq_zero
    (hx.hasGradientAt.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E p).hasFDerivAt)
  exact ((InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp hz)).symm
end CompleteSpace
private lemma FunctionalInequalities.Analysis.inverse_subgradient_isClosed {u : E → ℝ} (hu : Continuous u)
    {S : Set E} (hS : IsCompact S) :
    IsClosed {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : Set (S × E) :=
    ⋂ y : E, {q | u q.2 + ⟪q.1.1, y - q.2⟫ ≤ u y}
  have hA : IsClosed A := by
    refine isClosed_iInter fun y => ?_
    exact isClosed_le
      ((hu.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).inner
          (continuous_const.sub continuous_snd)))
      continuous_const
  have himage :
      Prod.snd '' A = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, hz, rfl⟩
      exact ⟨p.1, p.2, mem_iInter.mp hz⟩
    · rintro ⟨p, hp, hx⟩
      exact ⟨(⟨p, hp⟩, x), mem_iInter.mpr hx, rfl⟩
  rw [← himage]
  exact isClosedMap_snd_of_compactSpace A hA
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.inverse_subgradient_measurableSet
    {u : E → ℝ} (hu : Continuous u) {G : Set E} (hG : IsOpen G) :
    MeasurableSet {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let S : ℕ → Set E := fun n => Subtype.val '' compactCovering G n
  have hScompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_compactCovering G n).image continuous_subtype_val
  have hSunion : (⋃ n, S n) = G := by
    change (⋃ n, Subtype.val '' compactCovering G n) = G
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hTunion :
      {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} =
        ⋃ n, {x | ∃ p ∈ S n, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
    rw [← hSunion]
    ext x
    constructor
    · rintro ⟨p, hp, hx⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨n, p, hn, hx⟩
    · intro hx
      obtain ⟨n, p, hp, hx⟩ := mem_iUnion.mp hx
      exact ⟨p, mem_iUnion.mpr ⟨n, hp⟩, hx⟩
  rw [hTunion]
  exact MeasurableSet.iUnion fun n =>
    (inverse_subgradient_isClosed hu (hScompact n)).measurableSet
/-- **Reciprocal Alexandrov bounds** (weak Letwin route; KLS500
`exists_local_relativeSubgradientImage_volume_bounds`): for the moment potential `u` (convex, Lipschitz,
`ν = e^{-u} dx` normalised, `ν.map ∇u = μ = ρ dx` with `c ≤ ρ ≤ C` on a closed convex `K`) and a radius `M`,
the set `(∂u)⁻¹(G) = {x | ∃ p ∈ G, p ∈ ∂u(x)}` of an open `G ⊆ K` that lies in `closedBall 0 M` has volume
comparable to `vol G`. -/
theorem solution
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = μ)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (hμ : μ = (volume : Measure E).withDensity ρ)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {c C : ℝ} (hc : 0 < c) (hρK : ∀ p ∈ K, ENNReal.ofReal c ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal C)
    (M : ℝ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → G ⊆ K →
      {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ⊆ closedBall (0 : E) M →
      ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ∧
        (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ≤
          ENNReal.ofReal b * (volume : Measure E) G := by
  have _hρ : Measurable ρ := hρ
  have _hK : IsClosed K := hK
  have _hKc : Convex ℝ K := hKc
  let ν : Measure E := (volume : Measure E).tilted (-u)
  have hν : ν ≪ (volume : Measure E) := by
    dsimp [ν, Measure.tilted]
    exact withDensity_absolutelyContinuous _ _
  have hν_eq :
      ν = (volume : Measure E).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-u x))) := by
    dsimp [ν, Measure.tilted]
    rw [hnorm]
    simp
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ u x :=
    ae_iff.mpr
      (hν (ae_iff.mp (hu.ae_differentiableAt (μ := (volume : Measure E)))))
  let Q : Set E := closedBall (0 : E) (max M 0)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  have hQne : Q.Nonempty :=
    nonempty_closedBall.mpr (le_max_right M 0)
  obtain ⟨xm, _, hxm⟩ := hQ.exists_isMaxOn hQne hu.continuous.continuousOn
  obtain ⟨xn, _, hxn⟩ := hQ.exists_isMinOn hQne hu.continuous.continuousOn
  let m : ℝ := u xm
  let n : ℝ := u xn
  let a : ℝ := c / Real.exp (-n)
  let b : ℝ := C / Real.exp (-m)
  have ha : 0 < a := div_pos hc (Real.exp_pos (-n))
  refine ⟨a, b, ha, ?_⟩
  intro G hG hGK hTG
  let T : Set E := {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
  have hT : MeasurableSet T :=
    FunctionalInequalities.Analysis.inverse_subgradient_measurableSet hu.continuous hG
  have hTQ : T ⊆ Q :=
    hTG.trans (closedBall_subset_closedBall (le_max_left M 0))
  have hsets : T =ᵐ[ν] (gradient u ⁻¹' G) := by
    filter_upwards [hdiff] with x hx
    change (∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y) =
      (gradient u x ∈ G)
    apply propext
    constructor
    · rintro ⟨p, hpG, hp⟩
      exact (FunctionalInequalities.Analysis.inverse_subgradient_eq_gradient hx hp) ▸ hpG
    · intro hxG
      exact ⟨gradient u x, hxG, FunctionalInequalities.Analysis.inverse_subgradient_gradient_support hconv hx⟩
  have hident : ν T = μ G := by
    calc
      ν T = ν (gradient u ⁻¹' G) := measure_congr hsets
      _ = (ν.map (gradient u)) G := (Measure.map_apply hgrad hG.measurableSet).symm
      _ = μ G := congrArg (fun η : Measure E => η G) hmap
  have hνT :
      ν T = ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) := by
    rw [hν_eq]
    exact withDensity_apply _ hT
  have hlowerν :
      ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤ ν T := by
    rw [hνT]
    calc
      ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T =
          ∫⁻ x in T, ENNReal.ofReal (Real.exp (-m)) :=
        (setLIntegral_const T _).symm
      _ ≤ ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) := by
        apply setLIntegral_mono' hT
        intro x hx
        have hxu : u x ≤ m := hxm (hTQ hx)
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
  have hupperν :
      ν T ≤ ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T := by
    rw [hνT]
    calc
      ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) ≤
          ∫⁻ x in T, ENNReal.ofReal (Real.exp (-n)) := by
        apply setLIntegral_mono' hT
        intro x hx
        have hxu : n ≤ u x := hxn (hTQ hx)
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
      _ = ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T :=
        setLIntegral_const T _
  have hμlower :
      ENNReal.ofReal c * (volume : Measure E) G ≤ μ G := by
    rw [hμ, withDensity_apply ρ hG.measurableSet]
    calc
      ENNReal.ofReal c * (volume : Measure E) G =
          ∫⁻ p in G, ENNReal.ofReal c := (setLIntegral_const G _).symm
      _ ≤ ∫⁻ p in G, ρ p :=
        setLIntegral_mono' hG.measurableSet fun p hp => (hρK p (hGK hp)).1
  have hμupper :
      μ G ≤ ENNReal.ofReal C * (volume : Measure E) G := by
    rw [hμ, withDensity_apply ρ hG.measurableSet]
    calc
      ∫⁻ p in G, ρ p ≤ ∫⁻ p in G, ENNReal.ofReal C :=
        setLIntegral_mono' hG.measurableSet fun p hp => (hρK p (hGK hp)).2
      _ = ENNReal.ofReal C * (volume : Measure E) G := setLIntegral_const G _
  constructor
  · have hmul :
        ENNReal.ofReal c * (volume : Measure E) G ≤
          ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T := by
      calc
        ENNReal.ofReal c * (volume : Measure E) G ≤ μ G := hμlower
        _ = ν T := hident.symm
        _ ≤ _ := hupperν
    have hn0 : ENNReal.ofReal (Real.exp (-n)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-n)))
    have hdiv :
        (ENNReal.ofReal c * (volume : Measure E) G) /
            ENNReal.ofReal (Real.exp (-n)) ≤ (volume : Measure E) T := by
      apply (ENNReal.div_le_iff hn0 ENNReal.ofReal_ne_top).mpr
      simpa only [mul_comm] using hmul
    change ENNReal.ofReal (c / Real.exp (-n)) * (volume : Measure E) G ≤
      (volume : Measure E) T
    rw [ENNReal.ofReal_div_of_pos (Real.exp_pos (-n))]
    exact (ENNReal.mul_div_right_comm ▸ hdiv)
  · have hmul :
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤
          ENNReal.ofReal C * (volume : Measure E) G := by
      calc
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤ ν T := hlowerν
        _ = μ G := hident
        _ ≤ _ := hμupper
    have hm0 : ENNReal.ofReal (Real.exp (-m)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-m)))
    have hdiv :
        (volume : Measure E) T ≤
          (ENNReal.ofReal C * (volume : Measure E) G) /
            ENNReal.ofReal (Real.exp (-m)) := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hm0) (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hmul
    change (volume : Measure E) T ≤
      ENNReal.ofReal (C / Real.exp (-m)) * (volume : Measure E) G
    rw [ENNReal.ofReal_div_of_pos (Real.exp_pos (-m))]
    exact (ENNReal.mul_div_right_comm ▸ hdiv)
