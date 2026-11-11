-- Prove2me | solution 1 for FeinbergPOMDP.WStar.filter_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T00:09:31.001721+00:00
-- url     : https://prove2.me/submissions/fe302cbb-a085-4cb4-8371-c4bfcb360a6b

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

/-! FeinbergPOMDP.WStar.filter_exists (a2d63d04). The posterior kernel is Mathlib's
`Kernel.condKernelBorel` of the swapped joint law, viewed as a kernel on `ℙ(𝕏) × 𝔸`.
The key extra fact is that the Borel σ-algebra of the weak topology on `ℙ(𝕏)` equals the
Giry σ-algebra (separable metrizable Borel `𝕏`). -/

namespace FeinbergPOMDP.WStar.DraftA2d6

open FeinbergPOMDP.WStar

/-- A countable convergence-determining family of bounded continuous functions. -/
def CountableDetermining (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] :
    Prop :=
  ∃ fs : ℕ → X →ᵇ ℝ, (∀ k, ‖fs k‖ ≤ 1) ∧
    ∀ (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X),
      (∀ k, Tendsto (fun n => ∫ x, fs k x ∂(μs n : Measure X)) atTop
        (𝓝 (∫ x, fs k x ∂(μ : Measure X)))) → Tendsto μs atTop (𝓝 μ)

theorem delta_pos (m : ℕ) : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat

/-- Real-valued thickened indicator. -/
noncomputable def thR {X : Type*} [PseudoMetricSpace X] (m : ℕ) (E : Set X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (thickenedIndicator (delta_pos m) E x : ℝ),
      NNReal.continuous_coe.comp (thickenedIndicator (delta_pos m) E).continuous⟩ 1
    (fun x y => by
      have h1 := thickenedIndicator_le_one (delta_pos m) E x
      have h2 := thickenedIndicator_le_one (delta_pos m) E y
      have h1' : ((thickenedIndicator (delta_pos m) E x : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h1
      have h2' : ((thickenedIndicator (delta_pos m) E y : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h2
      have h3 := (thickenedIndicator (delta_pos m) E x).2
      have h4 := (thickenedIndicator (delta_pos m) E y).2
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]; constructor <;> linarith)

theorem thR_apply {X : Type*} [PseudoMetricSpace X] (m : ℕ) (E : Set X) (x : X) :
    thR m E x = (thickenedIndicator (delta_pos m) E x : ℝ) := rfl

/-- Approximation of an open set `V` from below. -/
noncomputable def hfun {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) : X →ᵇ ℝ :=
  1 - thR m Vᶜ

theorem hfun_apply {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    hfun V m x = 1 - (thickenedIndicator (delta_pos m) Vᶜ x : ℝ) := rfl

theorem hfun_bounds {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    0 ≤ hfun V m x ∧ hfun V m x ≤ 1 := by
  rw [hfun_apply]
  have h1 : ((thickenedIndicator (delta_pos m) Vᶜ x : ℝ≥0) : ℝ) ≤ 1 := by
    exact_mod_cast thickenedIndicator_le_one (delta_pos m) Vᶜ x
  have h3 := (thickenedIndicator (delta_pos m) Vᶜ x).2
  constructor <;> linarith

theorem hfun_norm {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) : ‖hfun V m‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2 fun x => by
    rw [Real.norm_eq_abs, abs_le]
    have := hfun_bounds V m x
    constructor <;> linarith

theorem hfun_le_indicator {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    hfun V m x ≤ V.indicator 1 x := by
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]; exact (hfun_bounds V m x).2
  · rw [Set.indicator_of_notMem hx, hfun_apply,
      thickenedIndicator_one (delta_pos m) Vᶜ hx]
    simp

theorem open_le_liminf {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (V G : Set X) (hV : IsOpen V) (hVG : V ⊆ G)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hconv : ∀ m, Tendsto (fun n => ∫ x, hfun V m x ∂(μs n : Measure X)) atTop
      (𝓝 (∫ x, hfun V m x ∂(μ : Measure X)))) :
    (μ : Measure X) V ≤ liminf (fun n => (μs n : Measure X) G) atTop := by
  have step : ∀ (ν : ProbabilityMeasure X) m,
      ENNReal.ofReal (∫ x, hfun V m x ∂(ν : Measure X)) ≤ (ν : Measure X) G := by
    intro ν m
    have hle : ∫ x, hfun V m x ∂(ν : Measure X) ≤ (ν : Measure X).real V := by
      rw [← integral_indicator_one hV.measurableSet]
      exact integral_mono ((hfun V m).integrable _)
        ((integrable_const (1 : ℝ)).indicator hV.measurableSet) (hfun_le_indicator V m)
    calc ENNReal.ofReal (∫ x, hfun V m x ∂(ν : Measure X))
        ≤ ENNReal.ofReal ((ν : Measure X).real V) := ENNReal.ofReal_le_ofReal hle
      _ = (ν : Measure X) V := ofReal_measureReal (measure_ne_top _ _)
      _ ≤ (ν : Measure X) G := measure_mono hVG
  have hm : ∀ m, ENNReal.ofReal (∫ x, hfun V m x ∂(μ : Measure X)) ≤
      liminf (fun n => (μs n : Measure X) G) atTop := by
    intro m
    have hlim := ENNReal.tendsto_ofReal (hconv m)
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Filter.Eventually.of_forall fun n => step (μs n) m)
  -- the approximants converge to `μ V`
  have hint : ∀ m, ∫ x, hfun V m x ∂(μ : Measure X) =
      1 - (∫⁻ x, (thickenedIndicator (delta_pos m) Vᶜ x : ℝ≥0∞) ∂(μ : Measure X)).toReal := by
    intro m
    have e1 : ∫ x, hfun V m x ∂(μ : Measure X) =
        ∫ x, (1 : ℝ) ∂(μ : Measure X) - ∫ x, thR m Vᶜ x ∂(μ : Measure X) :=
      integral_sub (integrable_const _) ((thR m Vᶜ).integrable _)
    rw [e1, integral_const, probReal_univ, one_smul]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by
        rw [thR_apply]; exact (thickenedIndicator (delta_pos m) Vᶜ x).2)
      (thR m Vᶜ).continuous.aestronglyMeasurable]
    simp only [thR_apply, ENNReal.ofReal_coe_nnreal]
  have hT := tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure X) hV.isClosed_compl
    delta_pos tendsto_one_div_add_atTop_nhds_zero_nat
  have hT2 : Tendsto (fun m => ENNReal.ofReal (∫ x, hfun V m x ∂(μ : Measure X))) atTop
      (𝓝 ((μ : Measure X) V)) := by
    simp_rw [hint]
    have h1 := ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) Vᶜ)).comp hT).const_sub 1
    have h2 := ENNReal.tendsto_ofReal h1
    have hlimV : ENNReal.ofReal (1 - ((μ : Measure X) Vᶜ).toReal) = (μ : Measure X) V := by
      rw [prob_compl_eq_one_sub hV.measurableSet,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, sub_sub_cancel,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [← hlimV]
    exact h2
  exact le_of_tendsto' hT2 hm

theorem countableDetermining_of (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] : CountableDetermining X := by
  classical
  let _ := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set X, insert ∅ b = Set.range B :=
    (hbc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  have hBopen : ∀ i, IsOpen (B i) := by
    intro i
    have : B i ∈ insert ∅ b := hB ▸ Set.mem_range_self i
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  have hBcov : ∀ G : Set X, IsOpen G → ∀ x ∈ G, ∃ i, x ∈ B i ∧ B i ⊆ G := by
    intro G hG x hx
    obtain ⟨s, hs, hxs, hsG⟩ := hb.exists_subset_of_mem_open hx hG
    have : s ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hs
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, hxs, hsG⟩
  let V : Finset ℕ → Set X := fun s => ⋃ i ∈ s, B i
  have hVopen : ∀ s, IsOpen (V s) := fun s => isOpen_biUnion fun i _ => hBopen i
  obtain ⟨e, he⟩ := exists_surjective_nat (Finset ℕ × ℕ)
  refine ⟨fun n => hfun (V (e n).1) (e n).2, fun n => hfun_norm _ _, ?_⟩
  intro μs μ hconv
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  have hconv' : ∀ s m, Tendsto (fun n => ∫ x, hfun (V s) m x ∂(μs n : Measure X)) atTop
      (𝓝 (∫ x, hfun (V s) m x ∂(μ : Measure X))) := by
    intro s m
    obtain ⟨n, hn⟩ := he (s, m)
    have := hconv n
    simp only [hn] at this
    exact this
  let C : ℕ → Set X := fun i => if B i ⊆ G then B i else ∅
  have hCU : ⋃ i, C i = G := by
    ext x
    simp only [Set.mem_iUnion, C]
    constructor
    · rintro ⟨i, hi⟩
      split_ifs at hi with h
      exacts [h hi, hi.elim]
    · intro hx
      obtain ⟨i, hxi, hiG⟩ := hBcov G hG x hx
      exact ⟨i, by rw [if_pos hiG]; exact hxi⟩
  have hacc := tendsto_measure_iUnion_accumulate (μ := (μ : Measure X)) (f := C)
  rw [hCU] at hacc
  refine le_of_tendsto' hacc fun N => ?_
  let s := (Finset.range (N + 1)).filter (fun i => B i ⊆ G)
  have h1 : Set.accumulate C N ⊆ V s := by
    intro x hx
    simp only [Set.mem_accumulate, C] at hx
    obtain ⟨i, hiN, hi⟩ := hx
    split_ifs at hi with h
    · simp only [V, s, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
      exact ⟨i, ⟨by omega, h⟩, hi⟩
    · exact hi.elim
  have h2 : V s ⊆ G := by
    intro x hx
    simp only [V, s, Set.mem_iUnion, Finset.mem_filter] at hx
    obtain ⟨i, ⟨-, h⟩, hi⟩ := hx
    exact h hi
  exact (measure_mono h1).trans (open_le_liminf (V s) G (hVopen s) h2 μs μ (hconv' s))

/-- Integrals against a Borel function are Giry-measurable in the measure. -/
theorem measurable_integral_pm {X : Type*} [MeasurableSpace X] (f : X → ℝ) (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X)) := by
  let ζ : Kernel (ProbabilityMeasure X) X := ⟨fun μ => (μ : Measure X), measurable_subtype_coe⟩
  exact (hf.stronglyMeasurable.integral_kernel (κ := ζ)).measurable

/-- Every weakly open set of `ℙ(𝕏)` is Giry-measurable. -/
theorem borel_le_giry (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    borel (ProbabilityMeasure X) ≤ (inferInstance : MeasurableSpace (ProbabilityMeasure X)) := by
  obtain ⟨fs, -, hfs⟩ := countableDetermining_of X
  let Φ : ProbabilityMeasure X → (ℕ → ℝ) := fun μ k => ∫ x, fs k x ∂(μ : Measure X)
  have hΦm : Measurable Φ := measurable_pi_lambda _ fun k =>
    measurable_integral_pm _ (fs k).continuous.measurable
  refine MeasurableSpace.generateFrom_le fun U (hU : IsOpen U) => ?_
  have key : U = Φ ⁻¹' (closure (Φ '' Uᶜ))ᶜ := by
    ext μ
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hμ hcl
      obtain ⟨νs, hν, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
      choose ν hνU hνΦ using hν
      have hνs : νs = fun n => Φ (ν n) := funext fun n => (hνΦ n).symm
      have hT : Tendsto ν atTop (𝓝 μ) := hfs ν μ fun k => by
        have h1 := ((continuous_apply k).tendsto (Φ μ)).comp hlim
        rw [hνs] at h1
        exact h1
      exact (hU.isClosed_compl.mem_of_tendsto hT (Eventually.of_forall hνU)) hμ
    · intro h
      by_contra hμ
      exact h (subset_closure ⟨μ, hμ, rfl⟩)
  rw [key]
  exact hΦm isClosed_closure.isOpen_compl.measurableSet

/-- The Giry σ-algebra is contained in the Borel σ-algebra of the weak topology. -/
theorem giry_le_borel (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    (inferInstance : MeasurableSpace (ProbabilityMeasure X)) ≤ borel (ProbabilityMeasure X) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  letI mB : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  haveI : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  have hm : Measurable (fun μ : ProbabilityMeasure X => (μ : Measure X)) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S := {s : Set X | IsOpen s})
      (by rw [BorelSpace.measurable_eq (α := X)]; rfl) isPiSystem_isOpen ?_
    intro U hU
    refine LowerSemicontinuous.measurable ?_
    refine lowerSemicontinuous_iff_le_liminf.2 fun μ => ?_
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto (μs := id) tendsto_id hU
  exact hm.comap_le

theorem borel_eq_giry (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    borel (ProbabilityMeasure X) = (inferInstance : MeasurableSpace (ProbabilityMeasure X)) :=
  le_antisymm (borel_le_giry X) (giry_le_borel X)

/-- `(z, a) ↦ R(t | z, a)` is measurable (Giry σ-algebra on `ℙ(𝕏)`). -/
theorem measurable_joint_apply {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    {t : Set (X × Y)} (ht : MeasurableSet t) :
    Measurable (fun p : ProbabilityMeasure X × A => (jointLaw P Q p.1 p.2 : Measure (X × Y)) t) := by
  have hG : Measurable (fun q : A × X => Q q (Prod.mk q.2 ⁻¹' t)) :=
    Kernel.measurable_kernel_prodMk_left (κ := Q)
      (t := (fun r : (A × X) × Y => (r.1.2, r.2)) ⁻¹' t)
      (((measurable_snd.comp measurable_fst).prodMk measurable_snd) ht)
  have hF : Measurable (fun r : X × A => ∫⁻ x', Q (r.2, x') (Prod.mk x' ⁻¹' t) ∂(P r)) :=
    Measurable.lintegral_kernel_prod_right (κ := P)
      (f := fun r x' => Q (r.2, x') (Prod.mk x' ⁻¹' t))
      (hG.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  let ζ : Kernel (ProbabilityMeasure X × A) X :=
    ⟨fun p => (p.1 : Measure X), measurable_subtype_coe.comp measurable_fst⟩
  haveI : IsMarkovKernel ζ :=
    ⟨fun p => by show IsProbabilityMeasure (p.1 : Measure X); infer_instance⟩
  have hK : Measurable (fun p : ProbabilityMeasure X × A =>
      ∫⁻ x, ∫⁻ x', Q (p.2, x') (Prod.mk x' ⁻¹' t) ∂(P (x, p.2)) ∂(ζ p)) :=
    Measurable.lintegral_kernel_prod_right (κ := ζ)
      (f := fun p x => ∫⁻ x', Q (p.2, x') (Prod.mk x' ⁻¹' t) ∂(P (x, p.2)))
      (hF.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  convert hK using 1
  funext p
  show (Measure.compProd (Measure.bind (p.1 : Measure X)
      (P.comap (fun x => (x, p.2)) measurable_prodMk_right))
      (Q.comap (fun x' => (p.2, x')) measurable_prodMk_left)) t = _
  rw [Measure.compProd_apply ht, Measure.lintegral_bind
    (f := fun x' => (Q.comap (fun x' => (p.2, x')) measurable_prodMk_left) x' (Prod.mk x' ⁻¹' t))
    (Kernel.measurable _).aemeasurable
    (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable]
  rfl

end FeinbergPOMDP.WStar.DraftA2d6

open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar in
theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q] :
    ∃ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H := by
  have hEq := DraftA2d6.borel_eq_giry X
  let κ : Kernel (ProbabilityMeasure X × A) (Y × X) :=
    ⟨fun p => (jointLaw P Q p.1 p.2 : Measure (X × Y)).map Prod.swap, by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.map_apply measurable_swap hs]
      exact DraftA2d6.measurable_joint_apply P Q (measurable_swap hs)⟩
  haveI : IsMarkovKernel κ := ⟨fun p => Measure.isProbabilityMeasure_map measurable_swap.aemeasurable⟩
  let η : Kernel ((ProbabilityMeasure X × A) × Y) X := Kernel.condKernelBorel κ
  refine ⟨fun z a y => ⟨η ((z, a), y), inferInstance⟩, ⟨fun z a => ?_, ?_, fun z a B C hB hC => ?_⟩⟩
  · exact (η.measurable.comp measurable_prodMk_left).subtype_mk
  · rw [hEq]
    exact η.measurable.subtype_mk
  · have hd : κ.fst ⊗ₖ η = κ := Kernel.disintegrate κ η
    have hfst : κ.fst (z, a) = (obsLaw P Q z a : Measure Y) := by
      rw [Kernel.fst_apply]
      show ((jointLaw P Q z a : Measure (X × Y)).map Prod.swap).map Prod.fst = _
      rw [Measure.map_map measurable_fst measurable_swap, obsLaw, ProbabilityMeasure.toMeasure_map]
      rfl
    calc (jointLaw P Q z a : Measure (X × Y)) (B ×ˢ C) = κ (z, a) (C ×ˢ B) := by
          show _ = ((jointLaw P Q z a : Measure (X × Y)).map Prod.swap) (C ×ˢ B)
          rw [Measure.map_apply measurable_swap (hC.prod hB), Set.preimage_swap_prod]
      _ = (κ.fst ⊗ₖ η) (z, a) (C ×ˢ B) := by rw [hd]
      _ = ∫⁻ y in C, η ((z, a), y) B ∂(κ.fst (z, a)) := Kernel.compProd_apply_prod hC hB
      _ = _ := by rw [hfst]; rfl
