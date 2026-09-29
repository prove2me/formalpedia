-- Prove2me | solution 1 for EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c10fd51b-b324-54f6-8c7c-04e79f7e64dd

import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain

noncomputable section

namespace FiniteAdelicFactorization

open IsDedekindDomain Filter Topology
open scoped RestrictedProduct ENNReal NNReal

section Recognition

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Y : Type*} [MeasurableSpace Y]

private theorem exists_eq_prod_of_forall_map_add_left [T2Space G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (ρ : Measure (G × Y)) (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ Set.univ) < ∞) :
    ∃ σ : Measure Y, IsFiniteMeasure σ ∧ ρ = μ.prod σ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨K₀, hK₀c, hK₀n⟩ := exists_compact_mem_nhds (0 : G)
  have hK₀m : MeasurableSet K₀ := hK₀c.measurableSet
  have hK₀pos : μ K₀ ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK₀n).ne'
  have hK₀top : μ K₀ ≠ ∞ := hK₀c.measure_lt_top.ne
  have hT : ∀ a : G, Measurable fun p : G × Y => (a + p.1, p.2) := fun a =>
    (measurable_fst.const_add a).prodMk measurable_snd

  have hrect : ∀ (a : G) (A : Set G) (B : Set Y), MeasurableSet A → MeasurableSet B →
      ρ (((fun g => a + g) ⁻¹' A) ×ˢ B) = ρ (A ×ˢ B) := by
    intro a A B hA hB
    have h := congrArg (fun m : Measure (G × Y) => m (A ×ˢ B)) (hinv a)
    rw [Measure.map_apply (hT a) (hA.prod hB)] at h
    have hpre : (fun p : G × Y => (a + p.1, p.2)) ⁻¹' (A ×ˢ B) = ((fun g => a + g) ⁻¹' A) ×ˢ B := by
      ext ⟨g, y⟩
      simp only [Set.mem_preimage, Set.mem_prod]
    rw [hpre] at h
    exact h

  let ρB : Set Y → Measure G := fun B => (ρ.restrict (Set.univ ×ˢ B)).map Prod.fst
  have hρB : ∀ (B : Set Y) (A : Set G), MeasurableSet A → ρB B A = ρ (A ×ˢ B) := by
    intro B A hA
    simp only [ρB]
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    congr 1
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]

  let σ : Measure Y := (μ K₀)⁻¹ • (ρ.restrict (K₀ ×ˢ Set.univ)).map Prod.snd
  have hσ : ∀ B : Set Y, MeasurableSet B → σ B = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    intro B hB
    simp only [σ, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 2
    ext ⟨g, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  have hσfin : IsFiniteMeasure σ := by
    refine ⟨?_⟩
    rw [hσ _ MeasurableSet.univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hK₀pos)) (hfin K₀ hK₀c)
  haveI := hσfin
  refine ⟨σ, hσfin, (Measure.prod_eq fun A B hA hB => ?_).symm⟩

  haveI hBinv : (ρB B).IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun A' hA' => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hA', hρB B _ (measurable_const_add a hA'), hρB B A' hA']
    exact hrect a A' B hA' hB
  haveI hBfin : IsFiniteMeasureOnCompacts (ρB B) := by
    refine ⟨fun K hK => ?_⟩
    rw [hρB B K hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono (Set.prod_mono le_rfl (Set.subset_univ _))) (hfin K hK)
  have huniq : ρB B = (ρB B).addHaarScalarFactor μ • μ := Measure.isAddLeftInvariant_eq_smul (ρB B) μ
  set c : ℝ≥0 := (ρB B).addHaarScalarFactor μ with hc_def
  have hcA : ∀ A' : Set G, MeasurableSet A' → ρ (A' ×ˢ B) = (c : ℝ≥0∞) * μ A' := by
    intro A' hA'
    rw [← hρB B A' hA', huniq]
    exact Measure.coe_nnreal_smul_apply c μ A'
  have hc : (c : ℝ≥0∞) = (μ K₀)⁻¹ * ρ (K₀ ×ˢ B) := by
    rw [hcA K₀ hK₀m, mul_comm (c : ℝ≥0∞) (μ K₀), ← mul_assoc, ENNReal.inv_mul_cancel hK₀pos hK₀top, one_mul]
  rw [hcA A hA, hc, hσ B hB]
  ring

end Recognition

section Places

variable (F : Type) [Field F] [NumberField F]

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := by
    have e := (Module.finBasis ℚ F).equivFun.toEquiv
    exact (Equiv.countable_iff e).mpr inferInstance
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [local instance] countable_heightOneSpectrum

private theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

private abbrev Stratum (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((↑T : Set _)ᶜ)]

omit [NumberField F] in
private theorem cofinite_le (T : Finset (HeightOneSpectrum (𝓞 F))) :
    cofinite ≤ 𝓟 ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite

private def incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (cofinite_le F T)

variable {F} in
@[scoped simp] private theorem incl_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (v : HeightOneSpectrum (𝓞 F)) : incl F T x v = x v := rfl

private theorem isOpenEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : IsOpenEmbedding (incl F T) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal (isOpen_adicCompletionIntegers F) (cofinite_le F T)

private def stratumSet (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, v ∉ T → x v ∈ v.adicCompletionIntegers F}

private abbrev GT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type := ∀ i : ↥T, (i.1).adicCompletion F

private abbrev YT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  ∀ i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}, (i.1).adicCompletionIntegers F

variable {F} in
private theorem mem_of_not_mem {T : Finset (HeightOneSpectrum (𝓞 F))} (x : Stratum F T)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) : x v ∈ v.adicCompletionIntegers F :=
  (Filter.eventually_principal.mp x.2) v (by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv)

private theorem range_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Set.range (incl F T) = stratumSet F T := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ v hv
    exact mem_of_not_mem y hv
  · intro hx
    refine ⟨⟨fun v => x v, Filter.eventually_principal.mpr fun v hv => hx v ?_⟩,
      RestrictedProduct.ext _ _ fun v => rfl⟩
    simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv

open scoped Classical in

private def glue (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F :=
  if h : v ∈ T then p.1 ⟨v, h⟩ else ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F)

variable {F} in
private theorem glue_of_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) : glue F T p v = p.1 ⟨v, h⟩ := by
  simp only [glue, dif_pos h]

variable {F} in
private theorem glue_of_not_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    glue F T p v = ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  simp only [glue, dif_neg h]

private def splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) : GT F T × YT F T :=
  (fun i => x i.1, fun i => ⟨x i.1, mem_of_not_mem x i.2⟩)

private def splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) : Stratum F T :=
  ⟨glue F T p, Filter.eventually_principal.mpr fun v hv => by
    have hv' : v ∉ T := by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv
    rw [glue_of_not_mem T p hv']
    exact Subtype.coe_prop _⟩

variable {F} in
@[scoped simp] private theorem splitInv_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    (v : HeightOneSpectrum (𝓞 F)) : splitInv F T p v = glue F T p v := rfl

variable {F} in
@[scoped simp] private theorem splitFun_fst (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) (i : ↥T) :
    (splitFun F T x).1 i = x i.1 := rfl

variable {F} in
@[scoped simp] private theorem coe_splitFun_snd (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    ((splitFun F T x).2 i : (i.1).adicCompletion F) = x i.1 := rfl

variable {F} in
private theorem splitInv_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    splitInv F T (splitFun F T x) = x := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  rw [splitInv_apply]
  by_cases h : v ∈ T
  · rw [glue_of_mem T _ h, splitFun_fst]
  · rw [glue_of_not_mem T _ h, coe_splitFun_snd]

variable {F} in
private theorem splitFun_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    splitFun F T (splitInv F T p) = p := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · rw [splitFun_fst, splitInv_apply, glue_of_mem T p i.2]
  · rw [coe_splitFun_snd, splitInv_apply, glue_of_not_mem T p i.2]

private theorem continuous_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitFun F T) :=
  continuous_prodMk.mpr
    ⟨continuous_pi fun i => RestrictedProduct.continuous_eval i.1,
      continuous_pi fun i => (RestrictedProduct.continuous_eval i.1).subtype_mk _⟩

private theorem continuous_glue (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun p : GT F T × YT F T => glue F T p v := by
  by_cases h : v ∈ T
  · simp only [glue, dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [glue, dif_neg h]
    exact continuous_subtype_val.comp
      ((continuous_apply (⟨v, h⟩ : {w : HeightOneSpectrum (𝓞 F) // w ∉ T})).comp continuous_snd)

private theorem continuous_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitInv F T) :=
  RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun v => continuous_glue F T v)

private def split (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T ≃ₜ GT F T × YT F T where
  toFun := splitFun F T
  invFun := splitInv F T
  left_inv := splitInv_splitFun T
  right_inv := splitFun_splitInv T
  continuous_toFun := continuous_splitFun F T
  continuous_invFun := continuous_splitInv F T

variable {F} in
@[scoped simp] private theorem split_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    split F T x = splitFun F T x := rfl

variable {F} in
@[scoped simp] private theorem split_symm_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    (split F T).symm p = splitInv F T p := rfl

variable {F} in
private theorem incl_add (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x + y) = incl F T x + incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

variable {F} in
private theorem incl_sub (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x - y) = incl F T x - incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

private theorem split_add_symm (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) (p : GT F T × YT F T) :
    split F T ((split F T).symm (a, 0) + (split F T).symm p) = (a + p.1, p.2) := by
  simp only [split_apply, split_symm_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = a i + p.1 i
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_mem T _ i.2, glue_of_mem T _ i.2]
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = (p.2 i : (i.1).adicCompletion F)
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_not_mem T _ i.2,
      glue_of_not_mem T _ i.2]
    show ((0 : (i.1).adicCompletionIntegers F) : (i.1).adicCompletion F) + (p.2 i : (i.1).adicCompletion F)
      = (p.2 i : (i.1).adicCompletion F)
    rw [ZeroMemClass.coe_zero, zero_add]

private scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (Stratum F T) := borel _
private scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : BorelSpace (Stratum F T) := ⟨rfl⟩

end Places

attribute [local instance] countable_heightOneSpectrum

section Measures

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
private theorem measurableEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableEmbedding (incl F T) :=
  (isOpenEmbedding_incl F T).measurableEmbedding

private def rhoT (T : Finset (HeightOneSpectrum (𝓞 F))) : Measure (GT F T × YT F T) :=
  (ν.comap (incl F T)).map (split F T).toMeasurableEquiv

omit [ν.IsAddHaarMeasure] in

private theorem setIntegral_stratumSet_eq (T : Finset (HeightOneSpectrum (𝓞 F))) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : FiniteAdeleRing (𝓞 F) F → E) :
    ∫ x in stratumSet F T, f x ∂ν = ∫ p, f (incl F T ((split F T).symm p)) ∂(rhoT F ν T) := by
  rw [← range_incl F T, ← (measurableEmbedding_incl F T).map_comap ν,
    (measurableEmbedding_incl F T).integral_map]
  unfold rhoT
  rw [integral_map_equiv]
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in

private theorem comap_incl_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (b : Stratum F T) :
    (ν.comap (incl F T)).map (fun x => b + x) = ν.comap (incl F T) := by
  have hme := measurableEmbedding_incl F T
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_add b) hs, hme.comap_apply, hme.comap_apply]
  have hset : incl F T '' ((fun x => b + x) ⁻¹' s) = (fun y => incl F T b + y) ⁻¹' (incl F T '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b + x, hx, incl_add T b x⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨z - b, ?_, ?_⟩
      · show b + (z - b) ∈ s
        rwa [add_sub_cancel]
      · rw [incl_sub, hzy, add_sub_cancel_left]
  rw [hset, measure_preimage_add]

private theorem rhoT_map_add_left (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) :
    (rhoT F ν T).map (fun p : GT F T × YT F T => (a + p.1, p.2)) = rhoT F ν T := by
  have hTa : Measurable fun p : GT F T × YT F T => (a + p.1, p.2) :=
    (measurable_fst.const_add a).prodMk measurable_snd
  have hem : Measurable (split F T).toMeasurableEquiv := (split F T).toMeasurableEquiv.measurable
  have hconj : (fun p : GT F T × YT F T => (a + p.1, p.2)) ∘ (split F T).toMeasurableEquiv
      = (split F T).toMeasurableEquiv ∘ fun x => (split F T).symm (a, 0) + x := by
    funext x
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe]
    have h := split_add_symm F T a (split F T x)
    rw [Homeomorph.symm_apply_apply] at h
    exact h.symm
  unfold rhoT
  rw [Measure.map_map hTa hem, hconj, ← Measure.map_map hem (measurable_const_add _), comap_incl_map_add_left]

private theorem rhoT_prod_univ_lt_top (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (GT F T)) (hK : IsCompact K) :
    rhoT F ν T (K ×ˢ Set.univ) < ∞ := by
  unfold rhoT
  rw [MeasurableEquiv.map_apply, (measurableEmbedding_incl F T).comap_apply, Homeomorph.toMeasurableEquiv_coe,
    ← Homeomorph.image_symm]
  exact (((hK.prod isCompact_univ).image (split F T).symm.continuous).image
    (isOpenEmbedding_incl F T).continuous).measure_lt_top

private theorem exists_rhoT_eq_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure] :
    ∃ σ : Measure (YT F T), IsFiniteMeasure σ ∧
      rhoT F ν T = (Measure.pi fun i : ↥T => μ i.1).prod σ ∧
      ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)
        = (∏ v ∈ T, μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ Set.univ := by
  obtain ⟨σ, hσfin, hρ⟩ := exists_eq_prod_of_forall_map_add_left (Measure.pi fun i : ↥T => μ i.1) (rhoT F ν T)
    (rhoT_map_add_left F ν T) (rhoT_prod_univ_lt_top F ν T)
  haveI := hσfin
  refine ⟨σ, hσfin, hρ, ?_⟩

  have hbox : AdelicBox.integralFiniteAdeles (𝓞 F) F = incl F T '' ((split F T).toMeasurableEquiv ⁻¹'
      ((Set.univ.pi fun i : ↥T => ((i.1).adicCompletionIntegers F : Set ((i.1).adicCompletion F))) ×ˢ
        (Set.univ : Set (YT F T)))) := by
    rw [Homeomorph.toMeasurableEquiv_coe]
    ext y
    constructor
    · intro hy
      have hy' : y ∈ Set.range (incl F T) := by
        rw [range_incl]
        exact fun v _ => hy v
      obtain ⟨x, rfl⟩ := hy'
      refine ⟨x, ?_, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst]
      exact fun i => hy i.1
    · rintro ⟨x, hx, rfl⟩ v
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_univ_pi, split_apply,
        splitFun_fst] at hx
      by_cases hv : v ∈ T
      · exact hx ⟨v, hv⟩
      · exact mem_of_not_mem x hv
  rw [hbox, ← (measurableEmbedding_incl F T).comap_apply, ← MeasurableEquiv.map_apply]
  show rhoT F ν T _ = _
  rw [hρ, Measure.prod_prod, Measure.pi_pi]
  congr 1
  exact Finset.prod_coe_sort T fun v => μ v (v.adicCompletionIntegers F : Set (v.adicCompletion F))

end Measures

section StratumIdentity

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)] in
private theorem measureReal_box_ne_zero :
    ν.real (AdelicBox.integralFiniteAdeles (𝓞 F) F) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨((AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩).ne',
    (AdelicBox.isCompact_integralFiniteAdeles F).measure_ne_top⟩

end StratumIdentity

section LocalIntegrals

variable (F : Type) [Field F] [NumberField F]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

end LocalIntegrals

variable (F : Type) [Field F] [NumberField F]

section FinitePlaces

private def integralOffSet (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F}

private theorem finprod_incl_split_symm {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (p : GT F T × YT F T) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F T ((split F T).symm p) v) = ∏ i : ↥T, h i.1 (p.1 i) := by
  have hcoord : ∀ v, incl F T ((split F T).symm p) v = glue F T p v := fun v => rfl
  simp only [hcoord]
  have hone : ∀ v, v ∉ T → h v (glue F T p v) = 1 := fun v hv => by
    rw [glue_of_not_mem T p hv]
    exact h₁ v (fun hvS => hv (hST hvS)) _ (Subtype.coe_prop _)
  rw [finprod_eq_prod_of_mulSupport_subset (fun v => h v (glue F T p v)) (s := T) ?_]
  · rw [← Finset.prod_coe_sort T]
    exact Fintype.prod_congr _ _ fun i => by rw [glue_of_mem T p i.2]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hvT
    exact hv (hone v fun h' => hvT (Finset.mem_coe.mpr h'))

private theorem inv_measure_mul_setIntegral_integralOffSet_finprod_eq
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in integralOffSet F S, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v y ∂(μ v)) := by
  obtain ⟨σ, hσfin, hρ, hboxm⟩ := exists_rhoT_eq_prod F ν S μ
  haveI := hσfin

  have hI : ∫ x in integralOffSet F S, ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = (σ.real Set.univ : ℂ) * ∏ v ∈ S, ∫ y, h v y ∂(μ v) := by
    rw [show integralOffSet F S = stratumSet F S from rfl, setIntegral_stratumSet_eq]
    have hfun : (fun p : GT F S × YT F S =>
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (incl F S ((split F S).symm p) v))
        = fun p => (fun g : GT F S => ∏ i : ↥S, h i.1 (g i)) p.1 := by
      funext p
      exact finprod_incl_split_symm F (Finset.Subset.refl S) h h₁ p
    have hfst := integral_fun_fst (μ := Measure.pi fun i : ↥S => μ i.1) (ν := σ)
      (fun g : GT F S => ∏ i : ↥S, h i.1 (g i))
    have hprod : ∫ g : GT F S, ∏ i : ↥S, h i.1 (g i) ∂(Measure.pi fun i : ↥S => μ i.1)
        = ∏ i : ↥S, ∫ y, h i.1 y ∂(μ i.1) :=
      integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := fun i : ↥S => μ i.1) (fun i : ↥S => h i.1)
    rw [hfun, hρ, hfst, hprod]
    rw [Complex.real_smul]
    congr 1
    exact Finset.prod_coe_sort S fun v => ∫ y, h v y ∂(μ v)

  have hbox : ν.real (integralFiniteAdeles (𝓞 F) F)
      = (∏ v ∈ S, (μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) * σ.real Set.univ := by
    simp only [measureReal_def]
    rw [hboxm, ENNReal.toReal_mul, ENNReal.toReal_prod]

  have hσ0 : (σ.real Set.univ : ℂ) ≠ 0 := by
    have h0 := measureReal_box_ne_zero F ν
    rw [hbox] at h0
    exact Complex.ofReal_ne_zero.mpr (right_ne_zero_of_mul h0)
  rw [hI, hbox]
  push_cast
  rw [mul_inv, mul_assoc, inv_mul_cancel_left₀ hσ0, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end FinitePlaces

end FiniteAdelicFactorization
p2m_reactivate "P2MW.S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq.FiniteAdelicFactorization"

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1) :
    (ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x in {x : FiniteAdeleRing (𝓞 F) F |
              ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F},
            ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v) ∂ν
      = ∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
          * ∫ y, h v y ∂(μ v)) :=
  FiniteAdelicFactorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq F ν S μ h h₁

#print axioms solution

end
end S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq
end P2MW
export P2MW.S_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq (solution)
