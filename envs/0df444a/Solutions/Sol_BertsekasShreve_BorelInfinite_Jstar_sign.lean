-- Prove2me | solution 1 for BertsekasShreve.BorelInfinite.Jstar_sign
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:49:08.466196+00:00
-- url     : https://prove2.me/submissions/f15961ad-b8a5-4827-a4b4-da7049e4c634

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Theorems.Thm_BertsekasShreve_AnalyticSelection_jankov_von_neumann
import Theorems.Thm_BertsekasShreve_AnalyticSelection_analytic_universallyMeasurable
import Theorems.Thm_BertsekasShreve_AnalyticSelection_image_preimage_analytic

open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection

namespace BSSignAux

universe u v

lemma secondCountable_of_isBorel {X : Type u} [TopologicalSpace X] [IsBorelSpace X] :
    SecondCountableTopology X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.secondCountableTopology

lemma isBorel_prod {X : Type u} {Y : Type v} [TopologicalSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [IsBorelSpace Y] : IsBorelSpace (X × Y) := by
  obtain ⟨Z, i1, i2, i3, B, hB, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  obtain ⟨Z', j1, j2, j3, B', hB', ⟨e'⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := Y)
  letI := i1; letI := j1
  refine ⟨⟨Z × Z', inferInstance, inferInstance, inferInstance, B ×ˢ B', ?_, ⟨?_⟩⟩⟩
  · letI : MeasurableSpace Z := borel Z
    haveI : BorelSpace Z := ⟨rfl⟩
    letI : MeasurableSpace Z' := borel Z'
    haveI : BorelSpace Z' := ⟨rfl⟩
    have h := hB.prod hB'
    rwa [(Prod.borelSpace (α := Z) (β := Z')).measurable_eq] at h
  · exact (e.prodCongr e').trans (Homeomorph.Set.prod B B').symm

lemma um_of_analyticallyMeasurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (hA : ∀ A : Set X, AnalyticSet A → IsUniversallyMeasurable A)
    (E : Set X) (hE : IsAnalyticallyMeasurable E) : IsUniversallyMeasurable E := by
  unfold IsAnalyticallyMeasurable analyticSigmaAlgebra at hE
  induction hE with
  | basic s hs => exact hA s hs
  | empty => intro p _; exact nullMeasurableSet_empty
  | compl s _ ih => intro p hp; exact (ih p hp).compl
  | iUnion f _ ih => intro p hp; exact NullMeasurableSet.iUnion fun i => ih i p hp

end BSSignAux


open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection

namespace BSSignAux
open BertsekasShreve.BorelInfinite

lemma exists_policy {S C W : Type*}
    [TopologicalSpace S] [IsBorelSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [IsBorelSpace C] [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace W] (M : Model S C W) : Nonempty M.Policy := by
  haveI : SecondCountableTopology C := secondCountable_of_isBorel
  haveI : T2Space C := by
    obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := C)
    exact e.isEmbedding.t2Space
  obtain ⟨φ, hφm, hφ⟩ := jankov_von_neumann (X := S) (Y := C) _ M.graph_analytic
  have hmem : ∀ x : S, x ∈ Prod.fst '' {z : S × C | z.2 ∈ M.U z.1} := by
    intro x
    obtain ⟨u, hu⟩ := M.U_nonempty x
    exact ⟨(x, u), hu, rfl⟩
  let σ : S → C := fun x => φ ⟨x, hmem x⟩
  have hσU : ∀ x, σ x ∈ M.U x := fun x => hφ ⟨x, hmem x⟩
  have hσ : ∀ B : Set C, MeasurableSet B → IsUniversallyMeasurable (σ ⁻¹' B) := by
    intro B hB
    have h1 := hφm.2 B hB
    have h2 : Subtype.val '' (φ ⁻¹' B) = σ ⁻¹' B := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; simpa [σ] using hy
      · intro hx; exact ⟨⟨x, hmem x⟩, hx, rfl⟩
    rw [← h2]
    exact um_of_analyticallyMeasurable (fun A hA => analytic_universallyMeasurable A hA) _ h1
  let κ : UKernel S C :=
    { toFun := fun x => Measure.dirac (σ x)
      isProbability := fun x => inferInstance
      univMeasurable := by
        intro B hB A _
        have hset : (fun x => Measure.dirac (σ x) B) ⁻¹' A =
            {x | (B.indicator (fun _ => (1 : ENNReal)) (σ x)) ∈ A} := by
          ext x; simp [Measure.dirac_apply' _ hB]; rfl
        rw [hset]
        by_cases h1 : (1 : ENNReal) ∈ A <;> by_cases h0 : (0 : ENNReal) ∈ A
        · have : {x | (B.indicator (fun _ => (1 : ENNReal)) (σ x)) ∈ A} = Set.univ := by
            ext x; by_cases hx : σ x ∈ B <;> simp [Set.indicator, hx, h1, h0]
          rw [this]; intro p _; exact nullMeasurableSet_univ
        · have : {x | (B.indicator (fun _ => (1 : ENNReal)) (σ x)) ∈ A} = σ ⁻¹' B := by
            ext x; by_cases hx : σ x ∈ B <;> simp [Set.indicator, hx, h1, h0]
          rw [this]; exact hσ B hB
        · have : {x | (B.indicator (fun _ => (1 : ENNReal)) (σ x)) ∈ A} = (σ ⁻¹' B)ᶜ := by
            ext x; by_cases hx : σ x ∈ B <;> simp [Set.indicator, hx, h1, h0]
          rw [this]; intro p hp; exact (hσ B hB p hp).compl
        · have : {x | (B.indicator (fun _ => (1 : ENNReal)) (σ x)) ∈ A} = ∅ := by
            ext x; by_cases hx : σ x ∈ B <;> simp [Set.indicator, hx, h1, h0]
          rw [this]; intro p _; exact nullMeasurableSet_empty }
  let μ : M.UCS := ⟨κ, fun x => Measure.dirac_apply_of_mem (hσU x)⟩
  exact ⟨μ.toPolicy⟩

end BSSignAux


open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection

namespace BSSignAux
open BertsekasShreve.BorelInfinite

lemma bind_univ_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (m : Measure α)
    (f : α → Measure β) (hf : ∀ a, f a Set.univ ≤ 1) : (m.bind f) Set.univ ≤ m Set.univ := by
  by_cases h : AEMeasurable f m
  · rw [Measure.bind_apply MeasurableSet.univ h]
    calc ∫⁻ a, f a Set.univ ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono hf
      _ = m Set.univ := by simp
  · simp [Measure.bind, Measure.map_of_not_aemeasurable h]

lemma map_univ_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (m : Measure α)
    (f : α → β) : (m.map f) Set.univ ≤ m Set.univ := by
  by_cases h : AEMeasurable f m
  · rw [Measure.map_apply_of_aemeasurable h MeasurableSet.univ]; simp
  · simp [Measure.map_of_not_aemeasurable h]

lemma nullMeasurable_of_um {X : Type*} [MeasurableSpace X] (E : Set X)
    (hE : IsUniversallyMeasurable E) (q : Measure X) (hq : q Set.univ ≤ 1) :
    NullMeasurableSet E q := by
  by_cases h0 : q Set.univ = 0
  · rw [Measure.measure_univ_eq_zero.mp h0]; exact NullMeasurableSet.of_null (by simp)
  · have hfin : q Set.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
    set P := (q Set.univ)⁻¹ • q with hP
    haveI : IsProbabilityMeasure P := by
      constructor; simp [P, ENNReal.inv_mul_cancel h0 hfin]
    have hE' := hE P inferInstance
    refine hE'.mono_ac ?_
    have : q = (q Set.univ) • P := by
      simp [P, smul_smul, ENNReal.mul_inv_cancel h0 hfin]
    rw [this]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _

variable {S C W : Type*}
    [TopologicalSpace S] [IsBorelSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [IsBorelSpace C] [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace W]

lemma conc (M : Model S C W) {k : ℕ} (m : Measure (Hist S C k)) (hm : m Set.univ ≤ 1)
    (κ : Hist S C k → Measure C) (hκp : ∀ h, IsProbabilityMeasure (κ h))
    (hκU : ∀ h, κ h (M.U h.2) = 1) :
    ((m.bind (fun h => (κ h).map (fun u => (h, u)))).map
      (fun hu : Hist S C k × C => (hu.1.2, hu.2))) M.Γᶜ = 0 ∧
    (m.bind (fun h => (κ h).map (fun u => (h, u)))) Set.univ ≤ 1 := by
  haveI : SecondCountableTopology S := secondCountable_of_isBorel
  haveI : SecondCountableTopology C := secondCountable_of_isBorel
  haveI : IsBorelSpace (S × C) := isBorel_prod
  set F := fun h => (κ h).map (fun u => (h, u)) with hFdef
  have hF1 : ∀ h, F h Set.univ ≤ 1 := by
    intro h; haveI := hκp h
    calc F h Set.univ ≤ κ h Set.univ := map_univ_le _ _
      _ = 1 := measure_univ
  have hmass : (m.bind F) Set.univ ≤ 1 := (bind_univ_le m F hF1).trans hm
  refine ⟨?_, hmass⟩
  have hφ : Measurable (fun hu : Hist S C k × C => (hu.1.2, hu.2)) := by fun_prop
  set φ := (fun hu : Hist S C k × C => (hu.1.2, hu.2))
  by_cases hFa : AEMeasurable F m
  swap
  · simp [Measure.bind, Measure.map_of_not_aemeasurable hFa]
  set q := (m.bind F).map φ with hq
  have hq1 : q Set.univ ≤ 1 := (map_univ_le _ _).trans hmass
  have hΓ : NullMeasurableSet M.Γᶜ q :=
    (nullMeasurable_of_um _ (analytic_universallyMeasurable _ M.graph_analytic) q hq1).compl
  obtain ⟨G, hGsup, hGm, hGae⟩ := hΓ.exists_measurable_superset_ae_eq
  have hdiff : q (G \ M.Γᶜ) = 0 := (ae_eq_set.mp hGae).1
  set N := toMeasurable q (G \ M.Γᶜ)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNq : q N = 0 := by rw [measure_toMeasurable]; exact hdiff
  have hsub : G \ M.Γᶜ ⊆ N := subset_toMeasurable _ _
  have key : ∀ E : Set (S × C), MeasurableSet E →
      q E = ∫⁻ h, κ h {u | (h.2, u) ∈ E} ∂m := by
    intro E hE
    rw [hq, Measure.map_apply hφ hE, Measure.bind_apply (hφ hE) hFa]
    refine lintegral_congr fun h => ?_
    rw [hFdef]; dsimp only
    rw [Measure.map_apply measurable_prodMk_left (hφ hE)]
    rfl
  have hsec : ∀ h : Hist S C k, κ h (M.U h.2)ᶜ = 0 := by
    intro h
    haveI := hκp h
    have hUa : AnalyticSet (M.U h.2) := by
      have := (image_preimage_analytic (X := C) (Y := S × C) (fun u => (h.2, u))
        measurable_prodMk_left).2 _ M.graph_analytic
      simpa [Set.preimage] using this
    have hUn : NullMeasurableSet (M.U h.2) (κ h) :=
      analytic_universallyMeasurable _ hUa _ inferInstance
    rw [measure_compl₀ hUn (measure_ne_top _ _), hκU h, measure_univ, tsub_self]
  have hG0 : q G = 0 := by
    rw [key G hGm]
    have : ∫⁻ h, κ h {u | (h.2, u) ∈ G} ∂m ≤ ∫⁻ h, κ h {u | (h.2, u) ∈ N} ∂m := by
      refine lintegral_mono fun h => ?_
      calc κ h {u | (h.2, u) ∈ G} ≤ κ h ((M.U h.2)ᶜ ∪ {u | (h.2, u) ∈ N}) := by
            refine measure_mono fun u hu => ?_
            by_cases hU : u ∈ M.U h.2
            · right; exact hsub ⟨hu, fun hc => hc hU⟩
            · left; exact hU
        _ ≤ κ h (M.U h.2)ᶜ + κ h {u | (h.2, u) ∈ N} := measure_union_le _ _
        _ = κ h {u | (h.2, u) ∈ N} := by rw [hsec h, zero_add]
    rw [← key N hNm, hNq] at this
    exact le_antisymm this zero_le
  exact measure_mono_null hGsup hG0

end BSSignAux


open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection

namespace BSSignAux
open BertsekasShreve.BorelInfinite

variable {S C W : Type*}
    [TopologicalSpace S] [IsBorelSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [IsBorelSpace C] [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace W]

lemma jointLaw_props (M : Model S C W) (π : M.Policy) (p : Measure S) (hp : p Set.univ ≤ 1) :
    ∀ k, (π.jointLaw p k) Set.univ ≤ 1 ∧ (π.q p k) M.Γᶜ = 0 := by
  intro k
  have hκp := fun k h => (π.μ k).isProbability h
  have hκU := fun k h => π.admissible k h
  cases k with
  | zero =>
    have h := conc M (k := 0) (p.map (fun x : S => ((fun i : Fin 0 => i.elim0), x)))
      ((map_univ_le _ _).trans hp) (π.μ 0).toFun (hκp 0) (hκU 0)
    exact ⟨h.2, h.1⟩
  | succ k =>
    have ih := (jointLaw_props M π p hp k).1
    have hm : ((π.jointLaw p k).bind (fun hu =>
          (M.t (hu.1.2, hu.2)).map
            (fun x' => ((Fin.snoc (α := fun _ => S × C) hu.1.1 (hu.1.2, hu.2)), x')))) Set.univ
          ≤ 1 := by
      refine (bind_univ_le _ _ fun hu => ?_).trans ih
      haveI := M.p_markov
      refine (map_univ_le _ _).trans ?_
      refine (map_univ_le _ _).trans ?_
      simp
    have h := conc M (k := k + 1) _ hm (π.μ (k + 1)).toFun (hκp (k + 1)) (hκU (k + 1))
    exact ⟨h.2, h.1⟩

lemma q_univ_le (M : Model S C W) (π : M.Policy) (p : Measure S) (hp : p Set.univ ≤ 1) (k : ℕ) :
    (π.q p k) Set.univ ≤ 1 :=
  (map_univ_le _ _).trans (jointLaw_props M π p hp k).1

lemma ae_Γ (M : Model S C W) (π : M.Policy) (x : S) (k : ℕ) :
    ∀ᵐ z ∂(π.q (Measure.dirac x) k), z ∈ M.Γ := by
  rw [ae_iff]
  exact (jointLaw_props M π _ (by simp) k).2

lemma cost_nonneg_P (M : Model S C W) (hP : M.CaseP) (π : M.Policy) (x : S) :
    0 ≤ π.cost x := by
  have h0 : ∀ k, ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.q (Measure.dirac x) k) = 0 := by
    intro k
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [ae_Γ M π x k] with z hz
    rw [EReal.toENNReal_eq_zero_iff, EReal.neg_le, neg_zero]
    exact hP z.1 z.2 hz
  unfold Model.Policy.cost bsub
  simp only [h0, mul_zero, tsum_zero]
  split_ifs
  · exact le_top
  · simp only [EReal.coe_ennreal_zero, sub_zero]; exact EReal.coe_ennreal_nonneg _

lemma cost_nonpos_N (M : Model S C W) (hN : M.CaseN) (π : M.Policy) (x : S) :
    π.cost x ≤ 0 := by
  have h0 : ∀ k, ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.q (Measure.dirac x) k) = 0 := by
    intro k
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [ae_Γ M π x k] with z hz
    rw [EReal.toENNReal_eq_zero_iff]
    exact hN z.1 z.2 hz
  unfold Model.Policy.cost bsub
  simp only [h0, mul_zero, tsum_zero]
  simp only [ENNReal.zero_ne_top, if_false, EReal.coe_ennreal_zero, zero_sub,
    EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

lemma cost_bounded_D (M : Model S C W) (hD : M.CaseD) :
    ∃ c : ℝ, ∀ (π : M.Policy) (x : S), -(c : EReal) ≤ π.cost x ∧ π.cost x ≤ (c : EReal) := by
  obtain ⟨hα1, b, hb⟩ := hD
  set b' := max b 0
  have hα0 := M.α_pos
  set c := b' * (1 - M.α)⁻¹
  refine ⟨c, fun π x => ?_⟩
  have hsum : ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) = ENNReal.ofReal ((1 - M.α)⁻¹) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hα0.le k)
      (summable_geometric_of_lt_one hα0.le hα1), tsum_geometric_of_lt_one hα0.le hα1]
  have bound : ∀ (G : S × C → EReal), (∀ z ∈ M.Γ, G z ≤ (b' : EReal)) →
      ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) * ∫⁻ z, (G z).toENNReal ∂(π.q (Measure.dirac x) k)
        ≤ ENNReal.ofReal c := by
    intro G hG
    have hk : ∀ k, ∫⁻ z, (G z).toENNReal ∂(π.q (Measure.dirac x) k) ≤ ENNReal.ofReal b' := by
      intro k
      calc ∫⁻ z, (G z).toENNReal ∂(π.q (Measure.dirac x) k)
          ≤ ∫⁻ _, ENNReal.ofReal b' ∂(π.q (Measure.dirac x) k) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_Γ M π x k] with z hz
            have := EReal.toENNReal_le_toENNReal (hG z hz)
            simpa using this
        _ = ENNReal.ofReal b' * (π.q (Measure.dirac x) k) Set.univ := by rw [lintegral_const]
        _ ≤ ENNReal.ofReal b' * 1 := by
            gcongr; exact q_univ_le M π _ (by simp) k
        _ = ENNReal.ofReal b' := mul_one _
    calc ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) * ∫⁻ z, (G z).toENNReal ∂(π.q (Measure.dirac x) k)
        ≤ ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) * ENNReal.ofReal b' :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hk k
      _ = ENNReal.ofReal c := by
          rw [ENNReal.tsum_mul_right, hsum, ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith)),
            mul_comm]
  have hA := bound (fun z => M.g z.1 z.2) fun z hz =>
    (hb z.1 z.2 hz).2.trans (by exact_mod_cast le_max_left b 0)
  have hB := bound (fun z => -(M.g z.1 z.2)) fun z hz => by
    have := (hb z.1 z.2 hz).1
    rw [EReal.neg_le] at this
    exact this.trans (by exact_mod_cast le_max_left b 0)
  set A := ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
    ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.q (Measure.dirac x) k)
  set B := ∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
    ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.q (Measure.dirac x) k)
  have hAt : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hBt : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  have hc0 : 0 ≤ c := mul_nonneg (le_max_right _ _) (inv_nonneg.mpr (by linarith))
  have hAr : A.toReal ≤ c := ENNReal.toReal_le_of_le_ofReal hc0 hA
  have hBr : B.toReal ≤ c := ENNReal.toReal_le_of_le_ofReal hc0 hB
  have hcost : π.cost x = ((A.toReal - B.toReal : ℝ) : EReal) := by
    show bsub A B = _
    unfold bsub
    rw [if_neg hAt, ← ENNReal.ofReal_toReal hAt, ← ENNReal.ofReal_toReal hBt]
    rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
      max_eq_left ENNReal.toReal_nonneg, max_eq_left ENNReal.toReal_nonneg]
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [← EReal.coe_sub]
  rw [hcost]
  have hA0 := (ENNReal.toReal_nonneg : 0 ≤ A.toReal)
  have hB0 := (ENNReal.toReal_nonneg : 0 ≤ B.toReal)
  constructor
  · rw [← EReal.coe_neg]; exact_mod_cast (by linarith)
  · exact_mod_cast (by linarith)

end BSSignAux

theorem solution {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : BertsekasShreve.BorelInfinite.Model S C W) :
    (M.CaseP → ∀ x, 0 ≤ M.Jstar x) ∧ (M.CaseN → ∀ x, M.Jstar x ≤ 0) ∧
      (M.CaseD → ∃ c : ℝ, ∀ x, -(c : EReal) ≤ M.Jstar x ∧ M.Jstar x ≤ (c : EReal)) := by
  obtain ⟨π₀⟩ := BSSignAux.exists_policy M
  refine ⟨fun hP x => le_iInf fun π => BSSignAux.cost_nonneg_P M hP π x,
    fun hN x => (iInf_le _ π₀).trans (BSSignAux.cost_nonpos_N M hN π₀ x), fun hD => ?_⟩
  obtain ⟨c, hc⟩ := BSSignAux.cost_bounded_D M hD
  exact ⟨c, fun x => ⟨le_iInf fun π => (hc π x).1, (iInf_le _ π₀).trans (hc π₀ x).2⟩⟩
