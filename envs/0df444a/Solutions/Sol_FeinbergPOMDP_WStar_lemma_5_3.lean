-- Prove2me | solution 1 for FeinbergPOMDP.WStar.lemma_5_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:22:12.743187+00:00
-- url     : https://prove2.me/submissions/4e280e74-c6bb-480c-9700-43579b91da31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_FeinbergPOMDP_WStar_theorem_5_2

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

lemma fpw_R_eq {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (z : ProbabilityMeasure X) (a : A) (O : Set X) (hO : MeasurableSet O)
    (C : Set Y) (hC : MeasurableSet C) :
    ((jointLaw P Q z a : Measure (X × Y)) (O ×ˢ C)).toReal =
      ∫ x, (∫ x' in O, ((Q (a, x')) C).toReal ∂(P (x, a))) ∂(z : Measure X) := by
  have hg : Measurable fun x' : X => Q (a, x') C :=
    (Kernel.measurable_coe Q hC).comp measurable_prodMk_left
  have hL : Measurable fun x : X => ∫⁻ x', O.indicator (fun x' => Q (a, x') C) x' ∂(P (x, a)) :=
    (Measurable.lintegral_kernel_prod_right' (κ := P.comap (fun x => (x, a))
      measurable_prodMk_right) ((hg.indicator hO).comp measurable_snd))
  simp only [jointLaw, ProbabilityMeasure.coe_mk]
  rw [Measure.compProd_apply_prod hO hC]
  simp only [Kernel.comap_apply]
  rw [← lintegral_indicator hO, Measure.lintegral_bind (Kernel.aemeasurable _)
    (hg.indicator hO).aemeasurable]
  simp only [Kernel.comap_apply]
  have hin : ∀ x, ∫ x' in O, ((Q (a, x')) C).toReal ∂(P (x, a)) =
      (∫⁻ x', O.indicator (fun x' => Q (a, x') C) x' ∂(P (x, a))).toReal := by
    intro x
    rw [lintegral_indicator hO, integral_toReal hg.aemeasurable
      (Eventually.of_forall fun x' => measure_lt_top _ _)]
  simp_rw [hin]
  rw [integral_toReal hL.aemeasurable]
  refine Eventually.of_forall fun x => ?_
  calc ∫⁻ x', O.indicator (fun x' => Q (a, x') C) x' ∂(P (x, a))
      ≤ ∫⁻ _x', 1 ∂(P (x, a)) := lintegral_mono fun x' => by
        by_cases hx : x' ∈ O
        · simp [Set.indicator_of_mem hx, prob_le_one]
        · simp [Set.indicator_of_notMem hx]
    _ < ∞ := by simp

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q))
    (O₁ O₂ : Set X) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) :
    (∀ (C : {C : Set Y // MeasurableSet C}) (p : ProbabilityMeasure X × A),
        |RFamily P Q (O₁ \ O₂) C p| ≤ 1) ∧
    REquicontinuous P Q (O₁ \ O₂) := by
  have hRreal : ∀ (B : Set X) (C : {C : Set Y // MeasurableSet C}) (p : ProbabilityMeasure X × A),
      RFamily P Q B C p = ((jointLaw P Q p.1 p.2 : Measure (X × Y)) (B ×ˢ C.1)).toReal := by
    intro B C p
    simp only [RFamily]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  refine ⟨fun C p => ?_, ?_⟩
  · rw [hRreal, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  -- Step 1: the family `G_C(x', a) = Q(C | a, x')` is equicontinuous (TV continuity of `Q`).
  let G : {C : Set Y // MeasurableSet C} → X × A → ℝ := fun C q => ((Q (q.2, q.1)) C.1).toReal
  have hGeq : ∀ q, EquicontinuousAt G q := by
    intro q
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    rw [eventually_iff_seq_eventually]
    intro qs hqs
    have hsw : Tendsto (fun n => ((qs n).2, (qs n).1)) atTop (𝓝 (q.2, q.1)) :=
      ((continuous_snd.tendsto _).comp hqs).prodMk_nhds ((continuous_fst.tendsto _).comp hqs)
    obtain ⟨N, hN⟩ := hQ (q.2, q.1) _ hsw (ε / 2) (half_pos hε)
    rw [eventually_atTop]
    refine ⟨N, fun n hn C => ?_⟩
    have := hN n hn (C.1.indicator 1) (measurable_one.indicator C.2)
      (fun t => by by_cases ht : t ∈ C.1 <;> simp [Set.indicator, ht])
    rw [integral_indicator_one C.2, integral_indicator_one C.2] at this
    simp only [kernelPM, ProbabilityMeasure.coe_mk, measureReal_def] at this
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt this (half_lt_self hε)
  have hGc : ∀ C, Continuous (G C) := fun C =>
    continuous_iff_continuousAt.2 fun q => (hGeq q).continuousAt C
  have hGb : ∀ C q, |G C q| ≤ 1 := fun C q => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  -- Step 2: `R_O` is equicontinuous for every open `O` (two applications of Theorem 5.2).
  have hRO : ∀ O : Set X, IsOpen O → ∀ p : ProbabilityMeasure X × A,
      EquicontinuousAt (fun (C : {C : Set Y // MeasurableSet C}) p => RFamily P Q O C p) p := by
    intro O hO
    have h1 := (theorem_5_2 (S₁ := X × A) (S₂ := X) (S₃ := A) (kernelPM P) hP G hGc hGeq
      ⟨1, hGb⟩ O hO).1
    let G1 : {C : Set Y // MeasurableSet C} → X × A → ℝ :=
      fun C q => ∫ x' in O, G C (x', q.2) ∂(P q)
    have hG1eq : ∀ q, EquicontinuousAt G1 q := by
      intro q
      have h := h1 (q, q.2)
      rw [Metric.equicontinuousAt_iff_right] at h ⊢
      intro ε hε
      have hu : Tendsto (fun q' : X × A => (q', q'.2)) (𝓝 q) (𝓝 (q, q.2)) :=
        (continuous_id.prodMk continuous_snd).tendsto q
      exact hu.eventually (h ε hε)
    have hG1c : ∀ C, Continuous (G1 C) := fun C =>
      continuous_iff_continuousAt.2 fun q => (hG1eq q).continuousAt C
    have hG1b : ∀ C q, |G1 C q| ≤ 1 := fun C q => by
      have := norm_setIntegral_le_of_norm_le_const (μ := P q) (s := O)
        (f := fun x' => G C (x', q.2)) (C := 1) (measure_lt_top _ _)
        (fun x' _ => by rw [Real.norm_eq_abs]; exact hGb C (x', q.2))
      rw [Real.norm_eq_abs, one_mul] at this
      exact this.trans measureReal_le_one
    have hid : IsWeaklyContinuous (fun z : ProbabilityMeasure X => z) := fun _ _ h => h
    have h2 := (theorem_5_2 (S₁ := ProbabilityMeasure X) (S₂ := X) (S₃ := A) (fun z => z) hid
      G1 hG1c hG1eq ⟨1, hG1b⟩ Set.univ isOpen_univ).1
    intro p
    have hfun : (fun (C : {C : Set Y // MeasurableSet C}) p => RFamily P Q O C p) =
        (fun C (q : ProbabilityMeasure X × A) =>
          ∫ s₂ in Set.univ, G1 C (s₂, q.2) ∂((fun z : ProbabilityMeasure X => z) q.1 :
            Measure X)) := by
      funext C q
      rw [hRreal, fpw_R_eq P Q q.1 q.2 O hO.measurableSet C.1 C.2, Measure.restrict_univ]
    rw [hfun]
    exact h2 p
  -- Step 3: `O₁ \ O₂` via (5.16).
  have hdiff : ∀ C p, RFamily P Q (O₁ \ O₂) C p =
      RFamily P Q (O₁ ∪ O₂) C p - RFamily P Q O₂ C p := by
    intro C p
    rw [hRreal, hRreal, hRreal, eq_sub_iff_add_eq, ← ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _), ← measure_union _ (hO₂.measurableSet.prod C.2)]
    · congr 2
      rw [← Set.union_prod, Set.diff_union_self]
    · exact Set.disjoint_prod.2 (Or.inl Set.disjoint_sdiff_left)
  intro z a zs as hz ha ε hε
  have hpt : Tendsto (fun n => (zs n, as n)) atTop (𝓝 (z, a)) := hz.prodMk_nhds ha
  have e1 := hRO (O₁ ∪ O₂) (hO₁.union hO₂) (z, a)
  have e2 := hRO O₂ hO₂ (z, a)
  rw [Metric.equicontinuousAt_iff_right] at e1 e2
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hpt.eventually (e1 (ε / 2) (half_pos hε))).and (hpt.eventually (e2 (ε / 2) (half_pos hε))))
  refine ⟨N, fun n hn C => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have a1 := h1 C
  have a2 := h2 C
  rw [Real.dist_eq] at a1 a2
  rw [hdiff, hdiff]
  calc |RFamily P Q (O₁ ∪ O₂) C (zs n, as n) - RFamily P Q O₂ C (zs n, as n) -
        (RFamily P Q (O₁ ∪ O₂) C (z, a) - RFamily P Q O₂ C (z, a))|
      = |(RFamily P Q (O₁ ∪ O₂) C (z, a) - RFamily P Q (O₁ ∪ O₂) C (zs n, as n)) -
          (RFamily P Q O₂ C (z, a) - RFamily P Q O₂ C (zs n, as n))| := by
        rw [← abs_neg]; ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add a1.le a2.le
    _ = ε := by ring
