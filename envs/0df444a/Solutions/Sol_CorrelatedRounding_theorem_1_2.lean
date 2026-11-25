-- Prove2me | solution 2 for CorrelatedRounding.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:27:13.643197+00:00
-- url     : https://prove2.me/submissions/f96ff0b1-c912-4fcf-bd19-268998d26ecd

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
import Definitions.Def_CorrelatedRounding_alg1Prog
import Theorems.Thm_CorrelatedRounding_runtime_claim
import Theorems.Thm_CorrelatedRounding_lemma_1
import Theorems.Thm_CorrelatedRounding_display_p12
import Theorems.Thm_CorrelatedRounding_integral_p12

open MeasureTheory ProbabilityTheory

namespace CRTheorem1

open CorrelatedRounding Set

/-- Independent families on the two factors of a product space stay jointly independent. -/
lemma iIndepFun_sumElim_prod {Ω Ω' ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → ℝ} {Y : κ → Ω' → ℝ} (hX : iIndepFun X μ) (hY : iIndepFun Y ν) :
    iIndepFun (Sum.elim (fun i (ω : Ω × Ω') => X i ω.1) (fun j (ω : Ω × Ω') => Y j ω.2))
      (μ.prod ν) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hX hY ⊢
  intro S sets H
  have hA := hX S.toLeft (sets := fun i => sets (Sum.inl i))
    (fun i hi => H _ (Finset.mem_toLeft.1 hi))
  have hB := hY S.toRight (sets := fun j => sets (Sum.inr j))
    (fun j hj => H _ (Finset.mem_toRight.1 hj))
  have hset : (⋂ x ∈ S, Sum.elim (fun i (ω : Ω × Ω') => X i ω.1)
      (fun j (ω : Ω × Ω') => Y j ω.2) x ⁻¹' sets x) =
      (⋂ i ∈ S.toLeft, X i ⁻¹' sets (Sum.inl i)) ×ˢ
        (⋂ j ∈ S.toRight, Y j ⁻¹' sets (Sum.inr j)) := by
    ext ⟨ω, ω'⟩
    simp only [mem_iInter, mem_preimage, mem_prod, Finset.mem_toLeft, Finset.mem_toRight,
      Sum.forall, Sum.elim_inl, Sum.elim_inr]
  have hl : ∀ i, (μ.prod ν) ((fun ω : Ω × Ω' => X i ω.1) ⁻¹' sets (Sum.inl i)) =
      μ (X i ⁻¹' sets (Sum.inl i)) := by
    intro i
    rw [show (fun ω : Ω × Ω' => X i ω.1) ⁻¹' sets (Sum.inl i) =
      (X i ⁻¹' sets (Sum.inl i)) ×ˢ (univ : Set Ω') by ext; simp,
      Measure.prod_prod, measure_univ, mul_one]
  have hr : ∀ j, (μ.prod ν) ((fun ω : Ω × Ω' => Y j ω.2) ⁻¹' sets (Sum.inr j)) =
      ν (Y j ⁻¹' sets (Sum.inr j)) := by
    intro j
    rw [show (fun ω : Ω × Ω' => Y j ω.2) ⁻¹' sets (Sum.inr j) =
      (univ : Set Ω) ×ˢ (Y j ⁻¹' sets (Sum.inr j)) by ext; simp,
      Measure.prod_prod, measure_univ, one_mul]
  rw [hset, Measure.prod_prod, hA, hB]
  conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := S), Finset.prod_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, hl, hr]

/-- Existence of a draw. -/
lemma exists_draw {q K : ℕ} (u : Fin K → Fin q → ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E := by
  classical
  let ν : Fin K → Measure ℝ := fun k =>
    if 0 < y u k then expMeasure (y u k) else Measure.dirac 0
  have hν : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    by_cases h : 0 < y u k
    · simp only [ν, if_pos h]; exact isProbabilityMeasure_expMeasure h
    · simp only [ν, if_neg h]; infer_instance
  refine ⟨Fin K → ℝ, inferInstance, Measure.pi ν, inferInstance, fun k ω => ω k, ?_, ?_⟩
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro k hk
    have h := (measurePreserving_eval ν k).hasLaw
    simp only [ν, if_pos hk] at h
    exact h

/-- The competitive bound. -/
lemma competitive {q K : ℕ} (hq : 1 ≤ q) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) {Z : Ω → Fin q → Fin K}
    (hZ : ∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) (k : Fin K) :
    μ (⋃ i, {ω | Z ω i = k}) ≤ ENNReal.ofReal ((1 + Real.log q) * y u k) := by
  classical
  set bad := {ω | ¬ IsAlg1Output u (fun k => E k ω) (Z ω)} with hbad
  have hbad0 : μ bad = 0 := ae_iff.1 hZ
  have hcol : ∀ i, ∃ j, u j i ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    have := hu.2 i
    simp [hc] at this
  -- an item assigned to `k` sees `k` open no later than any other FC
  have key : ∀ ω i, ω ∉ bad → Z ω i = k → 0 < u k i ∧ ∀ k', k' ≠ k →
      ((y u k / u k i * E k ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i := by
    intro ω i hω hz
    have hgood : IsAlg1Output u (fun k => E k ω) (Z ω) := by
      by_contra h; exact hω h
    have hpos : 0 < u k i := by
      rcases eq_or_lt_of_le (hu.1 k i) with h0 | h
      · obtain ⟨j, hj⟩ := hcol i
        have h := hgood i j
        rw [hz] at h
        simp only [clock, if_pos h0.symm, if_neg hj] at h
        exact absurd h (not_le.2 (EReal.coe_lt_top _))
      · exact h
    refine ⟨hpos, fun k' _ => ?_⟩
    have h := hgood i k'
    rw [hz] at h
    have hc : clock u (fun k'' => E k'' ω) k i = ((y u k / u k i * E k ω : ℝ) : EReal) := by
      simp [clock, hpos.ne']
    rw [← hc]; exact h
  by_cases hk : 0 < y u k
  · have := isProbabilityMeasure_expMeasure hk
    let ν : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => expMeasure (y u k))
    let E' : Fin K → Ω × (ℕ → ℝ) → ℝ := fun k ω => E k ω.1
    let G : ℕ → Ω × (ℕ → ℝ) → ℝ := fun j ω => ω.2 j
    have hind : iIndepFun (Sum.elim E' G) (μ.prod ν) :=
      iIndepFun_sumElim_prod (Y := fun j (x : ℕ → ℝ) => x j) hE.1
        (iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id))
    have hE' : IsAlg1Draw u (μ.prod ν) E' :=
      ⟨hind.precomp Sum.inl_injective,
        fun k' hk' => (hE.2 k' hk').comp (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw⟩
    have hG : ∀ j, HasLaw (G j) (expMeasure (y u k)) (μ.prod ν) := fun j =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => expMeasure (y u k)) j).hasLaw.comp
        (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw
    let S : ℕ → Ω × (ℕ → ℝ) → ℝ := fun j ω => E k ω.1 + ∑ l ∈ Finset.range j, G l ω
    have hS0 : ∀ ω, S 0 ω = E' k ω := fun ω => by simp [S, E']
    have hS : ∀ j ω, S (j + 1) ω = S j ω + G j ω := fun j ω => by
      simp only [S, Finset.sum_range_succ]; ring
    have hp := display_p12 hu hE' k hk G hG hind S hS0 hS
    have hint := integral_p12 q hq
    rw [hint.1.trans (hint.2.1.trans hint.2.2)] at hp
    set D := ⋃ i ∈ {i | 0 < u k i}, ⋃ j, {ω : Ω × (ℕ → ℝ) |
        (∀ k', k' ≠ k →
          ((y u k / u k i * S j ω : ℝ) : EReal) ≤ clock u (fun k'' => E' k'' ω) k' i) ∧
        ∀ j' < j, y u k / u k i * S j ω ≤ y u k / u k i * S j' ω} with hD
    have hsub : (⋃ i, {ω | Z ω i = k}) ×ˢ (univ : Set (ℕ → ℝ)) ⊆ bad ×ˢ univ ∪ D := by
      rintro ⟨ω, ω'⟩ ⟨hω, -⟩
      by_cases hb : ω ∈ bad
      · exact Or.inl ⟨hb, mem_univ _⟩
      · right
        obtain ⟨i, hi⟩ := mem_iUnion.1 hω
        obtain ⟨hpos, hle⟩ := key ω i hb hi
        refine mem_iUnion₂.2 ⟨i, hpos, mem_iUnion.2 ⟨0, ?_, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩⟩
        intro k' hk'
        rw [hS0]
        exact hle k' hk'
    calc μ (⋃ i, {ω | Z ω i = k})
        = (μ.prod ν) ((⋃ i, {ω | Z ω i = k}) ×ˢ (univ : Set (ℕ → ℝ))) := by
          rw [Measure.prod_prod, measure_univ, mul_one]
      _ ≤ (μ.prod ν) (bad ×ˢ univ ∪ D) := measure_mono hsub
      _ ≤ (μ.prod ν) (bad ×ˢ univ) + (μ.prod ν) D := measure_union_le _ _
      _ = (μ.prod ν) D := by rw [Measure.prod_prod, hbad0, zero_mul, zero_add]
      _ ≤ ENNReal.ofReal (y u k * (1 + Real.log q)) := hp
      _ = ENNReal.ofReal ((1 + Real.log q) * y u k) := by rw [mul_comm]
  · have hsub : (⋃ i, {ω | Z ω i = k}) ⊆ bad := by
      intro ω hω
      by_contra hb
      obtain ⟨i, hi⟩ := mem_iUnion.1 hω
      have hpos := (key ω i hb hi).1
      have : u k i ≤ y u k := le_ciSup (Finite.bddAbove_range _) i
      exact hk (lt_of_lt_of_le hpos this)
    exact (measure_mono hsub).trans (by rw [hbad0]; exact zero_le)

end CRTheorem1

open CorrelatedRounding in
theorem solution :
    ∃ C : ℕ, ∀ (q K : ℕ), 1 ≤ q → ∀ (u : Fin K → Fin q → ℝ), IsInstance u →
      (∀ E : Fin K → ℝ,
        ((alg1Prog u E).run 0).2 ≤ C * q * K ∧
        ∃ z : Fin q → Fin K, (∀ i, ((alg1Prog u E).run 0).1 i = some (z i)) ∧ IsAlg1Output u E z) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E) ∧
      (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E →
        ∀ Z : Ω → Fin q → Fin K, (∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) →
          (∀ i k, μ {ω | Z ω i = k} = ENNReal.ofReal (u k i)) ∧
          ∀ k, μ (⋃ i, {ω | Z ω i = k}) ≤ ENNReal.ofReal ((1 + Real.log q) * y u k)) := by
  obtain ⟨C, hC⟩ := runtime_claim
  refine ⟨C, fun q K hq u hu => ⟨fun E => hC q K hq u hu E, CRTheorem1.exists_draw u, ?_⟩⟩
  intro Ω _ μ _ E hE Z hZ
  exact ⟨fun i k => lemma_1 hu hE hZ i k, fun k => CRTheorem1.competitive hq hu hE hZ k⟩
