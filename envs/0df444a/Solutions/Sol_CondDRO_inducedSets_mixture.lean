-- Prove2me | solution 1 for CondDRO.inducedSets_mixture
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:56:07.228856+00:00
-- url     : https://prove2.me/submissions/965e02dd-8ec4-4272-be15-b744c1293931

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_inducedSets
import Definitions.Def_CondDRO_mixture

open MeasureTheory ProbabilityTheory

private lemma cell_inter_apply_of_supp {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    (ϖ : CondDRO.FinitePartition Ω I) {q : Measure Ω} {i : I}
    (hsupp : q (ϖ.cell i)ᶜ = 0) {s : Set Ω} :
    q (s ∩ ϖ.cell i) = q s := by
  have hdiff : q (s \ ϖ.cell i) = 0 :=
    measure_mono_null (fun ω hω => hω.2) hsupp
  have hinter := measure_inter_add_sdiff s (ϖ.measurableSet_cell i) (μ := q)
  rw [hdiff, add_zero] at hinter
  exact hinter

private lemma cell_inter_apply_of_ne {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    (ϖ : CondDRO.FinitePartition Ω I) {q : Measure Ω} {i j : I} (hij : i ≠ j)
    (hsupp : q (ϖ.cell j)ᶜ = 0) {s : Set Ω} :
    q (s ∩ ϖ.cell i) = 0 := by
  refine measure_mono_null ?_ hsupp
  exact Set.inter_subset_right.trans (ϖ.pairwise_disjoint hij).subset_compl_right

private lemma mixture_restrict_cell_apply {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : CondDRO.FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (q : I → Measure Ω) (hq : ∀ i, q i ∈ A i) (i : I) (s : Set Ω) :
    (∑ j, ENNReal.ofReal (ν j) • q j) (s ∩ ϖ.cell i) = ENNReal.ofReal (ν i) * q i s := by
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hterm : ∀ j : I,
      ENNReal.ofReal (ν j) * q j (s ∩ ϖ.cell i) =
        if j = i then ENNReal.ofReal (ν i) * q i s else 0 := by
    intro j
    split_ifs with hji
    · subst hji
      rw [cell_inter_apply_of_supp ϖ (hA_supp j (q j) (hq j))]
    · rw [cell_inter_apply_of_ne ϖ (Ne.symm hji) (hA_supp j (q j) (hq j)), mul_zero]
  simp [hterm]

open CondDRO in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_ne : ∀ i, (A i).Nonempty)
    (hA_prob : ∀ i, ∀ Q ∈ A i, IsProbabilityMeasure Q)
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (hν_pos : ∀ i, 0 < ν i) (hν_sum : ∑ i, ν i = 1) :
    ∀ i, inducedSets (mixture A ν) ϖ i = A i := by
  classical
  have _ := hν_sum
  intro i
  ext Qi
  constructor
  · rintro ⟨Q, ⟨⟨q, hq, rfl⟩, _⟩, rfl⟩
    have hprob_i : IsProbabilityMeasure (q i) := hA_prob i (q i) (hq i)
    have hQ_cell : (∑ j, ENNReal.ofReal (ν j) • q j) (ϖ.cell i) = ENNReal.ofReal (ν i) := by
      simpa [Set.univ_inter, measure_univ, mul_one] using
        mixture_restrict_cell_apply ϖ A hA_supp ν q hq i Set.univ
    have hν0 : ENNReal.ofReal (ν i) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (hν_pos i)).ne'
    have hνtop : ENNReal.ofReal (ν i) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcond_eq : (∑ j, ENNReal.ofReal (ν j) • q j)[|ϖ.cell i] = q i := by
      ext s hs
      rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply hs, hQ_cell,
        mixture_restrict_cell_apply ϖ A hA_supp ν q hq i s,
        ← mul_assoc, ENNReal.inv_mul_cancel hν0 hνtop, one_mul]
    dsimp only
    rw [hcond_eq]
    exact hq i
  · intro hQi
    choose q₀ hq₀ using hA_ne
    let q : I → Measure Ω := fun j => if j = i then Qi else q₀ j
    have hq : ∀ j, q j ∈ A j := by
      intro j
      dsimp [q]
      split_ifs with hji
      · exact hji ▸ hQi
      · exact hq₀ j
    let Q : Measure Ω := ∑ j, ENNReal.ofReal (ν j) • q j
    have hQ_mem : Q ∈ mixture A ν := ⟨q, hq, rfl⟩
    have hprob_i : IsProbabilityMeasure (q i) := hA_prob i (q i) (hq i)
    have hQ_cell : Q (ϖ.cell i) = ENNReal.ofReal (ν i) := by
      simpa [Q, Set.univ_inter, measure_univ, mul_one] using
        mixture_restrict_cell_apply ϖ A hA_supp ν q hq i Set.univ
    have hν0 : ENNReal.ofReal (ν i) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (hν_pos i)).ne'
    have hνtop : ENNReal.ofReal (ν i) ≠ ⊤ := ENNReal.ofReal_ne_top
    refine ⟨Q, ⟨hQ_mem, hQ_cell.symm ▸ hν0⟩, ?_⟩
    dsimp only
    ext s hs
    have hqi : q i = Qi := if_pos rfl
    rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hs, hQ_cell]
    dsimp [Q]
    rw [mixture_restrict_cell_apply ϖ A hA_supp ν q hq i s,
      ← mul_assoc, ENNReal.inv_mul_cancel hν0 hνtop, one_mul, hqi]
