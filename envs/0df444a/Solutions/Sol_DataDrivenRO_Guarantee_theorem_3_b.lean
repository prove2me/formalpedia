-- Prove2me | solution 1 for DataDrivenRO.Guarantee.theorem_3_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:47:58.372792+00:00
-- url     : https://prove2.me/submissions/54312fdf-ba1f-4289-be82-d60a4fb5d3e6

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee.Pcbf

lemma clm_eq_dot {d : ℕ} (L : StrongDual ℝ (Fin d → ℝ)) (u : Fin d → ℝ) :
    L u = u ⬝ᵥ (fun i => L (Pi.single i 1)) := by
  conv_lhs => rw [pi_eq_sum_univ u]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

lemma prob_gt_le {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (w : Fin d → ℝ) (c : ℝ) (hc : VaR P ε w < c) :
    P {u | c < u ⬝ᵥ w} ≤ ENNReal.ofReal ε := by
  set A : Set ℝ := {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ w ≤ y}} with hA
  have hmeas : ∀ y : ℝ, MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ w ≤ y} := by
    intro y
    exact measurableSet_le (by fun_prop) measurable_const
  have hAne : A.Nonempty := by
    have hmono : Monotone (fun n : ℕ => {u : Fin d → ℝ | u ⬝ᵥ w ≤ (n : ℝ)}) := by
      intro m n hmn u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      exact hu.trans (by exact_mod_cast hmn)
    have hU : (⋃ n : ℕ, {u : Fin d → ℝ | u ⬝ᵥ w ≤ (n : ℝ)}) = Set.univ := by
      ext u
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge (u ⬝ᵥ w)
      exact ⟨n, hn⟩
    have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU, measure_univ] at ht
    have hlt : ENNReal.ofReal (1 - ε) < 1 := by
      rw [ENNReal.ofReal_lt_one]; linarith
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
    exact ⟨n, hn.le⟩
  have hVaR : VaR P ε w = sInf A := rfl
  rw [hVaR] at hc
  obtain ⟨y, hyA, hyc⟩ := exists_lt_of_csInf_lt hAne hc
  have hsub : {u : Fin d → ℝ | c < u ⬝ᵥ w} ⊆ {u | u ⬝ᵥ w ≤ y}ᶜ := by
    intro u hu
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le] at hu ⊢
    linarith
  calc P {u | c < u ⬝ᵥ w} ≤ P {u | u ⬝ᵥ w ≤ y}ᶜ := measure_mono hsub
    _ = 1 - P {u | u ⬝ᵥ w ≤ y} := prob_compl_eq_one_sub (hmeas y)
    _ ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub_left hyA _
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1; ring

end DataDrivenRO.Guarantee.Pcbf

open MeasureTheory DataDrivenRO.Guarantee in
lemma Pcbf_superlevel {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U) (hcpt : IsCompact U)
    (hVaR : ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v)
    (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    P {u | t ≤ f u xstar} ≤ ENNReal.ofReal ε := by
  have hcont : Continuous (fun u => f u xstar) := by
    rw [← continuousOn_univ]
    exact hf.continuousOn isOpen_univ
  have hSconv : Convex ℝ {u | t ≤ f u xstar} := by
    have := hf.convex_ge t
    simpa using this
  have hSclosed : IsClosed {u | t ≤ f u xstar} := isClosed_le continuous_const hcont
  have hdisj : Disjoint U {u | t ≤ f u xstar} := by
    rw [Set.disjoint_left]
    intro a ha hb
    have := hfeas a ha
    simp only [Set.mem_setOf_eq] at hb
    linarith
  obtain ⟨L, c1, c2, hU, hc12, hS⟩ :=
    geometric_hahn_banach_compact_closed hconv hcpt hSconv hSclosed hdisj
  set w : Fin d → ℝ := fun i => L (Pi.single i 1) with hw
  have hsupp : RobustMDP.Shared.supportFunction U w ≤ c1 := by
    unfold RobustMDP.Shared.supportFunction
    apply csSup_le (hne.image _)
    rintro _ ⟨p, hp, rfl⟩
    have h1 := hU p hp
    rw [Pcbf.clm_eq_dot L p] at h1
    simp only [dotProduct] at h1
    exact h1.le
  have hlt : VaR P ε w < c2 := lt_of_le_of_lt ((hVaR w).trans hsupp) hc12
  have hsub : {u | t ≤ f u xstar} ⊆ {u | c2 < u ⬝ᵥ w} := by
    intro u hu
    have := hS u hu
    rw [Pcbf.clm_eq_dot L u] at this
    exact this
  exact (measure_mono hsub).trans (Pcbf.prob_gt_le P ε hε0 hε1 w c2 hlt)


open MeasureTheory DataDrivenRO.Guarantee in
lemma Pcbf_prob_pos_le {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U) (hcpt : IsCompact U)
    (hVaR : ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v)
    (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0) :
    P {u | 0 < f u xstar} ≤ ENNReal.ofReal ε := by
  have hmono : Monotone (fun n : ℕ => {u : Fin d → ℝ | 1 / ((n : ℝ) + 1) ≤ f u xstar}) := by
    intro m n hmn u hu
    simp only [Set.mem_setOf_eq] at hu ⊢
    refine le_trans ?_ hu
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hU : (⋃ n : ℕ, {u : Fin d → ℝ | 1 / ((n : ℝ) + 1) ≤ f u xstar}) = {u | 0 < f u xstar} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le (by positivity) hn
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h
      exact ⟨n, hn.le⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at ht
  exact le_of_tendsto' ht (fun n => Pcbf_superlevel P ε hε0 hε1 U hne hconv hcpt hVaR f xstar hf hfeas
    (1 / ((n : ℝ) + 1)) (by positivity))


open MeasureTheory DataDrivenRO.Guarantee in
theorem solution {d N k m : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (region : (Fin N → Fin d → ℝ) → Set (Measure (Fin d → ℝ)))
    (U : (Fin N → Fin d → ℝ) → ℝ → Set (Fin d → ℝ))
    (hne : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, (U S ε).Nonempty)
    (hconv : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, Convex ℝ (U S ε))
    (hcpt : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsCompact (U S ε))
    (hstep2 : ∀ S, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ P ∈ region S, IsProbabilityMeasure P →
      ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction (U S ε) v)
    (hcover : ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ region S})
    (f : Fin m → (Fin d → ℝ) → (Fin k → ℝ) → ℝ)
    (hf : ∀ j x, ConcaveOn ℝ Set.univ (fun u => f j u x)) (εbar : ℝ) :
    ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar)
        {S | ∀ (x : Fin k → ℝ) (εs : Fin m → ℝ), (∀ j, εs j ∈ Set.Ioo (0 : ℝ) 1) →
          ∑ j, εs j ≤ εbar → (∀ j, ∀ u ∈ U S (εs j), f j u x ≤ 0) →
          ENNReal.ofReal (1 - εbar) ≤ Pstar {u | ∀ j, f j u x ≤ 0}} := by
  refine hcover.trans (measure_mono ?_)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  intro x εs hεs hsum hfeas
  have hj : ∀ j, Pstar {u | 0 < f j u x} ≤ ENNReal.ofReal (εs j) := fun j =>
    Pcbf_prob_pos_le Pstar (εs j) (hεs j).1 (hεs j).2 (U S (εs j)) (hne S _ (hεs j))
      (hconv S _ (hεs j)) (hcpt S _ (hεs j)) (hstep2 S _ (hεs j) Pstar hS inferInstance)
      (f j) x (hf j x) (hfeas j)
  have hεbar : 0 ≤ εbar := le_trans (Finset.sum_nonneg fun j _ => (hεs j).1.le) hsum
  have hbad : Pstar {u | ∀ j, f j u x ≤ 0}ᶜ ≤ ENNReal.ofReal εbar := by
    have hsub : {u | ∀ j, f j u x ≤ 0}ᶜ ⊆ ⋃ j, {u | 0 < f j u x} := by
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hu
      simpa using hu
    calc Pstar {u | ∀ j, f j u x ≤ 0}ᶜ ≤ Pstar (⋃ j, {u | 0 < f j u x}) := measure_mono hsub
      _ ≤ ∑ j, Pstar {u | 0 < f j u x} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, ENNReal.ofReal (εs j) := Finset.sum_le_sum fun j _ => hj j
      _ = ENNReal.ofReal (∑ j, εs j) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ => (hεs j).1.le).symm
      _ ≤ ENNReal.ofReal εbar := ENNReal.ofReal_le_ofReal hsum
  have htot : (1 : ENNReal) ≤ Pstar {u | ∀ j, f j u x ≤ 0} + Pstar {u | ∀ j, f j u x ≤ 0}ᶜ := by
    calc (1 : ENNReal) = Pstar Set.univ := measure_univ.symm
      _ = Pstar ({u | ∀ j, f j u x ≤ 0} ∪ {u | ∀ j, f j u x ≤ 0}ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  rw [ENNReal.ofReal_sub _ hεbar, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal εbar ≤ 1 - Pstar {u | ∀ j, f j u x ≤ 0}ᶜ := tsub_le_tsub_left hbad _
    _ ≤ Pstar {u | ∀ j, f j u x ≤ 0} := tsub_le_iff_right.mpr htot
