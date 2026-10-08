-- Prove2me | solution 1 for DataDrivenRO.Guarantee.prob_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:50:09.235117+00:00
-- url     : https://prove2.me/submissions/f6b3cb10-5f10-4ec5-886f-19f0f7e64e86

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee.P00f

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

end DataDrivenRO.Guarantee.P00f

open MeasureTheory DataDrivenRO.Guarantee in
lemma P00f_superlevel {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
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
    rw [P00f.clm_eq_dot L p] at h1
    simp only [dotProduct] at h1
    exact h1.le
  have hlt : VaR P ε w < c2 := lt_of_le_of_lt ((hVaR w).trans hsupp) hc12
  have hsub : {u | t ≤ f u xstar} ⊆ {u | c2 < u ⬝ᵥ w} := by
    intro u hu
    have := hS u hu
    rw [P00f.clm_eq_dot L u] at this
    exact this
  exact (measure_mono hsub).trans (P00f.prob_gt_le P ε hε0 hε1 w c2 hlt)


open MeasureTheory DataDrivenRO.Guarantee in
theorem solution {d k : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
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
  exact le_of_tendsto' ht (fun n => P00f_superlevel P ε hε0 hε1 U hne hconv hcpt hVaR f xstar hf hfeas
    (1 / ((n : ℝ) + 1)) (by positivity))
