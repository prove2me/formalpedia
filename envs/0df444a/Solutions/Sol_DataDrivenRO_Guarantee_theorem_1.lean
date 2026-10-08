-- Prove2me | solution 1 for DataDrivenRO.Guarantee.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:02:19.358419+00:00
-- url     : https://prove2.me/submissions/2a3fac69-8a64-4feb-ac9d-2079866d91b4

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace DDROG5d

lemma bdd_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) {α : ℝ} (hα : 0 < α) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} := by
  have hanti : Antitone (fun n : ℕ => {ω | Y ω ≤ -(n:ℝ)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hinter : (⋂ n : ℕ, {ω | Y ω ≤ -(n:ℝ)}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (-Y ω)
    exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_le hY measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  have hpos : (0:ENNReal) < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  refine ⟨-(N:ℝ), fun y hy => ?_⟩
  by_contra hlt
  push_neg at hlt
  have : P {ω | Y ω ≤ y} ≤ P {ω | Y ω ≤ -(N:ℝ)} :=
    measure_mono fun ω hω => by simp only [mem_ofPred_eq] at hω ⊢; linarith
  exact absurd (le_trans (show ENNReal.ofReal α ≤ P {ω | Y ω ≤ y} from hy) this)
    (not_le.mpr hN)

lemma ne_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) {α : ℝ} (hα : α < 1) :
    {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}}.Nonempty := by
  have hmono : Monotone (fun n : ℕ => {ω | Y ω ≤ (n:ℝ)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hunion : (⋃ n : ℕ, {ω | Y ω ≤ (n:ℝ)}) = univ := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (Y ω)
    exact ⟨n, hn⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hunion, measure_univ] at ht
  have hlt : ENNReal.ofReal α < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hα
  obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨N, hN.le⟩

lemma le_of_var_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) {α : ℝ} (hα1 : α < 1) {t : ℝ}
    (ht : MultistageStochastic.valueAtRisk P Y α ≤ t) :
    ENNReal.ofReal α ≤ P {ω | Y ω ≤ t} := by
  have hS : MultistageStochastic.valueAtRisk P Y α =
      sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} := rfl
  have hmem : ∀ n : ℕ, ENNReal.ofReal α ≤ P {ω | Y ω ≤ t + 1/((n:ℝ)+1)} := by
    intro n
    have hlt : sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} < t + 1/((n:ℝ)+1) := by
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
    obtain ⟨y, hyS, hy⟩ := exists_lt_of_csInf_lt (ne_set P Y hα1) hlt
    exact le_trans (show ENNReal.ofReal α ≤ P {ω | Y ω ≤ y} from hyS)
      (measure_mono fun ω hω => by simp only [mem_ofPred_eq] at hω ⊢; linarith)
  have hanti : Antitone (fun n : ℕ => {ω | Y ω ≤ t + 1/((n:ℝ)+1)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hmn' : (m:ℝ) ≤ n := by exact_mod_cast hmn
    have : 1/((n:ℝ)+1) ≤ 1/((m:ℝ)+1) := by gcongr
    linarith
  have hinter : (⋂ n : ℕ, {ω | Y ω ≤ t + 1/((n:ℝ)+1)}) = {ω | Y ω ≤ t} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
      have := h n
      linarith
    · intro h n
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
  have htend := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_le hY measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter] at htend
  exact ge_of_tendsto' htend (fun n => hmem n)

lemma dot_cont {d : ℕ} (v : Fin d → ℝ) : Continuous (fun u : Fin d → ℝ => u ⬝ᵥ v) := by
  simp only [dotProduct]; fun_prop

lemma dual_repr {d : ℕ} (φ : StrongDual ℝ (Fin d → ℝ)) :
    ∃ w : Fin d → ℝ, ∀ u : Fin d → ℝ, u ⬝ᵥ w = -φ u := by
  refine ⟨fun i => -φ (Pi.single i 1), fun u => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single u]
  rw [map_sum, ← Finset.sum_neg_distrib]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (u i) : Fin d → ℝ) = u i • Pi.single i 1 := by
    ext j; by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  rw [this, map_smul, smul_eq_mul]
  ring

end DDROG5d

open MeasureTheory DataDrivenRO.Guarantee in
theorem solution {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ U : Set (Fin d → ℝ), U.Nonempty → Convex ℝ U → IsCompact U →
      (∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v) → ImpliesGuarantee P U ε) ∧
    (∀ U : Set (Fin d → ℝ), U.Nonempty →
      (∃ v, BddAbove ((fun u => u ⬝ᵥ v) '' U) ∧
        RobustMDP.Shared.supportFunction U v < VaR P ε v) →
      ∃ f : (Fin d → ℝ) → (Fin 1 → ℝ) → ℝ, IsBiaffine f ∧ ∃ xstar : Fin 1 → ℝ,
        (∀ u ∈ U, f u xstar ≤ 0) ∧ P {u | f u xstar ≤ 0} < ENNReal.ofReal (1 - ε)) := by
  have hα1 : 1 - ε < 1 := by linarith
  have hα0 : 0 < 1 - ε := by linarith
  constructor
  · intro U hne hconv _hcomp hvar k f hconc xstar hfeas
    have hg : ConcaveOn ℝ univ (fun u => f u xstar) := hconc xstar
    have hgc : Continuous (fun u => f u xstar) :=
      continuousOn_univ.mp (hg.continuousOn isOpen_univ)
    have hAconv : Convex ℝ {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} := hg.convex_gt 0
    have hAopen : IsOpen {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} := by
      simpa only [mem_univ, true_and, Set.sep_univ] using isOpen_lt continuous_const hgc
    have hdisj : Disjoint {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} U := by
      rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ hU
      exact absurd (hfeas a hU) (not_le.mpr ha)
    obtain ⟨φ, s, hA, hB⟩ := geometric_hahn_banach_open hAconv hAopen hconv hdisj
    obtain ⟨w, hw⟩ := DDROG5d.dual_repr φ
    have hσ : RobustMDP.Shared.supportFunction U w ≤ -s := by
      apply csSup_le (hne.image _)
      rintro _ ⟨b, hb, rfl⟩
      have := hB b hb
      have h2 := hw b
      simp only [dotProduct] at h2
      linarith
    have hv := DDROG5d.le_of_var_le P (fun u => u ⬝ᵥ w) (DDROG5d.dot_cont w).measurable hα1
      ((hvar w).trans hσ)
    refine le_trans hv (measure_mono fun u hu => ?_)
    simp only [mem_ofPred_eq] at hu ⊢
    by_contra hpos
    push_neg at hpos
    have := hA u ⟨mem_univ _, hpos⟩
    have h2 := hw u
    linarith
  · rintro U _hne ⟨v, hbdd, hlt⟩
    refine ⟨fun u x => u ⬝ᵥ v - x 0, ?_, fun _ => RobustMDP.Shared.supportFunction U v, ?_, ?_⟩
    · refine ⟨0, v, fun _ => -1, 0, fun u x => ?_⟩
      have h1 : (fun _ : Fin 1 => (-1:ℝ)) ⬝ᵥ x = -x 0 := by simp [dotProduct]
      rw [Matrix.zero_mulVec, dotProduct_zero, dotProduct_comm v u, h1]
      ring
    · intro u hu
      have : u ⬝ᵥ v ≤ sSup ((fun u => u ⬝ᵥ v) '' U) := le_csSup hbdd (mem_image_of_mem _ hu)
      show u ⬝ᵥ v - RobustMDP.Shared.supportFunction U v ≤ 0
      have heq : RobustMDP.Shared.supportFunction U v = sSup ((fun u => u ⬝ᵥ v) '' U) := rfl
      linarith
    · by_contra h
      push_neg at h
      have hset : {u : Fin d → ℝ | u ⬝ᵥ v - RobustMDP.Shared.supportFunction U v ≤ 0} =
          {u | (fun u => u ⬝ᵥ v) u ≤ RobustMDP.Shared.supportFunction U v} := by
        ext u; simp only [mem_ofPred_eq, sub_nonpos]
      rw [hset] at h
      have : VaR P ε v ≤ RobustMDP.Shared.supportFunction U v :=
        csInf_le (DDROG5d.bdd_set P (fun u => u ⬝ᵥ v) (DDROG5d.dot_cont v).measurable hα0) h
      linarith
