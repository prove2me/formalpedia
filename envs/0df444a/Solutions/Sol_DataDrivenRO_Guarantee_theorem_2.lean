-- Prove2me | solution 1 for DataDrivenRO.Guarantee.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:51:32.692129+00:00
-- url     : https://prove2.me/submissions/cec8bf3c-06af-4f7b-8834-7c0d8b0a9662

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

set_option autoImplicit false

namespace P01013868

open MeasureTheory ProbabilityTheory DataDrivenRO.Guarantee

/-- The Value at Risk is attained: `P(u ⬝ᵥ v ≤ VaR) ≥ 1 - ε` (right-continuity of the CDF). -/
lemma var_mem {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ VaR P ε v} := by
  have hYc : Continuous (fun u : Fin d → ℝ => u ⬝ᵥ v) := by
    unfold dotProduct; fun_prop
  have hY : Measurable (fun u : Fin d → ℝ => u ⬝ᵥ v) := hYc.measurable
  set μ : Measure ℝ := P.map (fun u : Fin d → ℝ => u ⬝ᵥ v) with hμ
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hP : ∀ y, P {u | u ⬝ᵥ v ≤ y} = ENNReal.ofReal (cdf μ y) := by
    intro y
    rw [ofReal_cdf, hμ, Measure.map_apply hY measurableSet_Iic]
    rfl
  set A : Set ℝ := {y | ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ y}} with hAdef
  have hA : ∀ y, y ∈ A ↔ 1 - ε ≤ cdf μ y := by
    intro y
    simp only [hAdef, Set.mem_setOf_eq, hP]
    exact ENNReal.ofReal_le_ofReal_iff (cdf_nonneg μ y)
  have hVaR : VaR P ε v = sInf A := rfl
  have hne : A.Nonempty := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually
      (lt_mem_nhds (by linarith : 1 - ε < 1))).exists
    exact ⟨b, (hA b).2 hb.le⟩
  have hbdd : BddBelow A := by
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.1 ((tendsto_cdf_atBot μ).eventually
      (gt_mem_nhds (by linarith : (0:ℝ) < 1 - ε)))
    refine ⟨b, fun a ha => ?_⟩
    by_contra h
    push_neg at h
    have := hb a h.le
    have := (hA a).1 ha
    linarith
  have hmem : sInf A ∈ A := by
    rw [hA]
    have hc : ContinuousWithinAt (cdf μ) (Set.Ioi (sInf A)) (sInf A) :=
      ((cdf μ).right_continuous (sInf A)).mono Set.Ioi_subset_Ici_self
    apply ge_of_tendsto hc
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨a, haA, haz⟩ := exists_lt_of_csInf_lt hne hz
    exact ((hA a).1 haA).trans (monotone_cdf μ haz.le)
  rw [hVaR]
  exact hmem

/-- Theorem 1(a): a support-function bound on VaR gives a probabilistic guarantee. -/
lemma guarantee_of_var {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (U : Set (Fin d → ℝ)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hne : U.Nonempty) (hconv : Convex ℝ U)
    (hvar : ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v) :
    ImpliesGuarantee P U ε := by
  intro k f hf xstar hU
  set g : (Fin d → ℝ) → ℝ := fun u => f u xstar with hgdef
  have hgc : Continuous g := continuousOn_univ.mp ((hf xstar).continuousOn isOpen_univ)
  set s : Set ((Fin d → ℝ) × ℝ) := {p | p.1 ∈ Set.univ ∧ p.2 < g p.1} with hsdef
  have hs_conv : Convex ℝ s := (hf xstar).convex_strict_hypograph
  have hs_open : IsOpen s := by
    have : s = {p | p.2 < g p.1} := by ext p; simp [hsdef]
    rw [this]
    exact isOpen_lt continuous_snd (hgc.comp continuous_fst)
  set t : Set ((Fin d → ℝ) × ℝ) := U ×ˢ Set.Ici 0 with htdef
  have ht_conv : Convex ℝ t := hconv.prod (convex_Ici 0)
  have disj : Disjoint s t := by
    refine Set.disjoint_left.2 fun p hp hq => ?_
    have h1 := hU p.1 hq.1
    have h2 : (0:ℝ) ≤ p.2 := hq.2
    have h3 := hp.2
    simp only [hgdef] at h3
    linarith
  obtain ⟨φ, c, hs, ht⟩ := geometric_hahn_banach_open hs_conv hs_open ht_conv disj
  set ψ : (Fin d → ℝ) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ) with hψ
  have hψa : ∀ u, ψ u = φ (u, 0) := fun u => rfl
  have h0 : ∀ u ∈ U, c ≤ ψ u := by
    intro u hu
    rw [hψa]
    exact ht (u, 0) ⟨hu, Set.mem_Ici.2 le_rfl⟩
  have hbound : ∀ u, c ≤ ψ u → g u ≤ 0 := by
    intro u hu
    by_contra h
    push_neg at h
    have := hs (u, 0) ⟨trivial, h⟩
    rw [← hψa] at this
    linarith
  set v : Fin d → ℝ := fun j => -ψ (Pi.single j 1) with hvdef
  have hv : ∀ u, u ⬝ᵥ v = -ψ u := by
    intro u
    calc u ⬝ᵥ v = -∑ j, u j * ψ (Pi.single j 1) := by
          simp [dotProduct, hvdef, Finset.sum_neg_distrib]
      _ = -ψ (∑ j, u j • Pi.single j 1) := by simp [map_sum, map_smul]
      _ = -ψ u := by rw [← pi_eq_sum_univ']
  have hsup : RobustMDP.Shared.supportFunction U v ≤ -c := by
    unfold RobustMDP.Shared.supportFunction
    apply csSup_le (hne.image _)
    rintro _ ⟨p, hp, rfl⟩
    change p ⬝ᵥ v ≤ -c
    rw [hv]
    linarith [h0 p hp]
  calc ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ VaR P ε v} := var_mem P ε hε0 hε1 v
    _ ≤ P {u | f u xstar ≤ 0} := by
      apply measure_mono
      intro u hu
      have hu' : u ⬝ᵥ v ≤ VaR P ε v := hu
      rw [hv] at hu'
      exact hbound u (by linarith [hvar v, hsup])

end P01013868

open MeasureTheory DataDrivenRO.Guarantee in
theorem solution {d N : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (region : (Fin N → Fin d → ℝ) → Set (Measure (Fin d → ℝ)))
    (U : (Fin N → Fin d → ℝ) → Set (Fin d → ℝ))
    (hne : ∀ S, (U S).Nonempty) (hconv : ∀ S, Convex ℝ (U S)) (hcpt : ∀ S, IsCompact (U S))
    (hstep2 : ∀ S, ∀ P ∈ region S, IsProbabilityMeasure P →
      ∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction (U S) v)
    (hcover : ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ region S}) :
    ENNReal.ofReal (1 - α) ≤
      Measure.pi (fun _ : Fin N => Pstar) {S | ImpliesGuarantee Pstar (U S) ε} := by
  refine hcover.trans (measure_mono ?_)
  intro S hS
  exact P01013868.guarantee_of_var Pstar (U S) ε hε0 hε1 (hne S) (hconv S)
    (fun v => hstep2 S Pstar hS inferInstance v)
