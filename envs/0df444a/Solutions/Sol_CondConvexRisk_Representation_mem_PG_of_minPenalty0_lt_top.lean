-- Prove2me | solution 1 for CondConvexRisk.Representation.mem_PG_of_minPenalty0_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:10:39.894988+00:00
-- url     : https://prove2.me/submissions/35e54d6a-ef4e-4095-b723-a7fbb0a85b11

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- For `A ∈ G` and `t : ℝ`, the penalty term at `t • 1_A` equals `t * (P(A) - Q(A))`. -/
theorem aux_mPG_term {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Set Ω) (hA : MeasurableSet[m] A) (t : ℝ) :
    ((t * (P.real A - Q.real A) : ℝ) : EReal) ≤
      minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q := by
  have hA' : MeasurableSet[mΩ] A := hm A hA
  set Z : Ω → ℝ := A.indicator (fun _ => t) with hZdef
  have hZmem : MemLp Z ⊤ P := (memLp_top_const t).indicator hA'
  have hZsm : StronglyMeasurable[m] Z :=
    (@stronglyMeasurable_const Ω ℝ m _ t).indicator hA
  have h0mem : MemLp (0 : Ω → ℝ) ⊤ P := MemLp.zero
  have htr := hρ.translation 0 Z h0mem hZmem hZsm
  rw [zero_add] at htr
  have hρZ : ρ Z =ᵐ[P] fun ω => -Z ω := by
    filter_upwards [htr, hρ.map_zero] with ω h1 h2
    rw [h1]
    simp [h2]
  have hintP : ∫ ω, ρ Z ω ∂P = -(P.real A * t) := by
    rw [integral_congr_ae hρZ, integral_neg, hZdef, integral_indicator_const t hA']
    simp
  have hintQ : ∫ ω, Z ω ∂Q = Q.real A * t := by
    rw [hZdef, integral_indicator_const t hA']
    simp
  unfold minPenalty₀
  refine le_iSup_of_le (⟨Z, hZmem⟩ : {X : Ω → ℝ // MemLp X ⊤ P}) ?_
  apply le_of_eq
  congr 1
  simp only
  rw [hintP, hintQ]
  ring

end CondConvexRisk.Representation

open CondConvexRisk.Representation
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Q ≪ P)
    (hfin : minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q < ⊤) :
    ∀ A : Set Ω, MeasurableSet[m] A → Q A = P A := by
  intro A hA
  obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.1 hfin
  have key : ∀ t : ℝ, t * (P.real A - Q.real A) ≤ c := by
    intro t
    have h1 := aux_mPG_term m P hm ρ hρ Q A hA t
    have h2 : ((t * (P.real A - Q.real A) : ℝ) : EReal) ≤ (c : EReal) := h1.trans hc.le
    exact_mod_cast h2
  have hd : P.real A - Q.real A = 0 := by
    by_contra hne
    have := key ((c + 1) / (P.real A - Q.real A))
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  have hreal : Q.real A = P.real A := by linarith
  have hfQ : Q A ≠ ⊤ := measure_ne_top Q A
  have hfP : P A ≠ ⊤ := measure_ne_top P A
  exact (ENNReal.toReal_eq_toReal_iff' hfQ hfP).1 hreal
