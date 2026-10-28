-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:47:32.371574+00:00
-- url     : https://prove2.me/submissions/6931887c-b8ca-46cb-9efc-754665cb62a0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let D : Set Ω := {ω | T ω < ⊤}
     let discount : ℝ≥0 → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E,
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
       ∂Qp) =
     (∫⁻ ω in D, discount (age ω) ∂P) *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let D : Set Ω := {ω | T ω < ⊤}
  let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
  let discount : ℝ≥0 → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let K : Ω × ℝ → ℝ≥0∞ := fun z => H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
    (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
  let M : ℝ≥0∞ := ∫⁻ r : ℝ, (∫⁻ ω,
    ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω -
      (Real.toNNReal r : ℝ) * X.ψ θ)) *
    H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P) ∂(expMeasure p)
  let Dn : ℕ → Set Ω := fun n => {ω | T ω < (n : ℝ≥0∞)}
  let En : ℕ → Set (Ω × ℝ) := fun n => {z | T z.1 < (n : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2}
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge : Measurable age := hT.ennreal_toNNReal
  have hDn (n : ℕ) : MeasurableSet (Dn n) := measurableSet_lt hT measurable_const
  have hEn (n : ℕ) : MeasurableSet (En n) := by
    exact (measurableSet_lt (hT.comp measurable_fst) measurable_const).inter
      (measurableSet_le ((hAge.coe_nnreal_real).comp measurable_fst) measurable_snd)
  have hDunion : D = ⋃ n : ℕ, Dn n := by
    simpa only [D, Dn, T] using (avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion X b).1
  have hEunion : E = ⋃ n : ℕ, En n := by
    simpa only [E, En, T, age] using (avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion X b).2
  have hDmono : Monotone Dn := by
    intro m n hmn ω hw; change T ω < (m : ℝ≥0∞) at hw; exact lt_of_lt_of_le hw (by exact_mod_cast hmn)
  have hEmono : Monotone En := by
    intro m n hmn z hz; change T z.1 < (m : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2 at hz; exact ⟨lt_of_lt_of_le hz.1 (by exact_mod_cast hmn), hz.2⟩
  have hCap (n : ℕ) : (Qp.withDensity K) (En n) =
      (P.withDensity (fun ω => discount (age ω))) (Dn n) * M := by
    exact avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
      X b hb n θ p hθ hp H hH
  have hEmeas : MeasurableSet E := by rw [hEunion]; exact MeasurableSet.iUnion hEn
  have hDmeas : MeasurableSet D := by rw [hDunion]; exact MeasurableSet.iUnion hDn
  change (∫⁻ z in E, K z ∂Qp) =
    (∫⁻ ω in D, discount (age ω) ∂P) * M
  rw [← withDensity_apply K hEmeas, ← withDensity_apply (fun ω => discount (age ω)) hDmeas,
      hEunion, hDunion, hEmono.measure_iUnion, hDmono.measure_iUnion]
  simp_rw [hCap]
  exact (ENNReal.iSup_mul (fun n => (P.withDensity (fun ω => discount (age ω))) (Dn n)) M).symm
