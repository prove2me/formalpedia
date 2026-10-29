-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:54:29.237897+00:00
-- url     : https://prove2.me/submissions/bf2f1436-d595-4b98-83db-69ca77182a48

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
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
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b : ℝ) (hb : 0 ≤ b)
    (D : Ω × ℝ → ℝ) (hD : Measurable D)
    (B : Set ℝ) (hB : MeasurableSet B)
    (E : Set (Ω × ℝ))
    (hEdef : E = {z : Ω × ℝ |
      twoSidedExitUpTime X b z.1 < ⊤ ∧
        (((twoSidedExitUpTime X b z.1).toNNReal : ℝ)) ≤ z.2})
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (hFresh : ∀ (ω : Ω) (r : ℝ),
      H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) (D (ω, r)))
    (hReset : ∀ z : Ω × ℝ, z ∈ E →
      H (Real.toNNReal
        (z.2 - ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
        (fun s : ℝ≥0 =>
          X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
            X.X ((twoSidedExitUpTime X b z.1).toNNReal) z.1) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) (D z)) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp (E ∩ D ⁻¹' B) = Qp E * Qp (D ⁻¹' B)) := by
  classical
  let density : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity density
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let E0 : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
  have hE0 : E = E0 := hEdef
  let W : Ω × ℝ → ℝ≥0∞ := fun z => if D z ∈ B then 1 else 0
  have hDB : MeasurableSet (D ⁻¹' B) := hB.preimage hD
  have hW : Measurable W :=
    Measurable.ite hDB measurable_const measurable_const
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge : Measurable age := hT.ennreal_toNNReal
  have hE0Meas : MeasurableSet E0 :=
    (measurableSet_lt (hT.comp measurable_fst) measurable_const).inter
      (measurableSet_le ((hAge.coe_nnreal_real).comp measurable_fst)
        measurable_snd)
  have hEMeas : MeasurableSet E := by simpa only [hE0] using hE0Meas
  let M : ℝ≥0∞ := ∫⁻ r : ℝ, (∫⁻ ω : Ω,
    density (ω, r) *
      H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
      ∂(expMeasure p)
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hProd : Measurable (fun z : Ω × ℝ => density z * W z) :=
    hJoint.mul hW
  have hM : M = (∫⁻ z : Ω × ℝ, W z ∂Qp) := by
    calc
      M = (∫⁻ r : ℝ, (∫⁻ ω : Ω,
          density (ω, r) * W (ω, r) ∂P) ∂(expMeasure p)) := by
        dsimp [M]
        congr 1
        funext r
        congr 1
        funext ω
        rw [hFresh ω r]
        simp only [Set.indicator, W]
      _ = ∫⁻ z : Ω × ℝ, density z * W z ∂(P.prod (expMeasure p)) := by
        exact (MeasureTheory.lintegral_prod_symm
          (fun z : Ω × ℝ => density z * W z) hProd.aemeasurable).symm
      _ = ∫⁻ z : Ω × ℝ, W z ∂Qp := by
        rw [lintegral_withDensity_eq_lintegral_mul
          (P.prod (expMeasure p)) hJoint hW]
        rfl
  have hReg :=
    avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
      X b hb θ p hθ hp H hH
  change (∫⁻ z in E0,
      H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
        (fun s : ℝ≥0 =>
          X.X (age z.1 + s) z.1 - X.X (age z.1) z.1) ∂Qp) =
    Qp E0 * M at hReg
  rw [← hE0] at hReg
  have hFactorE :
      (∫⁻ z in E, W z ∂Qp) =
        Qp E * (∫⁻ z, W z ∂Qp) := by
    calc
      _ = (∫⁻ z in E,
          H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
            (fun s : ℝ≥0 =>
              X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
          ∂Qp) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem hEMeas] with z hz
        exact (hReset z hz).symm
      _ = Qp E * M := hReg
      _ = _ := by rw [hM]
  have hMassWhole : (∫⁻ z, W z ∂Qp) = Qp (D ⁻¹' B) := by
    change (∫⁻ z, (D ⁻¹' B).indicator
      (fun _ => (1 : ℝ≥0∞)) z ∂Qp) = _
    exact lintegral_indicator_one hDB
  have hMassE :
      (∫⁻ z in E, W z ∂Qp) = Qp (E ∩ D ⁻¹' B) := by
    change (∫⁻ z, (D ⁻¹' B).indicator
      (fun _ => (1 : ℝ≥0∞)) z ∂(Qp.restrict E)) = _
    calc
      _ = (Qp.restrict E) (D ⁻¹' B) :=
        lintegral_indicator_one hDB
      _ = Qp (D ⁻¹' B ∩ E) := Measure.restrict_apply hDB
      _ = Qp (E ∩ D ⁻¹' B) := by rw [Set.inter_comm]
  change Qp (E ∩ D ⁻¹' B) = Qp E * Qp (D ⁻¹' B)
  calc
    Qp (E ∩ D ⁻¹' B) = (∫⁻ z in E, W z ∂Qp) := hMassE.symm
    _ = Qp E * (∫⁻ z, W z ∂Qp) := hFactorE
    _ = Qp E * Qp (D ⁻¹' B) := by rw [hMassWhole]
