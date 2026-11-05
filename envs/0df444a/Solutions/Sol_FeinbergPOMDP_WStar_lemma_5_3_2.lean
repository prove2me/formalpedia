-- Prove2me | solution 2 for FeinbergPOMDP.WStar.lemma_5_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:36:32.650361+00:00
-- url     : https://prove2.me/submissions/7e168b57-17ae-4911-a714-c5125ce06d29

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

theorem solution : ¬ (∀ {X Y A : Type}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q))
    (O₁ O₂ : Set X) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂),
    (∀ (C : {C : Set Y // MeasurableSet C}) (p : ProbabilityMeasure X × A),
        |RFamily P Q (O₁ \ O₂) C p| ≤ 1) ∧
    REquicontinuous P Q (O₁ \ O₂)) := by
  intro h
  have hsc : SecondCountableTopology (ULift.{0} ℝ) :=
    Homeomorph.ulift.{0} (X := ℝ).isInducing.secondCountableTopology
  have hsc2 : SecondCountableTopology (ULift.{0} ℝ) :=
    Homeomorph.ulift.{0} (X := ℝ).isInducing.secondCountableTopology
  have hsc3 : SecondCountableTopology (ULift.{0} ℝ) :=
    Homeomorph.ulift.{0} (X := ℝ).isInducing.secondCountableTopology
  let g : ULift.{0} ℝ × ULift.{0} ℝ → ULift.{0} ℝ := fun p => ⟨p.2.down⟩
  have hgc : Continuous g := continuous_uliftUp.comp (continuous_uliftDown.comp continuous_snd)
  let P : Kernel (ULift.{0} ℝ × ULift.{0} ℝ) (ULift.{0} ℝ) :=
    Kernel.deterministic g hgc.measurable
  let Q : Kernel (ULift.{0} ℝ × ULift.{0} ℝ) (ULift.{0} ℝ) :=
    Kernel.const _ (Measure.dirac ⟨0⟩)
  have hP : IsWeaklyContinuous (kernelPM P) := by
    intro s ss hss
    have : ∀ p, kernelPM P p = diracProba (g p) := fun p => rfl
    simp only [this]
    exact ((continuous_diracProba.comp hgc).tendsto s).comp hss
  have hQ : IsTVContinuous (kernelPM Q) := by
    intro s ss hss ε hε
    exact ⟨0, fun n _ f _ _ => by
      have e : ∫ t, f t ∂(kernelPM Q (ss n) : Measure _) =
          ∫ t, f t ∂(kernelPM Q s : Measure _) := rfl
      simp only [e, sub_self, abs_zero]; exact hε.le⟩
  have hO : IsOpen {x : ULift.{0} ℝ | 0 < x.down} := isOpen_lt continuous_const continuous_uliftDown
  obtain ⟨-, hR⟩ := @h (ULift.{0} ℝ) (ULift.{0} ℝ) (ULift.{0} ℝ) _ _ hsc _ _ _ _ hsc2 _ _
    _ _ hsc3 _ _ P _ Q _ hP hQ {x : ULift.{0} ℝ | 0 < x.down} ∅ hO isOpen_empty
  -- value of R((O₁ \ ∅) × 𝕐 | z, a)
  have hval : ∀ (z : ProbabilityMeasure (ULift.{0} ℝ)) (a : ULift.{0} ℝ),
      RFamily P Q ({x : ULift.{0} ℝ | 0 < x.down} \ ∅) ⟨Set.univ, MeasurableSet.univ⟩ (z, a)
        = if 0 < a.down then 1 else 0 := by
    intro z a
    have hco : ∀ (ν : ProbabilityMeasure (ULift.{0} ℝ × ULift.{0} ℝ)) (S : Set _),
        ((ν S : ℝ≥0) : ℝ) = ((ν : Measure _) S).toReal := fun ν S => by
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
    simp only [RFamily]
    rw [hco]
    simp only [jointLaw, ProbabilityMeasure.coe_mk, Set.sdiff_empty]
    rw [Measure.compProd_apply_prod hO.measurableSet MeasurableSet.univ]
    simp only [Q, Kernel.comap_apply, Kernel.const_apply, measure_univ, lintegral_const,
      one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [Measure.bind_apply hO.measurableSet (Kernel.aemeasurable _)]
    simp only [P, Kernel.comap_apply, Kernel.deterministic_apply, g,
      Measure.dirac_apply' _ hO.measurableSet, lintegral_const, measure_univ, mul_one]
    by_cases ha : 0 < a.down <;> simp [Set.indicator, ha]
  obtain ⟨N, hN⟩ := hR (diracProba ⟨0⟩) ⟨0⟩ (fun _ => diracProba ⟨0⟩)
    (fun n => ⟨1 / ((n : ℝ) + 1)⟩) tendsto_const_nhds
    ((continuous_uliftUp.tendsto _).comp tendsto_one_div_add_atTop_nhds_zero_nat)
    (1 / 2) (by norm_num)
  have := hN N le_rfl ⟨Set.univ, MeasurableSet.univ⟩
  rw [hval, hval] at this
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  simp only [hpos, if_true, lt_irrefl, if_false] at this
  norm_num at this
