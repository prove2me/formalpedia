-- Prove2me | solution 3 for ConvexRiskFn.Order.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:01:25.015237+00:00
-- url     : https://prove2.me/submissions/d36fa0d2-fbab-4061-8703-64ea982878f9

import Mathlib
import Definitions.Def_ConvexRiskFn_Order_Setting
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Theorems.Thm_ConvexRiskFn_Order_strassen_icx_coupling

-- carved verbatim out of submission 4f9bdecc-c28b-4367-bdfd-b0ebe646d4b8, lines 2442-2468

section
set_option autoImplicit false
open MeasureTheory Set
open MeasureTheory Set Finset
open scoped Classical
open Finset
open MeasureTheory Filter Topology
open MeasureTheory Set Finset StochasticOrders.MonotoneConvex
open Matrix Finset
open MeasureTheory ProbabilityTheory
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction
open scoped Topology BoundedContinuousFunction
open scoped Topology NNReal BoundedContinuousFunction
open scoped ENNReal Topology
open ConvexRiskFn.Order
open ProbabilityTheory
open MeasureTheory

lemma risk_condExp_icx_le {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (X : Ω → ℝ) (hX : MemLp X p P) :
    MemLp (P[X|m]) p P ∧ StochasticOrders.MonotoneConvex.IcxOrder P P (P[X|m]) X := by
  refine ⟨MemLp.condExp hp1 hX, ?_⟩
  intro φ _ hφ hleft hright
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hJ := hφ.map_condExp_le_univ hm hc.lowerSemicontinuous (hX.integrable hp1) hright
  calc
    (∫ ω, φ (P[X|m] ω) ∂P) ≤ ∫ ω, P[φ ∘ X|m] ω ∂P :=
      integral_mono_ae hleft integrable_condExp hJ
    _ = ∫ ω, φ (X ω) ∂P := integral_condExp hm

lemma forward {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (ρ : (Ω → ℝ) → ℝ) (h : ConsistentIcx P p ρ) :
    A2 P p ρ ∧ RiskAverse P p ρ := by
  constructor
  · intro X Y hX hY hxy
    apply h X Y hX hY
    intro φ hφ _ hiX hiY
    apply integral_mono_ae hiX hiY
    filter_upwards [hxy] with ω hω using hφ hω
  · intro m hm X hX Y _ hY
    letI : MeasurableSpace Ω := mΩ
    have hc := risk_condExp_icx_le m hm P p hp1 X hX
    have hmem : MemLp Y p P := hc.1.ae_eq hY.symm
    apply h Y X hmem hX
    intro φ hmono hcvx hiY hiX
    have hiCE : Integrable (φ ∘ P[X|m]) P := hiY.congr (hY.fun_comp φ)
    calc
      (∫ ω, φ (Y ω) ∂P) = ∫ ω, φ (P[X|m] ω) ∂P := integral_congr_ae (hY.fun_comp φ)
      _ ≤ ∫ ω, φ (X ω) ∂P := hc.2 φ hmono hcvx hiCE hiX

lemma backward_of_coupling {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ)
    (hcoupling : ∀ X Y : Ω → ℝ, MemLp X p P → MemLp Y p P →
      StochasticOrders.MonotoneConvex.IcxOrder P P X Y →
      ∃ A B : Ω → ℝ, Measurable A ∧ Measurable B ∧ MemLp A p P ∧ MemLp B p P ∧
        (∀ t : ℝ, P {ω | A ω ≤ t} = P {ω | X ω ≤ t}) ∧
        (∀ t : ℝ, P {ω | B ω ≤ t} = P {ω | Y ω ≤ t}) ∧
        A ≤ᵐ[P] P[B|MeasurableSpace.comap A inferInstance])
    (hmono : A2 P p ρ) (haverse : RiskAverse P p ρ) : ConsistentIcx P p ρ := by
  intro X Y hX hY hi
  obtain ⟨A, B, hmA, _, hlA, hlB, hdA, hdB, hAB⟩ := hcoupling X Y hX hY hi
  let m := MeasurableSpace.comap A inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hmA.comap_le
  have hlCE : MemLp (P[B|m]) p P := MemLp.condExp hp1 hlB
  have har : ρ (P[B|m]) ≤ ρ B :=
    haverse m hm B hlB _ stronglyMeasurable_condExp (Filter.EventuallyEq.refl _ _)
  calc
    ρ X = ρ A := (hρ A X hlA hX hdA).symm
    _ ≤ ρ (P[B|m]) := hmono A _ hlA hlCE hAB
    _ ≤ ρ B := har
    _ = ρ Y := hρ B Y hlB hY hdB

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hU : ∃ U : Ω → ℝ, IsUniformRV P U)
    (ρ : (Ω → ℝ) → ℝ) (hρ : DistInvariant P p ρ) :
    ConsistentIcx P p ρ ↔ A2 P p ρ ∧ RiskAverse P p ρ  := by
  constructor
  · exact forward P p hp1 ρ
  · intro h
    exact backward_of_coupling P p hp1 ρ hρ
      (fun X Y hX hY hi => ConvexRiskFn.Order.strassen_icx_coupling P p hp1 hpt hU X Y hX hY hi) h.1 h.2

end
