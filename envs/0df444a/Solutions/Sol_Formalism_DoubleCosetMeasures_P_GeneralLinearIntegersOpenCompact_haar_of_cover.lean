-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:19.617692+00:00
-- url     : https://prove2.me/submissions/a5969a7f-ef8a-46bc-b116-56e64f2c3b14

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (K₁ : Subgroup G) (hKo : IsOpen (K₁ : Set G))
    (hKc : IsCompact (K₁ : Set G)) (L : ℕ → Subgroup G) (hLo : ∀ m, IsOpen (L m : Set G))
    (hLc : ∀ m, IsCompact (L m : Set G)) (hcov : ∀ g : G, ∃ m, g ∈ L m) :
    ∃ μ : Measure G, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (K₁ : Set G) = 1 := by
  have hint : (interior (K₁ : Set G)).Nonempty := ⟨1, by rw [hKo.interior_eq]; exact K₁.one_mem⟩
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K₁, hKc⟩, hint⟩
  have : LocallyCompactSpace G :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K₁.one_mem)
  have : SigmaCompactSpace G := ⟨⟨fun m => (L m : Set G), hLc,
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (hcov g)⟩⟩
  refine ⟨haarMeasure K₀, inferInstance, ?_, inferInstance, haarMeasure_self⟩
  constructor
  intro g
  obtain ⟨m, hm⟩ := hcov g
  have hreg : (Measure.map (· * g) (haarMeasure K₀)).Regular := Regular.map (Homeomorph.mulRight g)
  have e := isMulLeftInvariant_eq_smul_of_regular (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀)
  have hL : Measure.map (· * g) (haarMeasure K₀) (L m) = haarMeasure K₀ (L m) := by
    rw [map_apply (measurable_mul_const g) (hLo m).measurableSet]
    congr 1
    ext x
    simp [Set.mem_preimage, (L m).mul_mem_cancel_right hm]
  have hpos : haarMeasure K₀ (L m) ≠ 0 := ((hLo m).measure_pos _ ⟨1, (L m).one_mem⟩).ne'
  have hfin : haarMeasure K₀ (L m) ≠ ⊤ := (hLc m).measure_lt_top.ne
  have hc : haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) = 1 := by
    have h2 := congrArg (fun ν : Measure G => ν (L m)) e
    simp only [hL, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : (1 : ENNReal) * haarMeasure K₀ (L m) =
        (haarScalarFactor (Measure.map (· * g) (haarMeasure K₀)) (haarMeasure K₀) : ENNReal) *
          haarMeasure K₀ (L m) := by rw [one_mul]; exact h2
    have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
    exact_mod_cast h4.symm
  rw [hc, one_smul] at e
  exact e
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
