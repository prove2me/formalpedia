-- Prove2me | solution 1 for Ehrhart.Volume.momentNormalizedDiagonalRadialWeakTests_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/27add995-029f-482a-9bcd-a6e87db3393c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_tendsto_moving_lattice_sum_of_ae_tag_convergence
import Theorems.Thm_Ehrhart_BergmanJetDiagonalObservableLatticeIdentity_integral_momentNormalizedDiagonal_eq_laurentObservable_average
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_norm_momentTaggedLaurentObservable_le_of_mem_interior
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
import Theorems.Thm_Ehrhart_Volume_interior_dualGradient_average_eq_sourceGibbs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Volume
open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
namespace Ehrhart.Volume
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F))) := by
  intro f
  have hf : Continuous (fun x : Space n => f x) := f.continuous
  have hC : ∀ x : Space n, |f x| ≤ ‖f‖ := fun x => by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  obtain ⟨B, hB, hsubset⟩ :=
    BoxIntegral.le_hasIntegralVertices_of_isBounded
      (K.compact.isBounded.subset interior_subset)
  let G : ℕ → Space n → ℝ := fun k u =>
    momentTaggedLaurentObservable F k (fun x => f x) u
  let g : Space n → ℝ := fun u =>
    f (SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential) u)
  have hbound :
      ∀ k : ℕ, 0 < k → ∀ u ∈ interior K.carrier,
        u ∈ scaledIntegerLattice n k → ‖G k u‖ ≤ ‖f‖ := by
    intro k hk u hu hulattice
    exact norm_momentTaggedLaurentObservable_le_of_mem_interior
      F htransport (fun x => f x) hf ‖f‖ hC k u hu
  have hpoint :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        Tendsto
          (fun k : ℕ =>
            (interior K.carrier).indicator
              (G (k + 1))
              (BoxIntegral.unitPartition.tag (k + 1)
                (BoxIntegral.unitPartition.index (k + 1) x)))
          atTop (𝓝 ((interior K.carrier).indicator g x)) :=
    ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
      F htransport (fun x => f x) hf ‖f‖ hC
  have hscaled :=
    tendsto_moving_lattice_sum_of_ae_tag_convergence
      B hB (interior K.carrier) hsubset
      isOpen_interior.measurableSet
      G g ‖f‖ (norm_nonneg f) hbound hpoint
  have hscaled' :
      Tendsto
        (fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            G (k + 1) (u : Space n)) /
              (((k + 1 : ℕ) : ℝ) ^ n))
        atTop
        (𝓝 (∫ u in interior K.carrier,
          g u ∂(volume : Measure (Space n)))) := by
    simpa [monomialIndex] using hscaled
  have haverage :
      Tendsto
        (fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            G (k + 1) (u : Space n)) /
              (bergmanDimension K (k + 1) : ℝ))
        atTop
        (𝓝 ((∫ u in interior K.carrier,
          g u ∂(volume : Measure (Space n))) /
            normalizedVolume K.carrier)) := by
    have hquot := hscaled'.div
      ((bergmanDimension_div_pow_tendsto_volume K).comp
        (Filter.tendsto_add_atTop_nat 1)) K.volume_pos.ne'
    refine hquot.congr' (Filter.Eventually.of_forall fun k => ?_)
    exact div_div_div_cancel_right₀ (by positivity)
      (∑' u : monomialIndex K (k + 1),
        G (k + 1) (u : Space n))
      (bergmanDimension K (k + 1) : ℝ)
  have hG :
      (fun k : ℕ =>
        (∑' u : monomialIndex K (k + 1),
          G (k + 1) (u : Space n)) /
            (bergmanDimension K (k + 1) : ℝ)) =
      fun k : ℕ =>
        (∑' u : monomialIndex K (k + 1),
          momentNormalizedLaurentObservable
            F (k + 1) (fun x => f x) (u : Space n)) /
            (bergmanDimension K (k + 1) : ℝ) := by
    funext k
    congr 1
    apply tsum_congr
    intro u
    change
      momentTaggedLaurentObservable
        F (k + 1) (fun x => f x) (u : Space n) =
        momentNormalizedLaurentObservable
          F (k + 1) (fun x => f x) (u : Space n)
    simp [momentTaggedLaurentObservable,
      Nat.zero_lt_succ k, u.property.2]
  rw [hG] at haverage
  have hlimit :
      (∫ u in interior K.carrier,
        g u ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
        ∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F) :=
    interior_dualGradient_average_eq_sourceGibbs
      F htransport (fun x => f x) hf
  rw [hlimit] at haverage
  have hdiagonal :
      (fun k : ℕ =>
        ∫ x : Space n,
          f x * normalizedDiagonalDensity
            K (k + 1) (momentNormalizedPotential F) x
            ∂(volume : Measure (Space n))) =
        fun k : ℕ =>
          (∑' u : monomialIndex K (k + 1),
            momentNormalizedLaurentObservable
              F (k + 1) (fun x => f x) (u : Space n)) /
              (bergmanDimension K (k + 1) : ℝ) := by
    funext k
    exact integral_momentNormalizedDiagonal_eq_laurentObservable_average
      K (Nat.zero_lt_succ k) F htransport (fun x => f x) hf ‖f‖ hC
  rw [← hdiagonal] at haverage
  exact haverage
end Ehrhart.Volume
