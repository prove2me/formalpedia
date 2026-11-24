-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.zero_of_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:06.382501+00:00
-- url     : https://prove2.me/submissions/6429849c-fa3d-4a6a-8a3a-8340c7b2f8b7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_uh_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
variable {k r : ℕ}
local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
theorem _root_.solution {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    {E : Type*} [NormedAddCommGroup E] {f : MX → E} (hf : ContinuousOn f UHk)
    (hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → f (Matrix.of x) = 0)
    {g0 : MX} (hg0 : g0 ∈ UHk) : f g0 = 0 := by
  by_contra hne
  obtain ⟨V, hVo, hV⟩ := (continuousOn_iff'.mp hf) {0}ᶜ isOpen_compl_singleton
  have hg0V : g0 ∈ V := by
    have hm : g0 ∈ f ⁻¹' {0}ᶜ ∩ UHk := ⟨hne, hg0⟩
    rw [hV] at hm
    exact hm.1
  have hnull0 : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ V ∧ Matrix.of x ∈ UHk} = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx
    obtain ⟨hxV, hxU⟩ := hx
    have hm : Matrix.of x ∈ V ∩ UHk := ⟨hxV, hxU⟩
    rw [← hV] at hm
    exact fun h => hm.1 (h hxU)
  have hc0 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  let O : UHk → Set (Formalism.QuantumDeterminants.Mt k r) := fun g => {y | (g : MX)⁻¹ * Matrix.of y ∈ V}
  have hO : ∀ g, IsOpen (O g) := fun g => hVo.preimage (continuous_const.matrix_mul hc0)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcover : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of y ∈ UHk → ∃ g ∈ T, y ∈ O g := by
    intro y hy
    have hy' : y ∈ ⋃ g, O g := by
      refine Set.mem_iUnion.2 ⟨⟨Matrix.of y * g0⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg0)⟩, ?_⟩
      show (Matrix.of y * g0⁻¹)⁻¹ * Matrix.of y ∈ V
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0),
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), Matrix.mul_one]
      exact hg0V
    rw [← hTU] at hy'
    obtain ⟨g, hgT, hyg⟩ := Set.mem_iUnion₂.1 hy'
    exact ⟨g, hgT, hyg⟩
  have hnullg : ∀ g : UHk,
      μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} = 0 := by
    intro g
    have hinv := hμ.2.2.2 g g.2
    have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
    have hmeasO : MeasurableSet (O g) := (hO g).measurableSet
    have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} :=
      uh_meas.inter hmeasO
    have hcm : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul hc1
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := hcm.measurable
    rw [← hinv, Measure.map_apply hlm hmeas]
    refine measure_mono_null ?_ hnull0
    intro x hx
    obtain ⟨hxU, hxO⟩ := hx
    have hgu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh g.2
    have h1 : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) = Matrix.of x := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    have hxO' : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) ∈ V := hxO
    have hxU' : (g : MX) * Matrix.of x ∈ UHk := hxU
    refine ⟨?_, ?_⟩
    · rw [h1] at hxO'
      exact hxO'
    · have := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2) hxU'
      rwa [h1] at this
  have hUnull : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk} = 0 := by
    refine measure_mono_null
      (t := ⋃ g ∈ T, {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g})
      ?_ ((measure_biUnion_null_iff hTc).2 (fun g _ => hnullg g))
    intro x hx
    obtain ⟨g, hgT, hxg⟩ := hcover x hx
    exact Set.mem_iUnion₂.2 ⟨g, hgT, hx, hxg⟩
  apply hμ.2.1
  rw [← Measure.measure_univ_eq_zero]
  have hsplit : (Set.univ : Set (Formalism.QuantumDeterminants.Mt k r)) =
      {x | Matrix.of x ∈ UHk} ∪ {x | Matrix.of x ∉ UHk} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    exact em _
  rw [hsplit]
  exact measure_union_null hUnull hμ.2.2.1
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
