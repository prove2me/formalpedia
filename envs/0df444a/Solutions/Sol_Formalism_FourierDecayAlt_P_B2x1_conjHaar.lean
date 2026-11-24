-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.conjHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:44.361823+00:00
-- url     : https://prove2.me/submissions/7c782e5c-cc9d-473e-8f98-5657d29fdb22

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_rmulF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : ConjHaar := by
  intro k r U μ a hU ha h1 h2 hμ
  have hm := (conjM_cont a).measurable
  have haa : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a ha
  have haa' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hm (show IsOpen (Uᶜ : Set (Mt k r)) from hU.closed.isOpen_compl).measurableSet]
    refine measure_mono_null ?_ hμ.conc
    intro x hx hxU
    exact hx (h1 x hxU)
  · intro u hu
    rw [Measure.map_map (lmulM_cont u).measurable hm]
    have : (lmulM u ∘ conjM a : Mt k r → Mt k r) = conjM a ∘ lmulM (a⁻¹ * u * a) := by
      funext x
      show u * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * u * a * Matrix.of x) * a⁻¹
      have : a * (a⁻¹ * u * a * Matrix.of x) = (a * a⁻¹) * u * a * Matrix.of x := by simp only [Matrix.mul_assoc]
      rw [this, haa, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    rw [this, ← Measure.map_map hm (lmulM_cont _).measurable, hμ.left _ (h2 u hu)]
  · intro u hu
    rw [Measure.map_map (rmulF_cont u).measurable hm]
    have : (rmulF u ∘ conjM a : Mt k r → Mt k r) = conjM a ∘ rmulF (a⁻¹ * u * a) := by
      funext x
      show (a * Matrix.of x * a⁻¹) * u = a * (Matrix.of x * (a⁻¹ * u * a)) * a⁻¹
      have : a * (Matrix.of x * (a⁻¹ * u * a)) * a⁻¹ = a * Matrix.of x * a⁻¹ * u * (a * a⁻¹) := by
        simp only [Matrix.mul_assoc]
      rw [this, haa, Matrix.mul_one]
    rw [this, ← Measure.map_map hm (rmulF_cont _).measurable, hμ.right _ (h2 u hu)]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    have hsub : (conjM a : Mt k r → Mt k r) ⁻¹' K ⊆ (conjM a⁻¹ : Mt k r → Mt k r) '' K := by
      intro x hx
      refine ⟨conjM a x, hx, ?_⟩
      show a⁻¹ * (a * Matrix.of x * a⁻¹) * a⁻¹⁻¹ = x
      rw [Matrix.nonsing_inv_nonsing_inv a ha]
      have : a⁻¹ * (a * Matrix.of x * a⁻¹) * a = (a⁻¹ * a) * Matrix.of x * (a⁻¹ * a) := by simp only [Matrix.mul_assoc]
      rw [this, haa', Matrix.one_mul, Matrix.mul_one]; rfl
    exact lt_of_le_of_lt (measure_mono hsub) (hμ.finite_compact _ (hK.image (conjM_cont a⁻¹)))
  · intro h0
    apply hμ.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.mp this
end Formalism.FourierDecayAlt.P.B2x1
