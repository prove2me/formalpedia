-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Ff_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:45.482722+00:00
-- url     : https://prove2.me/submissions/6c05b5c0-05f9-45d4-a951-b8f6531955b8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Tm_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_UH_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) {ρ σ : ℝ} {Y : Q → m → ℂ} (hY : tb H Ep Y ∈ Kset P Q σ) {gY : Matrix m m ℂ}
    {a : Matrix Q Q ℂ} (hgY : gY ∈ UH H) (ha : IsUnit a.det) (hYe : cm Y = gY * Em * a) {g : m → m → ℂ}
    (hg : Matrix.of g ∈ UH H) :
    Ff H Ep ρ (act g Y) = (Bset Ep Em ρ).indicator 1 (rmF gY g) := by
  have e1 : cm (act g Y) = Matrix.of g * cm Y := cm_mulVec _ _
  have e2 : Tm H (cm (act g Y)) = Tm H (cm Y) := by rw [e1, Tm_mul_left hg]
  have e3 : cm (fun j => Epᴴ *ᵥ act g Y j) = Epᴴ * ((Matrix.of g * gY) * Em * a) := by
    rw [cm_mulVec, e1, hYe]; simp only [Matrix.mul_assoc]
  have e4 : Tm H (cm (act g Y)) = Tm H ((Matrix.of g * gY) * Em * a) := by
    rw [e1, hYe]; simp only [Matrix.mul_assoc]
  have key : tb H Ep (act g Y) ∈ Kset P Q ρ ↔ rmF gY g ∈ Bset Ep Em ρ := by
    constructor
    · intro h
      have h3 : qf (Tm H (cm (act g Y))) (cm (fun j => Epᴴ *ᵥ act g Y j)) ≤ ρ ^ 2 := h.2.2
      rw [e3, e4, qf_orbit F (UH_mul hg hgY) ha] at h3
      exact h3
    · intro h
      have h3 : bet Ep Em (Matrix.of g * gY) ≤ ρ ^ 2 := h
      refine ⟨?_, ?_, ?_⟩
      · show (Tm H (cm (act g Y))).PosDef
        rw [e2]; exact hY.1
      · show (Matrix.trace (Tm H (cm (act g Y)))).re ≤ 1
        rw [e2]; exact hY.2.1
      · show qf (Tm H (cm (act g Y))) (cm (fun j => Epᴴ *ᵥ act g Y j)) ≤ ρ ^ 2
        rw [e3, e4, qf_orbit F (UH_mul hg hgY) ha]; exact h3
  by_cases h : rmF gY g ∈ Bset Ep Em ρ
  · rw [Set.indicator_of_mem h]; exact Set.indicator_of_mem (key.mpr h) _
  · rw [Set.indicator_of_notMem h]; exact Set.indicator_of_notMem (fun h' => h (key.mp h')) _
end Formalism.FourierDecayAlt.P.HermitianFormFactor
