-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.haarG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:39:28.801718+00:00
-- url     : https://prove2.me/submissions/17471429-9e6e-42c0-82e4-4b25bf9275a7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_push
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_ne_zero
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_uHConj
import Theorems.Thm_Formalism_REAL_uJEmb
import Theorems.Thm_Formalism_REAL_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : HaarGExists := by
  intro k r
  obtain ⟨-, -, -, ε, -, P, hP, hPH⟩ := hpkFacts k r
  have : (muG ε).IsMulRightInvariant := ⟨fun g => unimodular _ ε g⟩
  have hemb := uJEmb _ ε
  let c : Mt k r → Mt k r := fun x => (P⁻¹ * Matrix.of x * P : Mat k r)
  let c' : Mt k r → Mt k r := fun x => (P * Matrix.of x * P⁻¹ : Mat k r)
  have hc : Continuous c := (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)
  have hc' : Continuous c' := (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const)
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have hli : Function.LeftInverse c' c := by
    intro x
    show (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = x
    have : (P * (P⁻¹ * Matrix.of x * P) * P⁻¹ : Mat k r) = (P * P⁻¹) * Matrix.of x * (P * P⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.one_mul, Matrix.mul_one]; rfl
  have hce : IsClosedEmbedding c := hli.isClosedEmbedding hc' hc
  let ι : UJ ε → Mt k r := fun g => ((g : (Mat k r)ˣ) : Mat k r)
  have hι : IsClosedEmbedding ι := hemb.1
  have hιr : ∀ x : Mat k r, inUJ ε x ↔ ∃ g, ι g = x := fun x => by
    have := Set.ext_iff.mp hemb.2 x
    exact this.symm
  refine ⟨(muG ε).map (c ∘ ι), ?_⟩
  apply haar_push (muG ε) (haar_ne_zero _) _ (hce.comp hι)
  · intro a b
    show (P⁻¹ * ((a : (Mat k r)ˣ) * (b : (Mat k r)ˣ) : Mat k r) * P : Mat k r) =
      (P⁻¹ * ((a : (Mat k r)ˣ) : Mat k r) * P) * (P⁻¹ * ((b : (Mat k r)ˣ) : Mat k r) * P)
    calc (P⁻¹ * ((a : (Mat k r)ˣ) * (b : (Mat k r)ˣ) : Mat k r) * P : Mat k r)
        = P⁻¹ * ((a : (Mat k r)ˣ) : Mat k r) * 1 * ((b : (Mat k r)ˣ) : Mat k r) * P := by
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by rw [← h2]; simp only [Matrix.mul_assoc]
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      apply (uHConj _ ε _ P hP hPH _).mpr
      have : (P * Matrix.of (c (ι x)) * P⁻¹ : Mat k r) = Matrix.of (ι x) := hli (ι x)
      show inUJ ε (P * Matrix.of (c (ι x)) * P⁻¹)
      rw [this]; exact (hιr _).mpr ⟨x, rfl⟩
    · intro hg
      obtain ⟨x, hx⟩ := (hιr _).mp ((uHConj _ ε _ P hP hPH g).mp hg)
      refine ⟨x, ?_⟩
      show (P⁻¹ * Matrix.of (ι x) * P : Mat k r) = g
      rw [hx]
      show (P⁻¹ * (P * Matrix.of g * P⁻¹) * P : Mat k r) = Matrix.of g
      calc (P⁻¹ * (P * Matrix.of g * P⁻¹) * P : Mat k r) = (P⁻¹ * P) * Matrix.of g * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.of g := by rw [h1, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.B2x3
