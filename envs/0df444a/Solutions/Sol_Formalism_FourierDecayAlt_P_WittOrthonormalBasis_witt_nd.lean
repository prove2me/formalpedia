-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WittOrthonormalBasis.witt_nd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:44.929741+00:00
-- url     : https://prove2.me/submissions/63306608-1db6-4591-a5d0-8b83e79cbb85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis
import Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_left_inv_square
import Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_onb
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_det
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WittOrthonormalBasis
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {g₁ g₂ : B.Mat k r}
    (hp1 : C2.PosPt k r z z' g₁) (hp2 : C2.PosPt k r z z' g₂)
    (hΓ : (gnB k r z z' g₁)ᴴ * Hpk k r * gnB k r z z' g₁ = (gnB k r z z' g₂)ᴴ * Hpk k r * gnB k r z z' g₂) :
    ∃ s0 ∈ B.GV k r, s0 * gnB k r z z' g₁ = gnB k r z z' g₂ := by
  classical
  obtain ⟨Bm1, h01, h11⟩ := onb hstd hp1
  obtain ⟨Bm2, h02, h12⟩ := onb hstd hp2
  have hdet : IsUnit ((gnB k r z z' g₁)ᴴ * Hpk k r * gnB k r z z' g₁).det := gram_det z z' g₁ hstd hp1
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hk := hstd.1
  generalize gnB k r z z' g₁ = V1 at *
  generalize gnB k r z z' g₂ = V2 at *
  have hBV : ∀ (V : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ)
      (Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ),
      Vᴴ * Hpk k r * Bm = 0 → Bmᴴ * Hpk k r * V = 0 := by
    intro V Bm h
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc] using this
  have hB1V := hBV V1 Bm1 h01
  have hB2V := hBV V2 Bm2 h02
  have hGW : ∀ (V : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ)
      (Bm : Matrix (Fin (2 * r + k + 1)) (Fin (k - 1) ⊕ Fin 0) ℂ),
      (Matrix.fromCols V Bm)ᴴ * Hpk k r * Matrix.fromCols V Bm =
        Matrix.fromBlocks (Vᴴ * Hpk k r * V) (Vᴴ * Hpk k r * Bm) (Bmᴴ * Hpk k r * V) (Bmᴴ * Hpk k r * Bm) := by
    intro V Bm
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  obtain ⟨W1, hW1⟩ : ∃ W, W = Matrix.fromCols V1 Bm1 := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W, W = Matrix.fromCols V2 Bm2 := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ L, L = Matrix.fromRows ((V1ᴴ * Hpk k r * V1)⁻¹ * V1ᴴ * Hpk k r) (Bm1ᴴ * Hpk k r) :=
    ⟨_, rfl⟩
  have hLW : L1 * W1 = 1 := by
    rw [hL1, hW1, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, hB1V, h11⟩
    · have e1 := Matrix.nonsing_inv_mul _ hdet
      simpa only [Matrix.mul_assoc] using e1
    · have e1 := congrArg (fun X => (V1ᴴ * Hpk k r * V1)⁻¹ * X) h01
      simpa only [Matrix.mul_assoc, Matrix.mul_zero] using e1
  have hcard : Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ (Fin (k - 1) ⊕ Fin 0)) = 2 * r + k + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hWL : W1 * L1 = 1 := left_inv_square W1 L1 hcard hLW
  have hWW : W2ᴴ * Hpk k r * W2 = W1ᴴ * Hpk k r * W1 := by
    rw [hW1, hW2, hGW, hGW, h01, h02, hB1V, hB2V, h11, h12, hΓ]
  refine ⟨W2 * L1, ?_, ?_⟩
  · show (W2 * L1)ᴴ * Hpk k r * (W2 * L1) = Hpk k r
    calc (W2 * L1)ᴴ * Hpk k r * (W2 * L1) = L1ᴴ * (W2ᴴ * Hpk k r * W2) * L1 := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = L1ᴴ * (W1ᴴ * Hpk k r * W1) * L1 := by rw [hWW]
      _ = (W1 * L1)ᴴ * Hpk k r * (W1 * L1) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hWL]; simp
  · have h : (W2 * L1) * W1 = W2 := by rw [Matrix.mul_assoc, hLW, Matrix.mul_one]
    generalize W2 * L1 = s0 at h
    rw [hW1, hW2] at h
    ext i j
    have := congrFun (congrFun h i) (Sum.inl j)
    simpa [Matrix.mul_apply] using this
end Formalism.FourierDecayAlt.P.WittOrthonormalBasis
