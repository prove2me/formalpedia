-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.polar_decomposition_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:52.328735+00:00
-- url     : https://prove2.me/submissions/c5785223-ae90-482e-bf3b-e1ff98292de5

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_unitary_conj_b
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_neg_b
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exp_sq_psd_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PolarInv := by
  intro N k X hk hX
  have hk1 : k * kᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.1 hk)
  have hk2 : kᴴ * k = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 hk)
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv hk1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, hk1, hk2⟩, rfl⟩
  have hexp : NormedSpace.exp (-(k * X * kᴴ)) = k * (NormedSpace.exp X)⁻¹ * kᴴ := by
    have : -(k * X * kᴴ) = k * (-X) * k⁻¹ := by rw [hinv]; simp
    rw [this, Matrix.exp_conj k _ hunit, Matrix.exp_neg, hinv]
  have hdet : IsUnit (NormedSpace.exp X).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.inv_eq_right_inv
    rw [hexp]
    calc k * NormedSpace.exp X * (kᴴ * (k * (NormedSpace.exp X)⁻¹ * kᴴ))
        = k * (NormedSpace.exp X * ((kᴴ * k) * (NormedSpace.exp X)⁻¹)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk2, Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, hk1]
  · exact (Matrix.isHermitian_mul_mul_conjTranspose k hX).neg
  · rw [hs_neg_b, hs_unitary_conj_b k X hk2]
  · have e : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp X * NormedSpace.exp X := by
      rw [conjTranspose_mul, (hX.exp).eq]
      calc NormedSpace.exp X * kᴴ * (k * NormedSpace.exp X)
          = NormedSpace.exp X * ((kᴴ * k) * NormedSpace.exp X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hk2, Matrix.one_mul]
    rw [e]
    exact exp_sq_psd_b X hX
end Formalism.HermitianLatticeCounting.P
