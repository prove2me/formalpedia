-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.conjugation_invariant_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:21:26.759958+00:00
-- url     : https://prove2.me/submissions/337a67e2-897d-49af-80ba-46d182a05406

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_unitary_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_mul_unitary
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_conj
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ConjInv := by
  intro N ep k X hk hkb hX hXb
  have hu : IsUnit k := ⟨⟨k, kᴴ, unitary_right hk, unitary_left hk⟩, rfl⟩
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (unitary_left hk)
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul k hX, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero; intro d _
    by_cases hd : ep d = ep b
    · have : ∑ c, star (k c a) * X c d = 0 := by
        apply Finset.sum_eq_zero; intro c _
        by_cases hc : ep c = ep a
        · rw [hXb c d (by rw [hc, hab, hd]), mul_zero]
        · rw [hkb c a hc, star_zero, zero_mul]
      rw [this, zero_mul]
    · rw [hkb d b hd, mul_zero]
  · rw [hs_mul_unitary hk, hs_unitary_mul (unitary_conj hk)]
  · rw [← hinv]; exact (Matrix.exp_conj' k X hu).symm
end Formalism.HermitianLatticeCounting.P
