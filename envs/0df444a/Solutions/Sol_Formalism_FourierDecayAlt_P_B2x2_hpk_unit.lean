-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.hpk_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:31.212821+00:00
-- url     : https://prove2.me/submissions/d41a30e4-48ac-4acf-b575-487ff1d5a68d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r : ℕ) : IsUnit (Hpk k r).det := by
  have hsq : Hpk k r * Hpk k r = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hi := i.isLt
    have hj := j.isLt
    let m : Fin (2 * r + k + 1) :=
      ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
    have hm : m.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := rfl
    rw [Finset.sum_eq_single m]
    · simp only [Hpk, Fin.ext_iff, hm]
      split_ifs <;> first | omega | norm_num
    · intro l _ hl
      have hl' : l.val ≠ m.val := fun h => hl (Fin.ext h)
      rw [hm] at hl'
      have hl2 := l.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hl' ⊢ <;> first | omega | norm_num
    · intro h
      exact absurd (Finset.mem_univ m) h
  have h2 := congrArg Matrix.det hsq
  rw [Matrix.det_mul, Matrix.det_one] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul] at h2
  exact zero_ne_one h2
end Formalism.FourierDecayAlt.P.B2x2
