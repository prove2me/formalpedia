-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.sum_zero_lattice_spanning
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:28.773992+00:00
-- url     : https://prove2.me/submissions/973f3575-f846-46e9-9a3c-2ff53a952143

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : SumZeroLatticeSpanning := by
  intro n
  constructor
  · intro v hv
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc] at hv
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne']
      linarith
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne]
      simp only [← Fin.ext_iff]; simp
  · have : (Matrix.of fun i j : Fin n =>
        ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ
          (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))) =
        1 + Matrix.replicateCol Unit (fun _ => (1:ℚ)) * Matrix.replicateRow Unit (fun _ => (1:ℚ)) := by
      ext i j
      simp [Matrix.one_apply, Matrix.mul_apply, dotProduct_sub, sub_dotProduct, Pi.single_apply, Fin.ext_iff,
        (Fin.is_lt _).ne, (Fin.is_lt _).ne']
      by_cases h : (j:ℕ) = i
      · simp [h]
      · simp [h, Ne.symm h]
    rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct]; ring
end Formalism.HermitianLattices.LocalLatticeBases
