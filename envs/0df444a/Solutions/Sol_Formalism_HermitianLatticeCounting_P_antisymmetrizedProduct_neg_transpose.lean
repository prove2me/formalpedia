-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_neg_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:26.035588+00:00
-- url     : https://prove2.me/submissions/c815c846-957f-4c54-8140-2eb24be3d9f9

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_orderedTermProduct_neg_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) :
    doublyAntisymmetrizedProduct (fun a b => -E b a) arg = (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -arg k) := by
  simp only [doublyAntisymmetrizedProduct, orderedTermProduct_neg_transpose]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_

  rw [show ((-1 : A)) ^ n = (((-1 : ℤ) ^ n : ℤ) : A) by push_cast; rfl]
  simp only [← zsmul_eq_mul, smul_smul]
  congr 1
  ring
end Formalism.HermitianLatticeCounting.P
