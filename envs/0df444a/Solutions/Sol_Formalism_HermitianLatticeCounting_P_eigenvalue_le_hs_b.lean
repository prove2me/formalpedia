-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eigenvalue_le_hs_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:10.16626+00:00
-- url     : https://prove2.me/submissions/9012f148-2f2a-4caa-a0b1-02d80aa6cfca

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sum_sq_eigenvalues


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
theorem _root_.solution {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (i : Fin N) :
    hX.eigenvalues i ≤ hs X := by
  unfold hs
  rw [← Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues X hX]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun j => hX.eigenvalues j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
end Formalism.HermitianLatticeCounting.P
