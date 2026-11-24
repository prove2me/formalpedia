-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gg_antidiag_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:51.989086+00:00
-- url     : https://prove2.me/submissions/97fbf162-eadc-42f8-a341-b36454402b78

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] (t : R) (s : ℕ) :
    (Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0).det =
      (-1) ^ (s.choose 2) * t ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last s)]
    · have : ((Matrix.of fun i j : Fin (s + 1) => if (i : ℕ) + (j : ℕ) + 1 = s + 1 then t else 0).submatrix
          Fin.succ (Fin.last s).succAbove) =
          Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0 := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ,
          Fin.val_castSucc]
        congr 1
        exact propext ⟨fun h => by omega, fun h => by omega⟩
      rw [this, ih]
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_last, zero_add, if_true]
      have hc : (s + 1).choose 2 = s + s.choose 2 := by
        rw [Nat.choose_succ_succ' s 1, Nat.choose_one_right]
      rw [hc]
      ring
    · intro j _ hj
      have : ¬ (((0 : Fin (s + 1)) : ℕ) + (j : ℕ) + 1 = s + 1) := by
        intro h
        apply hj
        ext
        simp at h ⊢
        omega
      simp only [Matrix.of_apply, this, if_false]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.HermitianLatticeCounting.P
