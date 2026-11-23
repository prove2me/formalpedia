-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.rtt_mul_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:58.330004+00:00
-- url     : https://prove2.me/submissions/69aaca3f-b280-4803-a755-f64002e444f4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entries_mem_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_second_embedding_commute


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (M N : K → M2 B) (Y Y' : K) (hM : RTTat M Y Y') (hN : RTTat N Y Y')
    (hc : ∀ Y Y' i j k l, Commute (M Y i j) (N Y' k l)) : RTTat (fun Y => M Y * N Y) Y Y' := by
  unfold RTTat at hM hN ⊢
  set Rm := (Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B with hRm
  have c1 : E1 (N Y') * E2 (M Y) = E2 (M Y) * E1 (N Y') :=
    first_second_embedding_commute _ _ fun i j k l => ((hc Y Y' k l i j).eq).symm
  have c2 : E1 (M Y') * E2 (N Y) = E2 (N Y) * E1 (M Y') :=
    first_second_embedding_commute _ _ fun i j k l => (hc Y' Y i j k l).eq
  show Rm * E1 (M Y' * N Y') * E2 (M Y * N Y) = E2 (M Y * N Y) * E1 (M Y' * N Y') * Rm
  rw [first_embedding_mul, entries_mem_mul]
  calc Rm * (E1 (M Y') * E1 (N Y')) * (E2 (M Y) * E2 (N Y))
      = Rm * E1 (M Y') * (E1 (N Y') * E2 (M Y)) * E2 (N Y) := by simp only [mul_assoc]
    _ = Rm * E1 (M Y') * (E2 (M Y) * E1 (N Y')) * E2 (N Y) := by rw [c1]
    _ = (Rm * E1 (M Y') * E2 (M Y)) * E1 (N Y') * E2 (N Y) := by simp only [mul_assoc]
    _ = E2 (M Y) * E1 (M Y') * (Rm * E1 (N Y') * E2 (N Y)) := by rw [hM]; simp only [mul_assoc]
    _ = E2 (M Y) * E1 (M Y') * (E2 (N Y) * E1 (N Y') * Rm) := by rw [hN]
    _ = E2 (M Y) * (E1 (M Y') * E2 (N Y)) * E1 (N Y') * Rm := by simp only [mul_assoc]
    _ = E2 (M Y) * (E2 (N Y) * E1 (M Y')) * E1 (N Y') * Rm := by rw [c2]
    _ = (E2 (M Y) * E2 (N Y)) * (E1 (M Y') * E1 (N Y')) * Rm := by simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd4
