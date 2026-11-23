-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.uo_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:00.966816+00:00
-- url     : https://prove2.me/submissions/d792174a-4360-4576-8d41-f9ca8c71bfc3

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ}
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι K) (hJ : Jᴴ = J) (hd : IsUnit J.det) :
    (Nat.card {g : Matrix ι ι K // gᴴ * J * g = J} : ℝ) =
      (q : ℝ) ^ ((Fintype.card ι) ^ 2) * densP (-1) q 1 (Fintype.card ι) := by
  set e := Fintype.equivFin ι
  have h := hUO (Fintype.card ι) (J.submatrix e.symm e.symm)
    (by rw [conjTranspose_submatrix, hJ]) (by rw [det_submatrix_equiv_self]; exact hd)
  rw [← h]
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Matrix.reindex e e) (fun g => ?_)
  rw [reindex_apply, gram_reindex]
  constructor
  · intro hg; rw [hg]
  · intro hg
    have := congrArg (fun M => M.submatrix e e) hg
    simpa using this
end Formalism.FourierDecayAlt.P.S3x5
