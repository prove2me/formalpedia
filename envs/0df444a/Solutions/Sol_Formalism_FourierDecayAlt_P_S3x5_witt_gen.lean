-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.witt_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:41.023642+00:00
-- url     : https://prove2.me/submissions/b82fa6f3-7972-4795-b8a6-2896ad8c10dc

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
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α] (J : Matrix ν ν K)
    (X Y : Matrix ν α K) (hJ : Jᴴ = J) (hd : IsUnit J.det) (hX : X.rank = Fintype.card α)
    (hY : Y.rank = Fintype.card α) (h : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix ν ν K, gᴴ * J * g = J ∧ g * X = Y := by
  set e := Fintype.equivFin ν
  set f := Fintype.equivFin α
  obtain ⟨g, hg1, hg2⟩ := hW _ _ (J.submatrix e.symm e.symm) (X.submatrix e.symm f.symm)
    (Y.submatrix e.symm f.symm) (by rw [conjTranspose_submatrix, hJ])
    (by rw [det_submatrix_equiv_self]; exact hd) (by rw [rank_submatrix, hX]) (by rw [rank_submatrix, hY])
    (by rw [gram_reindex, gram_reindex, h])
  refine ⟨g.submatrix e e, ?_, ?_⟩
  · have h1 := gram_reindex e e (J.submatrix e.symm e.symm) g
    rw [hg1] at h1
    simpa using h1
  · have h2 := congrArg (fun M => M.submatrix e f) hg2
    simp only [← submatrix_mul_equiv g _ e e f] at h2
    simpa using h2
end Formalism.FourierDecayAlt.P.S3x5
