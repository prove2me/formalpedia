-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_gram_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.510554+00:00
-- url     : https://prove2.me/submissions/3be27043-a010-4d5d-ad77-c2adbe3a5abc

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_hJ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (J : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) α K) (Y : Matrix (Fin n) β K) (i : α) (j : β) :
    (fconj q X * J * Y) i j = hJ σ J (fun k => X k i) (fun k => Y k j) := by
  rw [hJ_apply]
  simp only [Matrix.mul_apply, fconj, Matrix.transpose_apply, Matrix.map_apply, hσ, Finset.sum_mul]
  rw [Finset.sum_comm]
end Formalism.FourierDecayAlt.P.S3x6
