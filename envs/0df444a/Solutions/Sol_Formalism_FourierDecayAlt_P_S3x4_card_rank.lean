-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.card_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:36.40365+00:00
-- url     : https://prove2.me/submissions/35cb8b50-ac3f-4228-bf06-d050e152ad4b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_rank_eq_iff_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution [Fintype K] (n a : ℕ) :
    Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a} =
      ∏ j ∈ range a, (Fintype.card K ^ n - Fintype.card K ^ j) := by
  have e : {X : Matrix (Fin n) (Fin a) K // X.rank = a} ≃
      {f : (Fin a → K) →ₗ[K] (Fin n → K) // Function.Injective f} :=
    (Matrix.toLin' (R := K) (m := Fin n) (n := Fin a)).toEquiv.subtypeEquiv
      (p := fun X : Matrix (Fin n) (Fin a) K => X.rank = a)
      (q := fun f : (Fin a → K) →ₗ[K] (Fin n → K) => Function.Injective f)
      (fun X => rank_eq_iff_injective X)
  rw [Nat.card_congr e, card_injective, Module.finrank_fin_fun, Module.finrank_fin_fun]
end Formalism.FourierDecayAlt.P.S3x4
