-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.s3_split_frame_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:55.165057+00:00
-- url     : https://prove2.me/submissions/092705e9-a858-454b-8b00-c941fe687ee6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_rank
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.SplitFrameCount := by
  intro K _ _ n a R
  classical
  let e : {p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin a) K //
        p.1.rank = a ∧ p.2.rank = a ∧ p.2ᵀ * p.1 = Rᵀ} ≃
      Σ X₁ : {X : Matrix (Fin n) (Fin a) K // X.rank = a},
        {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁.1 = Rᵀ} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  let _ : Fintype {X : Matrix (Fin n) (Fin a) K // X.rank = a} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma,
    Finset.sum_congr rfl (fun X₁ _ => card_fibre n a R X₁.1 X₁.2), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_rank, smul_eq_mul, mul_assoc]
end Formalism.FourierDecayAlt.P
