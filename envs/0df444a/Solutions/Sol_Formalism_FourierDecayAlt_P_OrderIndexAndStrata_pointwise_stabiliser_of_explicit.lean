-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.pointwise_stabiliser_of_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:01.445526+00:00
-- url     : https://prove2.me/submissions/91bd39b0-7db2-4cd4-9eff-4ec545ab6e7f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_det_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_mid_form
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution (hS : SExplicit) : FrameStabiliserPointwise := by
  intro A _ r k x hx
  unfold IsInertiaInfiniteCyclotomic
  rw [hS]
  constructor
  · rintro ⟨⟨-, -, h21, h31, h32, h, -, h22⟩, h11, h33, h12, h23⟩
    have E11 : ∀ a b, x (Sum.inl a) (Sum.inl b) = (1 : Matrix (Fin r) (Fin r) A) a b :=
      fun a b => by simpa [b11] using congrFun (congrFun h11 a) b
    have E33 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) = (1 : Matrix (Fin r) (Fin r) A) a b :=
      fun a b => by simpa [b33] using congrFun (congrFun h33 a) b
    have E21 : ∀ a b, x (Sum.inr (Sum.inl a)) (Sum.inl b) = 0 :=
      fun a b => by simpa [b21] using congrFun (congrFun h21 a) b
    have E31 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inl b) = 0 :=
      fun a b => by simpa [b31] using congrFun (congrFun h31 a) b
    have E32 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) = 0 :=
      fun a b => by simpa [b32] using congrFun (congrFun h32 a) b
    have E22 : ∀ a b, x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) = midEmb h a b :=
      fun a b => by simpa [b22] using congrFun (congrFun h22 a) b
    have E12 : ∀ a, x (Sum.inl a) (Sum.inr (Sum.inl (Sum.inr ()))) = 0 :=
      fun a => by simpa [b12] using h12 a
    have E23 : ∀ b, x (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inr b)) = 0 :=
      fun b => by simpa [b23] using h23 b
    refine ⟨fun i b => ?_, fun i => ?_, fun a i => ?_, fun i => ?_⟩
    · rcases i with i | i | i
      · rw [E11]; simp [Matrix.one_apply]
      · rw [E21]; simp
      · rw [E31]; simp
    · rcases i with i | (i | ⟨⟩) | i
      · rw [E12]; simp
      · rw [E22]; simp [midEmb]
      · rw [E22]; simp [midEmb]
      · rw [E32]; simp
    · rcases i with i | i | i
      · rw [E31]; simp
      · rw [E32]; simp
      · rw [E33]; simp [Matrix.one_apply]
    · rcases i with i | (i | ⟨⟩) | i
      · rw [E21]; simp
      · rw [E22]; simp [midEmb]
      · rw [E22]; simp [midEmb]
      · rw [E23]; simp
  · rintro ⟨C1, C2, C3, C4⟩
    have h21 : b21 x = 0 := by ext a b; simpa [b21] using C1 (Sum.inr (Sum.inl a)) b
    have h31 : b31 x = 0 := by ext a b; simpa [b31] using C1 (Sum.inr (Sum.inr a)) b
    have h11 : b11 x = 1 := by ext a b; simpa [b11, Matrix.one_apply] using C1 (Sum.inl a) b
    have h32 : b32 x = 0 := by ext a b; simpa [b32] using C3 a (Sum.inr (Sum.inl b))
    have h33 : b33 x = 1 := by
      ext a b; simpa [b33, Matrix.one_apply] using C3 a (Sum.inr (Sum.inr b))
    have h12 : ∀ a, b12 x a (Sum.inr ()) = 0 := fun a => by simpa [b12] using C2 (Sum.inl a)
    have h23 : ∀ b, b23 x (Sum.inr ()) b = 0 := fun b => by
      simpa [b23] using C4 (Sum.inr (Sum.inr b))
    have c22 : ∀ a, b22 x a (Sum.inr ()) = if a = Sum.inr () then 1 else 0 := by
      intro a
      rcases a with a | ⟨⟩
      · simpa [b22] using C2 (Sum.inr (Sum.inl (Sum.inl a)))
      · simpa [b22] using C2 (Sum.inr (Sum.inl (Sum.inr ())))
    have r22 : ∀ b, b22 x (Sum.inr ()) b = if b = Sum.inr () then 1 else 0 := by
      intro b
      rcases b with b | ⟨⟩
      · simpa [b22] using C4 (Sum.inr (Sum.inl (Sum.inl b)))
      · simpa [b22] using C4 (Sum.inr (Sum.inl (Sum.inr ())))
    obtain ⟨h, hh, he⟩ := mid_form (b22 x) (det_mid x hx h21 h31 h32) c22 r22
    refine ⟨⟨?_, ?_, h21, h31, h32, h, hh, he⟩, h11, h33, h12, h23⟩
    · rw [h11]; exact isUpUni_one'
    · rw [h33]; exact isUpUni_one'
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
