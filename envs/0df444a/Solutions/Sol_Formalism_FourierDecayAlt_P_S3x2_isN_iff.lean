-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isN_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:09.733707+00:00
-- url     : https://prove2.me/submissions/0a50e548-2c01-4de1-abc3-8cc457b8abad

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ IsUc (cI r k) x := by
  constructor
  · rintro ⟨h11, h33, h22, h21, h31, h32⟩
    rintro (a | a | a) (b | b | b) hij
    · simp only [cI] at hij
      rcases hij.lt_or_eq with h | h
      · have h1 : b11 x a b = 0 := h11.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b11, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b11] using h11.2 a
    · simp only [cI] at hij; have := a.2; omega
    · simp only [cI] at hij; have := a.2; omega
    · simpa [b21] using congrFun (congrFun h21 a) b
    · simpa [b22, Matrix.one_apply] using congrFun (congrFun h22 a) b
    · simp only [cI] at hij; omega
    · simpa [b31] using congrFun (congrFun h31 a) b
    · simpa [b32] using congrFun (congrFun h32 a) b
    · simp only [cI] at hij
      have hij' : (b : ℕ) ≤ a := by omega
      rcases hij'.lt_or_eq with h | h
      · have h1 : b33 x a b = 0 := h33.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b33, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b33] using h33.2 a
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inl a) (Sum.inl b) (by simp only [cI]; exact hab'.le)
      simpa [b11, Matrix.one_apply, hne] using this
    · intro a
      simpa [b11] using h (Sum.inl a) (Sum.inl a) le_rfl
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) (by simp only [cI]; have : (b : ℕ) < a := hab'; omega)
      simpa [b33, Matrix.one_apply, hne] using this
    · intro a
      simpa [b33] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr a)) le_rfl
    · ext a b
      simpa [b22, Matrix.one_apply] using h (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) le_rfl
    · ext a b
      simpa [b21] using h (Sum.inr (Sum.inl a)) (Sum.inl b) (by simp only [cI]; exact b.2.le)
    · ext a b
      simpa [b31] using h (Sum.inr (Sum.inr a)) (Sum.inl b) (by simp only [cI]; have := b.2; omega)
    · ext a b
      simpa [b32] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) (by simp only [cI]; omega)
end Formalism.FourierDecayAlt.P.S3x2
