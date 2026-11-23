-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.block_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:50.6035+00:00
-- url     : https://prove2.me/submissions/92078490-b327-4157-a162-ef2c12bd6dfd

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_unit_of_gram
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_witt_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_stab_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_of_gram

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
theorem _root_.solution
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hT : Tᴴ = T) (hdT : IsUnit T.det) (hT' : T'ᴴ = T')
    (hdT' : IsUnit T'.det) :
    Nat.card {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * fromBlocks T 0 0 T' * g = fromBlocks T 0 0 T'} =
      Nat.card {X : Matrix (α ⊕ β) α K // Xᴴ * fromBlocks T 0 0 T' * X = T} *
        Nat.card {d : Matrix β β K // dᴴ * T' * d = T'} := by
  classical
  set J := fromBlocks T 0 0 T' with hJdef
  have hJ : Jᴴ = J := by rw [hJdef, fromBlocks_conjTranspose]; simp [hT, hT']
  have hdJ : IsUnit J.det := by rw [hJdef, det_fromBlocks_zero₂₁]; exact hdT.mul hdT'
  set X0 : Matrix (α ⊕ β) α K := fromRows 1 0 with hX0def
  have hX0 : X0ᴴ * J * X0 = T := by
    rw [hX0def, conjTranspose_fromRows_eq_fromCols_conjTranspose, hJdef, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
    simp
  have hch : ∀ X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T}, ∃ g, gᴴ * J * g = J ∧ g * X0 = X.1 :=
    fun X => witt_gen hW J X0 X.1 hJ hdJ (rank_of_gram J T hdT X0 hX0) (rank_of_gram J T hdT X.1 X.2)
      (by rw [hX0, X.2])
  choose γ hγ1 hγ2 using hch
  have hδ : ∀ d : Matrix β β K, fromBlocks (1 : Matrix α α K) 0 0 d * X0 = X0 := by
    intro d
    rw [hX0def, fromBlocks_mul_fromRows]; simp
  have hδ2 : ∀ d : Matrix β β K, dᴴ * T' * d = T' →
      (fromBlocks (1 : Matrix α α K) 0 0 d)ᴴ * J * fromBlocks (1 : Matrix α α K) 0 0 d = J := by
    intro d hd
    rw [hJdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hd]
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective
    (fun p : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} × {d : Matrix β β K // dᴴ * T' * d = T'} =>
      (⟨γ p.1 * fromBlocks 1 0 0 p.2.1, ?_⟩ : {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * J * g = J})) ⟨?_, ?_⟩
  · rw [conjTranspose_mul]
    calc _ = (fromBlocks (1 : Matrix α α K) 0 0 p.2.1)ᴴ * ((γ p.1)ᴴ * J * γ p.1) *
          fromBlocks (1 : Matrix α α K) 0 0 p.2.1 := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hγ1, hδ2 _ p.2.2]
  · rintro ⟨X, d⟩ ⟨X', d'⟩ h
    have h' : γ X * fromBlocks 1 0 0 d.1 = γ X' * fromBlocks 1 0 0 d'.1 := congrArg Subtype.val h
    have hX : X = X' := by
      apply Subtype.ext
      have := congrArg (fun M => M * X0) h'
      simp only [Matrix.mul_assoc, hδ, hγ2] at this
      exact this
    subst hX
    have hu : IsUnit (γ X) := (isUnit_iff_isUnit_det _).2 (unit_of_gram J _ hdJ (hγ1 X))
    have h3 := hu.mul_left_cancel h'
    rw [fromBlocks_inj] at h3
    have : d = d' := Subtype.ext h3.2.2.2
    rw [this]
  · rintro ⟨h, hh⟩
    have hXg : (h * X0)ᴴ * J * (h * X0) = T := by
      rw [conjTranspose_mul]
      calc _ = X0ᴴ * (hᴴ * J * h) * X0 := by simp only [Matrix.mul_assoc]
        _ = T := by rw [hh, hX0]
    set X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} := ⟨h * X0, hXg⟩ with hXdef
    have hu : IsUnit (γ X).det := unit_of_gram J _ hdJ (hγ1 X)
    set k := (γ X)⁻¹ * h with hk
    have hγk : γ X * k = h := by rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    have hk1 : k * X0 = X0 := by
      have e1 : γ X * X0 = h * X0 := hγ2 X
      rw [hk, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    have hk2 : kᴴ * J * k = J := by
      have : (γ X * k)ᴴ * J * (γ X * k) = J := by rw [hγk]; exact hh
      rw [conjTranspose_mul] at this
      calc _ = kᴴ * ((γ X)ᴴ * J * γ X) * k := by rw [hγ1]
        _ = kᴴ * (γ X)ᴴ * J * (γ X * k) := by simp only [Matrix.mul_assoc]
        _ = J := this
    obtain ⟨d, hd1, hd2⟩ := stab_form T T' hdT k hk1 hk2
    refine ⟨(X, ⟨d, hd2⟩), ?_⟩
    apply Subtype.ext
    show γ X * fromBlocks 1 0 0 d = h
    rw [← hd1, hγk]
end Formalism.FourierDecayAlt.P.S3x5
