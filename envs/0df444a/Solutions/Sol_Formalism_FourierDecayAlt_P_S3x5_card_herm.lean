-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:10.559958+00:00
-- url     : https://prove2.me/submissions/28b67fd8-512f-4add-b85d-9c36180eb793

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) (c : ℕ) :
    Nat.card {D : Matrix (Fin c) (Fin c) K // Dᴴ = D} = q ^ (c ^ 2) := by
  induction c with
  | zero =>
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero]
    have : Unique {D : Matrix (Fin 0) (Fin 0) K // Dᴴ = D} :=
      ⟨⟨⟨0, by simp⟩⟩, fun D => Subtype.ext (by ext i; exact i.elim0)⟩
    exact Nat.card_unique
  | succ c ih =>
    let F : ({A : Matrix (Fin c) (Fin c) K // Aᴴ = A} × (Fin c → K) × {d : K // star d = d}) →
        {D : Matrix (Fin (c + 1)) (Fin (c + 1)) K // Dᴴ = D} := fun x =>
      ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks x.1.1 (Matrix.of fun i (_ : Fin 1) => x.2.1 i)
          (Matrix.of fun i (_ : Fin 1) => x.2.1 i)ᴴ (Matrix.of fun (_ _ : Fin 1) => x.2.2.1)), by
        rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose, x.1.2,
          Matrix.conjTranspose_conjTranspose]
        congr 2
        ext i j
        simp [Matrix.conjTranspose_apply, x.2.2.2]⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨A, b, d⟩ ⟨A', b', d'⟩ h
        have h1 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val h)
        rw [Matrix.fromBlocks_inj] at h1
        obtain ⟨hA, hb, -, hd⟩ := h1
        have hb' : b = b' := by
          funext i
          exact congrFun (congrFun hb i) 0
        have hd' : d = d' := Subtype.ext (congrFun (congrFun hd 0) 0)
        have hA' : A = A' := Subtype.ext hA
        rw [hA', hb', hd']
      · rintro ⟨D, hD⟩
        set D' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm D with hD'
        have hDD : D = Matrix.reindex finSumFinEquiv finSumFinEquiv D' := by
          rw [hD', Equiv.apply_symm_apply]
        have hH : D'ᴴ = D' := by
          apply (Matrix.reindex (finSumFinEquiv (m := c) (n := 1)) (finSumFinEquiv (m := c) (n := 1))).injective
          rw [← Matrix.conjTranspose_reindex, ← hDD, hD]
        have hb := Matrix.fromBlocks_toBlocks D'
        rw [← hb, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_inj] at hH
        obtain ⟨h11, h21, h12, h22⟩ := hH
        refine ⟨⟨⟨D'.toBlocks₁₁, h11⟩, fun i => D'.toBlocks₁₂ i 0, ⟨D'.toBlocks₂₂ 0 0, ?_⟩⟩, ?_⟩
        · have := congrFun (congrFun h22 0) 0
          simpa [Matrix.conjTranspose_apply] using this
        · apply Subtype.ext
          show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = D
          rw [hDD]
          congr 1
          conv_rhs => rw [← hb]
          have e12 : (Matrix.of fun i (_ : Fin 1) => D'.toBlocks₁₂ i 0) = D'.toBlocks₁₂ := by
            ext i j; rw [Subsingleton.elim j 0]; rfl
          have e22 : (Matrix.of fun (_ _ : Fin 1) => D'.toBlocks₂₂ 0 0) = D'.toBlocks₂₂ := by
            ext i j; rw [Subsingleton.elim j 0, Subsingleton.elim i 0]; rfl
          rw [e12, e22, h12]
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_prod, ih, card_fix hs hc, Nat.card_fun,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hc, Fintype.card_fin]
    ring
end Formalism.FourierDecayAlt.P.S3x5
