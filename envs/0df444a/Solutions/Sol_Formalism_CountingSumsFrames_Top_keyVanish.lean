-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.keyVanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:36.586975+00:00
-- url     : https://prove2.me/submissions/9d4aff21-e299-413e-bfc3-f502f134f9fc

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
import Theorems.Thm_Formalism_CountingSumsFrames_frob_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.KeyVanish := by
  intro p _ F _ _ r k h hdet s
  classical
  haveI : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  have hpne : ∀ n, p ^ n ≠ 0 := fun n => pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hHmap : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h := by
    ext i j
    simp [iterateFrobenius_def]
  have hHdet : IsUnit (h.map (fun x => x ^ p ^ s)).det := by
    rw [hHmap, ← RingHom.map_det]
    exact hdet.map _
  refine ⟨?_, ?_⟩
  · intro A t cols hA ht
    let T' : Matrix (Fin (r + 1)) (Fin k) F := Matrix.of fun l i => t l i ^ p ^ (s - A l)
    let P : Matrix (Fin k) (Fin k) F := Matrix.diagonal fun i => if i.val < r then 1 else 0
    let G : Matrix (Fin k) (Fin (r + 1)) F := Matrix.of fun i c => (h.map (fun x => x ^ p ^ s)) i (cols c)
    have hz : (T' * P * G).det = 0 := by
      by_contra hne
      have hrank := Matrix.rank_of_isUnit (T' * P * G)
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
      have h1 : (T' * P * G).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      have h2 : P.rank ≤ r := by
        rw [Matrix.rank_diagonal]
        refine (Fintype.card_le_of_injective
          (fun i => (⟨i.1.val, by
            have hi := i.2
            by_contra hc
            simp [hc] at hi⟩ : Fin r)) ?_).trans (Fintype.card_fin r).le
        intro x y hxy
        apply Subtype.ext
        apply Fin.ext
        simpa using congrArg Fin.val hxy
      rw [hrank, Fintype.card_fin] at h1
      omega
    convert hz using 2
    ext l c
    rw [Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c)]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.vecMul, dotProduct, T', P, G, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < r
    · simp [hi, Matrix.diagonal_apply]
    · have h0 : t l i = 0 := ht l i (by omega)
      simp [hi, h0, zero_pow (hpne _)]
  · intro a t v ha ht hv
    have hrow : ∀ c, ((Matrix.vecMul t (h.map fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
        Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s) c :=
      fun c => frob_row h a s ha t c
    simp_rw [hrow]
    calc ∑ c, Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s) c *
          Matrix.vecMul v (Matrix.transpose (h.map fun x => x ^ p ^ s)⁻¹) c
        = dotProduct (Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s))
            (Matrix.vecMul v (Matrix.transpose (h.map fun x => x ^ p ^ s)⁻¹)) := rfl
      _ = dotProduct (fun i => t i ^ p ^ (s - a)) v := by
          rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
            Matrix.mul_nonsing_inv _ hHdet, Matrix.vecMul_one]
      _ = 0 := by
          simp only [dotProduct]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i.val < r
          · simp [hv i hi]
          · simp [ht i (by omega), zero_pow (hpne _)]
end Formalism.CountingSumsFrames.Top
