-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frobeniusDetVanishing_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:18.249113+00:00
-- url     : https://prove2.me/submissions/1bffa513-9256-449c-841e-72279621daa8

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Theorems.Thm_Formalism_CountingSumsFrames_frob_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : KeyVanish := by
  intro p _ F _ _ r k h hdet s
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨fun A t cols hA ht => ?_, fun a t v ha ht hv => ?_⟩
  · have hM : (Matrix.of fun l c =>
        ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)) =
        (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) =>
          t l i.1 ^ p ^ (s - A l)) *
        (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
          (h.map (fun x => x ^ p ^ s)) i.1 (cols c)) := by
      ext l c
      rw [Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c), Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.vecMul, dotProduct]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i.val < r)]
      have hz : ∑ i : {i : Fin k // ¬ i.val < r},
          t l i.1 ^ p ^ (s - A l) * (h.map (fun x => x ^ p ^ s)) i.1 (cols c) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ht l i.1 (not_lt.mp i.2), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]
      rw [hz, add_zero]
    rw [hM]
    by_contra hne
    have hu := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
    have hcard : Fintype.card {i : Fin k // i.val < r} ≤ r := by
      have := Fintype.card_le_of_injective (fun i : {i : Fin k // i.val < r} => (⟨i.1.val, i.2⟩ : Fin r))
        (fun x y hxy => by
          simp only [Fin.mk.injEq] at hxy
          exact Subtype.ext (Fin.ext hxy))
      simpa using this
    have h2 := (Matrix.rank_mul_le_left
      (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) => t l i.1 ^ p ^ (s - A l))
      (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
        (h.map (fun x => x ^ p ^ s)) i.1 (cols c))).trans ((Matrix.rank_le_card_width _).trans hcard)
    rw [hu, Fintype.card_fin] at h2
    omega
  · have hH : IsUnit (h.map (fun x => x ^ p ^ s)).det := by
      haveI : ExpChar F p := ExpChar.prime (Fact.out)
      have e : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h := by
        ext i j
        simp [iterateFrobenius_def]
      rw [e, ← RingHom.map_det]
      exact hdet.map _
    have e1 : ∀ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
        ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c :=
      fun c => frob_row h a s ha t c
    simp only [e1]
    change ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) ⬝ᵥ
      (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) = 0
    rw [Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    show t i ^ p ^ (s - a) * v i = 0
    by_cases hi : i.val < r
    · rw [hv i hi, mul_zero]
    · rw [ht i (not_lt.mp hi), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]
end Formalism.CountingSumsFrames
