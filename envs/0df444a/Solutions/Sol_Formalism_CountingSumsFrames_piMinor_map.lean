-- Prove2me | solution 1 for Formalism.CountingSumsFrames.piMinor_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:26.341737+00:00
-- url     : https://prove2.me/submissions/13fe47f4-6651-4e28-8975-a6ebed729626

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {p r k : ℕ} [Fact p.Prime] {F A : Type} [Field F] [CharP F p] [CommRing A] [Algebra F A]
    [Nontrivial A] (H : Matrix (Fin r) (Fin k) F) (pos : Fin r → ℕ) (t : Fin r → Fin r → A) (zj : ℕ)
    (cols : Fin r → Fin k) (hpos : ∀ l, pos l ≤ zj) :
    piMinor p r k (H.map (algebraMap F A)) pos t zj cols =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)).det *
        algebraMap F A ((H.submatrix id cols).det ^ p ^ zj) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  have : ExpChar A p := ExpChar.prime (Fact.out : p.Prime)
  have : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  let g : F →+* A := (algebraMap F A).comp (iterateFrobenius F p zj)
  have hg : ∀ x, g x = algebraMap F A (x ^ p ^ zj) := fun x => by
    simp [g, iterateFrobenius_def]
  have hmat : (Matrix.of fun l c' => (frameRow p r k (H.map (algebraMap F A)) (pos l) (t l) (cols c')) ^ p ^ (zj - pos l)) =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)) * (g.mapMatrix (H.submatrix id cols)) := by
    ext l c'
    simp only [Matrix.of_apply, frameRow, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply,
      RingHom.mapMatrix_apply, Matrix.submatrix_apply, id, hg]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le (hpos l), map_pow]
  unfold piMinor
  rw [hmat, Matrix.det_mul, ← RingHom.map_det, hg]
end Formalism.CountingSumsFrames
