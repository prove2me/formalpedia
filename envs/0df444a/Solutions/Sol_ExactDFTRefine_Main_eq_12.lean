-- Prove2me | solution 1 for ExactDFTRefine.Main.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:51:43.134046+00:00
-- url     : https://prove2.me/submissions/b991c04e-3e61-4140-b34c-4e36441482d6

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
namespace ExactDFTRefine.Main

/-- Auxiliary: sum over a multiset product factors as a product of sums. -/
private lemma multiset_product_sum (B A : Multiset ℕ) (f g : ℕ → ℝ) :
    ((B ×ˢ A).map (fun p : ℕ × ℕ => f p.1 * g p.2)).sum
      = (B.map f).sum * (A.map g).sum := by
  induction B using Multiset.induction with
  | empty => simp
  | cons b B ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih]
    have h1 : (A.map (Prod.mk b)).map (fun p : ℕ × ℕ => f p.1 * g p.2)
        = A.map (fun a => f b * g a) := by
      rw [Multiset.map_map]; rfl
    rw [h1]
    have h2 : (A.map (fun a => f b * g a)).sum = f b * (A.map g).sum := by
      rw [Multiset.sum_map_mul_left]
    rw [h2, Multiset.map_cons, Multiset.sum_cons]
    ring

/-- Auxiliary: moments multiply under the tensor product. -/
private lemma moment_tensor (t : ℝ) (B A : Multiset ℕ) :
    moment t (tensor B A) = moment t B * moment t A := by
  unfold tensor moment
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton,
    Multiset.map_map, Function.comp_apply]
  have h : (fun p : ℕ × ℕ => (((p.1 * p.2 : ℕ) : ℝ) ^ t))
         = (fun p : ℕ × ℕ => ((p.1 : ℝ) ^ t) * ((p.2 : ℝ) ^ t)) := by
    funext p
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [h]
  exact multiset_product_sum B A (fun n => (n : ℝ) ^ t) (fun n => (n : ℝ) ^ t)

/-- **§4, Eq. (12)**, p. 5. Moments multiply under tensor powers:
`M_t(A^{⊗v}) = M_t(A)^v`. -/
theorem eq_12 (t : ℝ) (A : Multiset ℕ) (v : ℕ) :
    moment t (tpow A v) = moment t A ^ v := by
  induction v with
  | zero =>
    rw [pow_zero]
    show moment t ({1} : Multiset ℕ) = 1
    simp [moment, Real.one_rpow]
  | succ n ih =>
    show moment t (tensor (tpow A n) A) = moment t A ^ (n + 1)
    rw [moment_tensor, ih, pow_succ]

/-- Alias of `eq_12` under the name `solution`. -/
theorem solution (t : ℝ) (A : Multiset ℕ) (v : ℕ) :
    moment t (tpow A v) = moment t A ^ v := eq_12 t A v

end ExactDFTRefine.Main

open ExactDFTRefine.Main

/-- Root-level export of the theorem. -/
theorem _root_.solution (t : ℝ) (A : Multiset ℕ) (v : ℕ) :
    moment t (tpow A v) = moment t A ^ v :=
  ExactDFTRefine.Main.eq_12 t A v
