-- Prove2me | solution 1 for Formalism.REAL.fockPairGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:59.46675+00:00
-- url     : https://prove2.me/submissions/1a8126e8-0501-4742-bc75-809759bbbe0e

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Theorems.Thm_Formalism_REAL_cCR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.REAL
end Formalism.REAL
namespace Formalism.REAL
private theorem mul_mul_commutator_eq_of_commutator_relations {A : Type*} [Ring A] (x y z w d1 d2 : A) (e1 : y * z = z * y + d1)
    (e2 : w * x = x * w + d2) (hxz : x * z = z * x) (hyw : y * w = w * y) :
    x * y * (z * w) - z * w * (x * y) = x * d1 * w - z * d2 * y := by
  calc x * y * (z * w) - z * w * (x * y) = x * (y * z) * w - z * (w * x) * y := by noncomm_ring
    _ = x * (z * y + d1) * w - z * (x * w + d2) * y := by rw [e1, e2]
    _ = (x * z) * (y * w) + x * d1 * w - ((z * x) * (w * y) + z * d2 * y) := by noncomm_ring
    _ = x * d1 * w - z * d2 * y := by rw [hxz, hyw]; abel
private theorem glRel_sum_p_mul_q_of_canonical_relations {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a)
    (hpp : ∀ i j a b, p i a * p j b = p j b * p i a) :
    GlRel (fun i j => ∑ a, p i a * q j a) := by
  intro i j k l
  show (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) =
    (if j = k then ∑ a, p i a * q l a else 0) - (if l = i then ∑ a, p k a * q j a else 0)
  have h1 : (∑ a, p i a * q j a) * (∑ c, p k c * q l c) - (∑ c, p k c * q l c) * (∑ a, p i a * q j a) =
      ∑ a, ∑ c, (p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hterm : ∀ a c, p i a * q j a * (p k c * q l c) - p k c * q l c * (p i a * q j a) =
      (if j = k ∧ a = c then p i a * q l c else 0) - (if l = i ∧ c = a then p k c * q j a else 0) := by
    intro a c
    rw [mul_mul_commutator_eq_of_commutator_relations (p i a) (q j a) (p k c) (q l c) _ _ (sub_eq_iff_eq_add'.mp (hqp j k a c))
      (sub_eq_iff_eq_add'.mp (hqp l i c a)) (hpp i k a c) (hqq j l a c)]
    split_ifs <;> simp
  rw [h1]
  simp only [hterm, Finset.sum_sub_distrib]
  by_cases hjk : j = k <;> by_cases hli : l = i <;> simp [hjk, hli]
private theorem glRel_neg_transpose {A : Type*} [Ring A] {n : ℕ} (F : Fin n → Fin n → A) (h : GlRel F) :
    GlRel (fun a b => -F b a) := by
  intro a b c d
  show -F b a * -F d c - -F d c * -F b a = (if b = c then -F d a else 0) - (if d = a then -F b c else 0)
  have h' := h b a d c
  rw [neg_mul_neg, neg_mul_neg, h']
  have e1 : (a = d) ↔ (d = a) := eq_comm
  have e2 : (c = b) ↔ (b = c) := eq_comm
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  split_ifs <;> abel
private theorem sum_pq_commute_sum_pq_of_canonical_relations {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a)
    (hpp : ∀ i j a b, p i a * p j b = p j b * p i a) (i j : Fin M) (a b : Fin N) :
    (∑ c, p i c * q j c) * (∑ k, p k b * q k a) = (∑ k, p k b * q k a) * (∑ c, p i c * q j c) := by
  rw [← sub_eq_zero]
  have h1 : (∑ c, p i c * q j c) * (∑ k, p k b * q k a) - (∑ k, p k b * q k a) * (∑ c, p i c * q j c) =
      ∑ c, ∑ k, (p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun k c => p k b * q k a * (p i c * q j c))]
    simp only [Finset.sum_sub_distrib]
  have hterm : ∀ c k, p i c * q j c * (p k b * q k a) - p k b * q k a * (p i c * q j c) =
      (if j = k ∧ c = b then p i c * q k a else 0) - (if k = i ∧ a = c then p k b * q j c else 0) := by
    intro c k
    rw [mul_mul_commutator_eq_of_commutator_relations (p i c) (q j c) (p k b) (q k a) _ _ (sub_eq_iff_eq_add'.mp (hqp j k c b))
      (sub_eq_iff_eq_add'.mp (hqp k i a c)) (hpp i k c b) (hqq j k c a)]
    split_ifs <;> simp
  rw [h1]
  simp only [hterm, Finset.sum_sub_distrib, ite_and]
  simp
end Formalism.REAL
end

set_option autoImplicit false
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : FockPairGl := by
  intro M n' ε ε'
  have hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (cCR M n' ε ε' i j a b).1
  have hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.1
  have hpp : ∀ i j a b, bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.2
  refine ⟨?_, ?_, ?_⟩
  · exact glRel_sum_p_mul_q_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp
  · have hqp' : ∀ x y i k, bop ε ε' i x * bpl ε ε' k y - bpl ε ε' k y * bop ε ε' i x =
        if x = y ∧ i = k then 1 else 0 := by
      intro x y i k
      rw [hqp i k x y]
      exact if_congr and_comm rfl rfl
    exact glRel_neg_transpose _ (glRel_sum_p_mul_q_of_canonical_relations (fun a i => bpl ε ε' i a) (fun a i => bop ε ε' i a)
      hqp' (fun x y i k => hqq i k x y) (fun x y i k => hpp i k x y))
  · intro i j a b
    show (∑ c, bpl ε ε' i c * bop ε ε' j c) * (-∑ k, bpl ε ε' k b * bop ε ε' k a) =
      (-∑ k, bpl ε ε' k b * bop ε ε' k a) * (∑ c, bpl ε ε' i c * bop ε ε' j c)
    rw [mul_neg, neg_mul, sum_pq_commute_sum_pq_of_canonical_relations (bpl ε ε') (bop ε ε') hqp hqq hpp i j a b]
end Formalism.REAL
