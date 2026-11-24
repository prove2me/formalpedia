-- Prove2me | solution 1 for Formalism.REAL.fockCas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:58.442575+00:00
-- url     : https://prove2.me/submissions/feeeafc1-38b4-4d91-b252-df268c57a212

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
private theorem sum_four_comm_unipotent_moves {A : Type*} [AddCommMonoid A] {α β γ δ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] (f : α → β → γ → δ → A) :
    ∑ c, ∑ a, ∑ i, ∑ j, f c a i j = ∑ i, ∑ j, ∑ a, ∑ c, f c a i j := by
  calc ∑ c, ∑ a, ∑ i, ∑ j, f c a i j = ∑ c, ∑ i, ∑ a, ∑ j, f c a i j :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, ∑ a, f c a i j :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ j, ∑ a, f c a i j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ c, ∑ a, f c a i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ c, f c a i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
private theorem cas_sum_pq_sub_smul_eq_cas_neg_sum_sub_smul {A : Type*} [Ring A] {M N : ℕ} (p q : Fin M → Fin N → A)
    (hqp : ∀ i j a b, q i a * p j b - p j b * q i a = if i = j ∧ a = b then 1 else 0)
    (hqq : ∀ i j a b, q i a * q j b = q j b * q i a) :
    Cas (fun i j => ∑ a, p i a * q j a) - M • (∑ i, ∑ a, p i a * q i a) =
      Cas (fun a b => -∑ i, p i b * q i a) - N • (∑ i, ∑ a, p i a * q i a) := by
  have hE : Cas (fun i j => ∑ a, p i a * q j a) =
      (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + M • (∑ i, ∑ a, p i a * q i a) := by
    have t : ∀ i j a c, p i a * q j a * (p j c * q i c) =
        p i a * p j c * (q j a * q i c) + (if a = c then p i a * q i c else 0) := by
      intro i j a c
      have e : q j a * p j c = p j c * q j a + (if a = c then 1 else 0) := by
        have h0 := hqp j j a c
        simp only [true_and] at h0
        exact sub_eq_iff_eq_add'.mp h0
      calc p i a * q j a * (p j c * q i c) = p i a * (q j a * p j c) * q i c := by noncomm_ring
        _ = _ := by rw [e]; split_ifs <;> noncomm_ring
    show ∑ i, ∑ j, (∑ a, p i a * q j a) * (∑ c, p j c * q i c) = _
    simp only [Finset.sum_mul_sum, t, Finset.sum_add_distrib]
    congr 1
    simp [Finset.smul_sum]
  have hE' : Cas (fun a b => -∑ i, p i b * q i a) =
      (∑ i, ∑ j, ∑ a, ∑ c, p i a * p j c * (q j a * q i c)) + N • (∑ i, ∑ a, p i a * q i a) := by
    have t : ∀ a b i k, p i b * q i a * (p k a * q k b) =
        p i b * p k a * (q i a * q k b) + (if i = k then p i b * q k b else 0) := by
      intro a b i k
      have e : q i a * p k a = p k a * q i a + (if i = k then 1 else 0) := by
        have h0 := hqp i k a a
        simp only [and_true] at h0
        exact sub_eq_iff_eq_add'.mp h0
      calc p i b * q i a * (p k a * q k b) = p i b * (q i a * p k a) * q k b := by noncomm_ring
        _ = _ := by rw [e]; split_ifs <;> noncomm_ring
    show ∑ a, ∑ b, (-∑ i, p i b * q i a) * (-∑ k, p k a * q k b) = _
    simp only [neg_mul_neg, Finset.sum_mul_sum, t, Finset.sum_add_distrib]
    congr 1
    · refine (sum_four_comm_unipotent_moves (fun c a i j => p i a * p j c * (q i c * q j a))).trans ?_
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
          congrArg (p i a * p j c * ·) (hqq i j c a)
    · simp [Finset.smul_sum]
      rw [Finset.sum_comm]
  rw [hE, hE', add_sub_cancel_right, add_sub_cancel_right]
end Formalism.REAL
end

set_option autoImplicit false
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : FockCas := by
  intro M n' ε ε'
  have hqp : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (cCR M n' ε ε' i j a b).1
  have hqq : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (cCR M n' ε ε' i j a b).2.1
  refine ⟨?_, ?_⟩
  · show ∑ i, ∑ a, bpl ε ε' i a * bop ε ε' i a = -∑ a, -∑ i, bpl ε ε' i a * bop ε ε' i a
    rw [Finset.sum_neg_distrib, neg_neg, Finset.sum_comm]
  · rw [Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]
    exact cas_sum_pq_sub_smul_eq_cas_neg_sum_sub_smul (bpl ε ε') (bop ε ε') hqp hqq
end Formalism.REAL
