-- Prove2me | solution 1 for Formalism.REAL.commutator_of_sums_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:10.655485+00:00
-- url     : https://prove2.me/submissions/83235af4-2b15-4f55-b0ac-b4e3a9c1bda0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] {ι : Type*} (s : Finset ι) (S T : ι → A) (P Q : A)
    (hST : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → S i * T i' = T i' * S i)
    (hSQ : ∀ i ∈ s, S i * Q = Q * S i) (hPT : ∀ i ∈ s, P * T i = T i * P) :
    (∑ i ∈ s, S i + P) * (∑ i ∈ s, T i + Q) - (∑ i ∈ s, T i + Q) * (∑ i ∈ s, S i + P) =
      ∑ i ∈ s, (S i * T i - T i * S i) + (P * Q - Q * P) := by
  have key : ∀ i ∈ s, ∑ i' ∈ s, (S i * T i' - T i' * S i) = S i * T i - T i * S i := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · intro i' hi' hne
      rw [hST i hi i' hi' (Ne.symm hne), sub_self]
    · intro h
      exact absurd hi h
  have hSQ' : (∑ i ∈ s, S i) * Q = Q * ∑ i ∈ s, S i := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hSQ
  have hPT' : P * (∑ i ∈ s, T i) = (∑ i ∈ s, T i) * P := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hPT
  have e1 : (∑ i ∈ s, S i) * (∑ i ∈ s, T i) = ∑ i ∈ s, ∑ i' ∈ s, S i * T i' := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have e2 : (∑ i ∈ s, T i) * (∑ i ∈ s, S i) = ∑ i ∈ s, ∑ i' ∈ s, T i' * S i := by
    simp only [Finset.sum_mul, Finset.mul_sum]
  have hST' : (∑ i ∈ s, S i) * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * (∑ i ∈ s, S i) =
      ∑ i ∈ s, (S i * T i - T i * S i) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    exact key i hi
  have expand : (∑ i ∈ s, S i + P) * (∑ i ∈ s, T i + Q) - (∑ i ∈ s, T i + Q) * (∑ i ∈ s, S i + P) =
      ((∑ i ∈ s, S i) * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * (∑ i ∈ s, S i)) +
        ((∑ i ∈ s, S i) * Q - Q * ∑ i ∈ s, S i) + (P * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * P) +
        (P * Q - Q * P) := by
    noncomm_ring
  rw [expand, hST', hSQ', hPT']
  simp only [sub_self, add_zero]
end Formalism.REAL
