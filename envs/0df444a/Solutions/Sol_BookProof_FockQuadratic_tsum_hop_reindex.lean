-- Prove2me | solution 1 for BookProof.FockQuadratic.tsum_hop_reindex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:21.909086+00:00
-- url     : https://prove2.me/submissions/1799e2fb-b7a7-494e-962f-bb4ceb70eff1

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.tsum_hop_reindex
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {P Q : Idx ι} {F G : Idx ι → ℂ}
    (hF : ∀ a, ¬ P ≤ a → F a = 0) (hG : ∀ b, ¬ Q ≤ b → G b = 0)
    (hEq : ∀ a, P ≤ a → F a = G (tgt P Q a)) : ∑' a, F a = ∑' b, G b := by

  have hsF : Function.support F ⊆ {a : Idx ι | P ≤ a} := by
    intro a ha
    by_contra hc
    exact ha (hF a hc)
  have hsG : Function.support G ⊆ {b : Idx ι | Q ≤ b} := by
    intro b hb
    by_contra hc
    exact hb (hG b hc)
  have h1 : ∑' (a : {a : Idx ι // P ≤ a}), F (a : Idx ι) = ∑' a, F a :=
    tsum_subtype_eq_of_support_subset hsF
  have h2 : ∑' (b : {b : Idx ι // Q ≤ b}), G (b : Idx ι) = ∑' b, G b :=
    tsum_subtype_eq_of_support_subset hsG
  have h3 : ∑' (a : {a : Idx ι // P ≤ a}), G ((hopEquiv P Q a : {b : Idx ι // Q ≤ b}) : Idx ι)
      = ∑' (b : {b : Idx ι // Q ≤ b}), G (b : Idx ι) :=
    Equiv.tsum_eq (hopEquiv P Q) (fun b : {b : Idx ι // Q ≤ b} => G (b : Idx ι))
  rw [← h1, ← h2, ← h3]
  exact tsum_congr fun a => hEq (a : Idx ι) a.2
