-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.CS_le_of_indivRational
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:57:58.432421+00:00
-- url     : https://prove2.me/submissions/105c2b6f-aef2-4e4b-bc4a-dcc293e53d9c

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated in
theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x y : I → J → ℝ) (hsum : ∑ i, y i = ∑ i, x i) (hu : ∀ i, u i (x i) ≤ u i (y i)) : CS u g y ≤ CS u g x := by
  unfold CS
  apply iSup₂_le
  intro z hz
  set z' : I → J → ℝ := fun i => y i + z i - x i with hz'def
  have hz' : ∑ i, z' i = 0 := by
    simp only [hz'def, Finset.sum_sub_distrib, Finset.sum_add_distrib, hz, hsum]
    abel
  refine le_trans ?_ (le_iSup₂_of_le (f := fun (w : I → J → ℝ) (_ : ∑ i, w i = 0) =>
    ∑ i, indiffPrice (u i) g (x i) (w i)) z' hz' le_rfl)
  apply Finset.sum_le_sum
  intro i _
  unfold indiffPrice
  apply iSup₂_le
  intro r hr
  refine le_iSup₂_of_le (f := fun (r : ℝ) (_ : u i (x i) ≤ u i (x i + z' i - r • g)) =>
    ((r : ℝ) : EReal)) r ?_ le_rfl
  have e : x i + z' i - r • g = y i + z i - r • g := by
    simp only [hz'def]
    abel
  rw [e]
  exact (hu i).trans hr
