-- Prove2me | solution 1 for ConstrNestedLogit.Card.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:51:24.762169+00:00
-- url     : https://prove2.me/submissions/3e63a11e-31fd-4335-b40b-7cb6182fb8c3

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

set_option autoImplicit false

open NestedLogitVariants.LP

theorem solution {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) (S : Finset (Fin n)) (u : ℝ) :
    V I i S * (R I i S - u) = ∑ j ∈ S, I.v i j * (I.r i j - u) := by
  have hV : V I i S = ∑ j ∈ S, I.v i j := by unfold V; rw [hvnp, zero_add]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [hV]
  · have hpos : 0 < ∑ j ∈ S, I.v i j := Finset.sum_pos (fun j _ => hv j) hne
    unfold R
    rw [hV]
    have : ∑ j ∈ S, I.v i j * (I.r i j - u) =
        ∑ j ∈ S, I.r i j * I.v i j - u * ∑ j ∈ S, I.v i j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]
    field_simp
