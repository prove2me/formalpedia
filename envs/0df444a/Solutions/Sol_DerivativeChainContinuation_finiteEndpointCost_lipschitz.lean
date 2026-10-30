-- Prove2me | solution 1 for DerivativeChainContinuation.finiteEndpointCost_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T16:51:00.489579+00:00
-- url     : https://prove2.me/submissions/9d37b276-1921-42d2-aa12-855fc3c2152b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation



theorem finiteEndpointCost_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v : ℂ) :
    ∃ i, finiteEndpointCost c x v = c i + ‖x i-v‖ := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => c i+‖x i-v‖) Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ ?_⟩
  · apply ciInf_le
    exact ⟨c i+‖x i-v‖, by rintro _ ⟨j,rfl⟩; exact hi j (Finset.mem_univ j)⟩
  · exact le_ciInf fun j => hi j (Finset.mem_univ j)

theorem finiteEndpointCost_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v : ℂ) (i : ι) :
    finiteEndpointCost c x v ≤ c i+‖x i-v‖ := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ
    (fun j => c j+‖x j-v‖) Finset.univ_nonempty
  apply ciInf_le
  exact ⟨c j+‖x j-v‖, by rintro _ ⟨k,rfl⟩; exact hj k (Finset.mem_univ k)⟩






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v w : ℂ) :
    |finiteEndpointCost c x v-finiteEndpointCost c x w| ≤ ‖v-w‖ := by
  have step (a b : ℂ) : finiteEndpointCost c x a ≤ finiteEndpointCost c x b+‖a-b‖ := by
    obtain ⟨i,hi⟩ := finiteEndpointCost_attained c x b
    have hle := finiteEndpointCost_le c x a i
    have ht := dist_triangle (x i) b a
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev b a] at ht
    rw [hi]
    linarith
  apply abs_le.mpr
  constructor
  · have h := step w v
    rw [norm_sub_rev w v] at h
    linarith
  · have h := step v w
    linarith
