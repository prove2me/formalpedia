-- Prove2me | solution 1 for DerivativeChainContinuation.arbitrary_source_deficit_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:03:28.340175+00:00
-- url     : https://prove2.me/submissions/a5d47d44-847a-4faf-8f37-2fd4eb4d2929

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_deficit_determinant_inequality
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_nonneg
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem centeredSource_roots (p : Polynomial ℂ) :
    (centeredSource p).roots = p.roots.map (fun z => z-rootCentroid p) := by
  simpa [centeredSource] using
    (roots_comp_C_mul_X_add_C p 1 (rootCentroid p) isUnit_one)

theorem centeredSource_natDegree (p : Polynomial ℂ) :
    (centeredSource p).natDegree = p.natDegree := by
  rw [centeredSource, natDegree_comp, natDegree_X_add_C, mul_one]

theorem centeredSource_monic (p : Polynomial ℂ) (hp : p.Monic) :
    (centeredSource p).Monic := hp.comp_X_add_C _

theorem centeredSource_centered (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (centeredSource p).roots.sum = 0 := by
  rw [centeredSource_roots]
  have hc := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnC : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast hn
  simp [Multiset.sum_map_sub, hc, rootCentroid, nsmul_eq_mul]
  field_simp [hnC]
  ring




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) :
    0 ≤ schoenbergDeficit (centeredSource p) ∧
      (rootCovariance (centeredSource p)).det /
        (2*(rootRadius (centeredSource p))^2) ≤ schoenbergDeficit (centeredSource p) := by
  have hm := centeredSource_monic p hp
  have hd : 2 ≤ (centeredSource p).natDegree := by rwa [centeredSource_natDegree]
  have hc := centeredSource_centered p (by omega)
  exact ⟨schoenbergDeficit_nonneg _ hm hd hc, deficit_determinant_inequality _ hm hd hc⟩
