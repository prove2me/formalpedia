-- Prove2me | solution 1 for ChoiceRM.Policy.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:57:33.355175+00:00
-- url     : https://prove2.me/submissions/edcaa555-dd43-4ec9-8f40-26e4dde99baf

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
import Definitions.Def_ChoiceRM_Policy_Value
set_option autoImplicit false
open RevenueManagement ChoiceRM.Policy

theorem solution {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k)))
    (v v' : ℝ) (hv : 0 ≤ v) (hvv' : v ≤ v') (k k' : Fin m)
    (hk : IsLargestMaximizer P r Sq v k)
    (hk' : IsLargestMaximizer P r Sq v' k') :
    k' ≤ k := by
  by_contra hlt
  push_neg at hlt
  have hq : purchaseProb P (Sq k) ≤ purchaseProb P (Sq k') := hmono hlt.le
  have h1 := hk.1 k'
  have h2 := hk'.1 k
  -- sum: (Q k' - Q k) (v' - v) ≤ 0
  have h3 : (purchaseProb P (Sq k') - purchaseProb P (Sq k)) * (v' - v) ≤ 0 := by nlinarith
  have h4 : 0 ≤ (purchaseProb P (Sq k') - purchaseProb P (Sq k)) * (v' - v) :=
    mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hvv')
  have h5 : (purchaseProb P (Sq k') - purchaseProb P (Sq k)) * (v' - v) = 0 := le_antisymm h3 h4
  -- then both are equalities
  have h6 : expRevenue P r (Sq k') - purchaseProb P (Sq k') * v =
      expRevenue P r (Sq k) - purchaseProb P (Sq k) * v := by nlinarith
  exact absurd (hk.2 k' h6) (not_le.2 hlt)
