-- Prove2me | solution 1 for ChoiceRM.Policy.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:57:04.347278+00:00
-- url     : https://prove2.me/submissions/523b22a5-ee59-41e3-a9e5-f80ab7bb2435

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
set_option autoImplicit false
open RevenueManagement ChoiceRM.Policy

theorem solution {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k)))
    (k l : Fin m) (hkl : k < l) (v₀ : ℝ) (hv₀ : 0 ≤ v₀)
    (h : expRevenue P r (Sq k) - purchaseProb P (Sq k) * v₀ <
      expRevenue P r (Sq l) - purchaseProb P (Sq l) * v₀) :
    ∀ v : ℝ, v ≤ v₀ →
      expRevenue P r (Sq k) - purchaseProb P (Sq k) * v <
        expRevenue P r (Sq l) - purchaseProb P (Sq l) * v := by
  intro v hv
  have hq : purchaseProb P (Sq k) ≤ purchaseProb P (Sq l) := hmono hkl.le
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hv)]
