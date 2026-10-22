-- Prove2me | solution 1 for BSUMConv.BSUM.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:04:02.689262+00:00
-- url     : https://prove2.me/submissions/8cebc2c0-64d6-4046-b72a-91228f4d51cd

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting
set_option autoImplicit false
open TsengBCD.Stationary Filter Topology
open BSUMConv.BSUM

theorem solution {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (z : X n) (hzX : z ∈ Xset Xs) (hmin : ∀ (k : Fin N), ∀ w ∈ Xs k, u k (z k) z ≤ u k w z) :
    ∀ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))), z k + dk ∈ Xs k →
      0 ≤ dirDeriv (fun xk => (u k xk z : EReal)) (z k) dk := by
  intro k dk hdk
  have hzk : z k ∈ Xs k := by
    unfold Xset at hzX; rw [Set.mem_pi] at hzX; exact hzX k (Set.mem_univ _)
  unfold dirDeriv
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with t ht
  have hmem : z k + t • dk ∈ Xs k := by
    have := (hXconv k).add_smul_sub_mem hzk hdk (t := t) ⟨ht.1.le, ht.2.le⟩
    simpa using this
  have h1 := hmin k _ hmem
  rw [← EReal.coe_sub, ← EReal.coe_mul]
  exact_mod_cast mul_nonneg (sub_nonneg.2 h1) (inv_nonneg.2 ht.1.le)
