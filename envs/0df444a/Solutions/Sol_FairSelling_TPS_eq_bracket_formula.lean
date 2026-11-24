-- Prove2me | solution 1 for FairSelling.TPS_eq_bracket_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:12.480099+00:00
-- url     : https://prove2.me/submissions/cab523b6-9a9a-419d-b18d-5d9b1699c3b8

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_le_TPS_of_le_truncSum
import Theorems.Thm_FairSelling_truncSum_bracket
import Theorems.Thm_FairSelling_TPS_lt_of_no_fixed_above
import Theorems.Thm_FairSelling_TPS_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {a c : ℝ}
    (hac : a ≤ c) (hnb : NoBreak v p a c)
    (hfa : a ≤ truncSum n v p a) (hfc : truncSum n v p c < c)
    (hbv : ∀ g, c ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, c ≤ p g → truncSum n v p (p g) < p g) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by
  classical
  have hTPSlt : TPS n v p < c := TPS_lt_of_no_fixed_above v p hn hp hfc hbv hbp
  have hTPSge : a ≤ TPS n v p := le_TPS_of_le_truncSum v p hfa
  have hfix : truncSum n v p (TPS n v p) = TPS n v p := TPS_truncSum v p hp
  set t₀ := TPS n v p with ht₀
  set C := flatConst v p a c with hC
  set k := ((slopeGoods v p a c).card : ℝ) with hk
  have h1 := truncSum_bracket (n := n) v p hnb hTPSge (le_of_lt hTPSlt)
  have h2 := truncSum_bracket (n := n) v p hnb (le_refl a) hac
  have h3 := truncSum_bracket (n := n) v p hnb hac (le_refl c)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [hfix] at h1
  have e1 : C + k * t₀ = n * t₀ := by
    rw [eq_comm, div_eq_iff (ne_of_gt hn')] at h1
    linarith [h1]
  have e3 : C + k * c < n * c := by rw [h3, div_lt_iff₀ hn'] at hfc; linarith
  have hkn : k < n := by nlinarith [hTPSlt, e1, e3]
  refine ⟨hkn, ?_, hTPSge, hTPSlt⟩
  rw [eq_div_iff (by linarith : (n:ℝ) - k ≠ 0)]
  linarith
end FairSelling
