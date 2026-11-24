-- Prove2me | solution 1 for FairSelling.MoneyGoods.counting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:24.507881+00:00
-- url     : https://prove2.me/submissions/bfe66050-21e2-49a8-8453-df1b6d453dc1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
import Theorems.Thm_FairSelling_MoneyGoods_trunc_eq_price_of_mem_soldGoods
import Theorems.Thm_FairSelling_MoneyGoods_two_n_sub_one_thr
import Theorems.Thm_FairSelling_MoneyGoods_safe_cost
import Theorems.Thm_FairSelling_GeneralTPS_truncBundle_univ
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.MoneyGoods
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hclass : MoneyClass v p)
    {s : Stage G n} (hs : GoodM v p eps s) {j : Fin n} (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by
  classical
  set t := TPS n (v j) p with ht
  set w : G → ℝ := trunc (v j) p t with hw
  set U : Finset G := s.soldSet ∪ Finset.univ.biUnion s.bundle with hU
  -- the total truncated value
  have htotal : ∑ g : G, w g = (n : ℝ) * t := by
    have := truncBundle_univ (v j) p hn hp
    simpa [truncBundle, hw, ht] using this
  have hsplit : (∑ g ∈ s.pool, w g) + ∑ g ∈ U, w g = ∑ g : G, w g := by
    have : U ⊆ (Finset.univ : Finset G) := Finset.subset_univ _
    simpa [Stage.pool, hU] using Finset.sum_sdiff (f := w) this
  -- the union splits into the sold goods and the bundles
  have hdisjSU : Disjoint s.soldSet (Finset.univ.biUnion s.bundle) := by
    refine Finset.disjoint_left.mpr (fun x hx hxb => ?_)
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hxb
    exact Finset.disjoint_left.mp (hs.2.2.1 i) hx hxi
  have hdisjb : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint s.bundle := by
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hUsum : ∑ g ∈ U, w g
      = (∑ g ∈ s.soldSet, w g) + ∑ i : Fin n, ∑ g ∈ s.bundle i, w g := by
    rw [hU, Finset.sum_union hdisjSU, Finset.sum_biUnion hdisjb]
  -- the sold goods are liquid
  have hsold : ∑ g ∈ s.soldSet, w g = ∑ g ∈ s.soldSet, p g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    have hg' : g ∈ soldGoods p := by rwa [hs.2.2.2.2.2.2.1] at hg
    exact trunc_eq_price_of_mem_soldGoods hclass hg' j
  have hmoney : ∑ g ∈ s.soldSet, p g = (∑ i, s.cash i) + s.bank := hs.2.2.2.2.2.1.symm
  -- each bundle plus its cash costs at most `2τ`
  have hcost : ∀ i : Fin n, (∑ g ∈ s.bundle i, w g) + s.cash i
      ≤ if i ∈ s.served then 2 * thr v p j else 0 := by
    intro i
    by_cases hi : i ∈ s.served
    · simp only [hi, if_true]
      exact safe_cost v p eps hn hp hs hi hj
    · simp only [hi, if_false, (hs.1 i hi).1, (hs.1 i hi).2, Finset.sum_empty, add_zero, le_refl]
  have hcostsum : (∑ i : Fin n, ∑ g ∈ s.bundle i, w g) + ∑ i, s.cash i
      ≤ (s.served.card : ℝ) * (2 * thr v p j) := by
    have h1 : ∑ i : Fin n, ((∑ g ∈ s.bundle i, w g) + s.cash i)
        ≤ ∑ i : Fin n, if i ∈ s.served then 2 * thr v p j else 0 :=
      Finset.sum_le_sum (fun i _ => hcost i)
    have h2 : ∑ i : Fin n, (if i ∈ s.served then 2 * thr v p j else 0)
        = (s.served.card : ℝ) * (2 * thr v p j) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_add_distrib] at h1
    linarith [h1, h2.le, h2.ge]
  have hthr : (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * t :=
    two_n_sub_one_thr v p hn j
  have hpool : truncBundle (v j) p t s.pool = ∑ g ∈ s.pool, w g := rfl
  rw [hpool]
  have := hsplit
  rw [hUsum, hsold, hmoney, htotal] at this
  nlinarith [hcostsum, this, hthr]
end FairSelling.MoneyGoods
