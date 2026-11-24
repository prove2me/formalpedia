-- Prove2me | solution 1 for FairSelling.MoneyGoods.safe_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:17.888653+00:00
-- url     : https://prove2.me/submissions/fb134a35-b1e6-4882-978d-b764ea4c20b5

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
import Theorems.Thm_FairSelling_MoneyGoods_TPS_le_two_thr
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_le_vbarSum
import Theorems.Thm_FairSelling_vbarSum_sdiff_singleton
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.MoneyGoods
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : Stage G n} (hs : GoodM v p eps s)
    {i : Fin n} (hi : i ∈ s.served) {j : Fin n} (hj : j ∉ s.served) :
    truncBundle (v j) p (TPS n (v j) p) (s.bundle i) + s.cash i ≤ 2 * thr v p j := by
  classical
  have hthr0 : 0 ≤ thr v p j := thr_nonneg v p hn hp j
  have htle : TPS n (v j) p ≤ 2 * thr v p j := TPS_le_two_thr v p hn hp j
  have hguar : guarM v p eps s j = thr v p j - eps := by simp [guarM, hj]
  have hvbar0 : ∀ g : G, 0 ≤ vbar (v j) p g := fun g => le_trans (hp g) (le_max_left _ _)
  have hle : truncBundle (v j) p (TPS n (v j) p) (s.bundle i) ≤ vbarSum (v j) p (s.bundle i) :=
    truncBundle_le_vbarSum _ _ _ _
  rcases hs.2.2.2.2.2.2.2.2 i hi j with h | ⟨hc, _, h2⟩
  · rw [hguar] at h
    linarith
  · rw [hguar] at h2
    rw [hc, add_zero]
    set A := s.bundle i with hA
    rcases Finset.eq_empty_or_nonempty A with hempty | ⟨g, hg⟩
    · rw [hempty]
      simp only [truncBundle, Finset.sum_empty]
      linarith
    by_cases hsingle : A = {g}
    · have hg0 : p g ≤ thr v p j := by
        have := h2 g hg
        rw [hsingle] at this
        simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add] at this
        linarith
      rw [hsingle]
      simp only [truncBundle, Finset.sum_singleton, trunc]
      exact max_le (by linarith) (le_trans (min_le_right _ _) htle)
    · have hnsub : ¬ A ⊆ {g} := fun hsub =>
        hsingle (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hg))
      obtain ⟨h', hh', hhg⟩ := Finset.not_subset.mp hnsub
      have hhne : h' ≠ g := by simpa using hhg
      have hsplit : vbarSum (v j) p A = vbarSum (v j) p (A \ {g}) + vbar (v j) p g :=
        vbarSum_sdiff_singleton hg
      have hsafe_g : vbarSum (v j) p (A \ {g}) + p g ≤ thr v p j := by
        have := h2 g hg; linarith
      have hsafe_h : vbarSum (v j) p (A \ {h'}) + p h' ≤ thr v p j := by
        have := h2 h' hh'; linarith
      have hgh : g ∈ A \ {h'} := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hg, fun hc' => hhne (hc'.symm)⟩
      have hvg : vbar (v j) p g ≤ vbarSum (v j) p (A \ {h'}) :=
        Finset.single_le_sum (f := fun x => vbar (v j) p x) (fun x _ => hvbar0 x) hgh
      have hph : 0 ≤ p h' := hp h'
      have hpg : 0 ≤ p g := hp g
      linarith
end FairSelling.MoneyGoods
