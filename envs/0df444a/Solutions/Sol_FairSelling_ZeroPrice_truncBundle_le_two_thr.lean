-- Prove2me | solution 1 for FairSelling.ZeroPrice.truncBundle_le_two_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:59.902112+00:00
-- url     : https://prove2.me/submissions/6821941d-456f-447c-8dbb-d8177d044956

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
import Theorems.Thm_FairSelling_TPS_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {i : Fin n} (hi : i ∈ s.1) {j : Fin n} (hj : j ∉ s.1) :
    truncBundle (v j) p (TPS n (v j) p) (s.2 i) ≤ 2 * thr v p j := by
  classical
  have hp : ∀ g, 0 ≤ p g := fun g => le_of_eq (hp0 g).symm
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set t := TPS n (v j) p with ht
  have ht0 : 0 ≤ t := TPS_nonneg (v j) p hp
  have hthr : thr v p j = ((n : ℝ) / (2 * n - 1)) * t := rfl
  have hthr0 : 0 ≤ thr v p j := by
    rw [hthr]; exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) ht0
  have htle : t ≤ 2 * thr v p j := by
    rw [hthr]
    have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
      rw [show (2 : ℝ) * ((n : ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
        le_div_iff₀ hden]
      linarith
    nlinarith
  have htrunc_le_v : ∀ g, trunc (v j) p t g ≤ v j g := by
    intro g
    simp only [trunc, hp0 g]
    exact max_le (hv j g) (min_le_left _ _)
  have htrunc_le_t : ∀ g, trunc (v j) p t g ≤ t := by
    intro g
    simp only [trunc, hp0 g]
    exact max_le ht0 (min_le_right _ _)
  have hsum_le : truncBundle (v j) p t (s.2 i) ≤ bval (v j) (s.2 i) :=
    Finset.sum_le_sum (fun g _ => htrunc_le_v g)
  have htheta : theta v p s j = thr v p j := by simp [theta, hj]
  set A := s.2 i with hA
  rcases Finset.eq_empty_or_nonempty A with hempty | ⟨g, hg⟩
  · rw [hempty]
    simp only [truncBundle, Finset.sum_empty]
    linarith
  · by_cases hsingle : A = {g}
    · rw [hsingle]
      simp only [truncBundle, Finset.sum_singleton]
      exact le_trans (htrunc_le_t g) htle
    · have hnsub : ¬ A ⊆ {g} := fun hsub =>
        hsingle (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hg))
      obtain ⟨h, hh, hhg⟩ := Finset.not_subset.mp hnsub
      have hhne : h ≠ g := by simpa using hhg
      have hsplit : bval (v j) (A.erase g) + v j g = bval (v j) A :=
        Finset.sum_erase_add A _ hg
      have hsafe_g : bval (v j) (A.erase g) ≤ thr v p j := by
        have := hs.2.2.2 i hi j g hg
        rwa [htheta] at this
      have hsafe_h : bval (v j) (A.erase h) ≤ thr v p j := by
        have := hs.2.2.2 i hi j h hh
        rwa [htheta] at this
      have hgh : g ∈ A.erase h := Finset.mem_erase.mpr ⟨Ne.symm hhne, hg⟩
      have hvg : v j g ≤ bval (v j) (A.erase h) :=
        Finset.single_le_sum (f := v j) (fun x _ => hv j x) hgh
      have : bval (v j) A ≤ 2 * thr v p j := by linarith
      linarith
end FairSelling.ZeroPrice
