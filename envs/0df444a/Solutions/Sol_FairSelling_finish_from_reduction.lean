-- Prove2me | solution 1 for FairSelling.finish_from_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:40:19.37921+00:00
-- url     : https://prove2.me/submissions/d322fc83-3693-4edd-8a02-ca5c2923491f

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_restrictVal_nonneg
import Theorems.Thm_FairSelling_compose_three
import Theorems.Thm_FairSelling_exists_MMS_two

attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hRc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p)) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  set R : Finset G := Finset.univ \ (Ka ∪ Sa) with hR
  obtain ⟨o2, ho2, ho2util⟩ :=
    exists_MMS_two ![restrictVal R (v b), restrictVal R (v c)] (restrictVal R p)
      (by intro i g; fin_cases i <;> exact restrictVal_nonneg R (hv _) g)
      (restrictVal_nonneg R hp)
  have hb : (3/4 : ℝ) * MMS 3 (v b) p ≤ util (restrictVal R (v b)) o2 0 := by
    have h0 := ho2util 0
    simp only [Matrix.cons_val_zero] at h0
    exact le_trans hRb h0
  have hc : (3/4 : ℝ) * MMS 3 (v c) p ≤ util (restrictVal R (v c)) o2 1 := by
    have h1 := ho2util 1
    simp only [Matrix.cons_val_one] at h1
    exact le_trans hRc h1
  exact compose_three v p hp a b c hab hac hbc Ka Sa ma hKSa hma0 hmaS haU o2 ho2 hb hc
end FairSelling
