-- Prove2me | solution 1 for FairSelling.losses_of_stage1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:35.724123+00:00
-- url     : https://prove2.me/submissions/6a867ed6-2a1a-4b21-91d1-dd0c143b5268

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_thr_le_thr
import Theorems.Thm_FairSelling_losses_extend
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    {j : Fin n} (hj : j ∈ T) (hmin : ∀ a ∈ T, MMS n (v j) p ≤ MMS n (v a) p)
    {g : G} (hg : g ∈ R) (hprice : thr v p j ≤ p g) (hthr0 : 0 ≤ thr v p j) :
    Losses v p (T.erase j) (R.erase g) (D + p g - thr v p j) := by
  classical
  have key := losses_extend v p hL hj ∅ {g} (thr v p j) (Finset.empty_subset _)
    (by simpa using hg) (by simp) hthr0 ?_
  · have hR : R \ ((∅ : Finset G) ∪ {g}) = R.erase g := by
      simp [Finset.sdiff_singleton_eq_erase]
    have hD : D + (∑ x ∈ ({g} : Finset G), p x) - thr v p j = D + p g - thr v p j := by
      simp
    rw [hR, hD] at key
    exact key
  · intro i hi Ei
    by_cases hgS : g ∈ Ei.sell
    · -- the agent intended to sell `g` anyway: a loss of type `ℓ₂`
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have : thr v p j ≤ thr v p i :=
          thr_le_thr v p (hmin i (Finset.mem_of_mem_erase hi))
        simpa [vbarSum] using this
      · intro f hf
        rw [Finset.mem_singleton] at hf
        exact Or.inr (hf ▸ hgS)
    · exact Or.inl ⟨g, hgS, Or.inr ⟨rfl, rfl, hprice⟩⟩
end FairSelling
