-- Prove2me | solution 2 for ConstrNestedLogit.UpperBound.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T13:58:43.847235+00:00
-- url     : https://prove2.me/submissions/fb0e2b15-388f-45d2-8606-d76a1cbca070

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13
import Theorems.Thm_ConstrNestedLogit_UpperBound_claim

-- carved verbatim out of submission c748be7e-c628-431b-b202-12f0fe4a96f4, lines 193-218

section
open NestedLogitVariants.General ConstrNestedLogit.UpperBound

theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X)
    (Sstar : ι → Finset (Fin n)) (hfeas : ∀ i, SpaceFeasible w c i (Sstar i))
    (hopt : ∀ S : ι → Finset (Fin n), (∀ i, SpaceFeasible w c i (S i)) →
      revenue I S ≤ revenue I Sstar)
    (zhat : ℝ) (yhat : ι → ℝ) (hzy : LP13Optimal I X zhat yhat) :
    revenue I Sstar ≤ zhat := by 
  classical
  have hc := ConstrNestedLogit.UpperBound.claim I hvnp hv0 hv hγ w c X hw hwc hX Sstar hfeas zhat yhat hzy.1
  have hsum := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)).trans hzy.1.1
  have hn (i : ι) : 0 ≤ nestWeight I i (Sstar i) := by
    apply Real.rpow_nonneg
    simp only [V, hvnp i, zero_add]
    exact Finset.sum_nonneg (fun j hj => (hv i j).le)
  have hden : 0 < I.v0 + ∑ i, nestWeight I i (Sstar i) :=
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg (fun i hi => hn i))
  rw [revenue, div_le_iff₀ hden]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  nlinarith [hsum]

end
