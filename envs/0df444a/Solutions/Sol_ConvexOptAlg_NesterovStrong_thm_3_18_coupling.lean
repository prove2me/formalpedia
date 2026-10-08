-- Prove2me | solution 1 for ConvexOptAlg.NesterovStrong.thm_3_18_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:35:52.505135+00:00
-- url     : https://prove2.me/submissions/094a4e09-8587-43d6-ba0e-5f0e01fc62ed

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

set_option autoImplicit false

open ConvexOptAlg.NesterovStrong in
theorem solution {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) :
    v g α β x s - x s = Real.sqrt (kappa α β) • (x s - y s) := by
  obtain ⟨h1, hstep⟩ := hrun
  have hκ : 0 < kappa α β := div_pos hβ hα
  have hk : 0 < Real.sqrt (kappa α β) := Real.sqrt_pos.mpr hκ
  have hk2 : Real.sqrt (kappa α β) ^ 2 = β / α := Real.sq_sqrt hκ.le
  induction s, hs using Nat.le_induction with
  | base => simp [v, h1]
  | succ m hm ih =>
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    obtain ⟨hy, hx⟩ := hstep (j + 1) hm
    have hg : g (x (j + 1)) = β • (x (j + 1) - y (j + 1 + 1)) := by
      rw [hy, sub_sub_cancel, smul_smul, mul_one_div_cancel hβ.ne', one_smul]
    have hv : v g α β x (j + 1 + 1) = (1 - 1 / Real.sqrt (kappa α β)) • v g α β x (j + 1) +
        (1 / Real.sqrt (kappa α β)) • x (j + 1) -
          (1 / (α * Real.sqrt (kappa α β))) • g (x (j + 1)) := rfl
    have ih' : v g α β x (j + 1) = x (j + 1) + Real.sqrt (kappa α β) • (x (j + 1) - y (j + 1)) := by
      rw [← ih]; abel
    rw [hv, hg, hx, ih']
    generalize Real.sqrt (kappa α β) = k at hk hk2 ⊢
    have hβk : β = α * k ^ 2 := by rw [hk2]; field_simp
    subst hβk
    have hk0 : k ≠ 0 := hk.ne'
    have hα0 : α ≠ 0 := hα.ne'
    have hk1 : k + 1 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
