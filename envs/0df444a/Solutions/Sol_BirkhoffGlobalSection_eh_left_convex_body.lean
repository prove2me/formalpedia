-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_convex_body
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T19:09:55.487001+00:00
-- url     : https://prove2.me/submissions/b66bf839-ebcb-4b9a-b5c5-effcc6f83845
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical
import Theorems.Thm_BirkhoffGlobalSection_eh_left_component_regular_compact_starshaped
import Theorems.Thm_BirkhoffGlobalSection_convex_body_of_regular_starshaped_hessian
import Theorems.Thm_BirkhoffGlobalSection_eh_left_tangential_hessian_positive

open BirkhoffGlobalSection

theorem solution
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B := by
  obtain ⟨ε₁, η₁, hε₁, hη₁, hgeom⟩ :=
    eh_left_component_regular_compact_starshaped c₀ hc₀
  obtain ⟨ε₂, η₂, hε₂, hη₂, hhess⟩ :=
    eh_left_tangential_hessian_positive c₀ hc₀
  refine ⟨min ε₁ ε₂, min η₁ η₂, lt_min hε₁ hε₂, lt_min hη₁ hη₂, ?_⟩
  intro μ c hμ0 hμ1 hμ hcc hsub
  obtain ⟨hcompact, hreg, hstar⟩ :=
    hgeom μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_left _ _))
      (lt_of_lt_of_le hcc (min_le_left _ _)) hsub
  have hh := hhess μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_right _ _))
    (lt_of_lt_of_le hcc (min_le_right _ _)) hsub
  have hzero : ∀ y ∈ ehLeftEnergyComponent μ c,
      ehLeftHamiltonian μ c y = 0 := by
    intro y hy
    unfold ehLeftEnergyComponent at hy
    exact connectedComponentIn_subset
      {s : Phase | ehLeftHamiltonian μ c s = 0} (ehLeftCollisionPoint μ) hy
  have hcoll : ehLeftHamiltonian μ c (ehLeftCollisionPoint μ) = 0 := by
    simp [ehLeftHamiltonian, ehLeftCollisionPoint]
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - μ by linarith)]
    ring
  have hconn : IsConnected (ehLeftEnergyComponent μ c) :=
    isConnected_connectedComponentIn_iff.mpr hcoll
  exact convex_body_of_regular_starshaped_hessian (ehLeftHamiltonian μ c)
    (ehLeftEnergyComponent μ c) hcompact hconn hreg hstar hzero hh
