-- Prove2me | solution 3 for DiaconisStroock.Poincare.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:42:29.917293+00:00
-- url     : https://prove2.me/submissions/261c9498-e49f-4068-80ff-116f9a7295ff

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Kappa
import Definitions.Def_mm_spectral
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Theorems.Thm_MarkovMixing_dirichlet_gap
import Theorems.Thm_DiaconisStroock_Poincare_var_le_kappa_mul_dirichlet

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 1064-1113

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
set_option autoImplicit false
open MarkovMixing DiaconisStroock.Poincare

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hV : 2 ≤ Fintype.card V) (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / kappa P π Γ := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨f, hfmean, hfnorm, hfgap⟩ :=
    (MarkovMixing.dirichlet_gap hV P hP hirr π hπ hrev).2
  have hv : distVar π f = 1 := by
    calc
      distVar π f = ∑ x, (f x)^2 * π x := by simp [distVar, hfmean]
      _ = innerPi π f f := by simp only [innerPi, pow_two]
      _ = 1 := hfnorm
  have he : 0 ≤ dirichletForm P π f := by
    unfold dirichletForm
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hπ.1.1 x) (hP.1 x y))
  have hb := DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet P hP hirr π hπ hrev Γ hΓ f
  rw [hv, ← hfgap] at hb
  have hg : 0 ≤ spectralGap P := by rwa [hfgap]
  have hk : 0 < kappa P π Γ := by
    by_contra hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hg
    linarith
  have hi : 1 / kappa P π Γ ≤ spectralGap P :=
    (div_le_iff₀ hk).mpr (by nlinarith [hb])
  unfold spectralGap at hi
  linarith

end
