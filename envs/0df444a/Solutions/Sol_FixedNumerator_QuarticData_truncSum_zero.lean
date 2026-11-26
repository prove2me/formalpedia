-- Prove2me | solution 1 for FixedNumerator.QuarticData.truncSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:07.508651+00:00
-- url     : https://prove2.me/submissions/5409321f-b892-4482-98d2-0ea1bfade2eb

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
public import Theorems.Thm_FixedNumerator_mem_normBall
public import Theorems.Thm_FixedNumerator_not_four_dvd_zero_sub
public import Theorems.Thm_P2M_FixedNumerator_norm_nonneg__64b3937061ea


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (W : GaussianInt → ℂ) (μ γ : GaussianInt) {β : GaussianInt}
    (hβ : IsPrimary β) : truncSum D W μ β γ 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  simp only [Finset.mem_filter, mem_normBall] at hc
  exfalso
  have h0 : c = 0 := by
    have := norm_nonneg' c
    exact (Zsqrtd.norm_eq_zero_iff (by norm_num) c).mp (by push_cast at hc; omega)
  subst h0
  exact not_four_dvd_zero_sub hβ hc.2.1
end FixedNumerator.QuarticData
