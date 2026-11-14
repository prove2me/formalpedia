-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_unsynced_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:05:11.914822+00:00
-- url     : https://prove2.me/submissions/04168e1e-e6ff-4d00-ac3c-13af62059171

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
import all Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace FewNotInSync

variable (X : Ctx)

end FewNotInSync

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

open FewNotInSync

open Classical in
/-- **Few clusters are not in sync**: fewer than `632/(εβ)`. -/
theorem card_unsynced_lt : ((X.O.filter fun c ↦ ¬ X.IsSynced c).card : ℝ) < 632 / (X.ε * X.β) := by
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hβ := H.β_pos
  have hopt : 0 < X.opt := H.opt_pos
  have h4 : X.I.costF X.S ≤ 4 * X.opt := costF_le_four_opt H.valid H.k_le_m X.P.hN H.alo
  have hnat := H.card_unsynced_le_nat
  have hreal : ((X.O.filter fun c ↦ ¬ X.IsSynced c).card : ℝ) ≤
      2 * ((Oexp X).card : ℝ) + 2 * (O1t X).card + (O3t X).card := by exact_mod_cast hnat
  have hE := H.card_Oexp_le
  have h1 := H.card_O1t_le
  have h3 := H.card_O3t_le
  have ht1 : (0 : ℝ) ≤ (O1t X).card := Nat.cast_nonneg _
  have hE' : ((Oexp X).card : ℝ) * (X.ε * X.β) ≤ 90 := by
    have : ((Oexp X).card : ℝ) * (X.ε * X.β) * X.opt ≤ 90 * X.opt := by linarith
    exact le_of_mul_le_mul_right this hopt
  have h1' : ((O1t X).card : ℝ) * X.β ≤ 240 := by
    have ha : ((O1t X).card : ℝ) * ((1 - X.ε / 3) * X.β) * X.opt ≤ 120 * X.opt := by linarith
    have hb := le_of_mul_le_mul_right ha hopt
    have hc : 0 ≤ ((O1t X).card : ℝ) * X.β * (1 - 2 * X.ε / 3) :=
      mul_nonneg (mul_nonneg ht1 hβ.le) (by linarith)
    linarith
  have h3' : ((O3t X).card : ℝ) * (X.ε * X.β) ≤ 360 := by
    have : ((O3t X).card : ℝ) * (X.ε * X.β) * X.opt ≤ 360 * X.opt := by linarith
    exact le_of_mul_le_mul_right this hopt
  have h1'' : ((O1t X).card : ℝ) * X.β * X.ε ≤ 240 * X.ε := mul_le_mul_of_nonneg_right h1' hε.le
  have hεβ := mul_pos hε hβ
  rw [lt_div_iff₀ hεβ]
  have := mul_le_mul_of_nonneg_right hreal hεβ.le
  linarith

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_unsynced_lt := @BCFGJPSSV26.Stable.Hyp.card_unsynced_lt
