-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.Zv_ge_third
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:25.870481+00:00
-- url     : https://prove2.me/submissions/5f28da6d-1714-4dca-b943-f0806c37f601

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP
public import Definitions.Def_BCFGJPSSV26_Greedy_Embed
import all Definitions.Def_BCFGJPSSV26_Greedy_Embed
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_superset_far

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Embed

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

end Embed

namespace Run

variable {n m : ℕ} (R : Run n m)

variable (Dg : Finset (Fin n))

variable {Dg}

variable (hne : Dg.Nonempty)
include hne

section

variable {istar : Fin m}

/-- Under **FREEZING**, a client near the opened facility has `Z ≥ θ / 3` (by
[BCFGJPSSV26a, Lemma E.11]). -/
theorem Zv_ge_third (hF : R.Freezing hne istar) (j : R.DgT Dg)
    (hj : R.X.d j.val (R.opened (R.σ (R.kl hne).val) istar) ≤ R.θl hne / 3) :
    R.θl hne / 3 ≤ R.Zv j.val (R.σ (R.kl hne).val) := by
  obtain ⟨a, hop, hgt, hstr, -⟩ := hF
  rw [R.opened_eq hop] at hj
  have hθ := R.θl_pos hne
  have hs := R.σ_lt (R.kl hne).val
  unfold Zv
  split_ifs with hA hσ
  · have := R.θs_le_αs j.val
    rw [hσ] at this
    unfold θl at hθ hj ⊢
    linarith
  · unfold θl at hθ ⊢
    linarith
  · have hfar := R.superset_far hs hop hstr
    have hK : 2 * R.θl hne / 3 ≤ R.P.K := by
      have h1 := R.active_before (R.kl hne).val
      have h2 : R.Dpre (R.σ (R.kl hne).val) (R.kl hne).val ≤ R.P.K := profF_le_K _ _ _ _
      have hδ := R.good.δ_pos
      have hδ' := R.good.one_sub_δ_pos
      have hθ1 := R.one_le_θs (R.σ (R.kl hne).val)
      have h3 := mul_le_mul_of_nonneg_left h2 hδ'.le
      have hK0 : 0 ≤ R.P.K := by
        by_contra h
        push Not at h
        nlinarith
      have := mul_nonneg hδ.le hK0
      unfold θl
      linarith
    have hD : 2 * R.θl hne / 3 ≤ R.Dt (R.σ (R.kl hne).val) j.val := by
      refine le_profF R.P.K R.X.d hK fun q hq ↦ ?_
      have h1 := hfar q hq
      have h2 := R.X.dF_le j.val a.fac q.1
      unfold θl at hj ⊢
      linarith
    have hδ := R.good.half_le_one_sub_δ
    nlinarith

end

variable {istar : Fin m} (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j)
include hD

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.Zv_ge_third := @BCFGJPSSV26.Greedy.Run.Zv_ge_third
