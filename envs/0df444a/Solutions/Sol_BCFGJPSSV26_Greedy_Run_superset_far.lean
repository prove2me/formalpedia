-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.superset_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:56.556167+00:00
-- url     : https://prove2.me/submissions/b2925148-6d78-489d-a315-b3eb50a95ea8

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Structure
public import Mathlib.Data.Prod.Lex
public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
import all Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_pre

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

/-- **[BCFGJPSSV26a, Lemma E.11]**: a facility opened only with respect to a strict superset is at
distance at least `θ` from every pair of the superset. -/
theorem superset_far {s : ℕ} {a : Atom m} (hs : s < R.len) (hop : R.IsOp2 s a)
    (hstrict : ¬ ∃ T, R.WitOK s a (pairs (R.pre s)) T) :
    ∀ q ∈ (R.wit s).1, R.θs s ≤ R.X.dF a.fac q.1 + q.2 := by
  intro q hq
  by_contra hlt
  push Not at hlt
  apply hstrict
  have hw := R.wit_spec hs hop
  have hP := R.good
  have hθ := R.θs_nonneg s
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  -- all the bids are the values
  have heq : ∀ j, mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j =
      mval R.P (R.θs s) (R.Dt s) j := by
    intro j
    by_cases hact : R.θs s < (1 - R.P.δ) * R.Dt s j
    · have hfar : R.P.ε * R.θs s < R.X.d j a.fac := by
        by_contra hc
        push Not at hc
        have h1 := profF_le R.P.K R.X.d hq j
        have h2 := R.X.d_le_d_add_dF j q.1 a.fac
        have h3 : R.P.ε * (1 - R.P.δ) ≤ R.P.δ := (le_div_iff₀ hδ).1 hP.ε_le_δ_div
        have h4 : R.Dt s j < R.P.ε * R.θs s + R.θs s := by
          unfold Dt
          linarith
        have h5 := mul_lt_mul_of_pos_left h4 hδ
        nlinarith
      rw [mT_of_far hfar hact.le, mval, min_eq_left hact.le]
    · push Not at hact
      rw [mT_of_inactive hact, mval, min_eq_right hact]
  refine ⟨R.θs s, subset_rfl, fun q hq ↦ R.off_nonneg_of_mem_pairs hq, le_rfl,
    R.θs_le_θplus s, ?_, ?_⟩
  · have h1 : R.f - n * R.P.η ≤ lhs3 R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) :=
      hw.2.2.2.2.1
    have h2 : lhs3 R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) =
        lhs3 R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.θs s) := by
      unfold lhs3
      simp only [heq, mT_at_θ]
    rw [h2] at h1
    exact h1.trans (lhs3_mono_D hP (R.Dt_le s))
  · intro i₀
    rw [lhs4_at_θ]
    exact R.noOver_pre hs i₀

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.superset_far := @BCFGJPSSV26.Greedy.Run.superset_far
