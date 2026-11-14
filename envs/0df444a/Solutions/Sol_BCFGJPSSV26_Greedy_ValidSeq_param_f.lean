-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.ValidSeq.param_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:26.660578+00:00
-- url     : https://prove2.me/submissions/9b8da79d-ac99-48f7-85ca-738ce62dcf08

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid
import all Definitions.Def_BCFGJPSSV26_Greedy_Valid
public import Theorems.Thm_BCFGJPSSV26_Greedy_maximal_transfer

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

/-- **Changing the opening cost** ([BCFGJPSSV26a, Claim D.12], first case): a `0`-valid
sequence for `f'` is `η`-valid for `f ∈ (f', f' + η]`, without overbidding for `f'`. -/
theorem ValidSeq.param_f (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) (hn : 1 ≤ n) {f f' η : ℚ}
    (hff : f' ≤ f) (hdiff : f - f' ≤ η) {p : ℕ} {pre H : List (Atom m)}
    (h0 : ValidSeq P d f' 0 p pre H) (hno : NoOver P d f' (P.θseq p) (profL P.K d pre)) :
    ValidSeq P d f η p pre H := by
  have hη : 0 ≤ η := by linarith
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hnη : η ≤ n * η := by nlinarith
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · rcases h0.1 t ht with hfree | ⟨S, hS, hS0, hS'⟩
    · exact .inl hfree
    · refine .inr ⟨S, hS, hS0, ?_⟩
      cases hb : typ1 p <;> simp only [OpenT, hb, cond] at hS' ⊢
      · obtain ⟨T, h1, h2, h3, h4⟩ := hS'
        rw [mul_zero, sub_zero] at h3
        exact ⟨T, h1, h2, by linarith, fun i₀ ↦ (h4 i₀).trans hff⟩
      · unfold Open1 at hS' ⊢
        rw [mul_zero, sub_zero] at hS'
        linarith
  · have hno' : NoOver P d f' (P.θseq p) (profL P.K d (pre ++ H)) :=
      hno.mono hP fun j ↦ profL_anti _ _ (pairs_mono (List.subset_append_left _ _)) j
    exact maximal_transfer hP hd0 (typ1 p) (θseq_pos P p) hno' le_rfl hff h0.2

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.ValidSeq.param_f := @BCFGJPSSV26.Greedy.ValidSeq.param_f
