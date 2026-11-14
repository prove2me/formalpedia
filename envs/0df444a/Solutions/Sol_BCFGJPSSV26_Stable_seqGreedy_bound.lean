-- Prove2me | solution 1 for BCFGJPSSV26.Stable.seqGreedy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:43.187311+00:00
-- url     : https://prove2.me/submissions/1603f776-35bb-4d11-8e73-d334692a297c

module

public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Supermodular
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
import all Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {U : Type*} [DecidableEq U] {ρ T : ℕ}

/-- **The sequential greedy guarantee.** -/
theorem seqGreedy_bound {f : Finset U → ℝ} (hmono : IsMonoF f) (hsub : IsSubmod f)
    (h0 : f ∅ = 0) (hT : 0 < T) {P : Fin ρ → Finset U} {Lst : Fin ρ → Fin T → U}
    (hG : IsSeqGreedy f P Lst) (o : Fin ρ → U) (ho : ∀ j, o j ∈ P j) :
    (1 - ((T : ℝ) / (T + 1)) ^ T) * f (univ.image o) * (T : ℝ) ^ ρ ≤
      ∑ V : Fin ρ → Fin T, f (univ.image fun j ↦ Lst j (V j)) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set F := (T : ℝ) ^ ρ * f (univ.image o) with hF
  have hrec : ∀ t ≤ T, F - roundSum f Lst t ≤ ((T : ℝ) / (T + 1)) ^ t * F := by
    intro t
    induction t with
    | zero =>
      intro _
      have : roundSum f Lst 0 = 0 := by
        unfold roundSum roundSet
        simp [h0]
      rw [this, pow_zero, one_mul, sub_zero]
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := round_step hmono hsub hG o ho (t := t) (by omega)
      have h3 : ((T : ℝ) + 1) * (F - roundSum f Lst (t + 1)) ≤
          (T : ℝ) * (F - roundSum f Lst t) := by nlinarith
      have h4 : F - roundSum f Lst (t + 1) ≤ (T : ℝ) / (T + 1) * (F - roundSum f Lst t) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      calc F - roundSum f Lst (t + 1) ≤ (T : ℝ) / (T + 1) * (F - roundSum f Lst t) := h4
        _ ≤ (T : ℝ) / (T + 1) * (((T : ℝ) / (T + 1)) ^ t * F) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((T : ℝ) / (T + 1)) ^ (t + 1) * F := by ring
  have hfin := hrec T le_rfl
  have hT_eq : roundSum f Lst T = ∑ V : Fin ρ → Fin T, f (univ.image fun j ↦ Lst j (V j)) := by
    unfold roundSum roundSet
    refine sum_congr rfl fun V _ ↦ ?_
    congr 2
    ext j
    simp
  rw [← hT_eq]
  have : (1 - ((T : ℝ) / (T + 1)) ^ T) * f (univ.image o) * (T : ℝ) ^ ρ =
      F - ((T : ℝ) / (T + 1)) ^ T * F := by rw [hF]; ring
  rw [this]
  linarith

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.seqGreedy_bound := @BCFGJPSSV26.Stable.seqGreedy_bound
