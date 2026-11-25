-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.path_index_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:23.307527+00:00
-- url     : https://prove2.me/submissions/e137d251-27f6-49d9-be73-151bdfbbda38

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idx_empty
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : PathIdxFinite := by
  intro n N isVec B
  have hb : ∀ x : PathIdx n N isVec B, ∀ i : Fin (N + 1), ∀ m,
      x.1.1 i m ∈ Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ) := by
    intro x i m
    rw [Finset.mem_Icc, ← abs_le]
    exact path_bound' x.2.1 i.val (Nat.lt_succ_iff.mp i.isLt) m
  refine Finite.of_injective
    (fun x : PathIdx n N isVec B =>
      ((fun (i : Fin (N + 1)) (m : Fin n) => (⟨x.1.1 i m, hb x i m⟩ :
          Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ))),
        fun c : Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ) =>
          x.1.2 c.1)) ?_
  rintro ⟨⟨μ, I⟩, hp, hz, hstd⟩ ⟨⟨μ', I'⟩, hp', hz', hstd'⟩ h
  dsimp only at hp hz hstd hp' hz' hstd' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hμ : μ = μ' := by
    funext i m
    by_cases hi : i ≤ N
    · have := congrArg Subtype.val (congrFun (congrFun h1 ⟨i, Nat.lt_succ_of_le hi⟩) m)
      simpa using this
    · rw [hz i (by omega), hz' i (by omega)]
  have hI : I = I' := by
    funext c
    by_cases hc : c ∈ Finset.Icc (-((∑ k ∈ range N, B k : ℕ) : ℤ)) ((∑ k ∈ range N, B k : ℕ) : ℤ)
    · exact congrFun h2 ⟨c, hc⟩
    · rw [idx_empty hstd.1 _ (fun m => path_bound' hp N le_rfl m) c hc,
        idx_empty hstd'.1 _ (fun m => path_bound' hp' N le_rfl m) c hc]
  subst hμ hI
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
