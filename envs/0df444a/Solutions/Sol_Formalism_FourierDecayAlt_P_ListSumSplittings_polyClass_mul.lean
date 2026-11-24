-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:50.208814+00:00
-- url     : https://prove2.me/submissions/ec3fd44e-0918-4316-975d-94187b736edc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_splits_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_list_sum_mul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_smulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_norm_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_top_nat
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {D1 D2 : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D1 P) (hQ : PolyClass D2 Q) :
    PolyClass (D1 + D2) (fun g => P g * Q g) := by
  have hfun : (fun g => P g * Q g) = (fun g => P g • Q g) := by funext g; rw [smul_eq_mul]
  rw [hfun]
  refine ⟨ckOn_mulF hP.1 hQ.1, fun a ha => ?_⟩
  have hexP : ∀ l : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (AllLie l → ∀ g ∈ GV k r, ‖W l P g‖ ≤ C * gN g ^ D1) := by
    intro l; by_cases hl : AllLie l
    · obtain ⟨C, h0, h⟩ := hP.2 l hl; exact ⟨C, h0, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hl⟩
  have hexQ : ∀ l : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧
      (AllLie l → ∀ g ∈ GV k r, ‖W l Q g‖ ≤ C * gN g ^ D2) := by
    intro l; by_cases hl : AllLie l
    · obtain ⟨C, h0, h⟩ := hQ.2 l hl; exact ⟨C, h0, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hl⟩
  choose CP hCP0 hCP using hexP
  choose CQ hCQ0 hCQ using hexQ
  refine ⟨((splits a).map fun p => CP p.1 * CQ p.2).sum,
    list_sum_nonneg _ _ fun p _ => mul_nonneg (hCP0 _) (hCQ0 _), fun g hg => ?_⟩
  rw [W_smulF a ha P Q (ckOn_top_nat hP.1 _) (ckOn_top_nat hQ.1 _) g hg]
  refine (norm_list_sum_le _ _).trans ?_
  rw [← list_sum_mul_right]
  refine list_sum_le _ _ _ fun p hp => ?_
  obtain ⟨h1, h2⟩ := splits_mem a p hp
  have hl1 : AllLie p.1 := fun y hy => ha y (h1.subset hy)
  have hl2 : AllLie p.2 := fun y hy => ha y (h2.subset hy)
  rw [norm_smul, pow_add]
  calc ‖W p.1 P g‖ * ‖W p.2 Q g‖ ≤ (CP p.1 * gN g ^ D1) * (CQ p.2 * gN g ^ D2) :=
        mul_le_mul (hCP p.1 hl1 g hg) (hCQ p.2 hl2 g hg) (norm_nonneg _)
          (mul_nonneg (hCP0 _) (pow_nonneg (gN_pos hg).le _))
    _ = CP p.1 * CQ p.2 * (gN g ^ D1 * gN g ^ D2) := by ring
end Formalism.FourierDecayAlt.P.ListSumSplittings
