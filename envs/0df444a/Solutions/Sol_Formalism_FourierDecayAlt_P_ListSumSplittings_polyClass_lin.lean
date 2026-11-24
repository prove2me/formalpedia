-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:10.854354+00:00
-- url     : https://prove2.me/submissions/fd67ed73-7975-4f90-9765-e79fe6c3f0c3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN


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
theorem _root_.solution (ℓ : Mat k r →ₗ[ℝ] ℂ) : PolyClass 1 (fun g => ℓ g) := by
  refine ⟨?_, fun a _ => ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun g => ℓ g, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    have h := ((LinearMap.toContinuousLinearMap ℓ).contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffOn
      (s := Set.univ)
    exact h
  · obtain ⟨ℓ', he⟩ := W_lin ℓ a
    refine ⟨∑ j : J k r, ‖ℓ' (Eb j)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun g _ => ?_⟩
    rw [he, pow_one]
    have eg : ℓ' g = ∑ j : J k r, co g j • ℓ' (Eb j) := by
      conv_lhs => rw [← Mv_co g, Mv_sum]
      rw [map_sum]; simp only [map_smul]
    show ‖ℓ' g‖ ≤ _
    rw [eg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hco : |co g j| ≤ ‖g j.1 j.2.1‖ := by
      unfold co; split_ifs
      · exact Complex.abs_im_le_norm _
      · exact Complex.abs_re_le_norm _
    exact hco.trans (entry_le_gN g _ _)
end Formalism.FourierDecayAlt.P.ListSumSplittings
