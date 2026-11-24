-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.ccMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:25:53.620836+00:00
-- url     : https://prove2.me/submissions/743d42eb-582a-4a8a-a6b4-d9e33cb8c43a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
private theorem one_le_gN_of_mem_GV {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.frobeniusNormedAddCommGroup
  have hH : gᴴ * Hpk k r * g = Hpk k r := hg
  have hne : Hpk k r ≠ 0 := by
    intro h0
    have h00 := congrFun (congrFun h0 ⟨r, by omega⟩) ⟨r, by omega⟩
    simp [Hpk] at h00
    try (split_ifs at h00 <;> norm_num at h00)
  have h1 : ‖Hpk k r‖ ≤ ‖g‖ ^ 2 * ‖Hpk k r‖ := by
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [hH]
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
      _ = ‖g‖ ^ 2 * ‖Hpk k r‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
  have hpos : 0 < ‖Hpk k r‖ := norm_pos_iff.2 hne
  have h2 : 1 ≤ ‖g‖ ^ 2 := by nlinarith
  have h3 : 1 ≤ ‖g‖ := by nlinarith [norm_nonneg g]
  have h4 : B.gN g = ‖g‖ := by
    unfold B.gN
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
  rw [h4]
  exact h3
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : CCMono := by
  intro k ρ E _ _ a AB c mm F hAB hF
  obtain ⟨hck, hb⟩ := hF
  refine ⟨hck, fun u v hu hv hl g hg => le_trans ?_ (hb u v hu hv hl g hg)⟩
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_gN_of_mem_GV g hg) hAB) (norm_nonneg _)
end Formalism.FourierDecayAlt.P.Ux8
