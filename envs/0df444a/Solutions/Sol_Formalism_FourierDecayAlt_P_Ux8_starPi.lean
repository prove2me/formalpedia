-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.starPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:39.75159+00:00
-- url     : https://prove2.me/submissions/ffda37a4-da46-4d03-89bd-8640206e4b46

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_CkOn_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Dw_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : StarPi := by
  intro k j ρ ι E _ _ _ F₁ A₁ B₁ Q K hB h
  have hC : B.CkOn (Q:ℕ∞) (B.GV k (j+ρ)) F₁ := CkOn_pi fun i => (h i).1
  refine ⟨hC, ?_, ?_⟩
  · intro g hg hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact (h i).2.1 g hg hi
  · intro u v hu hv hl g hg
    have hw : ∀ x ∈ wL u ++ wR v, inLie k (j+ρ) x.2 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1.1
      · exact (hv X hX).1.1
    have hlen : (wL u ++ wR v).length ≤ Q := by simpa [wL, wR] using hl
    have hpos : 0 < gN g ^ A₁ := Real.rpow_pos_of_pos (gN_pos hg) _
    rw [← le_div_iff₀' hpos]
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hB hpos.le)).mpr
    intro i
    rw [le_div_iff₀' hpos, dLR_eq, Dw_pi hw (sCkOn_mono (by exact_mod_cast hlen) hC) g hg i, ← dLR_eq]
    exact (h i).2.2 u v hu hv hl g hg
end Formalism.FourierDecayAlt.P.Ux8
