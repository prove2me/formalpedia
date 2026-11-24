-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.cptInCC_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:53.414844+00:00
-- url     : https://prove2.me/submissions/f93be7ee-b487-4e69-b1bb-b136242cfc92

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_compact_support_finite_class
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this
end Formalism.FourierDecayAlt.P.JFxG
