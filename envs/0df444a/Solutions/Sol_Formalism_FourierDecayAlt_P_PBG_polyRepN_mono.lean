-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.polyRepN_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:31.244201+00:00
-- url     : https://prove2.me/submissions/494603d2-2125-4399-a939-09850a994017

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {d d' : ℕ} (hdd : d ≤ d') {f : ℂ → E} {top : E} (h : PolyRepN d f top) :
    PolyRepN d' f (if d = d' then top else 0) := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun l => if l ≤ d then c l else 0, ?_, fun u => ?_⟩
  · beta_reduce
    by_cases e : d = d'
    · subst e; simp [hc]
    · rw [if_neg (by omega), if_neg e]
  · beta_reduce
    rw [hf u]
    symm
    rw [← Finset.sum_subset (fun x hx => by simp at hx ⊢; omega : range (d + 1) ⊆ range (d' + 1))]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [if_pos (by simp at hl; omega)]
    · intro l _ hl
      rw [if_neg (by simp at hl; omega), smul_zero]
end Formalism.FourierDecayAlt.P.PBG
