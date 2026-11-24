-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.polyRepN_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:33.226259+00:00
-- url     : https://prove2.me/submissions/8891556b-5883-4a59-87da-194dedbdb826

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
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
theorem _root_.solution {d : ℕ} {f : ℂ → E} {top : E} (h : PolyRepN d f top) (a : ℂ) :
    PolyRepN d (fun Y => f (Y + a)) top := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun i => ∑ l ∈ range (d + 1), (a ^ (l - i) * (Nat.choose l i : ℂ)) • c l, ?_, fun Y => ?_⟩
  · beta_reduce
    rw [Finset.sum_eq_single d]
    · simp [hc]
    · intro l hl hne
      simp at hl
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · beta_reduce
    rw [hf (Y + a)]
    have e1 : ∀ l ∈ range (d + 1), (Y + a) ^ l • c l =
        ∑ i ∈ range (d + 1), (Y ^ i * (a ^ (l - i) * (Nat.choose l i : ℂ))) • c l := by
      intro l hl
      simp at hl
      rw [add_pow, Finset.sum_smul]
      rw [← Finset.sum_subset (fun x hx => by simp at hx ⊢; omega : range (l + 1) ⊆ range (d + 1))]
      · apply Finset.sum_congr rfl
        intro i _
        congr 1
        ring
      · intro i _ hi
        simp at hi
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [smul_smul]
end Formalism.FourierDecayAlt.P.PBG
