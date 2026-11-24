-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.existsNormalForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.949632+00:00
-- url     : https://prove2.me/submissions/3eacfd35-d1ee-4fb9-8a46-424e4a60d788

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVectorNotMemSup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormMeetNeBot
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormDegenerateImpossible
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isAnisotropicOfPosDef
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_signatureOneComplementOfMinorNeZero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_existsScalarOfGramDefectZero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_nf_full

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  intro K V _ _ _ _ _ σ H r F F' hσ hT hT' hP hP' hrel hg
  have hA := isAnisotropicOfPosDef K V σ H r F hP
  have hA' := isAnisotropicOfPosDef K V σ H r F' hP'
  have hμ : ∃ μ : K, μ + star μ ≠ 0 := by
    refine ⟨F.T, fun h0 => ?_⟩
    have h1 := congrArg (fun t => (σ t).re) h0
    simp only [map_add, hσ, map_zero, Complex.add_re, Complex.zero_re] at h1
    rw [show star (σ F.T) = (starRingEnd ℂ) (σ F.T) from rfl, Complex.conj_re] at h1
    linarith
  by_cases hm : Formalism.HermitianLatticeCounting.S6.II F F' = ⊥
  · have hD : Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) ≠ 0 := fun hD =>
      normalFormDegenerateImpossible K V H r F F' hA hA' hm hD hg
    have hsig := signatureOneComplementOfMinorNeZero K V σ H r F F' hT hP hD
    obtain ⟨c, hz⟩ := existsScalarOfGramDefectZero K V σ H r F F' hσ hT hT' hsig hD hg
    have hc : c ≠ 0 := by
      rintro rfl
      apply lastVectorNotMemSup K V H r F' F
      rw [sup_comm]
      simpa using hz
    refine ⟨r, le_rfl, c, nf_full F F' hA hA' r le_rfl c ?_⟩
    unfold Formalism.HermitianLatticeCounting.S6.NFShape
    refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩
    · rw [hm, finrank_bot, Nat.sub_self]
    · intro x hx hx0
      rw [hm] at hx
      exact absurd ((Submodule.mem_bot K).1 hx) hx0
    · intro a ha
      exact absurd a.isLt (by omega)
    · rw [hm, bot_inf_eq]
    · rw [hm, bot_inf_eq]
    · rw [hm, sup_bot_eq]
      rfl
    · rw [hm, sup_bot_eq]
      rfl
  · obtain ⟨j, c, hj, hS⟩ := normalFormMeetNeBot K V H r F F' hμ hrel hm
    exact ⟨j, hj.le, c, nf_full F F' hA hA' j hj.le c hS⟩
end Formalism.HermitianLatticeCounting.P
