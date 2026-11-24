-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:11:12.497717+00:00
-- url     : https://prove2.me/submissions/39216206-3df8-4c70-8df2-0a8be8bc9240

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} (P : (Fin m → Fin N) → Prop)
    [DecidablePred P] (X : Fin m → Fin N → ℂ) (S : Set (Fin N)) (hX : ∀ a p, p ∉ S → X a p = 0)
    (e : Fin m → Fin N) (he : P e) (huniq : ∀ c, P c → (∀ l, c l ∈ S) → c = e) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      (Matrix.of fun a l => X a (e l)).det • F e := by
  rw [Finset.sum_eq_single e]
  · rw [if_pos he]
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, c l ∈ S
      · exact absurd (huniq c hP hS) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hX a _ hl]), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ e) h
end Formalism.FourierDecayAlt.P.SignAntidiagonal
