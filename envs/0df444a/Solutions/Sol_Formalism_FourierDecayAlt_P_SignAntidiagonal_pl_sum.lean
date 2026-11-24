-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:25:50.334136+00:00
-- url     : https://prove2.me/submissions/408d1a40-d0c0-4d20-bb28-790e45809017

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_add
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
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pl_congr (fun u => by simp) (pl_zero t)
  | insert i s hi ih =>
    exact pl_congr (fun u => by simp [Finset.sum_insert hi])
      (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))
end Formalism.FourierDecayAlt.P.SignAntidiagonal
