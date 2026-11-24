-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:27.086381+00:00
-- url     : https://prove2.me/submissions/e9994207-ad0d-43d0-ba65-9c1706fb38ff

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_mono
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
theorem _root_.solution {N m : ℕ} (key : Fin N → ℕ) (hkey : Function.Injective key) (e c : Fin m → Fin N)
    (he : StrictMono (fun l => key (e l))) (hc : StrictMono (fun l => key (c l)))
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have h := uniq_mono (fun l => key (e l)) (fun l => key (c l)) he hc (by
    intro l; obtain ⟨x, hx⟩ := hS l; exact ⟨x, by simp only [hx]⟩)
  funext l; exact hkey (congrFun h l)
end Formalism.FourierDecayAlt.P.SignAntidiagonal
