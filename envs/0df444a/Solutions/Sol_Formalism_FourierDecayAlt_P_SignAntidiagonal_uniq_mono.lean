-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:32.534786+00:00
-- url     : https://prove2.me/submissions/5a69e9c2-f858-441b-bf72-cc0a8095c094

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
theorem _root_.solution {α : Type} [LinearOrder α] {m : ℕ} (e c : Fin m → α) (he : StrictMono e) (hc : StrictMono c)
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have hcard : (Finset.image e Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ he.injective]; simp
  have hS' : ∀ l, c l ∈ Finset.image e Finset.univ := by
    intro l; obtain ⟨x, hx⟩ := hS l; rw [← hx]; exact Finset.mem_image_of_mem e (Finset.mem_univ x)
  rw [Finset.orderEmbOfFin_unique hcard hS' hc]
  exact (Finset.orderEmbOfFin_unique hcard (fun l => Finset.mem_image_of_mem e (Finset.mem_univ l)) he).symm
end Formalism.FourierDecayAlt.P.SignAntidiagonal
