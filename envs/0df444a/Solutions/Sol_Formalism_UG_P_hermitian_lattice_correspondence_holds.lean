-- Prove2me | solution 1 for Formalism.UG.P.hermitian_lattice_correspondence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:30.498927+00:00
-- url     : https://prove2.me/submissions/6bf550c4-3057-4b49-909b-404d2c995d2a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Theorems.Thm_P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_Formalism_UG_P_hform_single
import Theorems.Thm_Formalism_UG_P_hform_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HermBridge := by
  intro K _ _ n _ _ h g
  unfold Formalism.UG.UJ HermitianLatticesTheory.isom
  constructor
  · intro hg x y
    have hg' : Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h := hg
    show h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y
    rw [glEquiv_apply', glEquiv_apply', hform_gram h ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y),
      hform_gram h x y, hform_mulVec, hg']
  · intro hg
    have hg' : ∀ x y : n → K, h (Formalism.UG.glEquiv g x) (Formalism.UG.glEquiv g y) = h x y := hg
    show Formalism.UG.cT (starRingEnd K) (g : Matrix n n K) * Formalism.UG.gram h * (g : Matrix n n K)
        = Formalism.UG.gram h
    ext i j
    have := hg' (Pi.single i 1) (Pi.single j 1)
    rw [glEquiv_apply', glEquiv_apply',
      hform_gram h ((g : Matrix n n K) *ᵥ Pi.single i 1) ((g : Matrix n n K) *ᵥ Pi.single j 1),
      hform_gram h (Pi.single i 1) (Pi.single j 1), hform_mulVec, hform_single, hform_single] at this
    exact this
end Formalism.UG.P
