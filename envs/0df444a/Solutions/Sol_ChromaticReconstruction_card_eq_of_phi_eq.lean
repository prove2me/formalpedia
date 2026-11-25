-- Prove2me | solution 1 for ChromaticReconstruction.card_eq_of_phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:00:57.075796+00:00
-- url     : https://prove2.me/submissions/68667227-f5be-42be-a907-f85d50b496a5

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_card_eq_aux

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.Connected)
    (h : phi (uniformLeafExt q G) = phi (uniformLeafExt q H)) :
    Fintype.card V = Fintype.card W := by
  by_contra hne
  have hV := hG.nonempty
  have hW := hH.nonempty
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have h1' : 1 ≤ Fintype.card W := Fintype.card_pos
  by_cases hVc : 2 ≤ Fintype.card V
  · exact card_eq_aux hq G H hG hVc h hne
  · exact card_eq_aux hq H G hH (by omega) h.symm (Ne.symm hne)
end ChromaticReconstruction
