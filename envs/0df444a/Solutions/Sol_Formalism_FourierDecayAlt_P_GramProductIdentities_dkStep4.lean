-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:52.646813+00:00
-- url     : https://prove2.me/submissions/0f136476-bfe6-40ae-9e1a-2a711928c2c2

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : DKStep4 := by
  intro S q w L hL
  induction L with
  | nil => simp [kapF]
  | cons l L ih =>
    have hl : l.plus = true := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true := fun l' h => hL l' (by simp [h])
    have h1 : (L.map fun l' => if l.plus = l'.plus then (1:ℂ)
        else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨l', hl', rfl⟩ := hx
      simp [hl, hL' l' hl']
    simp only [kapF, List.map_cons, List.prod_cons]
    rw [h1, ih hL']
    simp only [ypt, hl, if_true]
    ring
end Formalism.FourierDecayAlt.P.GramProductIdentities
