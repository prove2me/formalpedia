-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.charOf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:27.513048+00:00
-- url     : https://prove2.me/submissions/960c09e9-89e7-45e4-837b-bc27bf48fc31

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_charOf_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (A : AddSubgroup K) {L : AddSubgroup K} {z z' : K} (hz : z ∈ perp ψ L)
    (hz' : z' ∈ perp ψ L) : charOf A hz = charOf A hz' ↔ z - z' ∈ perp ψ A := by
  constructor
  · intro h r hr
    have := DFunLike.congr_fun h ((⟨r, hr⟩ : A) : A ⧸ L.addSubgroupOf A)
    rw [charOf_mk, charOf_mk] at this
    rw [sub_mul, AddChar.map_sub_eq_div, this]
    exact div_self (AddChar.val_isUnit _ _).ne_zero
  · intro h
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H r =>
      rw [charOf_mk, charOf_mk]
      have := h r r.2
      rw [sub_mul, AddChar.map_sub_eq_div, div_eq_one_iff_eq (AddChar.val_isUnit _ _).ne_zero] at this
      exact this
end Formalism.FourierDecayAlt.P.A6x3
