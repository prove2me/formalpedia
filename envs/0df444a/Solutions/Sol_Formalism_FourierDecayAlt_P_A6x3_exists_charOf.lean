-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.exists_charOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:42.475672+00:00
-- url     : https://prove2.me/submissions/b9c6abd7-a9ee-4d48-bff5-266f66c9a8d5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_charOf_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_bijective_mul

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
theorem _root_.solution {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A)
    (χ : AddChar (A ⧸ L.addSubgroupOf A) ℂ) : ∃ (z : K) (hz : z ∈ perp ψ L), χ = charOf A hz := by
  let π : A ⧸ (mulLat (b : K) A).addSubgroupOf A →+ A ⧸ L.addSubgroupOf A :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id A) (by
      intro x hx
      exact hbL hx)
  obtain ⟨q, hq⟩ := (dualMap_bijective_mul hA b hfin).2 (χ.compAddMonoidHom π)
  have hr : ∀ r : A, χ (r : A ⧸ L.addSubgroupOf A) = ψ (((Quotient.out q : perp ψ _) : K) * r) := by
    intro r
    have := DFunLike.congr_fun hq (r : A ⧸ (mulLat (b : K) A).addSubgroupOf A)
    rw [dualMap, charOf_mk] at this
    rw [this]
    rfl
  have hz : ((Quotient.out q : perp ψ _) : K) ∈ perp ψ L := by
    intro l hl
    rw [← hr ⟨l, hLA hl⟩]
    have : ((⟨l, hLA hl⟩ : A) : A ⧸ L.addSubgroupOf A) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hl
    rw [this, AddChar.map_zero_eq_one]
  refine ⟨_, hz, ?_⟩
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H r => rw [hr, charOf_mk]
end Formalism.FourierDecayAlt.P.A6x3
