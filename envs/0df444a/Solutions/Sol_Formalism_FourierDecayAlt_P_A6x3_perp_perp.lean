-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:25.969807+00:00
-- url     : https://prove2.me/submissions/a5f39e80-1190-4068-bd71-c05fce1538d0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_le_perp_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_charOf_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_exists_charOf

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
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    perp ψ (perp ψ L) = L := by
  refine le_antisymm ?_ (le_perp_perp L)
  intro x hx
  have hfin' : L.relIndex A ≠ 0 := by
    intro h
    apply hfin
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hbL hLA, h, mul_zero]
  have : Finite (A ⧸ L.addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin'
  have hxA : x ∈ A := by
    rw [← hA]
    exact perp_anti (by rw [← hA]; exact perp_anti hLA) hx
  by_contra hxL
  have hne : ((⟨x, hxA⟩ : A) : A ⧸ L.addSubgroupOf A) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hxL
  obtain ⟨χ, hχ⟩ := AddChar.exists_apply_ne_zero.2 hne
  obtain ⟨z, hz, rfl⟩ := exists_charOf hA b hfin hbL hLA χ
  apply hχ
  rw [charOf_mk, mul_comm]
  exact hx z hz
end Formalism.FourierDecayAlt.P.A6x3
