-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weylP_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:47.555279+00:00
-- url     : https://prove2.me/submissions/eaf97ff0-6d8b-499c-82a3-a0801a14db53

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_inf_pol_le
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylLat_self
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_zpClosed_toAddSubgroup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_iSup_weylLat_div
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_polLatData_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hW : WeylInt) (hB : LatBasisPol) : WeylP := by
  intro p _ N r LL j _ la x hx hxi
  have he : kapC p r LL.total = (univ : Finset (Fin r)).card.choose 2 *
      Nat.log p (LL.total + (univ : Finset (Fin r)).card - 1) := by
    rw [kapC, Finset.card_univ, Fintype.card_fin]
  rw [he]
  have h1 := hW p _ _ (GAe p LL j (enumC (univ : Finset (Fin r)))) (Pol p r LL)
    (IntPol p (Fin N × Fin r)).toAddSubgroup LL.total (polLatData_of hB LL LL j _) (la ∘ enumC univ) x
    (isoC_inf_pol_le LL LL j univ la hx) hxi
  have hle : DeltaLat p (GAe p LL j (enumC (univ : Finset (Fin r))))
      {h | (GAe p LL j (enumC (univ : Finset (Fin r)))).IsHW (la ∘ enumC univ) h ∧ h ∈ Pol p r LL ∧
        h ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup} ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
        (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)),
        WeylLat p LL j h).toAddSubgroup := by
    refine sInf_le ⟨?_, zpClosed_toAddSubgroup _, ?_⟩
    · rintro h ⟨h1, h2, h3⟩
      exact (le_iSup_of_le h (le_iSup_of_le ⟨⟨(hwc_iff LL j univ la h).mpr h1, h2⟩, h3⟩ le_rfl) :
        WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
          (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h)
        (weylLat_self LL j h)
    · intro a b hab k y hy
      exact iSup_weylLat_div LL j _ _ _ (fun h => hab ((enumC univ).injective h)) k y hy
  exact hle h1
end Formalism.InvariantFactorPaths.PW
