-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.orthogonal_isomorphism_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:35.229886+00:00
-- url     : https://prove2.me/submissions/c1fa58b0-734b-41b5-a006-64e66f479097

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpV
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_gSall_le_perpV
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_perpS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_surj
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090


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
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : OrthIso := by
  intro p _ N r LL j Cs la mu hne x hx y hy
  rw [isoC_eq] at hx hy
  have hne' : la ∘ (enumC Cs) ≠ mu ∘ (enumC Cs) := by
    obtain ⟨c, hc, hlc⟩ := hne
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    intro h
    exact hlc (congrFun h a)
  have hB : (GAe p LL j (enumC Cs)).Stable
      ((GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (mu ∘ enumC Cs) v}) :=
    (GAe p LL j (enumC Cs)).gS_stable _
  have hle : (GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) v} ≤
      perpS ((GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (mu ∘ enumC Cs) v}) := by
    refine (GAe p LL j (enumC Cs)).gS_le ?_ (perpS_stable LL j (enumC Cs) hB)
    intro v hv
    rw [SetLike.mem_coe, mem_perpS]
    intro z hz
    have hz' := gSall_le_perpV LL j (enumC Cs) (Ne.symm hne') hv hz
    rwa [mem_perpV] at hz'
  have hxy := hle hx
  rw [mem_perpS] at hxy
  rw [fock_symm']
  exact hxy y hy
end Formalism.InvariantFactorPaths.PW
