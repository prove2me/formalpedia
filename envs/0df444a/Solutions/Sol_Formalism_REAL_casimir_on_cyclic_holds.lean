-- Prove2me | solution 1 for Formalism.REAL.casimir_on_cyclic_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:28.601819+00:00
-- url     : https://prove2.me/submissions/8a866444-b4fb-40f8-be75-aa10e0c24375

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_casimir_central_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : CasOnCyc := by
  intro V _ _ n E c u hE hu x hx
  have hcom := (casimir_central_holds (Module.End ℂ V) n (fun _ => true) E hE).1
  have hle : cyc E u ≤ LinearMap.ker (Cas E - c • (1 : Module.End ℂ V)) := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · simp [hu]
    · intro a b y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy ⊢
      have := congrArg (fun T : Module.End ℂ V => T y) (hcom a b)
      simp only [Module.End.mul_apply] at this
      rw [this, sub_eq_zero.mp hy, map_smul, sub_self]
  have := hle hx
  simpa [sub_eq_zero] using this
end Formalism.REAL
