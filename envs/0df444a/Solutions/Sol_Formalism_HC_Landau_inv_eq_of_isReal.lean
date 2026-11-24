-- Prove2me | solution 1 for Formalism.HC.Landau.inv_eq_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:55.372467+00:00
-- url     : https://prove2.me/submissions/847e544a-b438-4c98-a684-4fdd172cb023

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution {ψ : PChar} (h : ψ.IsReal) : ψ.inv = ψ := by
  obtain ⟨N, χ, hp⟩ := ψ
  simp only [PChar.inv]
  congr 1
  refine MulChar.ext fun a => ?_
  rw [← MulChar.star_apply']
  exact Complex.conj_eq_iff_im.2 (h a)
end Formalism.HC.Landau
