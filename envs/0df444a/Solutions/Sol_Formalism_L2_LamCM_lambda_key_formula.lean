-- Prove2me | solution 1 for Formalism.L2.LamCM.lambda_key_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:24.436324+00:00
-- url     : https://prove2.me/submissions/e2ff9c0e-7350-44be-842f-ec2352f55039

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
import Theorems.Thm_Formalism_L2_LamCM_key_degree_essential
import Theorems.Thm_Formalism_L2_LamCM_hadamard_local_base
import Theorems.Thm_Formalism_L2_LamCM_degree_algebraic
import Theorems.Thm_Formalism_L2_LamCM_finrank_pos_real
import Theorems.Thm_Formalism_L2_LamCM_lambda_number_base


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution : LamKey := by
  intro hKC K _ _ x T abelian₂ ℓ U H La logOm V _ c G μ n S Rr hT hL hloc harch hℓ hdne hLa hH hn hlocU hsq hnd
    hcf hmem hS hRr hev
  have hdeg := key_degree_essential hKC K x T abelian₂ hT hL hloc harch
  have hHad := hadamard_local_base K x.P.g abelian₂ ℓ U H La hL.1 hℓ hdne (by linarith) hH hn hlocU hsq
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  have hd := finrank_pos_real K
  have hnd' : T.dual.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (x.P.g : ℝ) / 4 * Real.log (2 * Real.pi) := by
    apply le_of_eq
    simp only [MLine.ndeg]
    rw [hdeg]
    field_simp
  exact lambda_number_base K x.P.g abelian₂ ℓ T.dual La logOm V c G μ n S Rr ⟨hL, hℓ, hTd, hLa, hHad, hnd, hnd'⟩ hcf hmem hS
    hRr hev
end Formalism.L2.LamCM
