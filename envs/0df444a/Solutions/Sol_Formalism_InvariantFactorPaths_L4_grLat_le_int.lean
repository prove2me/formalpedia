-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.grLat_le_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:16.046316+00:00
-- url     : https://prove2.me/submissions/dd83fc55-6e2c-4eb6-a306-f4f15430781d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_norm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ IntPol p (Fin (K + 1) × Fin r) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ IntPol p (Fin (K + 1) × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2
  refine Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_
  rw [Formalism.GM.MeanGammaLemmas.coeff_initPart]
  split_ifs
  · exact Formalism.CountingSumsFrames.intPol_norm f hfI m
  · simp
end Formalism.InvariantFactorPaths.L4
