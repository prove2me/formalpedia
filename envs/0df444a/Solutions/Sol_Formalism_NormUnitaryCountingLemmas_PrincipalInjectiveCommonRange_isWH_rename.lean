-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:15.66816+00:00
-- url     : https://prove2.me/submissions/ed05bd8b-5008-4a96-8e5c-036422f52534

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_weight_mapDomain_castLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
theorem _root_.solution {N N' n : ℕ} (hN : N ≤ N') (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R)
    (hF : F.IsWeightedHomogeneous (blockWt N n) ν) :
    (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F).IsWeightedHomogeneous
      (blockWt N' n) (extW ν) := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    rw [weight_mapDomain_castLE, hr]
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
