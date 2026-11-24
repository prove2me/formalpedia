-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.weight_mapDomain_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:20.382824+00:00
-- url     : https://prove2.me/submissions/7002f899-12b3-43a4-80d9-b3b6821ca08d

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo

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
theorem _root_.solution {N N' n : ℕ} (hN : N ≤ N') (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (blockWt N' n)
        (Finsupp.mapDomain (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) d) =
      extW (Finsupp.weight (blockWt N n) d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by intro; simp)
    (by intros; simp [add_smul])]
  funext j
  simp only [extW, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWt, Pi.smul_apply,
    smul_eq_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
  · refine Finset.sum_eq_zero fun p _ => ?_
    have : j ≠ Fin.castLE hN p.1 := by
      intro e; apply h; rw [e]; simp
    simp [this]
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
