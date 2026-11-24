-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.brk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:59.979692+00:00
-- url     : https://prove2.me/submissions/5b998207-1c7e-4f12-9d5c-92f80bb4207f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_idx_out
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_canIdx_isIndex
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_minorF_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_factor
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_prod_Ioc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) :
    brk (genMat k n) (genMat k n)⁻¹ μ I =
      (∏ c ∈ Finset.Ioc lo hi, sgnU k μ I c) •
        ((∏ c ∈ Finset.Ioc lo hi, if 1 ≤ c then (1 : GenField k n) else ((genMat k n).det)⁻¹) *
          algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)
            (tabMinors k (colT lo (hi - lo).toNat I))) := by
  unfold brk
  rw [finprod_eq_prod_of_mulSupport_subset (s := Finset.Ioc lo hi)]
  · rw [Finset.prod_congr rfl (fun c _ => factor (k := k) μ hI c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← map_prod, ← map_prod, ← Units.coe_prod, Units.smul_def, Algebra.smul_def,
      mul_assoc, prod_Ioc_eq lo hi (fun c => minorF (genX k n) (initSeg n (hatIdx I c).card) (hatIdx I c))]
    rfl
  · intro c hc
    by_contra hcn
    apply hc
    have hcn' : c ∉ Finset.Ioc lo hi := hcn
    show minorF _ (canIdx μ c) (I c) = 1
    rw [idx_out hlo hhi hb hI hcn', idx_out hlo hhi hb (canIdx_isIndex μ) hcn', minorF_empty]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
