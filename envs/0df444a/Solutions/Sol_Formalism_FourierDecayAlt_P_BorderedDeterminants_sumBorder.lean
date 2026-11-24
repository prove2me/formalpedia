-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:03.083154+00:00
-- url     : https://prove2.me/submissions/3cb33509-a271-46e5-af62-e93b9ac157b3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Theorems.Thm_Formalism_FourierDecayAlt_P_BorderedDeterminants_icast_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.BorderedDeterminants
theorem _root_.solution {n : ℕ} (Y H : Fin n → Module.End ℂ V) (M : Fin n → Fin n → Module.End ℂ V)
    (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (v : V) (h1 : ∀ x, ∑ i, Ψ i x = H x v)
    (h3 : ∀ i x : Fin n, ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • M a x (Ψ i a) = c i • Ψ i x) :
    (∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) * (Y x * M w x * H w)) v =
      ∑ x, Y x (∑ i, c i • Ψ i x) := by
  have key : ∀ w x : Fin n, ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) * (Y x * M w x * H w)) v =
      Y x (∑ i, ((-1 : ℂ) ^ ((w : ℕ) + (x : ℕ))) • M w x (Ψ i w)) := by
    intro w x
    rw [icast_apply, Module.End.mul_apply, Module.End.mul_apply, ← h1 w]
    simp only [map_sum, map_smul, Finset.smul_sum, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simp only [LinearMap.sum_apply, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← map_sum (Y x), Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => h3 i x)
end Formalism.FourierDecayAlt.P.BorderedDeterminants
