-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.eF_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:38.681627+00:00
-- url     : https://prove2.me/submissions/549accac-5b7c-4119-ac82-d6b8aa5d617c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_coeff_genE

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
variable {K σ : Type} [CommRing K] [Fintype σ]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution {g : ℕ} (x : Fin (g + 1) → K) (l : ℕ) :
    eF x (l + 1) = eF (fun i : Fin g => x i.castSucc) (l + 1) +
      x (Fin.last g) * eF (fun i : Fin g => x i.castSucc) l := by
  have hg : genE x = genE (fun i : Fin g => x i.castSucc) *
      (1 + PowerSeries.C (x (Fin.last g)) * PowerSeries.X) := by
    unfold genE
    rw [Fin.prod_univ_castSucc]
  rw [← coeff_genE, hg, mul_add, mul_one, map_add,
    show genE (fun i : Fin g => x i.castSucc) * (PowerSeries.C (x (Fin.last g)) * PowerSeries.X) =
      PowerSeries.C (x (Fin.last g)) * genE (fun i : Fin g => x i.castSucc) * PowerSeries.X by ring,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul, coeff_genE, coeff_genE]
end Formalism.InvariantFactorPaths.G7.CSym
