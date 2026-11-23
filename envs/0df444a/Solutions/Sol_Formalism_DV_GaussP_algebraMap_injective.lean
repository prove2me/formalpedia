-- Prove2me | solution 1 for Formalism.DV.GaussP.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:29.707823+00:00
-- url     : https://prove2.me/submissions/52c4968a-ffa7-402f-a58b-289c2f0a61bd

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism Formalism.DV Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
namespace Formalism.DV.GaussP
theorem _root_.solution : Function.Injective (algebraMap O A) := by
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.coe_comp, MvPolynomial.algebraMap_eq]
  exact (IsLocalization.injective (S := A) (M := (gaussIdeal σ O).primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))).comp (MvPolynomial.C_injective σ O)
end Formalism.DV.GaussP
