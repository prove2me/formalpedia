-- Prove2me | solution 1 for Formalism.DV.GaussP.gaussIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:32.707799+00:00
-- url     : https://prove2.me/submissions/68b55d14-85d4-4b13-bb6a-a237789c60be

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
namespace Formalism.DV.GaussP
theorem _root_.solution : (gaussIdeal σ O).IsPrime := by
  have h := MvPolynomial.ker_map (σ := σ) (IsLocalRing.residue O)
  rw [IsLocalRing.ker_residue] at h
  unfold gaussIdeal
  rw [← h]
  exact RingHom.ker_isPrime _
end Formalism.DV.GaussP
