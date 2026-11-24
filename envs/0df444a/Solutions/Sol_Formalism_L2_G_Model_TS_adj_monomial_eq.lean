-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.adj_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:04.020803+00:00
-- url     : https://prove2.me/submissions/24551c0b-c6bb-4948-8546-d563436b25fb

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint

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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {σ R : Type*} [CommRing R] (m : σ →₀ ℕ) (c : R) :
    (monomial m c : MvPolynomial σ R) = c • map (Int.castRingHom R) (monomial m (1 : ℤ)) := by
  rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
end Formalism.L2.G.Model.TS
