-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CardInsertEmbedding.sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:36:33.976321+00:00
-- url     : https://prove2.me/submissions/dc87ac72-eff5-4a46-b6b7-9e6a1579a76b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Theorems.Thm_Formalism_QuantumDeterminants_sum_fin_castLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.CardInsertEmbedding
open C2x2
namespace Formalism.FourierDecayAlt.P.CardInsertEmbedding
theorem _root_.solution {m k : ℕ} (hkm : k ≤ m) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) (g : Fin m → ℂ)
    (hg : ∀ j : Fin m, k ≤ j.val → g j = 0) : ∑ j, g j = ∑ t, g (e t) := by
  rw [sum_fin_castLE hkm g hg]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1; exact Fin.ext (he t).symm
end Formalism.FourierDecayAlt.P.CardInsertEmbedding
