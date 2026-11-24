-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.prod_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:11.446134+00:00
-- url     : https://prove2.me/submissions/38324078-ebae-48d6-b508-c1b52ee3d12d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex

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
open Formalism.FourierDecayAlt.P.DeterminantReindex
open C2x2 CardInsertEmbedding
namespace Formalism.FourierDecayAlt.P.DeterminantReindex
theorem _root_.solution {m k n : ℕ} (hkn : k = n) (d : Fin m → ℂ) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) :
    ∏ t, d (e t) = ∏ j ∈ Finset.range n, (if h : j < m then d ⟨j, h⟩ else 1) := by
  subst hkn
  rw [← Fin.prod_univ_eq_prod_range (fun j => if h : j < m then d ⟨j, h⟩ else 1)]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hlt : t.val < m := by have := (e t).isLt; rw [he] at this; exact this
  rw [dif_pos hlt]; congr 1; exact Fin.ext (he t)
end Formalism.FourierDecayAlt.P.DeterminantReindex
