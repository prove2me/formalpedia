-- Prove2me | solution 1 for Formalism.REAL.isCompactInvariant_orthogonal_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:46.028985+00:00
-- url     : https://prove2.me/submissions/ae889d12-896f-4dd8-8a93-99aad5217e80

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F)
    {K S : Submodule ℂ V} (hK : KStable ε F K) (hS : KStable ε F S) : KStable ε F (Kᗮ ⊓ S) := by
  intro a b hab y hy
  rw [Submodule.mem_inf] at hy ⊢
  refine ⟨?_, hS a b hab y hy.2⟩
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hu b a hab.symm z y]
  exact (Submodule.mem_orthogonal K y).1 hy.1 _ (hK b a hab.symm z hz)
end Formalism.REAL
