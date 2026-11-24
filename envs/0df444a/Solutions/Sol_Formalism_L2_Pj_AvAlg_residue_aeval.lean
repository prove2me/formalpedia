-- Prove2me | solution 1 for Formalism.L2.Pj.AvAlg.residue_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:44.03492+00:00
-- url     : https://prove2.me/submissions/41882d32-ce02-4447-87a7-a6c6c26328bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
namespace Formalism.L2.Pj.AvAlg
theorem _root_.solution (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
end Formalism.L2.Pj.AvAlg
