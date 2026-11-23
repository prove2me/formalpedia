-- Prove2me | solution 1 for Formalism.GM.M.SSD.SFree.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:15.741128+00:00
-- url     : https://prove2.me/submissions/ea6728b3-9005-49e7-a5c8-ba9be18a8689

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)
omit [Nontrivial K]
namespace Formalism.GM.M.SSD
namespace SFree
theorem _root_.solution {f : MvPolynomial σ K} (hf : SFree sv f) (n : ℕ) : SFree sv (f ^ n) := by
  induction n with
  | zero => simpa using SFree.C sv (1 : K)
  | succ n ih => rw [pow_succ]; exact ih.mul sv hf
end SFree
end Formalism.GM.M.SSD
