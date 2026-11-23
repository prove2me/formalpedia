-- Prove2me | solution 1 for Formalism.GM.M.SSD.Good.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:21.948795+00:00
-- url     : https://prove2.me/submissions/e71f2868-b79a-4a49-907d-983135e06a30

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_Good_one

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
namespace Formalism.GM.M.SSD
namespace Good
theorem _root_.solution {f : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s) (n : ℕ) :
    Good sv (f ^ n) (n • a) (n • s) := by
  induction n with
  | zero => simpa using Good.one sv
  | succ n ih => rw [pow_succ, succ_nsmul, succ_nsmul]; exact ih.mul sv hf
end Good
end Formalism.GM.M.SSD
