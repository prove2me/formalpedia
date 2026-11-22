-- Prove2me | solution 1 for Formalism.GM.ProjS.tv_we
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:15.169799+00:00
-- url     : https://prove2.me/submissions/242c918c-70e3-48e3-8dd4-805ffb4eaa0c

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) :
    ∀ c d, (Fin.cons zv w : Fin (r + 1) → σ) c ≠ (Fin.cons sv e : Fin (r + 1) → σ) d := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c d
  induction c using Fin.cases with
  | zero =>
    induction d using Fin.cases with
    | zero => simpa using hzs
    | succ d => simpa using (hz d).2.2.1.symm
  | succ c =>
    induction d using Fin.cases with
    | zero => simpa using (hz c).2.1
    | succ d => simpa using hwe c d
end Formalism.GM.ProjS
