-- Prove2me | solution 1 for Formalism.UG.P.stdform_Q_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:49.515682+00:00
-- url     : https://prove2.me/submissions/b6953343-9120-4cd5-984b-bb5786dba942

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] (M : Matrix n n ℂ) (e : n ≃ m)
    (y : n → ℂ) : stdformQ (M.reindex e e) (fun k => y (e.symm k)) = stdformQ M y := by
  unfold stdformQ
  congr 1
  refine Fintype.sum_equiv e.symm _ _ (fun k => ?_)
  refine Fintype.sum_equiv e.symm _ _ (fun l => ?_)
  simp [Matrix.reindex_apply]
end Formalism.UG.P
