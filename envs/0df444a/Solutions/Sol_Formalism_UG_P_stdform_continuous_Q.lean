-- Prove2me | solution 1 for Formalism.UG.P.stdform_continuous_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:50.381747+00:00
-- url     : https://prove2.me/submissions/881d0b1e-30df-4a7b-9a83-7dfad493d0ba

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
theorem _root_.solution (M : Matrix n n ℂ) : Continuous (stdformQ M) := by
  unfold stdformQ
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((Complex.continuous_conj.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j))
end Formalism.UG.P
