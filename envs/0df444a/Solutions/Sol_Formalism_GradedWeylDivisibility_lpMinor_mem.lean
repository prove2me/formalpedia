-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lpMinor_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:53.595167+00:00
-- url     : https://prove2.me/submissions/f4247191-a149-4784-8889-d426211b3401

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem


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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lpMinor R s hr hn ∈ dualWeyl R r n (initW n s) := by
  have h : lpMinor R s hr hn = initMinor R (Fin.castLE hr) hn := rfl
  rw [h]
  exact initMinor_mem (Fin.castLE hr) hn
end Formalism.GradedWeylDivisibility
