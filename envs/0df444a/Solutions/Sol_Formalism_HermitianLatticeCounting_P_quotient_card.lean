-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:45.548752+00:00
-- url     : https://prove2.me/submissions/fe10528d-8c5c-434a-9f22-6590073307ff

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_count_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_count_le
import Theorems.Thm_Formalism_SLP_Final_omegaPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealCountLe := by
  intro E _ _ f y hf
  have h := DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 0 y Module.finrank_pos Formalism.SLP.Final.omegaPow
    (fun n hn => by simpa using ideal_count_eq E n hn)
  rw [hf] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  push_cast
  rw [zero_add]
end Formalism.HermitianLatticeCounting.P
