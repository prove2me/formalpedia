-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.hodgeDegreeWindow_and_multiplicitySum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:29.033038+00:00
-- url     : https://prove2.me/submissions/8a54ada2-5174-42d6-a561-0da308add0b7

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_thWindow_part
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_multiplicitySum_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : THWindow ∧ DimSum := ⟨thWindow_part, multiplicitySum_holds⟩
end Formalism.WeaklyAdmissibleFiltrations
