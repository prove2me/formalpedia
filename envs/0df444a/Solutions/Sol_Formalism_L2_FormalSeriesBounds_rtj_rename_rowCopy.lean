-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_rename_rowCopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:02.096827+00:00
-- url     : https://prove2.me/submissions/ca7aa443-5533-4f8d-b193-3be2ad86f2e2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rowCopy_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (i : Fin K) (ρ : Fin (what₂ i)) (F : MvPowerSeries (WV I) C) :
    MvPowerSeries.rename (rtjE hpl i) (rowCopy ρ F) = rowCopy (pl ⟨i, ρ⟩) F := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, MvPowerSeries.rename_rename]
  apply rtj_rename_congr
  funext w
  rfl
end Formalism.L2.FormalSeriesBounds
