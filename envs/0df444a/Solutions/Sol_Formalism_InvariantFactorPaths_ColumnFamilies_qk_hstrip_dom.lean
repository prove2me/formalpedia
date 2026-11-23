-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_hstrip_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:01.60186+00:00
-- url     : https://prove2.me/submissions/f8ceb2cf-2107-44c0-afad-e59bc9e7939d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_antitone_of_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) : Dominant nu ∧ Dominant mu :=
  ⟨qk_antitone_of_step fun a ha => (h.1 _).trans (h.2.1 a ha),
   qk_antitone_of_step fun a ha => (h.2.1 a ha).trans (h.1 a)⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
