-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.ngInputs_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:31.318796+00:00
-- url     : https://prove2.me/submissions/6001324e-e935-4567-813a-aeaa2c0c4f8e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
variable {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu)
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution (k f C1 C0 A : ℕ) (CB b rd g TT cSt AAre e1 Ire : ℝ) :
    PN.NGInputs X N k f C1 C0 A CB b rd g TT cSt AAre e1 Ire ↔
      NGFin X N k f C1 C0 rd g TT AAre e1 ∧ NGReal X N f A CB b cSt Ire := by
  unfold PN.NGInputs NGFin NGReal
  tauto
end Formalism.L2.SG.RowsOther
