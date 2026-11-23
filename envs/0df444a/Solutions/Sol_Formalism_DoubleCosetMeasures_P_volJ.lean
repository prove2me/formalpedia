-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.volJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:30.193125+00:00
-- url     : https://prove2.me/submissions/f23dd0a4-f988-4f25-aad1-b77598dc0958

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_card_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_relIndex_mul_measure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_congSub_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.VolJ := by
  intro F _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a μ _ J' hKJ hJL
  have hKL : congSub O ϖ a ≤ GLint O a := fun g hg => hg.1
  have hcard := GLRed.card_eq O a ϖ hϖ hϖ0 hloc
  have hfinGL : Finite (GL (Fin a) (kF O ϖ hϖ)) := by
    have : Finite (Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) :=
      inferInstanceAs (Finite (Fin a → Fin a → kF O ϖ hϖ))
    exact Finite.of_injective _ Units.val_injective
  have hpos : Nat.card (GL (Fin a) (kF O ϖ hϖ)) ≠ 0 := Nat.card_pos.ne'
  have hrel : (congSub O ϖ a).relIndex (GLint O a) = Nat.card (GL (Fin a) (kF O ϖ hϖ)) := by
    rw [← hcard]; rfl
  have hmul := Subgroup.relIndex_mul_relIndex (congSub O ϖ a) J' (GLint O a) hKJ hJL
  have hJfin : J'.relIndex (GLint O a) ≠ 0 := by
    intro h0; rw [h0, mul_zero, hrel] at hmul; exact hpos hmul.symm
  have : (J'.subgroupOf (GLint O a)).FiniteIndex := ⟨hJfin⟩
  have hJopen : IsOpen (J' : Set (GL (Fin a) F)) :=
    Subgroup.isOpen_mono hKJ (GLRed.congSub_open O hO ϖ a)
  have hmeas := GLRed.relIndex_mul_measure J' (GLint O a) hJL hJopen.measurableSet μ
  have hq : Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') = (congSub O ϖ a).relIndex J' := rfl
  rw [hq, ← hmeas, ← hrel, ← hmul]
  push_cast
  ring
end Formalism.DoubleCosetMeasures.P
