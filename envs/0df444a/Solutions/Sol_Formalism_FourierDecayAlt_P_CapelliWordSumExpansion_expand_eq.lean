-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:19:51.295967+00:00
-- url     : https://prove2.me/submissions/8785b19a-b161-4c16-b437-8dfacdf8e6c8

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_spread
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_Xa_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_Xb_unit
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_EH_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_expand_words
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_sum_map_mul_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (f : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (ts.length : ℕ∞) f g →
      foldT ts f g = ((expand k r ts).map fun cw => cw.1 • Rw cw.2 f g).sum := by
  induction ts with
  | nil =>
    intro f g _ _
    simp [foldT, expand, Rw]
  | cons t ts ih =>
    intro f g hg hloc
    obtain ⟨U, hU, hgU, hUloc⟩ := loc_spread (loc_mono (m := (ts.length : ℕ∞))
      (by exact_mod_cast Nat.le_succ ts.length) hloc)
    have heq : ∀ x ∈ U, x ∈ GV k r →
        foldT ts f x = ((expand k r ts).map fun cw => cw.1 • Rw cw.2 f x).sum :=
      fun x hx hxG => ih f x hxG (hUloc x hx)
    have hlocw : ∀ cw ∈ expand k r ts, Loc 1 (Rw cw.2 f) g := by
      intro cw hcw
      obtain ⟨h1, h2⟩ := expand_words ts cw hcw
      simpa using loc_Rw hloc cw.2 (fun X hX => And.left (h1 X hX)) 1
        (by simp only [List.length_cons]; omega)
    have hR : ∀ Y, inLie k r Y → RdV Y (foldT ts f) g =
        ((expand k r ts).map fun cw => cw.1 • Rw (Y :: cw.2) f g).sum := by
      intro Y hY
      rw [rdV_congr hU hgU hg hY heq]
      exact rdV_sum (expand k r ts) (fun cw => cw.1) (fun cw => Rw cw.2 f) hg hY hlocw
    have hXa : inLie k r (Xa k r t.2.1 t.2.2) := And.left (Xa_unit _ _)
    have hXb : inLie k r (Xb k r t.2.1 t.2.2) := And.left (Xb_unit _ _)
    show Top (Q.EH k r) t.1 t.2.1 t.2.2 (foldT ts f) g = _
    rw [top_apply', EH_apply, hR _ hXa, hR _ hXb, heq g hgU hg]
    simp only [expand, List.map_append, List.sum_append, List.map_map, Function.comp_def, sum_map_mul_smul]
    split_ifs <;> simp [add_assoc]
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
