-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_listSumF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:33:51.494895+00:00
-- url     : https://prove2.me/submissions/5ad56df1-2f16-409b-aa16-6ce7c2d41b88

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {α : Type*} (φ : α → Mat k r → E) {m : ℕ∞} :
    ∀ (L : List α), (∀ a ∈ L, CkOn m (GV k r) (φ a)) →
      CkOn m (GV k r) (fun g => (L.map fun a => φ a g).sum) := by
  intro L
  induction L with
  | nil => intro _; simpa using (ckOn_const' (k := k) (r := r) (m := m) (0 : E))
  | cons a L ih =>
    intro hL
    have e : (fun g => ((a :: L).map fun a => φ a g).sum) = φ a + (fun g => (L.map fun a => φ a g).sum) := by
      funext g; simp
    rw [e]
    exact ckOn_add (hL a List.mem_cons_self) (ih fun b hb => hL b (List.mem_cons_of_mem _ hb))
end Formalism.FourierDecayAlt.P.ListSumSplittings
