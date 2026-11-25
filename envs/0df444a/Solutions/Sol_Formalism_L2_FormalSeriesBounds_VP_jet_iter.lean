-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.jet_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:54.474416+00:00
-- url     : https://prove2.me/submissions/d59a5d3b-b7bd-452c-9cae-6c5a47b6ec84

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_lin
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (hD : DPullSt Y p) {n : ℕ} (b : Fin n) (u : Fin dd → C) (c : WVO I → C)
    (hu : u = ∑ w : WVO I, c w • (Y.raw (p w.1)).u w.2.1 w.2.2) (k : ℕ) :
    ∀ (q : MvPolynomial (Fin n × WVO I) C) (g : PS C n dd),
      jetAt0 q (pullN Y p ((DofN (Y.B.FK C) b u)^[k] g)) =
        jetAt0 (q * (∑ w : WVO I, MvPolynomial.C (c w) * MvPolynomial.X (b, w)) ^ k) (pullN Y p g) := by
  have hu' : u = fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i := by
    rw [hu]; funext i; rw [Finset.sum_apply]; rfl
  subst hu'
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, hD, ← jet_lin (fun w : WVO I => (b, w)), pow_succ, mul_assoc]
end Formalism.L2.FormalSeriesBounds.VP
