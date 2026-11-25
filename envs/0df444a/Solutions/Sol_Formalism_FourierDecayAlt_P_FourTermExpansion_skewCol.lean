-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.skewCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:12:27.955857+00:00
-- url     : https://prove2.me/submissions/9904e551-f95c-4c13-9c03-f043eb89ca17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_adj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {t : ℕ} (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin t)),
      qminorOp (Q.EH k r) a (b ∘ τ) u Φ g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • qminorOp (Q.EH k r) a b u Φ g := by
  intro b τ
  cases t with
  | zero =>
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; exact Submonoid.mem_top τ
    induction hτ using Submonoid.closure_induction generalizing b with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [adj a b i u Φ g hg hloc, Equiv.Perm.sign_swap (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne]
      simp
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [show b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y from rfl, ihy (b ∘ ⇑x), ihx b, smul_smul, Equiv.Perm.sign_mul]
      congr 1
      push_cast
      ring
end Formalism.FourierDecayAlt.P.FourTermExpansion
