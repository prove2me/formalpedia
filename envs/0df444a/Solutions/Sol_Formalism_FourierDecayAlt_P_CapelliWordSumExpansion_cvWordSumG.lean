-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.cvWordSumG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:59:33.730124+00:00
-- url     : https://prove2.me/submissions/872329a6-389c-4ac6-9f78-776e40af2c4b

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_expand_words
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_sum_map_mul_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_expand_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_sum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution (k r : ℕ) (Y : ℂ) : ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        Q.CV k r Y f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  let ts : Equiv.Perm (Fin (Q.mdim k r 0)) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin (Q.mdim k r 0) =>
      (Q.uC k r 0 Y - ((j : ℕ) : ℂ), Q.posL k r 0 (σ j), Q.posL k r 0 j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin (Q.mdim k r 0)))).toList.flatMap
      (fun σ => (expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts, hm]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts, hm] using c
    have e1 : Q.CV k r Y f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • foldT (ts σ) f g := by
      simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [foldT, ts, List.map_ofFn]
      rfl
    rw [e1, sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← sum_map_mul_smul]
    rfl
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
