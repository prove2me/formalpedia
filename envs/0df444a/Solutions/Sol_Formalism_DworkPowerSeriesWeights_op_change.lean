-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.op_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:11.135273+00:00
-- url     : https://prove2.me/submissions/f3ef0848-c9d9-4eb8-bad5-f5423f5821a9

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bT_mul_bM
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_phi_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_minorProd


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (hx : ∀ τ, (x τ).det ≠ 0) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
    (hp : ∀ τ c, p τ c ≤ N0) (I : ∀ τ c, Fin (p τ c) → Fin N1) :
    (∏ τ : Bool × H, minorProd
        (fun (i : Fin N0) (b : Fin N1) => (∑ a, C (x τ i a) * X (τ, a, b) :
          MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ)) =
      aeval (fun y : Bool × H × Fin N0 × Fin N1 =>
          (∑ z, C (bA x y z) * X z : MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K))
        (∏ τ : Bool × H, rename (fun y => bE H N0 N1 (τ, y))
          (minorProd (oldRowLow (N1 := N1) (bT x τ)) (p τ) (hp τ) (I τ))) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← AlgHom.comp_apply, map_minorProd]
  congr 1
  funext i b
  simp only [AlgHom.comp_apply, oldRowLow, map_sum, map_mul, rename_C, rename_X, aeval_C, aeval_X,
    algebraMap_eq, phi_eq]
  conv_lhs => rw [← bT_mul_bM x hx τ]
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end Formalism.DworkPowerSeriesWeights
