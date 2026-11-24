-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.entry_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:09.615012+00:00
-- url     : https://prove2.me/submissions/605f2395-2ee3-4271-9cc8-7fef5e1408f5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_sum_comp


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution [NeZero ν] {At Al : Type} [Fintype At] [Fintype Al]
    (ξ : ZMod (2 * ν) → Fin r0 → K) (g : At → TpV ν r1) (pos : Al → ZMod (2 * ν)) (ht : Al → ℕ)
    (Tm : ∀ x, Fin (ht x) → Fin r0 → K) (Ic : ∀ x, Fin (ht x) → Fin r1) :
    ∃ (C : ℕ) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
      (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
      (∏ x, topForm ξ (g x)) * ∏ x, minorAt (pos x) (Tm x) (Ic x) = entryOp ξ e l sf T I ∧
      (∀ f : TpV ν r1 → ℕ, ∑ y, f y * e y = ∑ x, f (g x)) ∧
      (∀ f : ZMod (2 * ν) → (h : ℕ) → (Fin h → Fin r1) → ℕ,
        ∑ c, f (sf c) (l c) (I c) = ∑ x, f (pos x) (ht x) (Ic x)) ∧
      (∀ c i a, ∃ x i', T c i a = Tm x i' a) := by
  classical
  let q := (Fintype.equivFin Al).symm
  refine ⟨Fintype.card Al, fun y => (univ.filter (fun x => g x = y)).card, fun c => ht (q c),
    fun c => pos (q c), fun c => Tm (q c), fun c => Ic (q c), ?_, ?_, ?_, ?_⟩
  · unfold entryOp lowOp
    congr 1
    · rw [← Finset.prod_fiberwise univ g]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [Finset.prod_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.prod_const]
    · exact (Equiv.prod_comp q (fun x => minorAt (pos x) (Tm x) (Ic x))).symm
  · intro f
    rw [← Finset.sum_fiberwise univ g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
      smul_eq_mul, mul_comm]
  · intro f
    exact Equiv.sum_comp q (fun x => f (pos x) (ht x) (Ic x))
  · intro c i a
    exact ⟨q c, i, rfl⟩
end Formalism.InvariantFactorPaths.G7.EGauss
