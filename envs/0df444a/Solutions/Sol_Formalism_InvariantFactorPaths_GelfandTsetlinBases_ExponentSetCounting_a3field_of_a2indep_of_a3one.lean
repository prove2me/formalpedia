-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.a3field_of_a2indep_of_a3one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:09.5828+00:00
-- url     : https://prove2.me/submissions/79b9a413-6876-4d6a-9af0-9d398ddbe7a6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_psiFam_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_psiFam_good
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_good_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_good_smul_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_mem_span_inter

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
theorem _root_.solution (hI : LemmaA2indep) (h1 : LemmaA3one) : LemmaA3field := by
  intro k _ n N isVec B θ M G hn
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  constructor
  · rintro ⟨hG, hg⟩
    have hsp : ∀ i : {i : ℕ // i ≤ N}, G ∈ Submodule.span k
        (psiFam k n N isVec B '' {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      fun i => h1 k n N i.1 isVec B (θ i.1) (M i.1) G hn i.2 hG (hg i.1 i.2)
    have hint : G ∈ Submodule.span k (psiFam k n N isVec B ''
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      mem_span_inter hli (fun i : {i : ℕ // i ≤ N} => {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)})
        ⟨0, Nat.zero_le _⟩ G hsp
    have hset : {x : PathIdx n N isVec B | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)} =
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Subtype.forall]
    rw [hset]
    exact hint
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨psiFam_mem k N isVec B y, fun i hi => psiFam_good k hn hi isVec B (θ i) (M i) y (hy i hi)⟩
    | zero => exact ⟨Submodule.zero_mem _, fun i _ => good_zero k isVec i (θ i) (M i)⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => ?_⟩
      have hxy := good_smul_add k isVec i (θ i) (M i) 1 x y (hx.2 i hi) (hy.2 i hi)
      rwa [one_smul] at hxy
    | smul a x _ hx =>
      refine ⟨Submodule.smul_mem _ a hx.1, fun i hi => ?_⟩
      have hax := good_smul_add k isVec i (θ i) (M i) a x 0 (hx.2 i hi) (good_zero k isVec i (θ i) (M i))
      rwa [add_zero] at hax
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
