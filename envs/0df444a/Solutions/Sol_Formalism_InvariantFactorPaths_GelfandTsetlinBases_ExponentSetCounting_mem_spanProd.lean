-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.mem_spanProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:47:20.797271+00:00
-- url     : https://prove2.me/submissions/c4a7a238-f108-43ab-b1a1-42217d70f748

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas

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
theorem _root_.solution (hT : LemmaA3top) (hF : FactSplit) (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodG isVec i θ M G) :
    G ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
  obtain ⟨T, Gc, hTβ, hGc, hsum, hgood⟩ := hF k n N i isVec B θ M G hi hG
  rw [hsum]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hβe : β ∈ expSet n i N B := hTβ β hβ
  have hsp := hT k n i isVec B θ M (Gc β) hn (hGc β hβ) (hgood hg β hβ)
  have key : ∀ P ∈ Submodule.span k (psiFam k n i isVec B '' {x | GoodW θ M (x.1.1 i)}),
      P * monomial β 1 ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨y, hy⟩, ⟨β, hβe⟩), rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ a hx
  exact key _ hsp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
