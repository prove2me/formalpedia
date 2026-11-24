-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.card_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:22.699053+00:00
-- url     : https://prove2.me/submissions/3cbbe593-cf3f-4c81-805e-c0adb839c8c5

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
theorem _root_.solution (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ)
    (M : WithTop ℤ) :
    Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} =
      Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  set K := ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) with hK
  have hanti : ∀ P : GP n i isVec B θ M, Antitone (P.1 i) := fun P => P.2.1.2.1 i le_rfl
  have hF : ∀ P : GP n i isVec B θ M, Finite {x // ContP i N isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i N isVec B (P.1 i) x} = dGT n (P.1 i) * K :=
    fun P => hC n i N isVec B (P.1 i) hi (hanti P)
  have hG : ∀ P : GP n i isVec B θ M, Finite {x // ContP i i isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i i isVec B (P.1 i) x} = dGT n (P.1 i) := by
    intro P
    have h := hC n i i isVec B (P.1 i) le_rfl (hanti P)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [Finset.Ico_self, Finset.prod_empty, mul_one] at h2
    exact h2
  have he : ∀ P : GP n i isVec B θ M, Nonempty ({x // ContP i N isVec B (P.1 i) x} ≃
      {x // ContP i i isVec B (P.1 i) x} × Fin K) := by
    intro P
    haveI := (hF P).1
    haveI := (hG P).1
    haveI := Fintype.ofFinite {x // ContP i N isVec B (P.1 i) x}
    haveI := Fintype.ofFinite {x // ContP i i isVec B (P.1 i) x}
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      (hF P).2, (hG P).2]
  let e : ∀ P : GP n i isVec B θ M,
      {x // ContP i N isVec B (P.1 i) x} ≃ {x // ContP i i isVec B (P.1 i) x} × Fin K :=
    fun P => Classical.choice (he P)
  let d : (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x} × Fin K) ≃
      (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K :=
    { toFun := fun y => (⟨y.1, y.2.1⟩, y.2.2)
      invFun := fun z => ⟨z.1.1, (z.1.2, z.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)}
      = Nat.card ((Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K) :=
        Nat.card_congr (((splitEquiv hi isVec B θ M).trans (Equiv.sigmaCongrRight e)).trans d)
    _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * K := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin K), Fintype.card_fin,
          ← Nat.card_congr (splitEquiv (le_refl i) isVec B θ M)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
