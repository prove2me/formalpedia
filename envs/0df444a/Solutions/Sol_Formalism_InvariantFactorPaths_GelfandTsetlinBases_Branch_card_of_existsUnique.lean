-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.card_of_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.694212+00:00
-- url     : https://prove2.me/submissions/164029f2-e902-4443-aabb-c67180bb09c7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
theorem _root_.solution {α β : Type*} (s : Finset β) (P : α → Prop) (Q : β → α → Prop)
    (h : ∀ a, P a → ∃ b ∈ s, Q b a)
    (hu : ∀ a b b', P a → b ∈ s → b' ∈ s → Q b a → Q b' a → b = b')
    (fin : ∀ b ∈ s, Finite {a // P a ∧ Q b a}) :
    Finite {a // P a} ∧ Nat.card {a // P a} = ∑ b ∈ s, Nat.card {a // P a ∧ Q b a} := by
  let e : {a // P a} ≃ Σ b : s, {a // P a ∧ Q b.1 a} :=
    { toFun := fun a => ⟨⟨(h a.1 a.2).choose, (h a.1 a.2).choose_spec.1⟩,
        ⟨a.1, a.2, (h a.1 a.2).choose_spec.2⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := fun x => by
        obtain ⟨⟨b, hb⟩, ⟨a, hPa, hQa⟩⟩ := x
        have hbb : (h a hPa).choose = b :=
          hu a _ _ hPa (h a hPa).choose_spec.1 hb (h a hPa).choose_spec.2 hQa
        subst hbb
        rfl }
  haveI hF : ∀ b : s, Finite {a // P a ∧ Q b.1 a} := fun b => fin b.1 b.2
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_coe_sort s (fun b => Nat.card {a // P a ∧ Q b a})
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
