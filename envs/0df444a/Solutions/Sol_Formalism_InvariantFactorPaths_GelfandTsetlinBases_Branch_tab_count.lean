-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.tab_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:50.273788+00:00
-- url     : https://prove2.me/submissions/4755e4b2-da62-40f6-8327-4fea66cdeb67

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_card_restr
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_gtBox_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_shape_unique
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_exists_shape
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_card_of_existsUnique

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
theorem _root_.solution (n : ℕ) : ∀ μ : Fin n → ℤ, Antitone μ →
    Finite {T : ℤ → Finset (Fin n) // TabP μ T} ∧
      Nat.card {T : ℤ → Finset (Fin n) // TabP μ T} = dGT n μ := by
  induction n with
  | zero =>
    intro μ _
    have e : ∀ s : Finset (Fin 0), s = ∅ := fun s => Finset.eq_empty_of_isEmpty s
    have hall : ∀ T : ℤ → Finset (Fin 0), TabP μ T := by
      intro T
      unfold TabP
      refine ⟨fun c => ?_, fun c => ?_⟩
      · rw [e (T c)]
        show (∅ : Finset (Fin 0)).card = (univ.filter fun m => c ≤ μ m).card
        rw [e (univ.filter fun m => c ≤ μ m)]
      · intro x
        show cnt (T (c + 1)) x ≤ cnt (T c) x
        rw [e (T (c + 1))]
        simp [cnt]
    haveI : Unique {T : ℤ → Finset (Fin 0) // TabP μ T} :=
      { default := ⟨fun _ => ∅, hall _⟩
        uniq := fun T => Subtype.ext (funext fun c => e _) }
    exact ⟨inferInstance, by rw [Nat.card_unique]; rfl⟩
  | succ n ih =>
    intro μ hμ
    have hex : ∀ T : ℤ → Finset (Fin (n + 1)), TabP μ T →
        ∃ κ ∈ gtBox μ, ∀ c, (restr (T c)).card = colHeight κ c := by
      intro T hT
      have hc := fun c => card_eq_restr (T c)
      obtain ⟨κ, hκ, he⟩ := exists_shape hμ (fun c => (restr (T c)).card)
        (fun c => by
          show (restr (T (c + 1))).card ≤ (restr (T c)).card
          rw [card_restr, card_restr]
          exact hT.2 c n)
        (fun c => by
          show (restr (T c)).card ≤ colHeight μ c
          have h4 := hc c
          rw [hT.1 c] at h4
          split_ifs at h4 <;> omega)
        (fun c => by
          show colHeight μ c ≤ (restr (T c)).card + 1
          have h4 := hc c
          rw [hT.1 c] at h4
          split_ifs at h4 <;> omega)
        (fun c => by
          show (restr (T c)).card ≤ n
          exact le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n))
      exact ⟨κ, hκ, fun c => he c⟩
    have huniq : ∀ (T : ℤ → Finset (Fin (n + 1))) (κ κ' : Fin n → ℤ), TabP μ T → κ ∈ gtBox μ →
        κ' ∈ gtBox μ → (∀ c, (restr (T c)).card = colHeight κ c) →
        (∀ c, (restr (T c)).card = colHeight κ' c) → κ = κ' := by
      intro T κ κ' _ hκ hκ' he he'
      exact shape_unique (gtBox_anti hμ hκ) (gtBox_anti hμ hκ') fun c => (he c).symm.trans (he' c)
    have hfin : ∀ κ ∈ gtBox μ, Finite {T : ℤ → Finset (Fin (n + 1)) //
        TabP μ T ∧ ∀ c, (restr (T c)).card = colHeight κ c} := by
      intro κ hκ
      haveI := (ih κ (gtBox_anti hμ hκ)).1
      exact Finite.of_equiv _ (fibEquiv hμ hκ).symm
    obtain ⟨hF, hN⟩ := card_of_existsUnique (gtBox μ) (fun T => TabP μ T)
      (fun κ T => ∀ c, (restr (T c)).card = colHeight κ c) hex huniq hfin
    refine ⟨hF, ?_⟩
    rw [hN]
    show _ = ∑ κ ∈ gtBox μ, dGT n κ
    exact Finset.sum_congr rfl fun κ hκ =>
      (Nat.card_congr (fibEquiv hμ hκ)).trans (ih κ (gtBox_anti hμ hκ)).2
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
