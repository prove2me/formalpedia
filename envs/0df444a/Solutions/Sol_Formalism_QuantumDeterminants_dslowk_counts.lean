-- Prove2me | solution 1 for Formalism.QuantumDeterminants.dslowk_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:42.162429+00:00
-- url     : https://prove2.me/submissions/3398fdc9-1cd4-430e-a048-e800083254de

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => a < c ∧ ε c = ε a).card =
        (univ.filter fun c => b < c ∧ ε c = ε b).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => c < b ∧ ε c = ε b).card =
        (univ.filter fun c => c < a ∧ ε c = ε a).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + ncBetween ε a b + 1 + (a : ℕ) =
        (b : ℕ) := by
  have key : ∀ (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
      (c0 : Fin n), (∀ c, P c ↔ (Q c ∨ R c ∨ c = c0)) → (∀ c, Q c → ¬ R c) → (∀ c, Q c → c ≠ c0) →
      (∀ c, R c → c ≠ c0) → (univ.filter P).card = (univ.filter Q).card + (univ.filter R).card + 1 := by
    intro P Q R _ _ _ c0 hP hQR hQ hR
    have d1 : Disjoint (univ.filter R) {c0} := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hR c0 h rfl
    have d2 : Disjoint (univ.filter Q) ((univ.filter R).disjUnion {c0} d1) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion,
        Finset.mem_singleton] at hc hc'
      rcases hc' with h | h
      · exact hQR c hc h
      · exact hQ c hc h
    have : univ.filter P = (univ.filter Q).disjUnion ((univ.filter R).disjUnion {c0} d1) d2 := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion, Finset.mem_singleton]
      exact hP c
    rw [this, Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_singleton, add_assoc]
  have key2 : ∀ (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R],
      (∀ c, P c ↔ (Q c ∨ R c)) → (∀ c, Q c → ¬ R c) →
      (univ.filter P).card = (univ.filter Q).card + (univ.filter R).card := by
    intro P Q R _ _ _ hP hQR
    have d : Disjoint (univ.filter Q) (univ.filter R) :=
      Finset.disjoint_filter.2 fun c _ h1 h2 => hQR c h1 h2
    have : univ.filter P = (univ.filter Q).disjUnion (univ.filter R) d := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion]
      exact hP c
    rw [this, Finset.card_disjUnion]
  have hIoo : (univ.filter fun c : Fin n => a < c ∧ c < b).card = (b : ℕ) - a - 1 := by
    have : (univ.filter fun c : Fin n => a < c ∧ c < b) = Finset.Ioo a b := by
      ext c
      simp
    rw [this, Fin.card_Ioo]
  have hlt : (a : ℕ) < b := hab
  have h3 := key2 (fun c => a < c ∧ c < b) (fun c => a < c ∧ c < b ∧ ε c = ε a)
    (fun c => a < c ∧ c < b ∧ ε c ≠ ε a) (fun c => by tauto) (fun c h1 h2 => h2.2.2 h1.2.2)
  unfold ncBetween
  refine ⟨key _ _ _ b ?_ ?_ ?_ ?_, key _ _ _ a ?_ ?_ ?_ ?_, by omega⟩
  all_goals first | (intro c; grind) | skip
end Formalism.QuantumDeterminants
