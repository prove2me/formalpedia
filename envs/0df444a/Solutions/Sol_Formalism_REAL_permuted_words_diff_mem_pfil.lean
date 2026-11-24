-- Prove2me | solution 1 for Formalism.REAL.permuted_words_diff_mem_pfil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:07.180849+00:00
-- url     : https://prove2.me/submissions/0c2244f1-b6f2-4600-b3d8-e7c129473357

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_ew_cons
import Theorems.Thm_Formalism_REAL_pfil_monotone_in_length
import Theorems.Thm_Formalism_REAL_gl_commutator_apply
import Theorems.Thm_Formalism_REAL_compact_generator_word_mem_pfil
import Theorems.Thm_Formalism_REAL_poincare_filtration_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
section U1Pfil
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
end U1Pfil
section U1Arr
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr
section U1Arr2
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr2
section U1Arr3
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr3
section U1Arr4
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr4
section U1Theta
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
private theorem bool_eq_of_ne_of_ne {p q r : Bool} (h1 : p ≠ q) (h2 : q ≠ r) : p = r := by
  cases p <;> cases q <;> cases r <;> simp_all
end U1Theta
end Formalism.REAL
end
end

set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (hE : GlRel E) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ l1 l2 : List (Fin n × Fin n), l1.Perm l2 → (∀ p ∈ l1, ε p.1 ≠ ε p.2) →
      ∀ m, l1.length = m + 1 → ew E l1 y - ew E l2 y ∈ pfil ε E u m := by
  intro l1 l2 hp
  induction hp with
  | nil =>
    intro _ m hm
    simp only [List.length_nil] at hm
    omega
  | @cons x l₁ l₂ h ih =>
    intro hnc m hm
    have hnc' : ∀ q ∈ l₁, ε q.1 ≠ ε q.2 := fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))
    simp only [ew_cons]
    rw [← map_sub]
    simp only [List.length_cons] at hm
    cases m with
    | zero =>
      have e1 : l₁ = [] := by
        first
        | exact List.eq_nil_of_length_eq_zero (by omega)
        | exact List.length_eq_zero_iff.mp (by omega)
        | exact List.length_eq_zero.mp (by omega)
      subst e1
      have e2 : l₂ = [] := by
        first
        | exact h.symm.eq_nil
        | exact h.nil_eq.symm
      subst e2
      rw [sub_self, map_zero]
      exact Submodule.zero_mem _
    | succ k =>
      exact poincare_filtration_succ ε E u hE k x.1 x.2 _ (ih hnc' k (by omega))
  | swap x z l =>
    intro hnc m hm
    simp only [List.length_cons] at hm
    have hx : ε x.1 ≠ ε x.2 := hnc x (by simp)
    have hz : ε z.1 ≠ ε z.2 := hnc z (by simp)
    have hl : ∀ q ∈ l, ε q.1 ≠ ε q.2 := fun q hq => hnc q (by simp [hq])
    have key : ∀ A B : V, A + B - A = B := fun A B => by abel
    simp only [ew_cons]
    rw [gl_commutator_apply E hE z.1 z.2 x.1 x.2, key]
    have hmono : pfil ε E u l.length ≤ pfil ε E u m := pfil_monotone_in_length ε E u (by omega)
    refine sub_mem ?_ ?_
    · split_ifs with h1
      · exact hmono (compact_generator_word_mem_pfil ε E u hE z.1 x.2
          (bool_eq_of_ne_of_ne hz (by rw [h1]; exact hx)) y hy l hl)
      · exact Submodule.zero_mem _
    · split_ifs with h2
      · exact hmono (compact_generator_word_mem_pfil ε E u hE x.1 z.2
          (bool_eq_of_ne_of_ne hx (by rw [h2]; exact hz)) y hy l hl)
      · exact Submodule.zero_mem _
  | @trans l₁ l₂ l₃ h12 h23 ih12 ih23 =>
    intro hnc m hm
    have hnc2 : ∀ q ∈ l₂, ε q.1 ≠ ε q.2 := fun q hq => hnc q (h12.mem_iff.mpr hq)
    have hlen : l₂.length = m + 1 := by rw [← h12.length_eq]; exact hm
    have e : ew E l₁ y - ew E l₃ y = (ew E l₁ y - ew E l₂ y) + (ew E l₂ y - ew E l₃ y) := by abel
    rw [e]
    exact add_mem (ih12 hnc m hm) (ih23 hnc2 m hlen)
end Formalism.REAL
