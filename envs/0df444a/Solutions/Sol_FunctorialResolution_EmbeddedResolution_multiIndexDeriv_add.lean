-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:00.221948+00:00
-- url     : https://prove2.me/submissions/4d1c9aa3-877a-4429-a67c-526f40d014d3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
private theorem foldr_comm_of_comm {A : Type*} (E : A → A) :
    ∀ (n : ℕ) (F : Fin n → A → A), (∀ (i : Fin n) (y : A), E (F i y) = F i (E y)) →
      ∀ x : A, E (Fin.foldr n F x) = Fin.foldr n F (E x) := by
  intro n
  induction n with
  | zero =>
      intro F _ x
      simp
  | succ n ih =>
      intro F hF x
      rw [Fin.foldr_succ, Fin.foldr_succ, hF 0,
        ih (fun i => F i.succ) (fun i y => hF i.succ y) x]
private theorem multiIndexDeriv_add_of_comm_forall :
    ∀ (n : ℕ) (D : Fin n → Derivation k R R),
      (∀ i j : Fin n, ∀ x : R, D i (D j x) = D j (D i x)) →
      ∀ (α β : Fin n → ℕ) (x : R),
        multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) := by
  intro n
  induction n with
  | zero =>
      intro D _ α β x
      simp
  | succ n ih =>
      intro D hD α β x
      have key : ∀ (γ : Fin (n + 1) → ℕ) (y : R),
          multiIndexDeriv D γ y =
            (⇑(D 0))^[γ 0]
              (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => γ i.succ) y) := by
        intro γ y
        exact Fin.foldr_succ (fun (i : Fin (n + 1)) (z : R) => (⇑(D i))^[γ i] z) y
      have hcomm0 : ∀ (γ : Fin n → ℕ) (y : R),
          (⇑(D 0)) (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0)) y) := by
        intro γ y
        have hc : ∀ (i : Fin n) (z : R),
            (⇑(D 0)) ((⇑(D i.succ))^[γ i] z) = (⇑(D i.succ))^[γ i] ((⇑(D 0)) z) := by
          intro i z
          have hcomm : Function.Commute (⇑(D 0) : R → R) (⇑(D i.succ) : R → R) :=
            fun w => hD 0 i.succ w
          exact hcomm.iterate_right (γ i) z
        exact foldr_comm_of_comm (⇑(D 0)) n (fun i z => (⇑(D i.succ))^[γ i] z) hc y
      have hcomm : ∀ (m : ℕ) (γ : Fin n → ℕ) (y : R),
          (⇑(D 0))^[m] (multiIndexDeriv (fun i : Fin n => D i.succ) γ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) γ ((⇑(D 0))^[m] y) := by
        intro m γ y
        have hc : Function.Commute (multiIndexDeriv (fun i : Fin n => D i.succ) γ)
            (⇑(D 0) : R → R) := fun w => (hcomm0 γ w).symm
        exact (hc.iterate_right m y).symm
      have hidx : (fun i : Fin n => (α + β) i.succ)
          = (fun i : Fin n => α i.succ) + (fun i : Fin n => β i.succ) := by
        funext i
        simp
      rw [key (α + β) x, hidx,
        ih (fun i : Fin n => D i.succ) (fun i j w => hD i.succ j.succ w)
          (fun i : Fin n => α i.succ) (fun i : Fin n => β i.succ) x,
        key β x, key α, Pi.add_apply, Function.iterate_add_apply,
        hcomm (β 0) (fun i : Fin n => α i.succ)
          (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => β i.succ) x)]
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α β : Fin h → ℕ) (x : R) :
    multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) :=
  multiIndexDeriv_add_of_comm_forall h D hD α β x
end FunctorialResolution.EmbeddedResolution
