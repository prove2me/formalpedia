-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.KP.regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:43.323776+00:00
-- url     : https://prove2.me/submissions/cf1f12e7-eb2a-4d81-833a-88bbac284492

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_TensorKP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
end Formalism.MainNotions.flipOneThree.Pf.KP
open MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf.KP
private theorem rg_prod_mem {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {T : Type} [DecidableEq T] (U : Finset T) (M : T → Submodule R A) (z : T → A)
    (hz : ∀ s, z s ∈ M s) : ∏ s ∈ U, z s ∈ ∏ s ∈ U, M s := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp (le_refl (1 : Submodule R A))
  | insert a U ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hz a) ih
end Formalism.MainNotions.flipOneThree.Pf.KP
end

set_option autoImplicit false
open MvPolynomial
open MvPolynomial
open MvPolynomial
open MvPolynomial
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
namespace Formalism.MainNotions.flipOneThree.Pf.KP
theorem _root_.solution {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {T α : Type} [Fintype T]
    [DecidableEq T] (N : T × Bool → Submodule R (MvPolynomial α K))
    (y : T → MvPolynomial (Bool × α) K)
    (hy : ∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)}) :
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K,
        (∀ x, F x ∈ N x) ∧ P = ∏ x, rename (fun v => (x, v)) (F x)} := by
  classical
  set G : T → Set (MvPolynomial (Bool × α) K) := fun s => {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)} with hG
  let ρ : ∀ s : T, MvPolynomial (Bool × α) K →ₗ[R] MvPolynomial ((T × Bool) × α) K := fun s =>
    ((rename (fun v : Bool × α => ((s, v.1), v.2)) :
      MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((T × Bool) × α) K).restrictScalars R).toLinearMap
  have h1 : ∀ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R (ρ s '' G s) := by
    intro s
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (f := ρ s) (hy s)
  have h2 := rg_prod_mem Finset.univ (fun s => Submodule.span R (ρ s '' G s)) _ h1
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro P hP
  rw [Set.mem_fintype_prod] at hP
  obtain ⟨g, hg, rfl⟩ := hP
  choose a ha hag using hg
  choose F hF hFa using ha
  refine ⟨fun x => F x.1 x.2, fun x => hF x.1 x.2, ?_⟩
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← hag s, hFa s]
  show rename (fun v : Bool × α => ((s, v.1), v.2)) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [rename_rename]
  rfl
end Formalism.MainNotions.flipOneThree.Pf.KP
