-- Prove2me | solution 1 for Conway99.conway_99_not_vertex_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T18:33:27.61873+00:00
-- url     : https://prove2.me/submissions/939c6a25-bc2b-4fa2-9ede-8e0225a9cdbf

import Theorems.Thm_Conway99_conway_99_no_fixed_point_of_prime_order
import Theorems.Thm_Conway99_conway_99_orbit_matrix_exists
import Theorems.Thm_Conway99_conway_99_no_orbit_matrix
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum.Prime

open SimpleGraph

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    ¬ ∀ v w : V, ∃ f : g ≃g g, f v = w := by
  classical
  intro htrans
  have hV : Fintype.card V = 99 := h.card
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]; norm_num
  obtain ⟨v0⟩ := hne
  -- the automorphism group acts on `V`
  let : MulAction (g ≃g g) V :=
    { smul := fun f v => f v
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have : Finite (g ≃g g) := by
    apply Finite.of_injective (fun f : g ≃g g => (f : V → V))
    intro f₁ f₂ hf
    ext x
    exact congrFun hf x
  have : Fintype (g ≃g g) := Fintype.ofFinite _
  have horb : MulAction.orbit (g ≃g g) v0 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    obtain ⟨f, hf⟩ := htrans v0 w
    exact ⟨f, hf⟩
  have : Fintype (MulAction.orbit (g ≃g g) v0) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer (g ≃g g) v0) := Fintype.ofFinite _
  have e : MulAction.orbit (g ≃g g) v0 ≃ V :=
    (Equiv.setCongr horb).trans (Equiv.Set.univ V)
  have hcard : Fintype.card (MulAction.orbit (g ≃g g) v0) = 99 := by
    rw [Fintype.card_congr e, hV]
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (g ≃g g) v0
  have hdvd : (99 : ℕ) ∣ Fintype.card (g ≃g g) :=
    ⟨Fintype.card (MulAction.stabilizer (g ≃g g) v0), by rw [← hos, hcard]⟩
  have h11 : (11 : ℕ) ∣ Fintype.card (g ≃g g) := dvd_trans ⟨9, by norm_num⟩ hdvd
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := g ≃g g) 11 h11
  exact Conway99.conway_99_no_orbit_matrix
    (Conway99.conway_99_orbit_matrix_exists h σ hσ
      (Conway99.conway_99_no_fixed_point_of_prime_order h (by norm_num) (by norm_num) σ hσ))
