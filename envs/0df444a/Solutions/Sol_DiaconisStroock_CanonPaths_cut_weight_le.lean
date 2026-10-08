-- Prove2me | solution 1 for DiaconisStroock.CanonPaths.cut_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:37:17.392305+00:00
-- url     : https://prove2.me/submissions/4be656a9-2a54-43e9-a7e1-1cbcd79f75e3

import Mathlib
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_DiaconisStroock_Poincare_Paths

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted canon_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE CutCrossing
section

/- Independently reconstructed list-induction proof. The same approach was published
by miao for exists_cut_edge, accepted submission 206e8095-ecda-4e09-ab8a-04cde09f11bb.
That complete proof body was unavailable in the pinned official export. -/
namespace DiaconisStroock.CanonPaths

theorem exists_cut_edge {V : Type*} [DecidableEq V] (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∉ S) (p : List V)
    (hp : p.head? = some x) (hp' : p.getLast? = some y) :
    ∃ e ∈ DiaconisStroock.Poincare.pathEdges p, e.1 ∈ S ∧ e.2 ∉ S := by
  induction p generalizing x with
  | nil => simp at hp
  | cons a p ih =>
    have ha : a = x := by simpa using hp
    subst a
    cases p with
    | nil =>
      have hxy : x = y := by simpa using hp'
      exact False.elim (hy (hxy ▸ hx))
    | cons b p =>
      by_cases hb : b ∈ S
      · have hlast : (b :: p).getLast? = some y := by simpa using hp'
        obtain ⟨e, he, heS⟩ := ih b hb (by simp) hlast
        exact ⟨e, by simpa [DiaconisStroock.Poincare.pathEdges] using Or.inr he, heS⟩
      · exact ⟨(x,b), by simp [DiaconisStroock.Poincare.pathEdges], hx, hb⟩

end DiaconisStroock.CanonPaths
end
-- END MODULE CutCrossing

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted canon_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE CutLoad
section

open scoped BigOperators
namespace DiaconisStroock.CanonPaths
open MarkovMixing
namespace Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def edgeLoad (π : V → ℝ) (Γ : V → V → List V) (u v : V) : ℝ :=
  ∑ x, ∑ y, if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
    then π x * π y else 0

lemma edgeLoad_nonneg (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (Γ : V → V → List V)
    (u v : V) : 0 ≤ edgeLoad π Γ u v := by
  unfold edgeLoad
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    by split_ifs; exact mul_nonneg (hπ x) (hπ y); exact le_rfl

lemma edgeLoad_le_eta (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) (u v : V) :
    edgeLoad π Γ u v ≤ eta P π Γ * edgeMeasure P π u v := by
  have hQ : 0 ≤ edgeMeasure P π u v := mul_nonneg (hπ u) (hP.1 u v)
  by_cases hp : 0 < edgeMeasure P π u v
  · have hi : (edgeMeasure P π u v)⁻¹ * edgeLoad π Γ u v ≤ eta P π Γ :=
      le_ciSup (f := fun e : {e : V × V // 0 < edgeMeasure P π e.1 e.2} =>
        (edgeMeasure P π e.1.1 e.1.2)⁻¹ * edgeLoad π Γ e.1.1 e.1.2)
        (Finite.bddAbove_range _) ⟨(u,v),hp⟩
    have := mul_le_mul_of_nonneg_right hi hp.le
    have he : (edgeMeasure P π u v)⁻¹ * edgeLoad π Γ u v * edgeMeasure P π u v =
        edgeLoad π Γ u v := by field_simp
    rwa [he] at this
  · have hz : edgeMeasure P π u v = 0 := le_antisymm (le_of_not_gt hp) hQ
    have hl : edgeLoad π Γ u v = 0 := by
      unfold edgeLoad
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      intro hc
      exact hp ((hΓ x y hc.1).2.2 (u,v) hc.2)
    rw [hz,hl,mul_zero]

lemma pair_weight_le_cut (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : ∀ x, 0 ≤ π x) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ)
    (S : Finset V) (x y : V) (hx : x ∈ S) (hy : y ∈ Sᶜ) :
    π x * π y ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ,
      if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
      then π x * π y else 0 := by
  have hy' : y ∉ S := Finset.mem_compl.mp hy
  have hxy : x ≠ y := by intro h; exact hy' (h ▸ hx)
  obtain ⟨⟨u,v⟩,he,hu,hv⟩ := exists_cut_edge S x y hx hy' (Γ x y)
    (hΓ x y hxy).1 (hΓ x y hxy).2.1
  have hnon : ∀ u v : V, 0 ≤
      (if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
      then π x * π y else 0) := by
    intro u v; split_ifs; exact mul_nonneg (hπ x) (hπ y); exact le_rfl
  calc
    π x * π y = (if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
      then π x * π y else 0) := by rw [if_pos ⟨hxy,he⟩]
    _ ≤ ∑ v ∈ Sᶜ, if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
      then π x * π y else 0 := Finset.single_le_sum (fun v _ => hnon u v)
        (Finset.mem_compl.mpr hv)
    _ ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ,
      if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
      then π x * π y else 0 := Finset.single_le_sum
        (fun u _ => Finset.sum_nonneg fun v _ => hnon u v) hu

lemma cut_weight_le (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ : ∀ x, 0 ≤ π x) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ)
    (S : Finset V) :
    (∑ x ∈ S, π x) * (∑ y ∈ Sᶜ, π y) ≤
      eta P π Γ * ∑ u ∈ S, ∑ v ∈ Sᶜ, edgeMeasure P π u v := by
  let w : V → V → V → V → ℝ := fun u v x y =>
    if x ≠ y ∧ (u,v) ∈ DiaconisStroock.Poincare.pathEdges (Γ x y)
    then π x * π y else 0
  have hw : ∀ u v x y, 0 ≤ w u v x y := by
    intro u v x y; dsimp [w]; split_ifs; exact mul_nonneg (hπ x) (hπ y); exact le_rfl
  have hle : ∀ u v, (∑ x ∈ S, ∑ y ∈ Sᶜ, w u v x y) ≤ edgeLoad π Γ u v := by
    intro u v
    apply le_trans (Finset.sum_le_sum fun x _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hw u v x y))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => Finset.sum_nonneg fun y _ => hw u v x y)
  calc
    (∑ x ∈ S, π x) * (∑ y ∈ Sᶜ, π y) = ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * π y := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v x y :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
        pair_weight_le_cut P π hπ Γ hΓ S x y hx hy
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, ∑ x ∈ S, ∑ y ∈ Sᶜ, w u v x y := by
      calc
        _ = ∑ x ∈ S, ∑ u ∈ S, ∑ y ∈ Sᶜ, ∑ v ∈ Sᶜ, w u v x y :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ u ∈ S, ∑ x ∈ S, ∑ y ∈ Sᶜ, ∑ v ∈ Sᶜ, w u v x y := Finset.sum_comm
        _ = ∑ u ∈ S, ∑ x ∈ S, ∑ v ∈ Sᶜ, ∑ y ∈ Sᶜ, w u v x y :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, edgeLoad π Γ u v :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle u v
    _ ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, eta P π Γ * edgeMeasure P π u v :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
        edgeLoad_le_eta P hP π hπ Γ hΓ u v
    _ = eta P π Γ * ∑ u ∈ S, ∑ v ∈ Sᶜ, edgeMeasure P π u v := by
      simp only [Finset.mul_sum]

end Proof
end DiaconisStroock.CanonPaths
end
-- END MODULE CutLoad

-- SPDX-License-Identifier: Apache-2.0
-- Reused accepted proof modules are credited in source-provenance.json.
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.CanonPaths


open MarkovMixing

/-- The aggregate weight of paths leaving a cut is at most η times the stationary flow
across that cut (§3B, proof of Proposition 7, p. 54). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ0 : ∀ x, 0 ≤ π x) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ)
    (S : Finset V) :
    (∑ x ∈ S, π x) * (∑ y ∈ Sᶜ, π y) ≤
      eta P π Γ * ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y := by
  exact DiaconisStroock.CanonPaths.Proof.cut_weight_le P hP π hπ0 Γ hΓ S



#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- The aggregate weight of paths leaving a cut is at most η times the stationary flow
across that cut (§3B, proof of Proposition 7, p. 54). -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ0 : ∀ x, 0 ≤ π x) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ)
    (S : Finset V) :
    (∑ x ∈ S, π x) * (∑ y ∈ Sᶜ, π y) ≤
      eta P π Γ * ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y := by
  exact solution P hP π hπ0 Γ hΓ S

end DiaconisStroock.CanonPaths

#print axioms solution
