-- Prove2me | solution 1 for DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T07:33:19.490733+00:00
-- url     : https://prove2.me/submissions/592fba1d-8eb7-4d6e-9dfe-33ec682e1a37

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Kappa
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_Poincare_Paths

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem DiaconisStroock.Poincare.var_eq_half_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : IsDist π) (φ : V → ℝ) :
    distVar π φ = 2⁻¹ * ∑ x, ∑ y, (φ x - φ y)^2 * (π x * π y) := by
  let m := distExp π φ
  let S := ∑ x, φ x ^ 2 * π x
  have hm : (∑ x, φ x * π x) = m := rfl
  have hv : distVar π φ = S - m ^ 2 := by
    unfold distVar
    change (∑ x, (φ x - m)^2 * π x) = S - m^2
    have he : ∀ x, (φ x - m)^2 * π x =
        φ x^2 * π x - (2*m)*(φ x*π x) + m^2*π x := fun x => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hm, hπ.2]
    change S - 2*m*m + m^2*1 = S-m^2
    ring
  have hi : ∀ x, (∑ y, (φ x-φ y)^2*(π x*π y)) =
      φ x^2*π x - (2*m)*(φ x*π x) + S*π x := by
    intro x
    have he : ∀ y, (φ x-φ y)^2*(π x*π y) =
        (φ x^2*π x)*π y - (2*φ x*π x)*(φ y*π y) + (φ y^2*π y)*π x :=
      fun y => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hπ.2, hm]
    change φ x^2*π x*1 - 2*φ x*π x*m + S*π x = _
    ring
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hm, hπ.2, hv]
  change S-m^2 = 2⁻¹*(S-2*m*m+S*1)
  norm_num
  ring
#print axioms DiaconisStroock.Poincare.var_eq_half_sum_sq

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare
namespace PoincarePath
lemma map_sum_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

lemma weighted {α : Type*} (l : List α) (w d : α → ℝ)
    (hw : ∀ a ∈ l, 0 < w a) :
    (l.map d).sum ^ 2 ≤ (l.map fun a => (w a)⁻¹).sum *
      (l.map fun a => w a * (d a)^2).sum := by
  simp_rw [map_sum_eq]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact le_of_lt (inv_pos.mpr (hw _ (List.get_mem _ _)))
  · intro i _; exact mul_nonneg (le_of_lt (hw _ (List.get_mem _ _))) (sq_nonneg _)
  · intro i _
    have hn : w (l.get i) ≠ 0 := ne_of_gt (hw _ (List.get_mem _ _))
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma telescope {V : Type*} (φ : V → ℝ) (p : List V) (x y : V)
    (hx : p.head? = some x) (hy : p.getLast? = some y) :
    ((pathEdges p).map fun e => φ e.2 - φ e.1).sum = φ y - φ x := by
  induction p generalizing x with
  | nil => simp at hx
  | cons a p ih =>
    have ha : a = x := by simpa using hx
    subst x
    cases p with
    | nil =>
      have ha : a = y := by simpa using hy
      subst y
      simp [pathEdges]
    | cons b p =>
      have ht := ih b (by rfl) (by simpa only [List.getLast?_cons_cons] using hy)
      simpa only [pathEdges, List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.sum_cons] using (show (φ b - φ a) +
          ((pathEdges (b :: p)).map fun e => φ e.2 - φ e.1).sum = φ y - φ a by
            rw [ht]; ring)
end PoincarePath

theorem DiaconisStroock.Poincare.sq_sub_le_qLength_mul {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (x y : V) (p : List V) (hp : IsWalk P π x y p) (φ : V → ℝ) :
    (φ y - φ x)^2 ≤ qLength P π p *
      ((pathEdges p).map fun e => edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1)^2).sum := by
  have h := PoincarePath.weighted (pathEdges p)
    (fun e => edgeMeasure P π e.1 e.2) (fun e => φ e.2 - φ e.1) hp.2.2
  rw [PoincarePath.telescope φ p x y hp.1 hp.2.1] at h
  exact h
#print axioms DiaconisStroock.Poincare.sq_sub_le_qLength_mul

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare
namespace PoincareCongestion
lemma list_sum {α : Type*} [Fintype α] [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → ℝ) :
    (l.map f).sum = ∑ a, if a ∈ l then f a else 0 := by
  rw [← List.sum_toFinset f hl]
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp
end PoincareCongestion

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) (φ : V → ℝ) :
    distVar π φ ≤ kappa P π Γ * dirichletForm P π φ := by
  classical
  let E : V × V → ℝ := fun e => edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1)^2
  let C : V × V → ℝ := fun e => ∑ x, ∑ y,
    if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y) * π x * π y else 0
  have hE : ∀ e, 0 ≤ E e := fun e =>
    mul_nonneg (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2)) (sq_nonneg _)
  have hpair : ∀ x y, (φ x - φ y)^2 * (π x * π y) ≤
      ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
        then qLength P π (Γ x y) * π x * π y else 0) * E e := by
    intro x y
    by_cases hxy : x = y
    · subst y; simp
    · have hp := hΓ x y hxy
      have hn := List.Nodup.of_map Sym2.mk hp.2
      have hb := DiaconisStroock.Poincare.sq_sub_le_qLength_mul P hP π x y (Γ x y) hp.1 φ
      have hw := mul_le_mul_of_nonneg_right hb (mul_nonneg (hπ.1.1 x) (hπ.1.1 y))
      have hs := PoincareCongestion.list_sum (pathEdges (Γ x y)) hn E
      change ((pathEdges (Γ x y)).map E).sum = _ at hs
      rw [hs] at hw
      have heq : qLength P π (Γ x y) * (∑ e : V × V, if e ∈ pathEdges (Γ x y) then E e else 0) * (π x*π y) =
          ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
            then qLength P π (Γ x y)*π x*π y else 0)*E e := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e ∈ pathEdges (Γ x y) <;> simp [hxy, he] <;> ring
      calc
        (φ x-φ y)^2*(π x*π y) = (φ y-φ x)^2*(π x*π y) := by ring
        _ ≤ _ := hw
        _ = _ := by
          convert heq using 1
          congr 2
          apply Finset.sum_congr rfl
          intro e _
          split <;> simp_all
  have htotal : (∑ x, ∑ y, (φ x-φ y)^2*(π x*π y)) ≤ ∑ e : V × V, C e * E e := by
    calc
      _ ≤ ∑ x, ∑ y, ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
          then qLength P π (Γ x y)*π x*π y else 0)*E e :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
      _ = _ := by
        simp_rw [show ∀ x, (∑ y, ∑ e : V × V,
            (if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y)*π x*π y else 0)*E e) =
            ∑ e : V × V, ∑ y, (if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y)*π x*π y else 0)*E e
            from fun x => Finset.sum_comm]
        rw [Finset.sum_comm]
        simp only [C, Finset.sum_mul]
  have hbound : ∀ e, C e * E e ≤ kappa P π Γ * E e := by
    intro e
    by_cases he : 0 < edgeMeasure P π e.1 e.2
    · have hc : C e ≤ kappa P π Γ :=
        le_ciSup (Finite.bddAbove_range
          (fun e : {e : V × V // 0 < edgeMeasure P π e.1 e.2} => C e.val)) ⟨e, he⟩
      exact mul_le_mul_of_nonneg_right hc (hE e)
    · have hz : edgeMeasure P π e.1 e.2 = 0 :=
        le_antisymm (le_of_not_gt he) (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2))
      simp [E, hz]
  have henergy : (∑ e : V × V, E e) = 2 * dirichletForm P π φ := by
    rw [Fintype.sum_prod_type]
    unfold dirichletForm
    have ht : ∀ x y, E (x,y) = (φ x-φ y)^2*(π x*P x y) := by
      intro x y
      dsimp [E, edgeMeasure]
      ring
    simp_rw [ht]
    ring
  rw [DiaconisStroock.Poincare.var_eq_half_sum_sq π hπ.1 φ]
  have hb := htotal.trans (Finset.sum_le_sum fun e _ => hbound e)
  rw [← Finset.mul_sum, henergy] at hb
  nlinarith
#print axioms solution

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- The Poincaré inequality reached in the proof of Proposition 1, p. 38. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) (φ : V → ℝ) :
    distVar π φ ≤ kappa P π Γ * dirichletForm P π φ := by
  exact solution P hP hirr π hπ hrev Γ hΓ φ

end DiaconisStroock.Poincare

#print axioms solution
