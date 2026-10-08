-- Prove2me | solution 1 for DiaconisStroock.OddPaths.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:03:44.547549+00:00
-- url     : https://prove2.me/submissions/f2196187-2ec7-4b13-a48c-4afd8c626dc9

import Mathlib
import Definitions.Def_DiaconisStroock_OddPaths_Iota
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_mm_basic

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem DiaconisStroock.OddPaths.eq_1_8 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ φ : V → ℝ, 2⁻¹ * ∑ x, ∑ y, (φ x+φ y)^2 * edgeMeasure P π x y =
      innerPi π φ φ + innerPi π φ (P.mulVec φ) := by
  intro φ
  have hc : ∀ y, ∑ x, π x * P x y = π y := by
    intro y
    exact congrFun hπ.2 y
  have ha : (∑ x, ∑ y, φ x^2 * (π x*P x y)) = innerPi π φ φ := by
    have ht : ∀ x y, φ x^2*(π x*P x y) = (φ x^2*π x)*P x y := by intros; ring
    simp_rw [ht, ← Finset.mul_sum, hP.2, mul_one]
    simp only [innerPi, pow_two]
  have hb : (∑ x, ∑ y, φ y^2 * (π x*P x y)) = innerPi π φ φ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hc]
    simp only [innerPi, pow_two]
  have hd : (∑ x, ∑ y, φ x*φ y*(π x*P x y)) = innerPi π φ (P.mulVec φ) := by
    change (∑ x, ∑ y, φ x*φ y*(π x*P x y)) =
      ∑ x, φ x * (∑ y, P x y * φ y) * π x
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have ht : ∀ x y, (φ x+φ y)^2 * edgeMeasure P π x y =
      φ x^2*(π x*P x y) + φ y^2*(π x*P x y) + 2*(φ x*φ y*(π x*P x y)) := by
    intro x y
    unfold edgeMeasure
    ring
  have hd2 : (∑ x, ∑ y, 2*(φ x*φ y*(π x*P x y))) =
      2 * (∑ x, ∑ y, φ x*φ y*(π x*P x y)) := by
    simp only [Finset.mul_sum]
  simp_rw [ht, Finset.sum_add_distrib]
  rw [ha, hb, hd2, hd]
  ring
#print axioms DiaconisStroock.OddPaths.eq_1_8

set_option autoImplicit false
open DiaconisStroock.Poincare
namespace OddPathAlternating
lemma telescope {V : Type*} (φ : V → ℝ) (p : List V) (x y : V)
    (hx : p.head? = some x) (hy : p.getLast? = some y) (k : ℕ) :
    ((pathEdges p).mapIdx fun i e => (-1 : ℝ)^(k+i)*(φ e.1+φ e.2)).sum =
      (-1 : ℝ)^k * φ x - (-1 : ℝ)^(k+(pathEdges p).length)*φ y := by
  induction p generalizing x k with
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
      have ht := ih b (by rfl) (by simpa only [List.getLast?_cons_cons] using hy) (k+1)
      have he : pathEdges (a :: b :: p) = (a,b) :: pathEdges (b :: p) := by
        simp [pathEdges]
      rw [he, List.mapIdx_cons, List.sum_cons]
      have hs : ((pathEdges (b :: p)).mapIdx fun i e =>
          (-1 : ℝ)^(k+(i+1))*(φ e.1+φ e.2)).sum =
          ((pathEdges (b :: p)).mapIdx fun i e =>
          (-1 : ℝ)^((k+1)+i)*(φ e.1+φ e.2)).sum := by
        congr 1
        congr 1
        funext i e
        rw [show k+(i+1)=(k+1)+i by omega]
      rw [hs, ht]
      simp only [Nat.add_zero, List.length_cons]
      rw [show k+1+(pathEdges (b :: p)).length = k+((pathEdges (b :: p)).length+1) by omega]
      rw [pow_succ]
      ring
end OddPathAlternating

theorem DiaconisStroock.OddPaths.two_mul_eq_alternating_sum {V : Type*} (x : V) (p : List V) (hhead : p.head? = some x)
    (hlast : p.getLast? = some x) (hodd : Odd (pathEdges p).length) :
    ∀ φ : V → ℝ, 2*φ x =
      ((pathEdges p).mapIdx fun i e => (-1 : ℝ)^i*(φ e.1+φ e.2)).sum := by
  intro φ
  have h := OddPathAlternating.telescope φ p x x hhead hlast 0
  simp only [Nat.zero_add, pow_zero, one_mul, hodd.neg_one_pow, neg_one_mul] at h
  linarith
#print axioms DiaconisStroock.OddPaths.two_mul_eq_alternating_sum

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.OddPaths
namespace OddPathCongestion
lemma map_sum_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl
lemma mapIdx_sum_eq {α : Type*} (l : List α) (f : ℕ → α → ℝ) :
    (l.mapIdx f).sum = ∑ i : Fin l.length, f i (l.get i) := by
  rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
lemma list_sum {α : Type*} [Fintype α] [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → ℝ) :
    (l.map f).sum = ∑ a, if a ∈ l then f a else 0 := by
  rw [← List.sum_toFinset f hl, ← Finset.sum_filter]
  congr 1
  ext a
  simp
lemma path_bound {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) (x : V) (p : List V)
    (hp : IsOddPath P π x p) (φ : V → ℝ) :
    (2*φ x)^2 ≤ qLength P π p *
      ((pathEdges p).map fun e => edgeMeasure P π e.1 e.2*(φ e.1+φ e.2)^2).sum := by
  let l := pathEdges p
  let w : Fin l.length → ℝ := fun i => edgeMeasure P π (l.get i).1 (l.get i).2
  let d : Fin l.length → ℝ := fun i => φ (l.get i).1+φ (l.get i).2
  have hw : ∀ i, 0 < w i := fun i => hp.1.2.2 _ (List.get_mem l i)
  have hcs : (∑ i : Fin l.length, (-1 : ℝ)^(i : ℕ)*d i)^2 ≤ (∑ i : Fin l.length, (w i)⁻¹)*(∑ i : Fin l.length, w i*(d i)^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact (inv_pos.mpr (hw i)).le
    · intro i _; exact mul_nonneg (hw i).le (sq_nonneg _)
    · intro i _
      have hs : ((-1 : ℝ)^(i : ℕ))^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      rw [mul_pow, hs, one_mul, ← mul_assoc, inv_mul_cancel₀ (hw i).ne', one_mul]
  rw [DiaconisStroock.OddPaths.two_mul_eq_alternating_sum x p hp.1.1 hp.1.2.1 hp.2.2 φ]
  unfold qLength
  simp_rw [map_sum_eq, mapIdx_sum_eq]
  exact hcs
end OddPathCongestion

theorem DiaconisStroock.OddPaths.inner_self_le_iota_mul {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    ∀ φ : V → ℝ, innerPi π φ φ ≤ iota P π S / 2 *
      (innerPi π φ φ + innerPi π φ (P.mulVec φ)) := by
  intro φ
  classical
  let E : V × V → ℝ := fun e => edgeMeasure P π e.1 e.2*(φ e.1+φ e.2)^2
  let C : V × V → ℝ := fun e => ∑ x,
    if e ∈ pathEdges (S x) then qLength P π (S x)*π x else 0
  have hE : ∀ e, 0 ≤ E e := fun e =>
    mul_nonneg (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2)) (sq_nonneg _)
  have hpair : ∀ x, 4*(φ x)^2*π x ≤
      ∑ e : V × V, (if e ∈ pathEdges (S x) then qLength P π (S x)*π x else 0)*E e := by
    intro x
    have hp := hS x
    have hw := mul_le_mul_of_nonneg_right (OddPathCongestion.path_bound P π x (S x) hp φ) (hπ.1.1 x)
    have hs := OddPathCongestion.list_sum (pathEdges (S x)) hp.2.1 E
    rw [hs] at hw
    have heq : qLength P π (S x)*(∑ e : V × V, if e ∈ pathEdges (S x) then E e else 0)*π x =
        ∑ e : V × V, (if e ∈ pathEdges (S x) then qLength P π (S x)*π x else 0)*E e := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ pathEdges (S x) <;> simp [he] <;> ring
    calc
      4*(φ x)^2*π x = (2*φ x)^2*π x := by ring
      _ ≤ _ := hw
      _ = _ := by
        convert heq using 1
        congr 2
        apply Finset.sum_congr rfl
        intro e _
        split <;> simp_all
  have htotal : 4*innerPi π φ φ ≤ ∑ e : V × V, C e*E e := by
    calc
      4*innerPi π φ φ = ∑ x, 4*(φ x)^2*π x := by
        simp only [innerPi, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ x, ∑ e : V × V, (if e ∈ pathEdges (S x) then qLength P π (S x)*π x else 0)*E e :=
        Finset.sum_le_sum fun x _ => hpair x
      _ = _ := by rw [Finset.sum_comm]; simp only [C, Finset.sum_mul]
  have hbound : ∀ e, C e*E e ≤ iota P π S*E e := by
    intro e
    by_cases he : 0 < edgeMeasure P π e.1 e.2
    · have hc : C e ≤ iota P π S := le_ciSup
        (Finite.bddAbove_range (fun e : {e : V × V // 0 < edgeMeasure P π e.1 e.2} => C e.val)) ⟨e,he⟩
      exact mul_le_mul_of_nonneg_right hc (hE e)
    · have hz : edgeMeasure P π e.1 e.2 = 0 :=
        le_antisymm (le_of_not_gt he) (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2))
      simp [E, hz]
  have henergy : (∑ e : V × V, E e) = 2*(innerPi π φ φ + innerPi π φ (P.mulVec φ)) := by
    rw [Fintype.sum_prod_type]
    have ht : ∀ x y, E (x,y) = (φ x+φ y)^2*edgeMeasure P π x y := by
      intro x y; dsimp [E]; ring
    simp_rw [ht]
    have h := DiaconisStroock.OddPaths.eq_1_8 P hP π hπ φ
    nlinarith [h]
  have hb := htotal.trans (Finset.sum_le_sum fun e _ => hbound e)
  rw [← Finset.mul_sum, henergy] at hb
  nlinarith [hb]
#print axioms DiaconisStroock.OddPaths.inner_self_le_iota_mul

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing
namespace OddPathStationary

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end OddPathStationary
#print axioms OddPathStationary.pi_pos

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.OddPaths

theorem DiaconisStroock.OddPaths.eigenvalue_ge {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    ∀ β : ℝ, IsEigenvalue P β → -1 + 2 / iota P π S ≤ β := by
  intro β hβ
  obtain ⟨f, hfne, hf⟩ := hβ
  have hpos := OddPathStationary.pi_pos hirr hπ hP
  have hx : ∃ x, f x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hfne (funext hn)
  obtain ⟨x, hfx⟩ := hx
  have hn : 0 < innerPi π f f := by
    unfold innerPi
    apply Finset.sum_pos'
    · intro y _; exact mul_nonneg (mul_self_nonneg _) (hπ.1.1 y)
    · exact ⟨x, Finset.mem_univ x, mul_pos (mul_self_pos.mpr hfx) (hpos x)⟩
  have hc : innerPi π f (P.mulVec f) = β * innerPi π f f := by
    rw [hf]
    change (∑ y, f y*(β*f y)*π y) = β*(∑ y, f y*f y*π y)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he : 0 ≤ innerPi π f f + innerPi π f (P.mulVec f) := by
    rw [← DiaconisStroock.OddPaths.eq_1_8 P hP π hπ f]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro y _
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hπ.1.1 y) (hP.1 y z))
  have hb := DiaconisStroock.OddPaths.inner_self_le_iota_mul P hP hirr π hπ hrev S hS f
  have hi : 0 < iota P π S := by
    by_contra hnot
    have hh : iota P π S / 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (by norm_num)
    have hp := mul_nonpos_of_nonpos_of_nonneg hh he
    linarith
  rw [hc] at hb
  have hs : 1 ≤ iota P π S / 2 * (1+β) := by
    apply (mul_le_mul_iff_right₀ hn).mp
    rw [mul_one]
    nlinarith [hb]
  have hd : 2 / iota P π S ≤ 1+β := (div_le_iff₀ hi).mpr (by nlinarith [hs])
  linarith
#print axioms DiaconisStroock.OddPaths.eigenvalue_ge

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.OddPaths

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (haper : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    -1 + 2 / iota P π S ≤ betaMin P := by
  have hx : ∃ x, 0 < π x := by
    by_contra hn
    push_neg at hn
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
    have hm := hπ.1.2
    linarith
  obtain ⟨x, hx⟩ := hx
  have h1 : IsEigenvalue P 1 := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hz
      have hc := congrFun hz x
      norm_num at hc
    · ext y
      change (∑ z, P y z*1) = 1*1
      simpa using hP.2 y
  apply le_csInf (show Set.Nonempty {β : ℝ | IsEigenvalue P β} from ⟨1, h1⟩)
  intro β hβ
  exact DiaconisStroock.OddPaths.eigenvalue_ge P hP hirr π hπ hrev S hS β hβ
#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.OddPaths

example {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (haper : Aperiodic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hrev : DetailedBalance P π) (S : V → List V)
    (hS : IsOddPathSystem P π S) :
    -1 + 2 / iota P π S ≤ betaMin P := by
  exact solution P hP hirr haper π hπ hrev S hS

end DiaconisStroock.OddPaths

#print axioms solution
