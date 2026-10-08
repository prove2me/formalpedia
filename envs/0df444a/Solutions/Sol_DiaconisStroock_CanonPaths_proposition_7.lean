-- Prove2me | solution 1 for DiaconisStroock.CanonPaths.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T23:47:51.393316+00:00
-- url     : https://prove2.me/submissions/cbb05a5c-f0c1-49a4-815e-fb54ebb129bc

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me ac1ca0df-5149-4f12-be4a-089746537ba5.
-- Reused accepted contributions are attributed beside their full proof bodies.
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Mathlib
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

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

-- BEGIN MODULE MarkovPowers
section

set_option autoImplicit false

namespace DiaconisStroock.VarDist.Proof

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem stochastic_pow (P : Matrix V V ℝ) (hP : IsStochastic P) (n : ℕ) :
    IsStochastic (P^n) := by
  induction n with
  | zero =>
    constructor
    · intro x y; by_cases h : x = y <;> simp [h]
    · intro x; simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    constructor
    · intro x y
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih.1 x z) (hP.1 z y))
    · intro x
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP.2, mul_one]
      exact ih.2 x

theorem stationary_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : IsStationary P π) (n : ℕ) : Matrix.vecMul π (P^n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

theorem stationary_positive (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ x, 0 < π x := by
  intro x
  have he : ∃ z, 0 < π z := by
    by_contra hh
    push Not at hh
    have hz : ∀ z, π z = 0 := fun z => le_antisymm (hh z) (hπ.1.1 z)
    have h := hπ.1.2
    simp only [hz, Finset.sum_const_zero] at h
    norm_num at h
  obtain ⟨z, hz⟩ := he
  obtain ⟨n, hn⟩ := hirr z x
  have hb : π z * (P^n) z x ≤ ∑ y, π y * (P^n) y x :=
    Finset.single_le_sum (fun y _ => mul_nonneg (hπ.1.1 y) ((stochastic_pow P hP n).1 y x))
      (Finset.mem_univ z)
  have heq := congrFun (stationary_pow P π hπ n) x
  change (∑ y, π y * (P^n) y x) = π x at heq
  exact (mul_pos hz hn).trans_le (hb.trans_eq heq)

theorem detailedBalance_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hdb : DetailedBalance P π) (n : ℕ) : DetailedBalance (P^n) π := by
  induction n with
  | zero =>
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    have ht (z : V) : π x * ((P^n) x z * P z y) = (P^n) z x * (π y * P y z) := by
      calc _ = (π x * (P^n) x z) * P z y := by ring
        _ = (π z * (P^n) z x) * P z y := by rw [ih x z]
        _ = (P^n) z x * (π z * P z y) := by ring
        _ = _ := by rw [hdb z y]
    simp_rw [ht]
    have hp : P^n * P = P * P^n := (Commute.self_pow P n).eq.symm
    rw [hp, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by ring)

end DiaconisStroock.VarDist.Proof

end
-- END MODULE MarkovPowers

-- BEGIN MODULE BottleneckTransport
section

open scoped BigOperators
namespace DiaconisStroock.CanonPaths
open MarkovMixing
namespace Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma eta_pos (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hpos : ∀ x, 0 < π x) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) : 0 < eta P π Γ := by
  obtain ⟨x,y,hxy⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
  have hcut := cut_weight_le P hP π (fun x => (hpos x).le) Γ hΓ {x}
  have hy : y ∈ ({x} : Finset V)ᶜ := by simpa using hxy.symm
  have hsum : 0 < ∑ z ∈ ({x} : Finset V)ᶜ, π z :=
    lt_of_lt_of_le (hpos y) (Finset.single_le_sum (fun z _ => (hpos z).le) hy)
  have hl : 0 < (∑ z ∈ ({x} : Finset V), π z) * ∑ z ∈ ({x} : Finset V)ᶜ, π z := by
    simpa using mul_pos (hpos x) hsum
  have hflow : 0 ≤ ∑ u ∈ ({x} : Finset V), ∑ v ∈ ({x} : Finset V)ᶜ, edgeMeasure P π u v :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (hpos u).le (hP.1 u v)
  exact (mul_pos_iff.mp (lt_of_lt_of_le hl hcut)).resolve_right
    (fun h => (not_lt_of_ge hflow) h.2) |>.1

lemma bottleneckStar_ge (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (π : V → ℝ)
    (hπ : IsStationary P π) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ) :
    1 / (2 * eta P π Γ) ≤ bottleneckStar P π := by
  have hpos := DiaconisStroock.VarDist.Proof.stationary_positive P hP hirr π hπ
  have heta := eta_pos hV P hP π hpos Γ hΓ
  have hsub : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := by
    obtain ⟨x,hx⟩ : ∃ x : V, π x ≤ 2⁻¹ := by
      by_contra h
      push Not at h
      obtain ⟨x,y,hxy⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
      have hl : π x + π y ≤ ∑ z, π z := by
        calc
          _ = ∑ z ∈ ({x,y} : Finset V), π z := (Finset.sum_pair hxy).symm
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun z _ _ => (hpos z).le)
      have hx := h x
      have hy := h y
      rw [hπ.1.2] at hl
      norm_num at hx hy
      linarith
    exact ⟨⟨{x}, Finset.singleton_nonempty x, by simpa using hx⟩⟩
  unfold bottleneckStar
  apply le_ciInf
  intro S
  have hmass : 0 < ∑ x ∈ S.1, π x := by
    obtain ⟨x,hx⟩ := S.2.1
    exact lt_of_lt_of_le (hpos x) (Finset.single_le_sum (fun z _ => (hpos z).le) hx)
  have hsum : (∑ x ∈ S.1, π x) + ∑ y ∈ S.1ᶜ, π y = 1 := by
    rw [Finset.sum_add_sum_compl, hπ.1.2]
  have hc := cut_weight_le P hP π (fun x => (hpos x).le) Γ hΓ S.1
  have hhalf := S.2.2
  unfold bottleneckRatio
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * eta P π Γ) hmass).mpr
  have hm : (∑ x ∈ S.1, π x) / 2 ≤
      (∑ x ∈ S.1, π x) * ∑ y ∈ S.1ᶜ, π y := by
    have hcomp : (1:ℝ)/2 ≤ ∑ y ∈ S.1ᶜ, π y := by norm_num at hhalf; linarith
    nlinarith
  nlinarith

end Proof
end DiaconisStroock.CanonPaths
end
-- END MODULE BottleneckTransport

-- BEGIN MODULE AttributedSpectral
section
-- Prove2me | solution 1 for MarkovMixing.spectral_representation
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T15:43:54.786951+00:00
-- url     : https://prove2.me/submissions/08fa445e-a88f-49d5-95a3-a08e6457e6a3


open MarkovMixing
open scoped BigOperators

theorem MarkovMixing.spectral_representation {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (_hP : IsStochastic P)
    (π : V → ℝ) (_hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  classical
  set s : V → ℝ := fun x => Real.sqrt (π x) with hs_def
  have hs : ∀ x, 0 < s x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hs2 : ∀ x, s x * s x = π x := fun x => Real.mul_self_sqrt (hpos x).le
  -- the symmetrized matrix
  set A : Matrix V V ℝ := Matrix.of (fun x y => s x * P x y / s y) with hA_def
  have hAxy : ∀ x y, A x y = s x * P x y / s y := fun _ _ => rfl
  have hA : A.IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, star_trivial, hAxy]
    rw [div_eq_div_iff (hs x).ne' (hs y).ne']
    have h1 := hs2 x
    have h2 := hs2 y
    have h3 := hrev x y
    linear_combination P y x * h2 - P x y * h1 - h3
  set U : Matrix V V ℝ := (hA.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set lamV : V → ℝ := hA.eigenvalues with hlamV_def
  have hUstar : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUstar' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal lamV * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have : (RCLike.ofReal ∘ lamV) = lamV := by
      funext i; simp [RCLike.ofReal_real_eq_id]
    rw [this] at h
    simpa [hU_def, Unitary.coe_star] using h
  have hpow : ∀ t : ℕ, A ^ t = U * Matrix.diagonal (fun i => lamV i ^ t) * star U := by
    intro t
    induction t with
    | zero => simp [Matrix.diagonal_one, hUstar']
    | succ t ih =>
      rw [pow_succ, ih, hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUstar, Matrix.one_mul]
      rw [← Matrix.mul_assoc (Matrix.diagonal fun i => lamV i ^ t) (Matrix.diagonal lamV),
        Matrix.diagonal_mul_diagonal]
      congr 2
  have hcol : ∀ (i x : V), ∑ y, A x y * U y i = lamV i * U x i := by
    intro i x
    have h := congrFun (hA.mulVec_eigenvectorBasis i) x
    simpa [Matrix.mulVec, dotProduct, hU_def, hlamV_def,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hApow : ∀ (t : ℕ) (x y : V), (A ^ t) x y = s x * (P ^ t) x y / s y := by
    intro t
    induction t with
    | zero =>
      intro x y
      by_cases h : x = y
      · subst h; simp [(hs x).ne']
      · simp [h]
    | succ t ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ih x z, hAxy]
      have hz := (hs z).ne'
      have hy := (hs y).ne'
      field_simp
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with he_def
  refine ⟨fun j => lamV (e j), fun j x => U x (e j) / s x, ?_, ?_, ?_⟩
  · intro j
    funext x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hstep : ∀ y : V, P x y * (U y (e j) / s y) = A x y * U y (e j) / s x := by
      intro y
      rw [hAxy]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hstep y), ← Finset.sum_div,
      hcol (e j) x]
    ring
  · intro j k
    have h1 : innerPi π (fun x => U x (e j) / s x) (fun x => U x (e k) / s x)
        = ∑ x, U x (e j) * U x (e k) := by
      unfold innerPi
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hs2 x]
      have hx := (hs x).ne'
      field_simp
    have h2 : ∑ x, U x (e j) * U x (e k) = (star U * U) (e j) (e k) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.star_apply, star_trivial]
    rw [h1, h2, hUstar, Matrix.one_apply]
    simp [he_def]
  · intro t x y
    have hAt : (A ^ t) x y = ∑ i, U x i * U y i * lamV i ^ t := by
      rw [hpow t, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
      ring
    have hxy : (P ^ t) x y / π y = ((A ^ t) x y) / (s x * s y) := by
      rw [hApow t x y, ← hs2 y]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [hxy, hAt, Finset.sum_div]
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro j
    have hx := (hs x).ne'
    have hy := (hs y).ne'
    field_simp

end
-- END MODULE AttributedSpectral

-- BEGIN MODULE AttributedHarmonic
section
-- Prove2me | solution 1 for MarkovMixing.harmonic_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:12:20.971581+00:00
-- url     : https://prove2.me/submissions/ca23fe4f-600a-4e3c-84ec-fbb002a2a921


open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.harmonic_eq_const {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (h : V → ℝ) (hh : Harmonic P h) (x y : V) :
    h x = h y := by
  have : Nonempty V := ⟨x⟩
  have hpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hpow_row : ∀ (t : ℕ) (a : V), ∑ b, (P ^ t) a b = 1 := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ n * P) a b = ∑ z, (P ^ n) a z * P z b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun z _ => by rw [← Finset.mul_sum, hP.2 z, mul_one]]
        exact ih a
  have hharm_pow : ∀ (t : ℕ) (a : V), h a = ∑ b, (P ^ t) a b * h b := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have hmul : ∀ z : V, (P ^ n * P) a z = ∑ b, (P ^ n) a b * P b z := fun z => rfl
        rw [Finset.sum_congr rfl fun z _ => by rw [hmul z]]
        have expand : ∑ z, (∑ b, (P ^ n) a b * P b z) * h z
            = ∑ b, (P ^ n) a b * ∑ z, P b z * h z := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => by ring
        rw [expand]
        rw [ih a]
        exact Finset.sum_congr rfl fun b _ => by rw [← hh b]
  obtain ⟨x₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) h Finset.univ_nonempty
  have hmax' : ∀ z : V, h z ≤ h x₀ := fun z => hmax z (Finset.mem_univ z)
  have key : ∀ (t : ℕ) (z : V), 0 < (P ^ t) x₀ z → h z = h x₀ := by
    intro t z hz
    have hle : ∀ b ∈ (Finset.univ : Finset V),
        (P ^ t) x₀ b * h b ≤ (P ^ t) x₀ b * h (x₀) :=
      fun b _ => mul_le_mul_of_nonneg_left (hmax' b) (hpow_nonneg t x₀ b)
    have hEq : ∑ b, (P ^ t) x₀ b * h b = ∑ b, (P ^ t) x₀ b * h x₀ := by
      rw [← hharm_pow t x₀, ← Finset.sum_mul, hpow_row t x₀, one_mul]
    have hptw := (Finset.sum_eq_sum_iff_of_le hle).mp hEq z (Finset.mem_univ z)
    exact mul_left_cancel₀ hz.ne' hptw
  obtain ⟨t₁, ht₁⟩ := hirr x₀ x
  obtain ⟨t₂, ht₂⟩ := hirr x₀ y
  rw [key t₁ x ht₁, key t₂ y ht₂]

end
-- END MODULE AttributedHarmonic

-- BEGIN MODULE AttributedPositivePower
section
-- Prove2me | solution 1 for MarkovMixing.exists_pow_pos
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:27:47.960144+00:00
-- url     : https://prove2.me/submissions/765c0b4d-2656-464e-a35e-cd4745d26e79


open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.exists_pow_pos {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) :
    ∃ r : ℕ, 0 < r ∧ ∀ x y : V, 0 < (P ^ r) x y := by
  classical
  have hpow_nonneg : ∀ (s : ℕ) (a b : V), 0 ≤ (P ^ s) a b := by
    intro s
    induction s with
    | zero => intro a b; by_cases hab : a = b <;> simp [hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hchain : ∀ (a b : ℕ) (u v w : V),
      (P ^ a) u v * (P ^ b) v w ≤ (P ^ (a + b)) u w := by
    intro a b u v w
    have hsum : (P ^ (a + b)) u w = ∑ z, (P ^ a) u z * (P ^ b) z w := by
      rw [pow_add]; rfl
    rw [hsum]
    exact Finset.single_le_sum (f := fun z => (P ^ a) u z * (P ^ b) z w)
      (fun z _ => mul_nonneg (hpow_nonneg a u z) (hpow_nonneg b z w)) (Finset.mem_univ v)
  -- return sets are nonempty and closed under addition
  have hret_ne : ∀ a : V, ∃ t₀, t₀ ∈ returnSet P a := by
    intro a
    obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset V), 0 < P a b := by
      by_contra hcon
      push Not at hcon
      have hle : ∑ b, P a b ≤ 0 := Finset.sum_nonpos fun b hb => hcon b hb
      rw [hP.2 a] at hle
      linarith
    obtain ⟨s, hs⟩ := hirr b a
    refine ⟨1 + s, ⟨by omega, ?_⟩⟩
    have h1 : (P ^ 1) a b * (P ^ s) b a ≤ (P ^ (1 + s)) a a := hchain 1 s a b a
    have hpb : (0:ℝ) < (P ^ 1) a b := by simpa [pow_one] using hb
    nlinarith [mul_pos hpb hs]
  have hret_add : ∀ (a : V) (s t : ℕ), s ∈ returnSet P a → t ∈ returnSet P a →
      s + t ∈ returnSet P a := by
    intro a s t hs ht
    have hs1 := hs.1
    have ht1 := ht.1
    refine ⟨by omega, ?_⟩
    have h1 := hchain s t a a a
    nlinarith [mul_pos hs.2 ht.2]
  -- aperiodicity says the gcd of the return set is one
  have hgcd : ∀ a : V, Nat.setGcd (returnSet P a) = 1 := by
    intro a
    obtain ⟨t₀, ht₀⟩ := hret_ne a
    have hg_dvd : Nat.setGcd (returnSet P a) ∣ t₀ := Nat.setGcd_dvd_of_mem ht₀
    have hgpos : 0 < Nat.setGcd (returnSet P a) := by
      rcases Nat.eq_zero_or_pos (Nat.setGcd (returnSet P a)) with h | h
      · rw [h] at hg_dvd
        have h0 := Nat.eq_zero_of_zero_dvd hg_dvd
        have h1 := ht₀.1
        omega
      · exact h
    have hset : {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t}
        = {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} := by
      ext d
      simp only [Set.mem_ofPred_eq]
      exact Nat.dvd_setGcd_iff.symm
    have hsup : sSup {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t} = Nat.setGcd (returnSet P a) := by
      rw [hset]
      have hne : ({d : ℕ | d ∣ Nat.setGcd (returnSet P a)}).Nonempty :=
        ⟨Nat.setGcd (returnSet P a), dvd_rfl⟩
      have hbd : BddAbove {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} :=
        ⟨Nat.setGcd (returnSet P a), fun d hd => Nat.le_of_dvd hgpos hd⟩
      refine le_antisymm (csSup_le hne fun d hd => Nat.le_of_dvd hgpos hd)
        (le_csSup hbd dvd_rfl)
    have := hap a
    rw [period, hsup] at this
    exact this
  -- every sufficiently large integer is a return time
  have hbig : ∀ a : V, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 1 ≤ m → m ∈ returnSet P a := by
    intro a
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (s := returnSet P a)
    refine ⟨N, fun m hm hm1 => ?_⟩
    have hmem : m ∈ AddSubmonoid.closure (returnSet P a) := by
      refine hN m hm ?_
      rw [hgcd a]
      exact one_dvd m
    have hQ : ∀ k : ℕ, k ∈ AddSubmonoid.closure (returnSet P a) →
        k = 0 ∨ k ∈ returnSet P a := by
      intro k hk
      induction hk using AddSubmonoid.closure_induction with
      | mem z hz => exact Or.inr hz
      | zero => exact Or.inl rfl
      | add u v _ _ ihu ihv =>
          rcases ihu with rfl | hu
          · simpa using ihv
          · rcases ihv with rfl | hv
            · simpa using Or.inr hu
            · exact Or.inr (hret_add a u v hu hv)
    rcases hQ m hmem with h | h
    · omega
    · exact h
  choose N hN using hbig
  choose r hr using hirr
  refine ⟨(Finset.univ.sup N) + (Finset.univ.sup fun x => Finset.univ.sup fun y => r x y) + 1,
    by omega, ?_⟩
  intro x y
  set Nm := Finset.univ.sup N with hNm
  set Rm := Finset.univ.sup fun x => Finset.univ.sup fun y => r x y with hRm
  have hrle : r x y ≤ Rm := by
    refine le_trans ?_ (Finset.le_sup (f := fun x => Finset.univ.sup fun y => r x y)
      (Finset.mem_univ x))
    exact Finset.le_sup (f := fun y => r x y) (Finset.mem_univ y)
  have hNle : N x ≤ Nm := Finset.le_sup (Finset.mem_univ x)
  have hsplit : Nm + Rm + 1 = (Nm + Rm + 1 - r x y) + r x y := by omega
  have hmem : (Nm + Rm + 1 - r x y) ∈ returnSet P x :=
    hN x _ (by omega) (by omega)
  have hbound := hchain (Nm + Rm + 1 - r x y) (r x y) x x y
  rw [← hsplit] at hbound
  have := mul_pos hmem.2 (hr x y)
  linarith

end
-- END MODULE AttributedPositivePower

-- BEGIN MODULE AttributedEigenvalue
section
-- Prove2me | solution 1 for MarkovMixing.eigenvalue_basic
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:27:31.258491+00:00
-- url     : https://prove2.me/submissions/0b86e3de-d0e6-43c8-9710-3b898901618a


open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem MarkovMixing.eigenvalue_basic {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) :
    (∀ lam : ℝ, IsEigenvalue P lam → |lam| ≤ 1) ∧
    (MarkovMixing.Irreducible P → ∀ f : V → ℝ, P.mulVec f = f → ∀ x y : V, f x = f y) ∧
    (MarkovMixing.Irreducible P → Aperiodic P → ¬ IsEigenvalue P (-1)) := by
  classical
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hpow_row : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  refine ⟨?_, ?_, ?_⟩
  · -- (i) every eigenvalue has modulus at most one
    rintro lam ⟨f, hfne, hf⟩
    obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hfne (funext hcon)
    have : Nonempty V := ⟨z⟩
    obtain ⟨x₀, -, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V) (fun x => |f x|) Finset.univ_nonempty
    have hmax' : ∀ w : V, |f w| ≤ |f x₀| := fun w => hmax w (Finset.mem_univ w)
    have hx₀pos : 0 < |f x₀| :=
      lt_of_lt_of_le (abs_pos.mpr hz) (hmax' z)
    have hval : lam * f x₀ = ∑ y, P x₀ y * f y := by
      have h := congrFun hf x₀
      show lam * f x₀ = (P.mulVec f) x₀
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul]
    have hbound : |lam| * |f x₀| ≤ |f x₀| := by
      rw [← abs_mul, hval]
      calc |∑ y, P x₀ y * f y| ≤ ∑ y, |P x₀ y * f y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, P x₀ y * |f x₀| := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_of_nonneg (hP.1 x₀ y)]
            exact mul_le_mul_of_nonneg_left (hmax' y) (hP.1 x₀ y)
        _ = |f x₀| := by rw [← Finset.sum_mul, hP.2 x₀, one_mul]
    nlinarith [hbound, hx₀pos]
  · -- (ii) eigenfunctions of eigenvalue one are constant
    intro hirr f hf x y
    have hharm : Harmonic P f := by
      intro w
      have h := congrFun hf w
      exact h.symm
    exact MarkovMixing.harmonic_eq_const P hP hirr f hharm x y
  · -- (iii) `-1` is not an eigenvalue of an irreducible aperiodic chain
    rintro hirr hap ⟨f, hfne, hf⟩
    have hfneg : P.mulVec f = -f := by
      rw [hf]
      funext w
      simp
    rcases isEmpty_or_nonempty V with hV | hV
    · exact hfne (funext fun w => (IsEmpty.false w).elim)
    obtain ⟨r, hr0, hrpos⟩ := MarkovMixing.exists_pow_pos P hP hirr hap
    -- the doubled power is positive and fixes `f`
    set R : ℕ := 2 * r with hR
    have hRpos : ∀ x y : V, 0 < (P ^ R) x y := by
      intro x y
      have hsplit : (P ^ R) x y = ∑ z, (P ^ r) x z * (P ^ r) z y := by
        rw [hR, two_mul, pow_add]; rfl
      rw [hsplit]
      refine Finset.sum_pos (fun z _ => mul_pos (hrpos x z) (hrpos z y)) ?_
      exact ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    have hiter : ∀ n : ℕ, (P ^ n).mulVec f = ((-1 : ℝ) ^ n) • f := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ← Matrix.mulVec_mulVec, hfneg]
          have : (P ^ m).mulVec (-f) = -((P ^ m).mulVec f) := by
            funext w
            show ∑ y, (P ^ m) w y * (-f y) = -∑ y, (P ^ m) w y * f y
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun y _ => by ring
          rw [this, ih]
          funext w
          simp [pow_succ]
    have hfix : (P ^ R).mulVec f = f := by
      rw [hiter R, hR]
      have : ((-1 : ℝ) ^ (2 * r)) = 1 := by
        rw [pow_mul]
        norm_num
      rw [this, one_smul]
    -- `P ^ R` is stochastic and irreducible, so `f` is constant
    have hstochR : IsStochastic (P ^ R) := ⟨fun a b => hpow_nonneg R a b, hpow_row R⟩
    have hirrR : MarkovMixing.Irreducible (P ^ R) := by
      intro a b
      exact ⟨1, by rw [pow_one]; exact hRpos a b⟩
    have hharmR : Harmonic (P ^ R) f := by
      intro w
      exact (congrFun hfix w).symm
    have hconst : ∀ a b : V, f a = f b :=
      fun a b => MarkovMixing.harmonic_eq_const (P ^ R) hstochR hirrR f hharmR a b
    -- a constant eigenfunction of eigenvalue `-1` must vanish
    set x₀ : V := Classical.arbitrary V with hx₀
    have hcv : ∀ w : V, f w = f x₀ := fun w => hconst w x₀
    have hzero : f x₀ = - f x₀ := by
      have h := congrFun hfneg x₀
      show f x₀ = -f x₀
      have hlhs : (P.mulVec f) x₀ = f x₀ := by
        show ∑ y, P x₀ y * f y = f x₀
        rw [Finset.sum_congr rfl fun y _ => by rw [hcv y], ← Finset.sum_mul, hP.2 x₀, one_mul]
      rw [hlhs] at h
      simpa using h
    have : f x₀ = 0 := by linarith
    exact hfne (funext fun w => by rw [hcv w, this]; rfl)

end
-- END MODULE AttributedEigenvalue

-- BEGIN MODULE AttributedDirichlet
section
-- Prove2me | solution 1 for MarkovMixing.dirichlet_gap
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:08:20.807413+00:00
-- url     : https://prove2.me/submissions/616189f1-3392-44b3-8844-8247c63bd122



open scoped BigOperators
open MarkovMixing

namespace DirichletGap

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [h]
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
    push Not at hcon
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

omit [DecidableEq V] in
lemma innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq V] in
lemma dirichlet_eq_inner {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by
  have hrow : ∀ x, ∑ y, P x y = 1 := hP.2
  have hcol : ∀ y, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have A : ∑ x, ∑ y, (g x) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hrow x, mul_one]
    ring
  have B : ∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hcol y]
    ring
  have C : ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y)
      = ∑ x : V, g x * (P.mulVec g) x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (P.mulVec g) x = ∑ y, P x y * g y from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hall : ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y)
      = (∑ x : V, ∑ y : V, (g x) ^ 2 * (π x * P x y))
        + (∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y))
        - 2 * ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  show 2⁻¹ * ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y) = _
  rw [hall, A, B, C]
  show _ = (∑ x : V, g x * g x * π x) - ∑ x : V, g x * (P.mulVec g) x * π x
  ring

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by
  have e1 : ∀ j, innerPi π g (ff j) * ff j x = ∑ y : V, g y * π y * (ff j y * ff j x) := by
    intro j
    show (∑ y : V, g y * ff j y * π y) * ff j x = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  have e2 : ∀ y : V, ∑ j, g y * π y * (ff j y * ff j x)
      = g y * π y * ((if y = x then 1 else 0) / π x) := by
    intro y
    rw [← Finset.mul_sum, hcomp y x]
  rw [Finset.sum_congr rfl (fun y _ => e2 y),
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [hb])]
  have hx := (hpos x).ne'
  field_simp
  simp

lemma norm_eq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

lemma mulVec_expand (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by
  have e1 : ∀ y : V, P x y * g y = ∑ j, innerPi π g (ff j) * (P x y * ff j y) := by
    intro y
    have : ∀ j, innerPi π g (ff j) * (P x y * ff j y)
        = (innerPi π g (ff j) * ff j y) * P x y := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g y]
    ring
  show ∑ y : V, P x y * g y = _
  rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : V, P x y * ff j y = lam j * ff j x := by
    have := congrFun (heig j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [this]
  ring

lemma inner_mulVec (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * (P.mulVec g) x * π x
      = ∑ j, (innerPi π g (ff j) * lam j) * (g x * ff j x * π x) := by
    intro x
    rw [mulVec_expand heig hpos hcomp g x, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ x : V, g x * (P.mulVec g) x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * lam j * innerPi π g (ff j) = _
  ring

end Spectral

end DirichletGap

open DirichletGap

theorem MarkovMixing.dirichlet_gap {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.spectralGap P =
      sInf {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
        MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} ∧
    ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧ MarkovMixing.innerPi π f f = 1 ∧
      MarkovMixing.spectralGap P = MarkovMixing.dirichletForm P π f := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [dirichlet_eq_inner hP hπ g, norm_eq hpos hcomp g, inner_mulVec heig hpos hcomp g,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : ∀ (a : Fin (Fintype.card V) → ℝ) (k : Fin (Fintype.card V)),
      innerPi π (fun x => ∑ j, a j * ff j x) (ff k) = a k := by
    intro a k
    have e : ∀ x : V, (∑ j, a j * ff j x) * ff k x * π x
        = ∑ j, a j * (ff j x * ff k x * π x) := by
      intro x
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    show ∑ x : V, (∑ j, a j * ff j x) * ff k x * π x = a k
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    have e2 : ∀ j, ∑ x : V, a j * (ff j x * ff k x * π x)
        = a j * (if j = k then 1 else 0) := by
      intro j
      rw [← Finset.mul_sum]
      exact congrArg _ (horth j k)
    rw [Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by simp [hb])]
    simp
  -- the constant function
  set one : V → ℝ := fun _ => 1 with hone_def
  have hPone : P.mulVec one = one := by
    funext x
    show ∑ y, P x y * 1 = 1
    simpa using hP.2 x
  have hone_eig : ∀ j, innerPi π one (ff j) * (lam j - 1) = 0 := by
    intro j
    have hA : P.mulVec one = fun x => ∑ k, (innerPi π one (ff k) * lam k) * ff k x := by
      funext x
      rw [mulVec_expand heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [expand hpos hcomp one (Classical.arbitrary V)] at h0
    exact one_ne_zero h0
  obtain ⟨j0, hj0⟩ := hc1
  have hlam0 : lam j0 = 1 := by
    rcases mul_eq_zero.mp (hone_eig j0) with h | h
    · exact absurd h hj0
    · linarith
  set x0 : V := Classical.arbitrary V with hx0_def
  have const_inner : ∀ u v : V → ℝ, (∀ x y : V, u x = u y) → (∀ x y : V, v x = v y) →
      innerPi π u v = u x0 * v x0 := by
    intro u v hu hv
    have e : ∀ x : V, u x * v x * π x = (u x0 * v x0) * π x := by
      intro x; rw [hu x x0, hv x x0]
    show ∑ x : V, u x * v x * π x = _
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hsum, mul_one]
  have hffconst : ∀ x y : V, ff j0 x = ff j0 y := by
    have h1 : P.mulVec (ff j0) = ff j0 := by
      rw [heig j0, hlam0, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j0) h1
  have ha : ff j0 x0 * ff j0 x0 = 1 := by
    have := horth j0 j0
    rw [const_inner _ _ hffconst hffconst] at this
    simpa using this
  have ha0 : ff j0 x0 ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hlamne : ∀ j, j ≠ j0 → lam j ≠ 1 := by
    intro j hj hlam1
    have h1 : P.mulVec (ff j) = ff j := by rw [heig j, hlam1, one_smul]
    have hcj : ∀ x y : V, ff j x = ff j y := (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) h1
    have hb : ff j x0 * ff j0 x0 = 0 := by
      have := horth j j0
      rw [const_inner _ _ hcj hffconst] at this
      simpa [hj] using this
    have hbb : ff j x0 * ff j x0 = 1 := by
      have := horth j j
      rw [const_inner _ _ hcj hcj] at this
      simpa using this
    have : ff j x0 = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h ha0
    rw [this] at hbb
    norm_num at hbb
  -- the second-largest eigenvalue
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jstar, hjs_mem, hjs⟩ := Finset.exists_max_image (Finset.univ.erase j0) lam hne
  have hjs_ne : jstar ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have := horth j j
    rw [h] at this
    simp [innerPi] at this
  have hgap : MarkovMixing.spectralGap P = 1 - lam jstar := by
    have hmem : lam jstar ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} :=
      ⟨⟨ff jstar, hffne jstar, heig jstar⟩, hlamne jstar hjs_ne⟩
    have hbdd : ∀ r ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1}, r ≤ lam jstar := by
      rintro r ⟨⟨g, hg0, hg⟩, hr1⟩
      have hex : ∃ k, innerPi π g (ff k) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hg0
        funext x
        rw [← expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [mulVec_expand heig hpos hcomp g x]
      have hL : innerPi π (P.mulVec g) (ff k) = innerPi π g (ff k) * lam k := by
        rw [hA]; exact hcoef _ k
      have hR : innerPi π (P.mulVec g) (ff k) = r * innerPi π g (ff k) := by
        rw [hg]
        show ∑ x : V, (r • g) x * ff k x * π x = r * ∑ x : V, g x * ff k x * π x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply]; ring
      have hlamk : lam k = r := by
        have : innerPi π g (ff k) * lam k = innerPi π g (ff k) * r := by rw [← hL, hR]; ring
        exact mul_left_cancel₀ hk this
      have hkne : k ≠ j0 := by
        intro h; rw [h, hlam0] at hlamk; exact hr1 hlamk.symm
      rw [← hlamk]
      exact hjs k (Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩)
    show 1 - MarkovMixing.lambdaTwo P = 1 - lam jstar
    rw [show MarkovMixing.lambdaTwo P = lam jstar from
      le_antisymm (csSup_le ⟨_, hmem⟩ hbdd) (le_csSup ⟨lam jstar, hbdd⟩ hmem)]
  -- the minimiser
  have hfs_exp : MarkovMixing.distExp π (ff jstar) = 0 := by
    have h1 : innerPi π (ff jstar) (ff j0) = ff j0 x0 * MarkovMixing.distExp π (ff jstar) := by
      have e : ∀ x : V, ff jstar x * ff j0 x * π x = ff j0 x0 * (ff jstar x * π x) := by
        intro x; rw [hffconst x x0]; ring
      show ∑ x : V, ff jstar x * ff j0 x * π x = _
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      rfl
    rw [horth jstar j0] at h1
    simp [hjs_ne] at h1
    rcases h1 with h | h
    · exact absurd h ha0
    · exact h
  have hfs_norm : innerPi π (ff jstar) (ff jstar) = 1 := by simpa using horth jstar jstar
  have hfs_dir : MarkovMixing.dirichletForm P π (ff jstar) = 1 - lam jstar := by
    rw [hdir]
    rw [Finset.sum_eq_single_of_mem jstar (Finset.mem_univ jstar)
      (fun b _ hb => by rw [horth jstar b]; simp [Ne.symm hb])]
    rw [horth jstar jstar]
    simp
  have hmemS : (1 - lam jstar) ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} :=
    ⟨ff jstar, hfs_exp, hfs_norm, hfs_dir.symm⟩
  have hlb : ∀ e ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f},
      1 - lam jstar ≤ e := by
    rintro e ⟨g, hgexp, hgnorm, rfl⟩
    have hc0 : innerPi π g (ff j0) = 0 := by
      have e1 : ∀ x : V, g x * ff j0 x * π x = ff j0 x0 * (g x * π x) := by
        intro x; rw [hffconst x x0]; ring
      have : innerPi π g (ff j0) = ff j0 x0 * MarkovMixing.distExp π g := by
        show ∑ x : V, g x * ff j0 x * π x = _
        rw [Finset.sum_congr rfl (fun x _ => e1 x), ← Finset.mul_sum]
        rfl
      rw [this, hgexp, mul_zero]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Fintype.card V))),
        (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) ≤ (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
      intro j _
      by_cases hj : j = j0
      · subst hj; rw [hc0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have := hjs j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
        linarith
    calc 1 - lam jstar = (∑ j, (innerPi π g (ff j)) ^ 2) * (1 - lam jstar) := by
          rw [← norm_eq hpos hcomp g, hgnorm, one_mul]
      _ = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := Finset.sum_le_sum hterm
      _ = MarkovMixing.dirichletForm P π g := (hdir g).symm
  refine ⟨?_, ff jstar, hfs_exp, hfs_norm, ?_⟩
  · rw [hgap]
    exact le_antisymm (le_csInf ⟨_, hmemS⟩ hlb) (csInf_le ⟨1 - lam jstar, hlb⟩ hmemS)
  · rw [hgap, hfs_dir]

end
-- END MODULE AttributedDirichlet

-- BEGIN MODULE AttributedCheegerUpper
section
-- Prove2me | solution 1 for MarkovMixing.cheeger_upper
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:46:28.017916+00:00
-- url     : https://prove2.me/submissions/eff72ab6-82ba-426f-a096-60e18752c4dc



open scoped BigOperators
open MarkovMixing

namespace CheegerUp

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [h]
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
    push Not at hcon
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

end CheegerUp

open CheegerUp

theorem MarkovMixing.cheeger_upper {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.spectralGap P ≤ 2 * MarkovMixing.bottleneckStar P π := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x, π x = 1 := hπ.1.2
  obtain ⟨hgap, -⟩ := MarkovMixing.dirichlet_gap hV P hP hirr π hπ hrev
  -- the constraint set is nonempty
  have hne : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := by
    obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ 2⁻¹ := by
      by_contra hcon
      push Not at hcon
      have hcard : 1 < Fintype.card V := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have h1 : π x + π y ≤ ∑ z, π z := by
        have : ({x, y} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
        calc π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := by
              rw [Finset.sum_pair hxy]
          _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg this
              (fun i _ _ => (hpos i).le)
      have := hcon x
      have := hcon y
      linarith
    exact ⟨⟨{x}, ⟨Finset.singleton_nonempty x, by simpa using hx⟩⟩⟩
  -- the key bound for a single set
  have hkey : ∀ S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹},
      MarkovMixing.spectralGap P / 2 ≤ MarkovMixing.bottleneckRatio P π S.1 := by
    rintro ⟨S, hSne, hShalf⟩
    set p : ℝ := ∑ x ∈ S, π x with hp_def
    set q : ℝ := ∑ x ∈ Sᶜ, π x with hq_def
    have hpq : p + q = 1 := by rw [hp_def, hq_def, Finset.sum_add_sum_compl S π, hsum]
    have hppos : 0 < p := by
      obtain ⟨x, hx⟩ := hSne
      have : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    have hqpos : (2:ℝ)⁻¹ ≤ q := by linarith
    -- the test function
    set f : V → ℝ := fun x => if x ∈ S then -q else p with hf_def
    have hexp : MarkovMixing.distExp π f = 0 := by
      show ∑ x, f x * π x = 0
      rw [← Finset.sum_add_sum_compl S (fun x => f x * π x)]
      have e1 : ∀ x ∈ S, f x * π x = -q * π x := by
        intro x hx; rw [hf_def]; simp [hx]
      have e2 : ∀ x ∈ Sᶜ, f x * π x = p * π x := by
        intro x hx
        rw [Finset.mem_compl] at hx
        rw [hf_def]; simp [hx]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hp_def, ← hq_def]
      ring
    have hnorm : MarkovMixing.innerPi π f f = p * q := by
      show ∑ x, f x * f x * π x = p * q
      rw [← Finset.sum_add_sum_compl S (fun x => f x * f x * π x)]
      have e1 : ∀ x ∈ S, f x * f x * π x = (q * q) * π x := by
        intro x hx; rw [hf_def]; simp [hx]
      have e2 : ∀ x ∈ Sᶜ, f x * f x * π x = (p * p) * π x := by
        intro x hx
        rw [Finset.mem_compl] at hx
        rw [hf_def]; simp [hx]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hp_def, ← hq_def]
      linear_combination (p * q) * hpq
    -- the Dirichlet form of the test function is the edge flow across the cut
    set Q : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y with hQ_def
    have hQnn : 0 ≤ Q := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hpos x).le (hP.1 x y)
    have hsplit : ∀ g : V → V → ℝ, ∑ x, ∑ y, g x y
        = ((∑ x ∈ S, ∑ y ∈ S, g x y) + ∑ x ∈ S, ∑ y ∈ Sᶜ, g x y)
          + ((∑ x ∈ Sᶜ, ∑ y ∈ S, g x y) + ∑ x ∈ Sᶜ, ∑ y ∈ Sᶜ, g x y) := by
      intro g
      have e : ∀ x : V, ∑ y, g x y = (∑ y ∈ S, g x y) + ∑ y ∈ Sᶜ, g x y :=
        fun x => (Finset.sum_add_sum_compl S (fun y => g x y)).symm
      rw [← Finset.sum_add_sum_compl S (fun x => ∑ y, g x y),
        Finset.sum_congr rfl (fun x (_ : x ∈ S) => e x),
        Finset.sum_congr rfl (fun x (_ : x ∈ Sᶜ) => e x),
        Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hdir : MarkovMixing.dirichletForm P π f = Q := by
      show 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y) = Q
      rw [hsplit]
      have z1 : ∑ x ∈ S, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y) = 0 := by
        refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
        rw [hf_def]; simp [hx, hy]
      have z2 : ∑ x ∈ Sᶜ, ∑ y ∈ Sᶜ, (f x - f y) ^ 2 * (π x * P x y) = 0 := by
        refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
        rw [Finset.mem_compl] at hx hy
        rw [hf_def]; simp [hx, hy]
      have z3 : ∑ x ∈ S, ∑ y ∈ Sᶜ, (f x - f y) ^ 2 * (π x * P x y) = Q := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_compl] at hy
        simp only [hf_def, if_pos hx, if_neg hy]
        have h1 : (-q - p) ^ 2 = 1 := by nlinarith [hpq]
        rw [h1, one_mul]
      have z4 : ∑ x ∈ Sᶜ, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y) = Q := by
        have e : ∑ x ∈ Sᶜ, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y)
            = ∑ x ∈ Sᶜ, ∑ y ∈ S, π y * P y x := by
          refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
          rw [Finset.mem_compl] at hx
          simp only [hf_def, if_neg hx, if_pos hy]
          have h1 : (p - -q) ^ 2 = 1 := by nlinarith [hpq]
          rw [h1, one_mul, hrev x y]
        rw [e, Finset.sum_comm, hQ_def]
      rw [z1, z2, z3, z4]
      ring
    -- normalise
    have hpqpos : 0 < p * q := by nlinarith
    set c : ℝ := (Real.sqrt (p * q))⁻¹ with hc_def
    have hcsq : c ^ 2 = (p * q)⁻¹ := by
      rw [hc_def, inv_pow, Real.sq_sqrt hpqpos.le]
    set g : V → ℝ := fun x => c * f x with hg_def
    have hgexp : MarkovMixing.distExp π g = 0 := by
      show ∑ x, g x * π x = 0
      have e : ∀ x : V, g x * π x = c * (f x * π x) := fun x => by rw [hg_def]; ring
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      show c * MarkovMixing.distExp π f = 0
      rw [hexp, mul_zero]
    have hgnorm : MarkovMixing.innerPi π g g = 1 := by
      show ∑ x, g x * g x * π x = 1
      have e : ∀ x : V, g x * g x * π x = c ^ 2 * (f x * f x * π x) := fun x => by
        rw [hg_def]; ring
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      show c ^ 2 * MarkovMixing.innerPi π f f = 1
      rw [hnorm, hcsq]
      field_simp
    have hgdir : MarkovMixing.dirichletForm P π g = Q / (p * q) := by
      show 2⁻¹ * ∑ x, ∑ y, (g x - g y) ^ 2 * (π x * P x y) = Q / (p * q)
      have e : ∀ x y : V, (g x - g y) ^ 2 * (π x * P x y)
          = c ^ 2 * ((f x - f y) ^ 2 * (π x * P x y)) := by
        intro x y; rw [hg_def]; ring
      have e2 : ∀ x : V, ∑ y, (g x - g y) ^ 2 * (π x * P x y)
          = c ^ 2 * ∑ y, (f x - f y) ^ 2 * (π x * P x y) := by
        intro x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => e x y
      rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum]
      have : 2⁻¹ * (c ^ 2 * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y))
          = c ^ 2 * MarkovMixing.dirichletForm P π f := by
        show _ = c ^ 2 * (2⁻¹ * _)
        ring
      rw [this, hdir, hcsq]
      field_simp
    -- compare with the infimum
    have hbdd : BddBelow {e : ℝ | ∃ h : V → ℝ, MarkovMixing.distExp π h = 0 ∧
        MarkovMixing.innerPi π h h = 1 ∧ e = MarkovMixing.dirichletForm P π h} := by
      refine ⟨0, ?_⟩
      rintro e ⟨h, -, -, rfl⟩
      show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (h x - h y) ^ 2 * (π x * P x y)
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hP.1 x y))
    have hle : MarkovMixing.spectralGap P ≤ Q / (p * q) := by
      rw [hgap]
      exact csInf_le hbdd ⟨g, hgexp, hgnorm, hgdir.symm⟩
    show MarkovMixing.spectralGap P / 2 ≤ Q / p
    have h1 : Q / (p * q) ≤ 2 * (Q / p) := by
      rw [div_le_iff₀ hpqpos]
      have e : 2 * (Q / p) * (p * q) = 2 * Q * q := by field_simp
      rw [e]
      nlinarith
    linarith
  have h2 : MarkovMixing.spectralGap P / 2 ≤ MarkovMixing.bottleneckStar P π := le_ciInf hkey
  linarith

end
-- END MODULE AttributedCheegerUpper

-- BEGIN MODULE AttributedCoarea
section
-- Prove2me | solution 1 for MarkovMixing.bottleneck_coarea
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:53:02.416069+00:00
-- url     : https://prove2.me/submissions/7bd5171f-08e4-4d85-9fc5-898b4a59e836



open scoped BigOperators
open MarkovMixing

namespace Coarea

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [h]
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
    push Not at hcon
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

end Coarea

open Coarea

theorem MarkovMixing.bottleneck_coarea {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (_hrev : MarkovMixing.DetailedBalance P π)
    (ψ : V → ℝ) (hψ : ∀ x : V, 0 ≤ ψ x)
    (hsupp : ∑ x ∈ Finset.univ.filter (fun x : V => 0 < ψ x), π x ≤ 2⁻¹) :
    MarkovMixing.bottleneckStar P π * MarkovMixing.distExp π ψ ≤
      ∑ x, ∑ y, max (ψ x - ψ y) 0 * MarkovMixing.edgeMeasure P π x y := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hQnn : ∀ x y : V, 0 ≤ MarkovMixing.edgeMeasure P π x y := fun x y =>
    mul_nonneg (hpos x).le (hP.1 x y)
  -- Φ⋆ is bounded above by the ratio of any admissible set
  have hbdd : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
      MarkovMixing.bottleneckRatio P π S.1) := by
    refine ⟨0, ?_⟩
    rintro b ⟨S, rfl⟩
    refine div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y) ?_
    exact Finset.sum_nonneg fun x _ => (hpos x).le
  have hcut : ∀ S : Finset V, S.Nonempty → (∑ x ∈ S, π x) ≤ 2⁻¹ →
      MarkovMixing.bottleneckStar P π * (∑ x ∈ S, π x)
        ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
    intro S hSne hShalf
    have hppos : 0 < ∑ x ∈ S, π x := by
      obtain ⟨x, hx⟩ := hSne
      have h1 : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    have h1 : MarkovMixing.bottleneckStar P π ≤ MarkovMixing.bottleneckRatio P π S :=
      ciInf_le hbdd ⟨S, hSne, hShalf⟩
    rw [MarkovMixing.bottleneckRatio, div_eq_mul_inv] at h1
    calc MarkovMixing.bottleneckStar P π * (∑ x ∈ S, π x)
        ≤ ((∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y) * (∑ x ∈ S, π x)⁻¹)
            * (∑ x ∈ S, π x) := by
          exact mul_le_mul_of_nonneg_right h1 hppos.le
      _ = ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
          field_simp
  -- strong induction on the size of the support
  suffices H : ∀ n : ℕ, ∀ φ : V → ℝ, (∀ x, 0 ≤ φ x) →
      (Finset.univ.filter (fun x : V => 0 < φ x)).card ≤ n →
      (∑ x ∈ Finset.univ.filter (fun x : V => 0 < φ x), π x) ≤ 2⁻¹ →
      MarkovMixing.bottleneckStar P π * MarkovMixing.distExp π φ ≤
        ∑ x, ∑ y, max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y by
    exact H _ ψ hψ le_rfl hsupp
  intro n
  induction n with
  | zero =>
    intro φ hφ hcard _
    have hzero : ∀ x : V, φ x = 0 := by
      intro x
      by_contra hx
      have : x ∈ Finset.univ.filter (fun x : V => 0 < φ x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne (hφ x) (Ne.symm hx)
      have := Finset.card_pos.mpr ⟨x, this⟩
      omega
    have hL : MarkovMixing.distExp π φ = 0 := by
      show ∑ x, φ x * π x = 0
      exact Finset.sum_eq_zero fun x _ => by rw [hzero x]; ring
    rw [hL, mul_zero]
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    exact mul_nonneg (le_max_right _ _) (hQnn x y)
  | succ n ih =>
    intro φ hφ hcard hsupp'
    set S : Finset V := Finset.univ.filter (fun x : V => 0 < φ x) with hS_def
    by_cases hSne : S.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := S.exists_min_image φ hSne
      set a : ℝ := φ x0 with ha_def
      have hapos : 0 < a := by
        have := Finset.mem_filter.mp hx0
        exact this.2
      set φ' : V → ℝ := fun x => max (φ x - a) 0 with hφ'_def
      have hφ'nn : ∀ x, 0 ≤ φ' x := fun x => le_max_right _ _
      have hmem : ∀ x : V, x ∈ S ↔ 0 < φ x := by
        intro x; rw [hS_def]; simp
      have hzero : ∀ x : V, x ∉ S → φ x = 0 := by
        intro x hx
        rcases lt_or_eq_of_le (hφ x) with h | h
        · exact absurd ((hmem x).mpr h) hx
        · exact h.symm
      have hge : ∀ x ∈ S, a ≤ φ x := fun x hx => hmin x hx
      have hφ'S : ∀ x ∈ S, φ' x = φ x - a := by
        intro x hx
        rw [hφ'_def]
        exact max_eq_left (by linarith [hge x hx])
      have hφ'out : ∀ x : V, x ∉ S → φ' x = 0 := by
        intro x hx
        have hd : φ' x = max (φ x - a) 0 := rfl
        rw [hd, hzero x hx]
        exact max_eq_right (by linarith)
      -- support of φ' shrinks
      have hsub : Finset.univ.filter (fun x : V => 0 < φ' x) ⊆ S.erase x0 := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hxS : x ∈ S := by
          by_contra hc
          rw [hφ'out x hc] at hx
          exact lt_irrefl 0 hx
        rw [hφ'S x hxS] at hx
        refine Finset.mem_erase.mpr ⟨?_, hxS⟩
        intro hc
        rw [hc] at hx
        simp [ha_def] at hx
      have hcard' : (Finset.univ.filter (fun x : V => 0 < φ' x)).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hx0] at h1
        have h2 : 1 ≤ S.card := Finset.card_pos.mpr hSne
        omega
      have hsupp'' : (∑ x ∈ Finset.univ.filter (fun x : V => 0 < φ' x), π x) ≤ 2⁻¹ := by
        refine le_trans ?_ hsupp'
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (hpos i).le)
        exact hsub.trans (Finset.erase_subset _ _)
      have IH := ih φ' hφ'nn hcard' hsupp''
      -- decomposition of the mean
      have hexp : MarkovMixing.distExp π φ = MarkovMixing.distExp π φ' + a * ∑ x ∈ S, π x := by
        have hA : ∑ x, φ x * π x = (∑ x ∈ S, φ x * π x) + ∑ x ∈ Sᶜ, φ x * π x :=
          (Finset.sum_add_sum_compl S _).symm
        have hB : ∑ x, φ' x * π x = (∑ x ∈ S, φ' x * π x) + ∑ x ∈ Sᶜ, φ' x * π x :=
          (Finset.sum_add_sum_compl S _).symm
        have e1 : ∑ x ∈ S, φ x * π x = (∑ x ∈ S, φ' x * π x) + a * ∑ x ∈ S, π x := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x hx => by rw [hφ'S x hx]; ring
        have e2 : ∑ x ∈ Sᶜ, φ x * π x = ∑ x ∈ Sᶜ, φ' x * π x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.mem_compl] at hx
          rw [hzero x hx, hφ'out x hx]
        show ∑ x, φ x * π x = (∑ x, φ' x * π x) + a * ∑ x ∈ S, π x
        rw [hA, hB, e1, e2]
        ring
      -- pointwise comparison of the edge terms
      have hpair : ∀ x y : V,
          max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
            + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
          ≤ max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y := by
        intro x y
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'S x hx, hφ'S y hy]
          have e : φ x - a - (φ y - a) = φ x - φ y := by ring
          rw [e]
        · rw [if_pos ⟨hx, hy⟩, hφ'S x hx, hφ'out y hy, hzero y hy]
          have h1 : max (φ x - a - 0) 0 = φ x - a := by
            rw [sub_zero]; exact max_eq_left (by linarith [hge x hx])
          have h2 : max (φ x - 0) 0 = φ x := by
            rw [sub_zero]; exact max_eq_left (hφ x)
          rw [h1, h2]
          have e : (φ x - a) * MarkovMixing.edgeMeasure P π x y
              + a * MarkovMixing.edgeMeasure P π x y
              = φ x * MarkovMixing.edgeMeasure P π x y := by ring
          rw [e]
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'out x hx, hzero x hx, hφ'S y hy]
          have h1 : max (0 - (φ y - a)) 0 = 0 := max_eq_right (by linarith [hge y hy])
          have h2 : max (0 - φ y) 0 = 0 := max_eq_right (by linarith [(hmem y).mp hy])
          rw [h1, h2]
        · rw [if_neg (by tauto), mul_zero, add_zero, hφ'out x hx, hφ'out y hy, hzero x hx,
            hzero y hy]
      -- the indicator sum is the cut
      have hind : ∑ x, ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
          = ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have h1 : ∀ x : V, ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0)
            = if x ∈ S then ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y else 0 := by
          intro x
          by_cases hx : x ∈ S
          · simp only [hx, true_and, if_true]
            rw [← Finset.sum_filter]
            congr 1
            ext y
            simp [Finset.mem_compl]
          · simp [hx]
        rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.sum_filter]
        congr 1
        ext x
        simp
      have hsum : ∑ x, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
          + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
          ≤ ∑ x, ∑ y, max (φ x - φ y) 0 * MarkovMixing.edgeMeasure P π x y :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
      have hsplit : ∑ x, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
          + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
          = (∑ x, ∑ y, max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y)
            + a * ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have e : ∀ x : V, ∑ y, (max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y
            + a * (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0))
            = (∑ y, max (φ' x - φ' y) 0 * MarkovMixing.edgeMeasure P π x y)
              + a * ∑ y, (if x ∈ S ∧ y ∉ S then MarkovMixing.edgeMeasure P π x y else 0) := by
          intro x
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, ← Finset.mul_sum, hind]
      have hcutS := hcut S hSne hsupp'
      rw [hexp, mul_add]
      have hstar : MarkovMixing.bottleneckStar P π * (a * ∑ x ∈ S, π x)
          ≤ a * ∑ x ∈ S, ∑ y ∈ Sᶜ, MarkovMixing.edgeMeasure P π x y := by
        have : MarkovMixing.bottleneckStar P π * (a * ∑ x ∈ S, π x)
            = a * (MarkovMixing.bottleneckStar P π * ∑ x ∈ S, π x) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hcutS hapos.le
      rw [hsplit] at hsum
      linarith
    · -- empty support
      have hzero : ∀ x : V, φ x = 0 := by
        intro x
        rcases lt_or_eq_of_le (hφ x) with h | h
        · exact absurd ⟨x, by rw [hS_def]; simp [h]⟩ hSne
        · exact h.symm
      have hL : MarkovMixing.distExp π φ = 0 := by
        show ∑ x, φ x * π x = 0
        exact Finset.sum_eq_zero fun x _ => by rw [hzero x]; ring
      rw [hL, mul_zero]
      refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
      exact mul_nonneg (le_max_right _ _) (hQnn x y)

end
-- END MODULE AttributedCoarea

-- BEGIN MODULE AttributedCheeger
section
-- Prove2me | solution 1 for MarkovMixing.cheeger_inequality
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:03:03.511539+00:00
-- url     : https://prove2.me/submissions/cddfc032-995a-4b16-86e7-0d3f80646d90



open scoped BigOperators
open MarkovMixing

namespace CheegerDirichletGap

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [h]
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
    push Not at hcon
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

omit [DecidableEq V] in
lemma innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq V] in
lemma dirichlet_eq_inner {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by
  have hrow : ∀ x, ∑ y, P x y = 1 := hP.2
  have hcol : ∀ y, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have A : ∑ x, ∑ y, (g x) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hrow x, mul_one]
    ring
  have B : ∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hcol y]
    ring
  have C : ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y)
      = ∑ x : V, g x * (P.mulVec g) x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (P.mulVec g) x = ∑ y, P x y * g y from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hall : ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y)
      = (∑ x : V, ∑ y : V, (g x) ^ 2 * (π x * P x y))
        + (∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y))
        - 2 * ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  show 2⁻¹ * ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y) = _
  rw [hall, A, B, C]
  show _ = (∑ x : V, g x * g x * π x) - ∑ x : V, g x * (P.mulVec g) x * π x
  ring

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by
  have e1 : ∀ j, innerPi π g (ff j) * ff j x = ∑ y : V, g y * π y * (ff j y * ff j x) := by
    intro j
    show (∑ y : V, g y * ff j y * π y) * ff j x = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  have e2 : ∀ y : V, ∑ j, g y * π y * (ff j y * ff j x)
      = g y * π y * ((if y = x then 1 else 0) / π x) := by
    intro y
    rw [← Finset.mul_sum, hcomp y x]
  rw [Finset.sum_congr rfl (fun y _ => e2 y),
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [hb])]
  have hx := (hpos x).ne'
  field_simp
  simp

lemma norm_eq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

lemma mulVec_expand (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by
  have e1 : ∀ y : V, P x y * g y = ∑ j, innerPi π g (ff j) * (P x y * ff j y) := by
    intro y
    have : ∀ j, innerPi π g (ff j) * (P x y * ff j y)
        = (innerPi π g (ff j) * ff j y) * P x y := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g y]
    ring
  show ∑ y : V, P x y * g y = _
  rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : V, P x y * ff j y = lam j * ff j x := by
    have := congrFun (heig j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [this]
  ring

lemma inner_mulVec (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * (P.mulVec g) x * π x
      = ∑ j, (innerPi π g (ff j) * lam j) * (g x * ff j x * π x) := by
    intro x
    rw [mulVec_expand heig hpos hcomp g x, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ x : V, g x * (P.mulVec g) x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * lam j * innerPi π g (ff j) = _
  ring

end Spectral

end CheegerDirichletGap

namespace Cheeger

open CheegerDirichletGap

/-- For an irreducible reversible chain with at least two states, `λ₂` is an
eigenvalue, realised by an eigenfunction of unit `ℓ²(π)`-norm and mean zero. -/
lemma exists_lambdaTwo_eigen {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
      P.mulVec g = (MarkovMixing.lambdaTwo P) • g := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [dirichlet_eq_inner hP hπ g, norm_eq hpos hcomp g, inner_mulVec heig hpos hcomp g,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : ∀ (a : Fin (Fintype.card V) → ℝ) (k : Fin (Fintype.card V)),
      innerPi π (fun x => ∑ j, a j * ff j x) (ff k) = a k := by
    intro a k
    have e : ∀ x : V, (∑ j, a j * ff j x) * ff k x * π x
        = ∑ j, a j * (ff j x * ff k x * π x) := by
      intro x
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    show ∑ x : V, (∑ j, a j * ff j x) * ff k x * π x = a k
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    have e2 : ∀ j, ∑ x : V, a j * (ff j x * ff k x * π x)
        = a j * (if j = k then 1 else 0) := by
      intro j
      rw [← Finset.mul_sum]
      exact congrArg _ (horth j k)
    rw [Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by simp [hb])]
    simp
  -- the constant function
  set one : V → ℝ := fun _ => 1 with hone_def
  have hPone : P.mulVec one = one := by
    funext x
    show ∑ y, P x y * 1 = 1
    simpa using hP.2 x
  have hone_eig : ∀ j, innerPi π one (ff j) * (lam j - 1) = 0 := by
    intro j
    have hA : P.mulVec one = fun x => ∑ k, (innerPi π one (ff k) * lam k) * ff k x := by
      funext x
      rw [mulVec_expand heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [expand hpos hcomp one (Classical.arbitrary V)] at h0
    exact one_ne_zero h0
  obtain ⟨j0, hj0⟩ := hc1
  have hlam0 : lam j0 = 1 := by
    rcases mul_eq_zero.mp (hone_eig j0) with h | h
    · exact absurd h hj0
    · linarith
  set x0 : V := Classical.arbitrary V with hx0_def
  have const_inner : ∀ u v : V → ℝ, (∀ x y : V, u x = u y) → (∀ x y : V, v x = v y) →
      innerPi π u v = u x0 * v x0 := by
    intro u v hu hv
    have e : ∀ x : V, u x * v x * π x = (u x0 * v x0) * π x := by
      intro x; rw [hu x x0, hv x x0]
    show ∑ x : V, u x * v x * π x = _
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hsum, mul_one]
  have hffconst : ∀ x y : V, ff j0 x = ff j0 y := by
    have h1 : P.mulVec (ff j0) = ff j0 := by
      rw [heig j0, hlam0, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j0) h1
  have ha : ff j0 x0 * ff j0 x0 = 1 := by
    have := horth j0 j0
    rw [const_inner _ _ hffconst hffconst] at this
    simpa using this
  have ha0 : ff j0 x0 ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hlamne : ∀ j, j ≠ j0 → lam j ≠ 1 := by
    intro j hj hlam1
    have h1 : P.mulVec (ff j) = ff j := by rw [heig j, hlam1, one_smul]
    have hcj : ∀ x y : V, ff j x = ff j y := (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) h1
    have hb : ff j x0 * ff j0 x0 = 0 := by
      have := horth j j0
      rw [const_inner _ _ hcj hffconst] at this
      simpa [hj] using this
    have hbb : ff j x0 * ff j x0 = 1 := by
      have := horth j j
      rw [const_inner _ _ hcj hcj] at this
      simpa using this
    have : ff j x0 = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h ha0
    rw [this] at hbb
    norm_num at hbb
  -- the second-largest eigenvalue
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jstar, hjs_mem, hjs⟩ := Finset.exists_max_image (Finset.univ.erase j0) lam hne
  have hjs_ne : jstar ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have := horth j j
    rw [h] at this
    simp [innerPi] at this
  have hgap : MarkovMixing.spectralGap P = 1 - lam jstar := by
    have hmem : lam jstar ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} :=
      ⟨⟨ff jstar, hffne jstar, heig jstar⟩, hlamne jstar hjs_ne⟩
    have hbdd : ∀ r ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1}, r ≤ lam jstar := by
      rintro r ⟨⟨g, hg0, hg⟩, hr1⟩
      have hex : ∃ k, innerPi π g (ff k) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hg0
        funext x
        rw [← expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [mulVec_expand heig hpos hcomp g x]
      have hL : innerPi π (P.mulVec g) (ff k) = innerPi π g (ff k) * lam k := by
        rw [hA]; exact hcoef _ k
      have hR : innerPi π (P.mulVec g) (ff k) = r * innerPi π g (ff k) := by
        rw [hg]
        show ∑ x : V, (r • g) x * ff k x * π x = r * ∑ x : V, g x * ff k x * π x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply]; ring
      have hlamk : lam k = r := by
        have : innerPi π g (ff k) * lam k = innerPi π g (ff k) * r := by rw [← hL, hR]; ring
        exact mul_left_cancel₀ hk this
      have hkne : k ≠ j0 := by
        intro h; rw [h, hlam0] at hlamk; exact hr1 hlamk.symm
      rw [← hlamk]
      exact hjs k (Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩)
    show 1 - MarkovMixing.lambdaTwo P = 1 - lam jstar
    rw [show MarkovMixing.lambdaTwo P = lam jstar from
      le_antisymm (csSup_le ⟨_, hmem⟩ hbdd) (le_csSup ⟨lam jstar, hbdd⟩ hmem)]
  -- the minimiser
  have hfs_exp : MarkovMixing.distExp π (ff jstar) = 0 := by
    have h1 : innerPi π (ff jstar) (ff j0) = ff j0 x0 * MarkovMixing.distExp π (ff jstar) := by
      have e : ∀ x : V, ff jstar x * ff j0 x * π x = ff j0 x0 * (ff jstar x * π x) := by
        intro x; rw [hffconst x x0]; ring
      show ∑ x : V, ff jstar x * ff j0 x * π x = _
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      rfl
    rw [horth jstar j0] at h1
    simp [hjs_ne] at h1
    rcases h1 with h | h
    · exact absurd h ha0
    · exact h
  have hfs_norm : innerPi π (ff jstar) (ff jstar) = 1 := by simpa using horth jstar jstar
  refine ⟨ff jstar, hfs_norm, hfs_exp, ?_⟩
  have : MarkovMixing.lambdaTwo P = lam jstar := by
    have h1 : MarkovMixing.spectralGap P = 1 - MarkovMixing.lambdaTwo P := rfl
    rw [h1] at hgap
    linarith
  rw [this]
  exact heig jstar

end Cheeger

namespace Cheeger2

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V] {P : Matrix V V ℝ} {π : V → ℝ}

omit [Fintype V] [DecidableEq V] in
lemma edge_symm (hrev : DetailedBalance P π) (x y : V) :
    edgeMeasure P π x y = edgeMeasure P π y x := hrev x y

omit [DecidableEq V] in
lemma edge_nonneg (hP : IsStochastic P) (hpos : ∀ x, 0 < π x) (x y : V) :
    0 ≤ edgeMeasure P π x y := mul_nonneg (hpos x).le (hP.1 x y)

omit [DecidableEq V] in
lemma swap_sum (hrev : DetailedBalance P π) (F : V → V → ℝ) :
    ∑ x, ∑ y, F x y * edgeMeasure P π x y = ∑ x, ∑ y, F y x * edgeMeasure P π x y := by
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [edge_symm hrev x y]

omit [DecidableEq V] in
lemma sum_left (hP : IsStochastic P) (f : V → ℝ) :
    ∑ x, ∑ y, f x ^ 2 * edgeMeasure P π x y = innerPi π f f := by
  have e : ∀ x : V, ∑ y, f x ^ 2 * edgeMeasure P π x y = f x * f x * π x := by
    intro x
    show ∑ y, f x ^ 2 * (π x * P x y) = _
    have : ∀ y : V, f x ^ 2 * (π x * P x y) = (f x ^ 2 * π x) * P x y := fun y => by ring
    rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum, hP.2 x, mul_one]
    ring
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  rfl

omit [DecidableEq V] in
lemma sum_right (hπ : IsStationary P π) (f : V → ℝ) :
    ∑ x, ∑ y, f y ^ 2 * edgeMeasure P π x y = innerPi π f f := by
  rw [Finset.sum_comm]
  have hcol : ∀ y : V, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have e : ∀ y : V, ∑ x, f y ^ 2 * edgeMeasure P π x y = f y * f y * π y := by
    intro y
    show ∑ x, f y ^ 2 * (π x * P x y) = _
    rw [← Finset.mul_sum, hcol y]
    ring
  rw [Finset.sum_congr rfl (fun y _ => e y)]
  rfl

omit [DecidableEq V] in
lemma sum_diff (f : V → ℝ) :
    ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y = 2 * dirichletForm P π f := by
  have hd : dirichletForm P π f = 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := rfl
  rw [hd]
  ring

omit [DecidableEq V] in
lemma sum_add_sq (hP : IsStochastic P) (hπ : IsStationary P π) (f : V → ℝ) :
    ∑ x, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 4 * innerPi π f f - 2 * dirichletForm P π f := by
  have e : ∀ x y : V, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 2 * (f x ^ 2 * edgeMeasure P π x y) + 2 * (f y ^ 2 * edgeMeasure P π x y)
        - (f x - f y) ^ 2 * edgeMeasure P π x y := fun x y => by ring
  have e2 : ∀ x : V, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y
      = 2 * (∑ y, f x ^ 2 * edgeMeasure P π x y) + 2 * (∑ y, f y ^ 2 * edgeMeasure P π x y)
        - ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => e x y
  rw [Finset.sum_congr rfl (fun x _ => e2 x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_left hP f, sum_right hπ f, sum_diff f]
  ring

omit [DecidableEq V] in
lemma pos_part_sq (f : V → ℝ) (hrev : DetailedBalance P π) :
    ∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * edgeMeasure P π x y = dirichletForm P π f := by
  have hswap := swap_sum hrev (fun x y => (max (f x - f y) 0) ^ 2)
  have hpt : ∀ x y : V, (max (f x - f y) 0) ^ 2 + (max (f y - f x) 0) ^ 2 = (f x - f y) ^ 2 := by
    intro x y
    rcases le_or_gt (f y) (f x) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hsum : (∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * edgeMeasure P π x y)
      + (∑ x, ∑ y, (max (f y - f x) 0) ^ 2 * edgeMeasure P π x y)
      = ∑ x, ∑ y, (f x - f y) ^ 2 * edgeMeasure P π x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← add_mul, hpt x y]
  rw [sum_diff f] at hsum
  linarith [hswap, hsum]

omit [DecidableEq V] in
lemma add_part_sq_le (hP : IsStochastic P) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    ∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0) * edgeMeasure P π x y
      ≤ 2 * innerPi π f f - dirichletForm P π f := by
  have hswap := swap_sum hrev (fun x y => if f y < f x then (f x + f y) ^ 2 else 0)
  have hpt : ∀ x y : V, (if f y < f x then (f x + f y) ^ 2 else 0)
      + (if f x < f y then (f y + f x) ^ 2 else 0) ≤ (f x + f y) ^ 2 := by
    intro x y
    rcases lt_trichotomy (f x) (f y) with h | h | h
    · rw [if_neg (by linarith), if_pos h, zero_add]
      have : (f y + f x) ^ 2 = (f x + f y) ^ 2 := by ring
      linarith [this.le, this.ge]
    · rw [if_neg (by linarith), if_neg (by linarith)]
      nlinarith [sq_nonneg (f x + f y)]
    · rw [if_pos h, if_neg (by linarith)]
      linarith
  have hle : (∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0) * edgeMeasure P π x y)
      + (∑ x, ∑ y, (if f x < f y then (f y + f x) ^ 2 else 0) * edgeMeasure P π x y)
      ≤ ∑ x, ∑ y, (f x + f y) ^ 2 * edgeMeasure P π x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (hpt x y) (edge_nonneg hP hpos x y)
  rw [sum_add_sq hP hπ f] at hle
  linarith [hswap, hle]

end Cheeger2

open Cheeger Cheeger2 CheegerDirichletGap

theorem checked_cheeger_cauchy_schwarz {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) (hpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hfnn : ∀ x, 0 ≤ f x) :
    (∑ x, ∑ y, max (f x ^ 2 - f y ^ 2) 0 * MarkovMixing.edgeMeasure P π x y)^2 ≤
      MarkovMixing.dirichletForm P π f *
        (2 * MarkovMixing.innerPi π f f - MarkovMixing.dirichletForm P π f) := by
  classical
  let N : ℝ := MarkovMixing.innerPi π f f
  let E : ℝ := MarkovMixing.dirichletForm P π f
  set A : ℝ := ∑ x, ∑ y, max (f x ^ 2 - f y ^ 2) 0 * MarkovMixing.edgeMeasure P π x y with hA_def
  have hQnn : ∀ x y : V, 0 ≤ MarkovMixing.edgeMeasure P π x y := fun x y =>
    edge_nonneg hP hpos x y
  have hEnn : 0 ≤ E := by
    show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y)
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hP.1 x y))
  -- Cauchy-Schwarz
  have hfact : ∀ x y : V, max (f x ^ 2 - f y ^ 2) 0
      = max (f x - f y) 0 * (if f y < f x then f x + f y else 0) := by
    intro x y
    by_cases h : f y < f x
    · rw [if_pos h, max_eq_left (show (0:ℝ) ≤ f x - f y by linarith),
        max_eq_left (show (0:ℝ) ≤ f x ^ 2 - f y ^ 2 by nlinarith [hfnn y])]
      ring
    · push Not at h
      rw [if_neg (not_lt.mpr h), mul_zero,
        max_eq_right (show f x ^ 2 - f y ^ 2 ≤ 0 by nlinarith [hfnn x])]
  have hprod : ∀ p : V × V,
      (max (f p.1 - f p.2) 0 * (if f p.2 < f p.1 then f p.1 + f p.2 else 0)
        * MarkovMixing.edgeMeasure P π p.1 p.2) ^ 2
      ≤ ((max (f p.1 - f p.2) 0) ^ 2 * MarkovMixing.edgeMeasure P π p.1 p.2)
        * ((if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0)
            * MarkovMixing.edgeMeasure P π p.1 p.2) := by
    intro p
    by_cases h : f p.2 < f p.1
    · exact le_of_eq (by rw [if_pos h, if_pos h]; ring)
    · exact le_of_eq (by rw [if_neg h, if_neg h]; ring)
  have hite : ∀ p : V × V, 0 ≤ (if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0) := by
    intro p
    by_cases h : f p.2 < f p.1
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hCS0 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (V × V))
    (r := fun p : V × V => max (f p.1 - f p.2) 0 * (if f p.2 < f p.1 then f p.1 + f p.2 else 0)
      * MarkovMixing.edgeMeasure P π p.1 p.2)
    (f := fun p : V × V => (max (f p.1 - f p.2) 0) ^ 2 * MarkovMixing.edgeMeasure P π p.1 p.2)
    (g := fun p : V × V => (if f p.2 < f p.1 then (f p.1 + f p.2) ^ 2 else 0)
      * MarkovMixing.edgeMeasure P π p.1 p.2)
    (fun p _ => mul_nonneg (sq_nonneg _) (hQnn p.1 p.2))
    (fun p _ => mul_nonneg (hite p) (hQnn p.1 p.2))
    (fun p _ => hprod p)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hCS0
  have hA_eq : A = ∑ x, ∑ y, max (f x - f y) 0 * (if f y < f x then f x + f y else 0)
      * MarkovMixing.edgeMeasure P π x y := by
    rw [hA_def]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hfact x y]
  have hE_eq : ∑ x, ∑ y, (max (f x - f y) 0) ^ 2 * MarkovMixing.edgeMeasure P π x y = E :=
    pos_part_sq f hrev
  have hW_le : ∑ x, ∑ y, (if f y < f x then (f x + f y) ^ 2 else 0)
      * MarkovMixing.edgeMeasure P π x y ≤ 2 * N - E := add_part_sq_le hP hπ hrev hpos f
  rw [← hA_eq, hE_eq] at hCS0
  have hCS : A ^ 2 ≤ E * (2 * N - E) :=
    le_trans hCS0 (mul_le_mul_of_nonneg_left hW_le hEnn)
  exact hCS

theorem MarkovMixing.cheeger_inequality {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.bottleneckStar P π ^ 2 / 2 ≤ MarkovMixing.spectralGap P ∧
    MarkovMixing.spectralGap P ≤ 2 * MarkovMixing.bottleneckStar P π := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x, π x = 1 := hπ.1.2
  have hQnn : ∀ x y : V, 0 ≤ MarkovMixing.edgeMeasure P π x y := fun x y =>
    edge_nonneg hP hpos x y
  have hrow : ∀ x : V, ∑ y, MarkovMixing.edgeMeasure P π x y = π x := by
    intro x
    show ∑ y, π x * P x y = π x
    rw [← Finset.mul_sum, hP.2 x, mul_one]
  -- the family of bottleneck ratios
  have hbdd : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} =>
      MarkovMixing.bottleneckRatio P π S.1) := by
    refine ⟨0, ?_⟩
    rintro b ⟨S, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y)
      (Finset.sum_nonneg fun x _ => (hpos x).le)
  have hsub : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := by
    obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ 2⁻¹ := by
      by_contra hcon
      push Not at hcon
      have hcard : 1 < Fintype.card V := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have h1 : π x + π y ≤ ∑ z, π z := by
        calc π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := (Finset.sum_pair hxy).symm
          _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => (hpos i).le)
      have := hcon x
      have := hcon y
      linarith
    exact ⟨⟨{x}, ⟨Finset.singleton_nonempty x, by simpa using hx⟩⟩⟩
  have hΦnn : 0 ≤ MarkovMixing.bottleneckStar P π := by
    refine le_ciInf fun S => ?_
    exact div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hQnn x y)
      (Finset.sum_nonneg fun x _ => (hpos x).le)
  have hΦle1 : MarkovMixing.bottleneckStar P π ≤ 1 := by
    obtain ⟨S⟩ := hsub
    refine le_trans (ciInf_le hbdd S) ?_
    obtain ⟨T, hTne, hThalf⟩ := S
    have hppos : 0 < ∑ x ∈ T, π x := by
      obtain ⟨x, hx⟩ := hTne
      have h1 : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    show (∑ x ∈ T, ∑ y ∈ Tᶜ, MarkovMixing.edgeMeasure P π x y) / (∑ x ∈ T, π x) ≤ 1
    rw [div_le_one hppos]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← hrow x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hQnn x i)
  refine ⟨?_, MarkovMixing.cheeger_upper hV P hP hirr π hπ hrev⟩
  rcases le_or_gt (1/2 : ℝ) (MarkovMixing.spectralGap P) with hg | hg
  · nlinarith [mul_le_mul hΦle1 hΦle1 hΦnn zero_le_one]
  -- the interesting case
  obtain ⟨g0, hg0norm, hg0exp, hg0eig⟩ := exists_lambdaTwo_eigen hV P hP hirr π hπ hrev
  obtain ⟨g, hgnorm, hgexp, hgeig, hgsupp⟩ :
      ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
        P.mulVec g = (MarkovMixing.lambdaTwo P) • g ∧
        ∑ x ∈ Finset.univ.filter (fun x : V => 0 < g x), π x ≤ 2⁻¹ := by
    by_cases hc : ∑ x ∈ Finset.univ.filter (fun x : V => 0 < g0 x), π x ≤ 2⁻¹
    · exact ⟨g0, hg0norm, hg0exp, hg0eig, hc⟩
    · push Not at hc
      refine ⟨fun x => -g0 x, ?_, ?_, ?_, ?_⟩
      · show ∑ x, (-g0 x) * (-g0 x) * π x = 1
        rw [← hg0norm]
        exact Finset.sum_congr rfl fun x _ => by ring
      · show ∑ x, (-g0 x) * π x = 0
        have : ∑ x, (-g0 x) * π x = -∑ x, g0 x * π x := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
        rw [this]
        show -MarkovMixing.distExp π g0 = 0
        rw [hg0exp, neg_zero]
      · funext x
        have h1 := congrFun hg0eig x
        show ∑ y, P x y * (-g0 y) = _
        have h2 : ∑ y, P x y * (-g0 y) = -∑ y, P x y * g0 y := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [h2]
        simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
        show -(∑ y, P x y * g0 y) = _
        rw [show ∑ y, P x y * g0 y = P.mulVec g0 x from rfl, h1]
        ring
      · have hdisj : Disjoint (Finset.univ.filter (fun x : V => 0 < g0 x))
            (Finset.univ.filter (fun x : V => 0 < -g0 x)) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          linarith
        have hle : (∑ x ∈ Finset.univ.filter (fun x : V => 0 < g0 x), π x)
            + ∑ x ∈ Finset.univ.filter (fun x : V => 0 < -g0 x), π x ≤ 1 := by
          rw [← Finset.sum_union hdisj, ← hsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => (hpos i).le)
        linarith
  -- the positive part of the eigenfunction
  set f : V → ℝ := fun x => max (g x) 0 with hf_def
  have hfnn : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hfge : ∀ x, g x ≤ f x := fun x => le_max_left _ _
  set N : ℝ := MarkovMixing.innerPi π f f with hN_def
  set E : ℝ := MarkovMixing.dirichletForm P π f with hE_def
  have hEnn : 0 ≤ E := by
    rw [hE_def]
    show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y)
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hP.1 x y))
  have hgexists : ∃ x, 0 < g x := by
    by_contra hcon
    push Not at hcon
    have hnp : ∀ y ∈ (Finset.univ : Finset V), g y * π y ≤ 0 := by
      intro y _
      nlinarith [hcon y, (hpos y).le]
    have hz := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hgexp
    have hzero : MarkovMixing.innerPi π g g = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rcases mul_eq_zero.mp (hz x (Finset.mem_univ x)) with h | h
      · rw [h]; ring
      · exact absurd h (hpos x).ne'
    rw [hgnorm] at hzero
    norm_num at hzero
  obtain ⟨x1, hx1⟩ := hgexists
  have hfx1 : 0 < f x1 := lt_max_iff.mpr (Or.inl hx1)
  have hNpos : 0 < N := by
    rw [hN_def]
    show 0 < ∑ x, f x * f x * π x
    refine Finset.sum_pos' (fun i _ => mul_nonneg (mul_nonneg (hfnn i) (hfnn i)) (hpos i).le)
      ⟨x1, Finset.mem_univ x1, mul_pos (mul_pos hfx1 hfx1) (hpos x1)⟩
  -- the Dirichlet energy of f is at most γ ‖f‖²
  have hEle : E ≤ MarkovMixing.spectralGap P * N := by
    have hd : E = N - MarkovMixing.innerPi π f (P.mulVec f) := dirichlet_eq_inner hP hπ f
    have hlam : ∀ x : V, MarkovMixing.lambdaTwo P * f x ≤ (P.mulVec f) x := by
      intro x
      by_cases hx : 0 < g x
      · have hfx : f x = g x := max_eq_left (le_of_lt hx)
        have h1 : (P.mulVec g) x ≤ (P.mulVec f) x := by
          show ∑ y, P x y * g y ≤ ∑ y, P x y * f y
          exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfge y) (hP.1 x y)
        have h2 : (P.mulVec g) x = MarkovMixing.lambdaTwo P * g x := by
          rw [hgeig]; simp
        rw [hfx]
        linarith [h1, h2]
      · push Not at hx
        have hfx : f x = 0 := max_eq_right hx
        rw [hfx, mul_zero]
        show 0 ≤ ∑ y, P x y * f y
        exact Finset.sum_nonneg fun y _ => mul_nonneg (hP.1 x y) (hfnn y)
    have hterm : MarkovMixing.lambdaTwo P * N ≤ MarkovMixing.innerPi π f (P.mulVec f) := by
      rw [hN_def]
      show MarkovMixing.lambdaTwo P * (∑ x, f x * f x * π x) ≤ ∑ x, f x * (P.mulVec f) x * π x
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 := hlam x
      have h2 : 0 ≤ f x * π x := mul_nonneg (hfnn x) (hpos x).le
      nlinarith
    have hgd : MarkovMixing.spectralGap P = 1 - MarkovMixing.lambdaTwo P := rfl
    rw [hd, hgd]
    nlinarith [hterm]
  -- the co-area inequality applied to f²
  have hfilt : (Finset.univ.filter (fun x : V => 0 < f x ^ 2))
      = Finset.univ.filter (fun x : V => 0 < g x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h1 : 0 < f x := by
        rcases (hfnn x).lt_or_eq with h2 | h2
        · exact h2
        · rw [← h2] at h; norm_num at h
      rcases lt_max_iff.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (lt_irrefl 0)
    · intro h
      have h1 : 0 < f x := lt_max_iff.mpr (Or.inl h)
      positivity
  have hdistf : MarkovMixing.distExp π (fun x => f x ^ 2) = N := by
    rw [hN_def]
    show ∑ x, f x ^ 2 * π x = ∑ x, f x * f x * π x
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcoarea := MarkovMixing.bottleneck_coarea P hP hirr π hπ hrev (fun x => f x ^ 2)
    (fun x => sq_nonneg _) (by rw [hfilt]; exact hgsupp)
  rw [hdistf] at hcoarea
  set A : ℝ := ∑ x, ∑ y, max (f x ^ 2 - f y ^ 2) 0 * MarkovMixing.edgeMeasure P π x y with hA_def
  have hcoarea' : MarkovMixing.bottleneckStar P π * N ≤ A := hcoarea
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (le_max_right _ _) (hQnn x y)
  have hCS : A ^ 2 ≤ E * (2 * N - E) :=
    checked_cheeger_cauchy_schwarz P hP π hπ hrev hpos f hfnn
  -- final algebra
  have hΦN : 0 ≤ MarkovMixing.bottleneckStar P π * N := mul_nonneg hΦnn hNpos.le
  have hsq : (MarkovMixing.bottleneckStar P π * N) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hΦN hcoarea' 2
  have hkey : MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2 ≤ E * (2 * N - E) := by
    have e : (MarkovMixing.bottleneckStar P π * N) ^ 2
        = MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2 := by ring
    rw [e] at hsq
    linarith [hsq, hCS]
  have h1 : (1 - MarkovMixing.spectralGap P) * N ≤ N - E := by nlinarith [hEle]
  have h2 : 0 ≤ (1 - MarkovMixing.spectralGap P) * N := by nlinarith [hNpos]
  have h3 : ((1 - MarkovMixing.spectralGap P) * N) ^ 2 ≤ (N - E) ^ 2 := by nlinarith [h1, h2]
  have h6 : MarkovMixing.bottleneckStar P π ^ 2 ≤ 1 - (1 - MarkovMixing.spectralGap P) ^ 2 := by
    have hN2 : 0 < N ^ 2 := by positivity
    have h5 : MarkovMixing.bottleneckStar P π ^ 2 * N ^ 2
        ≤ (1 - (1 - MarkovMixing.spectralGap P) ^ 2) * N ^ 2 := by nlinarith [hkey, h3]
    exact le_of_mul_le_mul_right h5 hN2
  nlinarith [h6, sq_nonneg (MarkovMixing.spectralGap P)]

end
-- END MODULE AttributedCheeger

-- BEGIN MODULE CanonicalPathBound
section

set_option autoImplicit false

namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- Proposition 7, p. 54: the second eigenvalue is bounded by the congestion of any
system of canonical walks on an irreducible reversible chain. -/
theorem proposition_7 {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / (8 * eta P π Γ ^ 2) := by
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpos := DiaconisStroock.VarDist.Proof.stationary_positive P hP hirr π hπ
  have heta := Proof.eta_pos hV P hP π hpos Γ hΓ
  have hphi := Proof.bottleneckStar_ge hV P hP hirr π hπ Γ hΓ
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (2 * eta P π Γ)) hphi 2
  have hn : (1 / (2 * eta P π Γ))^2 / 2 = 1 / (8 * eta P π Γ ^ 2) := by
    field_simp [heta.ne']
    ring
  have hlo : 1 / (8 * eta P π Γ ^ 2) ≤ bottleneckStar P π ^ 2 / 2 := by
    rw [← hn]
    exact div_le_div_of_nonneg_right hs (by norm_num)
  have hc := (MarkovMixing.cheeger_inequality hV P hP hirr π hπ hrev).1
  change bottleneckStar P π ^ 2 / 2 ≤ 1 - lambdaTwo P at hc
  linarith

end DiaconisStroock.CanonPaths

end
-- END MODULE CanonicalPathBound

-- BEGIN MODULE PublicSolution
section

open DiaconisStroock.CanonPaths

open MarkovMixing

/-- Proposition 7, p. 54: the second eigenvalue is bounded by the congestion of any
system of canonical walks on an irreducible reversible chain. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / (8 * eta P π Γ ^ 2) := by
  exact DiaconisStroock.CanonPaths.proposition_7 hV P hP hirr π hπ hrev Γ hΓ



end
-- END MODULE PublicSolution

#print axioms DiaconisStroock.CanonPaths.proposition_7
#print axioms solution
