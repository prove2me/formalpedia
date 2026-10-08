-- Prove2me | solution 1 for DiaconisStroock.CanonPaths.bottleneckStar_ge
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:37:19.633983+00:00
-- url     : https://prove2.me/submissions/7ea28315-bb77-4b8e-959e-c026a6c5de0e

import Mathlib
import Definitions.Def_DiaconisStroock_CanonPaths_Eta
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_mm_basic

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
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
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

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted canon_root proof; see source-provenance.json.
set_option autoImplicit false
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

-- SPDX-License-Identifier: Apache-2.0
-- Reused accepted proof modules are credited in source-provenance.json.
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.CanonPaths


open MarkovMixing

/-- Canonical-path congestion bounds the bottleneck constant from below
(§3B, proof of Proposition 7, p. 54). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    1 / (2 * eta P π Γ) ≤ bottleneckStar P π := by
  exact DiaconisStroock.CanonPaths.Proof.bottleneckStar_ge hV P hP hirr π hπ Γ hΓ



#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- Canonical-path congestion bounds the bottleneck constant from below
(§3B, proof of Proposition 7, p. 54). -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    1 / (2 * eta P π Γ) ≤ bottleneckStar P π := by
  exact solution hV P hP hirr π hπ hrev Γ hΓ

end DiaconisStroock.CanonPaths

#print axioms solution
