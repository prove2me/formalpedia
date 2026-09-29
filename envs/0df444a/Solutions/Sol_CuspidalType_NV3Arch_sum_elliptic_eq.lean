-- Prove2me | solution 1 for CuspidalType.NV3Arch.sum_elliptic_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5ecc2bfd-12fa-54ee-a46a-7c108c1233ce

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_exists_conj_eq_torus
import Theorems.Thm_CuspidalType_mul_torus_eq_torus_mul_iff
import Theorems.Thm_CuspidalType_eq_or_eq_pow_of_isConj_torus
import Theorems.Thm_CuspidalType_exists_conj_torus_eq_torus_pow
import Theorems.Thm_CuspidalType_not_isRoot_charpoly_torus
import Theorems.Thm_CuspidalType_torus_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_NV3Arch_sum_elliptic_eq

set_option autoImplicit false

namespace EllSum
open Polynomial CuspidalType

variable (q : ℕ) [hq : Fact q.Prime]

abbrev Reg (α : (GaloisField q 2)ˣ) : Prop := (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))

abbrev Ell (g : GL2 q) : Prop := ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x

theorem charpoly_conj (g h : GL2 q) :
    ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj h (g : Matrix (Fin 2) (Fin 2) (ZMod q))

theorem ell_conj_iff (g h : GL2 q) : Ell q (h * g * h⁻¹) ↔ Ell q g := by
  simp only [Ell, charpoly_conj]

theorem ell_torus {α : (GaloisField q 2)ˣ} (hα : Reg q α) : Ell q (torus q α) :=
  fun x => not_isRoot_charpoly_torus q hα x

section Frob
variable [Fintype (GaloisField q 2)ˣ]
set_option linter.unusedSectionVars false

omit [Fintype (GaloisField q 2)ˣ] in
theorem pow_card_GF (a : GaloisField q 2) : a ^ (q ^ 2) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card q 2 two_ne_zero]
  rw [← hc, FiniteField.pow_card]

omit [Fintype (GaloisField q 2)ˣ] in

theorem pow_q_pow_q (α : (GaloisField q 2)ˣ) : (α ^ q) ^ q = α := by
  rw [← pow_mul, ← sq]
  ext
  rw [Units.val_pow_eq_pow_val, pow_card_GF]

omit [Fintype (GaloisField q 2)ˣ] in

theorem mem_range_of_pow_q_eq {a : GaloisField q 2} (ha : a ^ q = a) :
    a ∈ Set.range (algebraMap (ZMod q) (GaloisField q 2)) := by
  classical

  let f : (GaloisField q 2)[X] := X ^ q - X
  have hq1 : 1 < q := hq.out.one_lt
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_zero] at this
    have hdeg : f.natDegree = q := by
      simp only [f]
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq1]
    omega
  have hdeg : f.natDegree = q := by
    simp only [f]
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq1]
  let S : Finset (GaloisField q 2) := Finset.univ.image (algebraMap (ZMod q) (GaloisField q 2))
  have hS : S ⊆ f.roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hcardS : S.card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod q) (GaloisField q 2)).injective, Finset.card_univ, ZMod.card]
  have hcardR : f.roots.toFinset.card ≤ q := by
    calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  have hSeq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hS (by omega)
  have ha' : a ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, ha, sub_self]
  rw [← hSeq] at ha'
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp ha'
  exact ⟨x, hx⟩

omit [Fintype (GaloisField q 2)ˣ] in
theorem pow_q_ne_of_reg {α : (GaloisField q 2)ˣ} (hα : Reg q α) : α ^ q ≠ α := by
  intro h
  apply hα
  apply mem_range_of_pow_q_eq q
  have := congrArg (fun u : (GaloisField q 2)ˣ => (u : GaloisField q 2)) h
  simpa [Units.val_pow_eq_pow_val] using this

omit [Fintype (GaloisField q 2)ˣ] in
theorem reg_pow_q {α : (GaloisField q 2)ˣ} (hα : Reg q α) : Reg q (α ^ q) := by
  rintro ⟨x, hx⟩
  apply hα
  refine ⟨x ^ q, ?_⟩
  rw [map_pow, hx, ← Units.val_pow_eq_pow_val, pow_q_pow_q]

end Frob

end EllSum

namespace EllSum
open Polynomial CuspidalType

variable (q : ℕ) [hq : Fact q.Prime]

theorem card_centraliser [Fintype (GaloisField q 2)ˣ] {α : (GaloisField q 2)ˣ} (hα : Reg q α) :
    (Finset.univ.filter fun h : GL2 q => h * torus q α = torus q α * h).card = q ^ 2 - 1 := by
  classical
  have : (Finset.univ.filter fun h : GL2 q => h * torus q α = torus q α * h) =
      Finset.univ.image (torus q) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [mul_torus_eq_torus_mul_iff q hα h, MonoidHom.mem_range]
  rw [this, Finset.card_image_of_injective _ (torus_injective q), Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_units, GaloisField.card q 2 two_ne_zero]

open scoped Classical in

theorem card_fibre_torus [Fintype (GaloisField q 2)ˣ] {α₀ : (GaloisField q 2)ˣ} (hα₀ : Reg q α₀) :
    ((Finset.univ ×ˢ (Finset.univ.filter (Reg q))).filter
        fun p : GL2 q × (GaloisField q 2)ˣ => p.1 * torus q p.2 * p.1⁻¹ = torus q α₀).card = 2 * (q ^ 2 - 1) := by
  classical
  obtain ⟨f, hf⟩ := exists_conj_torus_eq_torus_pow q

  let CA : Finset (GL2 q) := Finset.univ.filter fun h : GL2 q => h * torus q α₀ = torus q α₀ * h
  let CB : Finset (GL2 q) := Finset.univ.filter fun h : GL2 q => h * torus q (α₀ ^ q) * h⁻¹ = torus q α₀
  have hCA : CA.card = q ^ 2 - 1 := card_centraliser q hα₀
  have hCB : CB.card = q ^ 2 - 1 := by

    rw [← hCA]
    refine Finset.card_bij' (fun h _ => h * f) (fun h _ => h * f⁻¹) ?_ ?_ ?_ ?_
    · intro h hh
      simp only [CB, CA, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢

      have e1 : torus q (α₀ ^ q) = f * torus q α₀ * f⁻¹ := (hf α₀).symm
      rw [e1] at hh
      calc h * f * torus q α₀ = (h * (f * torus q α₀ * f⁻¹) * h⁻¹) * (h * f) := by group
        _ = torus q α₀ * (h * f) := by rw [hh]
    · intro h hh
      simp only [CB, CA, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      have e1 : torus q (α₀ ^ q) = f * torus q α₀ * f⁻¹ := (hf α₀).symm
      rw [e1]
      calc h * f⁻¹ * (f * torus q α₀ * f⁻¹) * (h * f⁻¹)⁻¹ = h * torus q α₀ * h⁻¹ := by group
        _ = torus q α₀ * h * h⁻¹ := by rw [hh]
        _ = torus q α₀ := by group
    · intro h _; group
    · intro h _; group

  have hdisj : α₀ ^ q ≠ α₀ := pow_q_ne_of_reg q hα₀
  have hsplit : ((Finset.univ ×ˢ (Finset.univ.filter (Reg q))).filter
        fun p : GL2 q × (GaloisField q 2)ˣ => p.1 * torus q p.2 * p.1⁻¹ = torus q α₀) =
      CA.map ⟨fun h => (h, α₀), fun a b hab => (Prod.ext_iff.mp hab).1⟩ ∪
        CB.map ⟨fun h => (h, α₀ ^ q), fun a b hab => (Prod.ext_iff.mp hab).1⟩ := by
    ext ⟨h, α⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk, Prod.mk.injEq, CA, CB]
    constructor
    · rintro ⟨hreg, hconj⟩
      have hc : IsConj (torus q α) (torus q α₀) := isConj_iff.mpr ⟨h, hconj⟩
      rcases eq_or_eq_pow_of_isConj_torus q hc with e | e
      · left
        subst e
        refine ⟨h, ?_, rfl, rfl⟩
        calc h * torus q α₀ = h * torus q α₀ * h⁻¹ * h := by group
          _ = torus q α₀ * h := by rw [hconj]
      · right
        have hαe : α = α₀ ^ q := by rw [e, pow_q_pow_q]
        subst hαe
        exact ⟨h, hconj, rfl, rfl⟩
    · rintro (⟨h', hh', rfl, rfl⟩ | ⟨h', hh', rfl, rfl⟩)
      · refine ⟨hα₀, ?_⟩
        calc h' * torus q α₀ * h'⁻¹ = torus q α₀ * h' * h'⁻¹ := by rw [hh']
          _ = torus q α₀ := by group
      · exact ⟨reg_pow_q q hα₀, hh'⟩
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map, hCA, hCB, two_mul]
  rw [Finset.disjoint_left]
  rintro ⟨h, α⟩ h1 h2
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq] at h1 h2
  obtain ⟨_, _, _, rfl⟩ := h1
  obtain ⟨_, _, _, e⟩ := h2
  exact hdisj e

end EllSum

namespace EllSum
open Polynomial CuspidalType

variable (q : ℕ) [hq : Fact q.Prime]

open scoped Classical in

theorem card_fibre [Fintype (GaloisField q 2)ˣ] {g : GL2 q} (hg : Ell q g) :
    ((Finset.univ ×ˢ (Finset.univ.filter (Reg q))).filter
        fun p : GL2 q × (GaloisField q 2)ˣ => p.1 * torus q p.2 * p.1⁻¹ = g).card = 2 * (q ^ 2 - 1) := by
  obtain ⟨h₀, α₀, hα₀, hconj⟩ := exists_conj_eq_torus q g hg
  rw [← card_fibre_torus q hα₀]
  refine Finset.card_bij' (fun p _ => (h₀ * p.1, p.2)) (fun p _ => (h₀⁻¹ * p.1, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨h, α⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [← hconj, ← hp.2]; group
  · rintro ⟨h, α⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨hp.1, ?_⟩
    have : g = h₀⁻¹ * torus q α₀ * h₀ := by rw [← hconj]; group
    rw [this, ← hp.2]; group
  · rintro ⟨h, α⟩ _; simp
  · rintro ⟨h, α⟩ _; simp

open scoped Classical in

theorem image_eq [Fintype (GaloisField q 2)ˣ] :
    (Finset.univ ×ˢ (Finset.univ.filter (Reg q))).image
        (fun p : GL2 q × (GaloisField q 2)ˣ => p.1 * torus q p.2 * p.1⁻¹) =
      Finset.univ.filter (Ell q) := by
  ext g
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨h, α, hα, rfl⟩
    exact (ell_conj_iff q _ h).mpr (ell_torus q hα)
  · intro hg
    obtain ⟨h, α, hα, hconj⟩ := exists_conj_eq_torus q g hg
    refine ⟨h⁻¹, α, hα, ?_⟩
    rw [← hconj]; group

open scoped Classical in
theorem main [Fintype (GaloisField q 2)ˣ] {K : Type*} [CommRing K] (F : GL2 q → K)
    (hF : ∀ g h : GL2 q, F (h * g * h⁻¹) = F g) :
    (2 * (q ^ 2 - 1 : ℕ) : K) * ∑ g ∈ Finset.univ.filter (Ell q), F g =
      (Nat.card (GL2 q) : K) * ∑ α ∈ Finset.univ.filter (Reg q), F (torus q α) := by
  let P : Finset (GL2 q × (GaloisField q 2)ˣ) := Finset.univ ×ˢ (Finset.univ.filter (Reg q))
  let Φ : GL2 q × (GaloisField q 2)ˣ → GL2 q := fun p => p.1 * torus q p.2 * p.1⁻¹

  have h1 : ∑ p ∈ P, F (Φ p) = (Nat.card (GL2 q) : K) * ∑ α ∈ Finset.univ.filter (Reg q), F (torus q α) := by
    rw [Finset.sum_product]
    have : ∀ h : GL2 q, ∑ α ∈ Finset.univ.filter (Reg q), F (Φ (h, α)) = ∑ α ∈ Finset.univ.filter (Reg q), F (torus q α) :=
      fun h => Finset.sum_congr rfl fun α _ => hF (torus q α) h
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

  have h2 : ∑ p ∈ P, F (Φ p) = (2 * (q ^ 2 - 1 : ℕ) : K) * ∑ g ∈ Finset.univ.filter (Ell q), F g := by
    rw [Finset.sum_comp, image_eq q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.mem_filter] at hg
    rw [show (P.filter fun p => Φ p = g).card = 2 * (q ^ 2 - 1) from card_fibre q hg.2, nsmul_eq_mul]
    push_cast; ring
  rw [← h2, h1]

end EllSum

open EllSum CuspidalType Polynomial in
open scoped Classical in
theorem solution (q : ℕ) [Fact q.Prime]
    [Fintype (GaloisField q 2)ˣ] {K : Type*} [CommRing K] (F : GL2 q → K)
    (hF : ∀ g h : GL2 q, F (h * g * h⁻¹) = F g) :
    (2 * (q ^ 2 - 1 : ℕ) : K) *
        ∑ g ∈ Finset.univ.filter
          (fun g : GL2 q => ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x), F g =
      (Nat.card (GL2 q) : K) *
        ∑ α ∈ Finset.univ.filter
          (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
          F (torus q α) :=
  EllSum.main q F hF

end S_CuspidalType_NV3Arch_sum_elliptic_eq
end P2MW
export P2MW.S_CuspidalType_NV3Arch_sum_elliptic_eq (solution)
