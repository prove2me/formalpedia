-- Prove2me | solution 1 for CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4bbdd603-e5ce-5f39-a6d1-05ab7a68c0de

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_NV3Arch_sum_elliptic_eq
import Theorems.Thm_CuspidalType_torus_unitsMap_algebraMap
import Theorems.Thm_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
import Theorems.Thm_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
import Theorems.Thm_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv

set_option autoImplicit false

open Polynomial CuspidalType
set_option maxHeartbeats 1600000

namespace Ws23NV3C7

open Polynomial CuspidalType

section NormalForms

variable (q : ℕ) [Fact q.Prime]

theorem scalarElem_comm (c : (ZMod q)ˣ) (g : GL2 q) : scalarElem q c * g = g * scalarElem q c := by
  have hc : scalarElem q c ∈ Subgroup.center (GL2 q) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.mp hc g).symm

theorem scalarElem_mem_center (c : (ZMod q)ˣ) : scalarElem q c ∈ Subgroup.center (GL2 q) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨c, rfl⟩

private theorem _root_.Ws23NV3C7.mem_center_iff (g : GL2 q) : g ∈ Subgroup.center (GL2 q) ↔ ∃ c : (ZMod q)ˣ, scalarElem q c = g := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; rfl

p2m_export "Ws23NV3C7" "mem_center_iff"
theorem scalarElem_injective : Function.Injective (scalarElem q) := by
  intro c c' h
  have h1 := congrArg (fun g : GL2 q => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h
  apply Units.ext
  simpa [scalarElem] using h1

theorem unipotent_inv (t : ZMod q) : (unipotent q t)⁻¹ = unipotent q (-t) := by
  apply Units.ext; simp [unipotent]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext; simp [unipotent, Matrix.one_fin_two]

theorem charpoly_scalarElem_mul_unipotent (c : (ZMod q)ˣ) (t : ZMod q) :
    ((scalarElem q c * unipotent q t : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (X - C (c : ZMod q)) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [scalarElem, unipotent, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem val_split (a d : (ZMod q)ˣ) (s : ZMod q) :
    ((unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹)) : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![(a : ZMod q), s * d; 0, d] := by
  have h1 : ((scalarElem q d * diagElem q (a * d⁻¹) : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![(a : ZMod q), 0; 0, d] := by
    rw [Units.val_mul]
    have hs : ((scalarElem q d : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(d : ZMod q), 0; 0, d] := by
      show Matrix.scalar (Fin 2) (d : ZMod q) = _
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]
    rw [hs, diagElem_val, Matrix.mul_fin_two]
    have hda : (d : ZMod q) * ((a * d⁻¹ : (ZMod q)ˣ) : ZMod q) = a := by
      rw [Units.val_mul, mul_comm, Units.inv_mul_cancel_right]
    simp only [mul_zero, add_zero, zero_mul, zero_add, mul_one, hda]
  rw [Units.val_mul, h1, unipotent_val, Matrix.mul_fin_two]
  congr 1 <;> simp <;> ring

theorem charpoly_split (a d : (ZMod q)ˣ) (s : ZMod q) :
    ((unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹)) : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly =
      (X - C (a : ZMod q)) * (X - C (d : ZMod q)) := by
  rw [val_split, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  simp only [map_add, map_mul, map_sub, mul_zero, sub_zero]
  ring

end NormalForms

end Ws23NV3C7

namespace Ws23NV3C7

open Polynomial CuspidalType
open scoped Classical

section Classify

variable (q : ℕ) [Fact q.Prime]

abbrev IsEll (g : GL2 q) : Prop := ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x

def IsPar (g : GL2 q) : Prop :=
  g ∉ Subgroup.center (GL2 q) ∧ ∃ z : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (X - C z) ^ 2

theorem charpoly_conj (h g : GL2 q) :
    ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem not_isEll_scalarElem (c : (ZMod q)ˣ) : ¬ IsEll q (scalarElem q c) := by
  intro h
  apply h (c : ZMod q)
  have := charpoly_scalarElem_mul_unipotent q c 0
  rw [unipotent_zero, mul_one] at this
  rw [this]
  simp

theorem not_isEll_of_isPar {g : GL2 q} (hg : IsPar q g) : ¬ IsEll q g := by
  obtain ⟨-, z, hz⟩ := hg
  intro h
  apply h z
  rw [hz]
  simp

theorem eq_of_X_sub_C_mul_eq_sq {a d z : ZMod q} (h : (X - C a) * (X - C d) = (X - C z) ^ 2) : a = d := by
  have ha : a = z := by
    have := congrArg (eval a) h
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, eval_pow] at this
    exact (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm))
  have hd : d = z := by
    have := congrArg (eval d) h
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, eval_pow] at this
    exact (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm))
  rw [ha, hd]

theorem normal_form {g : GL2 q} (hell : ¬ IsEll q g) (hcen : g ∉ Subgroup.center (GL2 q)) :
    (IsPar q g ∧ ∃ (h : GL2 q) (c : (ZMod q)ˣ) (t : ZMod q), t ≠ 0 ∧ h * g * h⁻¹ = scalarElem q c * unipotent q t) ∨
    (¬ IsPar q g ∧ ∃ (h : GL2 q) (a d : (ZMod q)ˣ) (s : ZMod q), a ≠ d ∧
      h * g * h⁻¹ = unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹))) := by
  have hx : ∃ x : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x := by
    by_contra hno
    push Not at hno
    exact hell hno
  obtain ⟨x, hx⟩ := hx
  obtain ⟨h, hh⟩ := CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly q g x hx
  rcases CuspidalType.eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero q (h * g * h⁻¹) hh with ⟨c, t, hb⟩ | ⟨a, d, s, had, hb⟩
  · by_cases ht : t = 0
    · exfalso
      apply hcen
      rw [ht, unipotent_zero, mul_one] at hb
      have hg : g = scalarElem q c := by
        have : g = h⁻¹ * (h * g * h⁻¹) * h := by group
        rw [this, hb, ← scalarElem_comm, inv_mul_cancel_right]
      rw [hg]; exact scalarElem_mem_center q c
    · left
      refine ⟨⟨hcen, c, ?_⟩, h, c, t, ht, hb⟩
      rw [← charpoly_conj q h g, hb, charpoly_scalarElem_mul_unipotent]
  · right
    refine ⟨fun hpar => ?_, h, a, d, s, had, hb⟩
    obtain ⟨-, z, hz⟩ := hpar
    rw [← charpoly_conj q h g, hb, charpoly_split] at hz
    exact had (Units.ext (eq_of_X_sub_C_mul_eq_sq q hz))

end Classify

section Values

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (ρ : Representation K (GL2 q) V)
  (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
  (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
  (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)

include hK2 in
theorem character_scalarElem (c : (ZMod q)ˣ) : ρ.character (scalarElem q c) = Module.finrank K V := by
  rw [← mul_one (scalarElem q c), hK2, Representation.char_one]

include hK2 hK3 in
theorem character_of_isPar {g : GL2 q} (hg : IsPar q g) : ρ.character g = -1 ∧ ρ.character g⁻¹ = -1 := by
  rcases normal_form q (not_isEll_of_isPar q hg) hg.1 with ⟨-, h, c, t, ht, hb⟩ | ⟨hnot, -⟩
  · constructor
    · rw [← Representation.char_conj ρ g h, hb, hK2, hK3 t ht]
    · have hb' : h * g⁻¹ * h⁻¹ = scalarElem q c⁻¹ * unipotent q (-t) := by
        have : h * g⁻¹ * h⁻¹ = (h * g * h⁻¹)⁻¹ := by group
        rw [this, hb, mul_inv_rev, unipotent_inv, ← map_inv, scalarElem_comm]
      rw [← Representation.char_conj ρ g⁻¹ h, hb', hK2, hK3 (-t) (neg_ne_zero.mpr ht)]
  · exact absurd hg hnot

include hK2 hK4 in
theorem character_of_not_isPar {g : GL2 q} (hell : ¬ IsEll q g) (hcen : g ∉ Subgroup.center (GL2 q))
    (hpar : ¬ IsPar q g) : ρ.character g = 0 := by
  rcases normal_form q hell hcen with ⟨hp, -⟩ | ⟨-, h, a, d, s, had, hb⟩
  · exact absurd hp hpar
  · rw [← Representation.char_conj ρ g h, hb, ← mul_assoc, ← scalarElem_comm, mul_assoc, hK2]
    refine hK4 (a * d⁻¹) s fun h1 => had ?_
    rw [mul_inv_eq_one] at h1
    exact h1

end Values

section Sums

variable (q : ℕ) [Fact q.Prime] {K : Type*} [Field K]

theorem filter_center_eq : (Finset.univ.filter fun g : GL2 q => ¬ IsEll q g).filter (fun g => g ∈ Subgroup.center (GL2 q)) =
    Finset.univ.image (scalarElem q) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨-, hg⟩
    exact (mem_center_iff q g).mp hg
  · rintro ⟨c, rfl⟩
    exact ⟨not_isEll_scalarElem q c, scalarElem_mem_center q c⟩

theorem filter_isPar_eq : ((Finset.univ.filter fun g : GL2 q => ¬ IsEll q g).filter
      (fun g => g ∉ Subgroup.center (GL2 q))).filter (IsPar q) = Finset.univ.filter (IsPar q) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨⟨not_isEll_of_isPar q h, h.1⟩, h⟩

theorem sum_split (F : GL2 q → K) (vZ vP : K) (hZ : ∀ c, F (scalarElem q c) = vZ)
    (hP : ∀ g, IsPar q g → F g = vP)
    (hS : ∀ g, ¬ IsEll q g → g ∉ Subgroup.center (GL2 q) → ¬ IsPar q g → F g = 0) :
    ∑ g, F g = Fintype.card (ZMod q)ˣ • vZ + (Finset.univ.filter (IsPar q)).card • vP +
      ∑ g ∈ Finset.univ.filter (IsEll q), F g := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (IsEll q), add_comm]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun g => g ∈ Subgroup.center (GL2 q))]
  congr 1
  · rw [filter_center_eq, Finset.sum_image (fun c _ c' _ h => scalarElem_injective q h),
      Finset.sum_congr rfl fun c _ => hZ c, Finset.sum_const, Finset.card_univ]
  · rw [← Finset.sum_filter_add_sum_filter_not _ (IsPar q), filter_isPar_eq]
    rw [Finset.sum_congr rfl fun g hg => hP g (Finset.mem_filter.mp hg).2, Finset.sum_const,
      Finset.sum_eq_zero (fun g hg => ?_), add_zero]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact hS g hg.1.1 hg.1.2 hg.2

theorem filter_not_regular_eq [Fintype (GaloisField q 2)ˣ] :
    Finset.univ.filter (fun α : (GaloisField q 2)ˣ =>
        ¬ ((α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2)))) =
      Finset.univ.image (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom) := by
  ext α
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_not]
  constructor
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact α.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext ha⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem unitsMap_injective :
    Function.Injective (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom) := fun c c' h =>
  Units.ext ((algebraMap (ZMod q) (GaloisField q 2)).injective (congrArg Units.val h))

theorem sum_torus_split [Fintype (GaloisField q 2)ˣ] (F : GL2 q → K) (vZ : K) (hZ : ∀ c, F (scalarElem q c) = vZ) :
    ∑ α : (GaloisField q 2)ˣ, F (torus q α) =
      ∑ α ∈ Finset.univ.filter
          (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
          F (torus q α) + Fintype.card (ZMod q)ˣ • vZ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2)))]
  congr 1
  rw [filter_not_regular_eq, Finset.sum_image (fun c _ c' _ h => unitsMap_injective q h),
    Finset.sum_congr rfl fun c _ => by rw [CuspidalType.torus_unitsMap_algebraMap, hZ], Finset.sum_const,
    Finset.card_univ]

theorem card_filter_isPar : (Finset.univ.filter (IsPar q)).card = (q - 1) * (q ^ 2 - 1) := by
  rw [← CuspidalType.natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq q, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr fun g _ => Iff.rfl)

theorem natCard_GL2 : Nat.card (GL2 q) = (q ^ 2 - 1) * (q ^ 2 - q) := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  simp

end Sums

end Ws23NV3C7

namespace Ws23NV3C7

open Polynomial CuspidalType
open scoped Classical

section Main

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

theorem main [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q)) :
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) = ((q ^ 2 - 1 : ℕ) : K) ∧
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) * ρ.character (torus q α)⁻¹ =
      (((q - 1) * (q ^ 2 - 1) : ℕ) : K) := by

  have hq : q.Prime := Fact.out
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  have hqq : q ≤ q ^ 2 := by nlinarith
  set n₁ : K := ((q - 1 : ℕ) : K) with hn₁def
  set n₂ : K := ((q ^ 2 - 1 : ℕ) : K) with hn₂def
  have hn₁ : n₁ = (q : K) - 1 := by rw [hn₁def, Nat.cast_sub hq1, Nat.cast_one]
  have hn₂ : n₂ = (q : K) ^ 2 - 1 := by rw [hn₂def, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one]
  have hqK : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hn₁0 : n₁ ≠ 0 := by
    rw [hn₁, sub_ne_zero]; exact_mod_cast hq.one_lt.ne'
  have hn₂0 : n₂ ≠ 0 := by
    rw [hn₂, sub_ne_zero]; exact_mod_cast (Nat.one_lt_pow two_ne_zero hq.one_lt).ne'
  have hG : (Nat.card (GL2 q) : K) = q * n₁ * n₂ := by
    rw [natCard_GL2, Nat.cast_mul, Nat.cast_sub hqq, Nat.cast_pow, ← hn₂def, hn₁, hn₂]; ring
  have hfin : (Module.finrank K V : K) = n₁ := by rw [hK1]
  have hU : ((Finset.univ.filter (IsPar q)).card : K) = n₁ * n₂ := by
    rw [card_filter_isPar, Nat.cast_mul]
  have hZc : (Fintype.card (ZMod q)ˣ : K) = n₁ := by rw [ZMod.card_units]

  have hsplit₁ := sum_split q ρ.character (Module.finrank K V : K) (-1) (character_scalarElem ρ hK2)
    (fun g hg => (character_of_isPar ρ hK2 hK3 hg).1)
    (fun g h1 h2 h3 => character_of_not_isPar ρ hK2 hK4 h1 h2 h3)
  have hC5₁ := CuspidalType.NV3Arch.sum_elliptic_eq q ρ.character (fun g h => Representation.char_conj ρ g h)
  have htor₁ := sum_torus_split q ρ.character (Module.finrank K V : K) (character_scalarElem ρ hK2)
  rw [hK5, nsmul_eq_mul, nsmul_eq_mul, hZc, hU, hfin] at hsplit₁
  rw [hG] at hC5₁
  set E₁ := ∑ g ∈ Finset.univ.filter (IsEll q), ρ.character g with hE₁
  set S₁ := ∑ α ∈ Finset.univ.filter
      (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
      ρ.character (torus q α) with hS₁
  have e1 : E₁ = n₁ * n₂ - n₁ * n₁ := by linear_combination -hsplit₁
  have e2 : 2 * n₂ * E₁ = q * n₁ * n₂ * S₁ := hC5₁
  have hS : S₁ = 2 * n₁ := by
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hqK hn₁0) hn₂0) ?_
    rw [← e2, e1, hn₁, hn₂]; ring

  let F : GL2 q → K := fun g => ρ.character g * ρ.character g⁻¹
  have hFZ : ∀ c : (ZMod q)ˣ, F (scalarElem q c) = (Module.finrank K V : K) * (Module.finrank K V : K) := fun c => by
    simp only [F]
    rw [← map_inv, character_scalarElem ρ hK2, character_scalarElem ρ hK2]
  have hFP : ∀ g, IsPar q g → F g = 1 := fun g hg => by
    simp only [F]
    rw [(character_of_isPar ρ hK2 hK3 hg).1, (character_of_isPar ρ hK2 hK3 hg).2]; norm_num
  have hFS : ∀ g, ¬ IsEll q g → g ∉ Subgroup.center (GL2 q) → ¬ IsPar q g → F g = 0 := fun g h1 h2 h3 => by
    simp only [F]
    rw [character_of_not_isPar ρ hK2 hK4 h1 h2 h3, zero_mul]
  have hFconj : ∀ g h : GL2 q, F (h * g * h⁻¹) = F g := fun g h => by
    simp only [F]
    rw [Representation.char_conj, show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group, Representation.char_conj]
  have hsplit₂ := sum_split q F _ 1 hFZ hFP hFS
  have hC5₂ := CuspidalType.NV3Arch.sum_elliptic_eq q F hFconj
  have htor₂ := sum_torus_split q F _ hFZ
  simp only [F] at hsplit₂ hC5₂ htor₂
  rw [hK6, nsmul_eq_mul, nsmul_eq_mul, hZc, hU, hfin, hG] at hsplit₂
  rw [hG] at hC5₂
  set E₂ := ∑ g ∈ Finset.univ.filter (IsEll q), ρ.character g * ρ.character g⁻¹ with hE₂
  set S₂ := ∑ α ∈ Finset.univ.filter
      (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
      ρ.character (torus q α) * ρ.character (torus q α)⁻¹ with hS₂
  have e3 : E₂ = q * n₁ * n₂ - n₁ * (n₁ * n₁) - n₁ * n₂ := by linear_combination -hsplit₂
  have e4 : 2 * n₂ * E₂ = q * n₁ * n₂ * S₂ := hC5₂
  have hS' : S₂ = 2 * (n₁ * n₁) := by
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hqK hn₁0) hn₂0) ?_
    rw [← e4, e3, hn₁, hn₂]; ring
  refine ⟨?_, ?_⟩
  · rw [htor₁, hS, nsmul_eq_mul, hZc, hfin, hn₁, hn₂]; ring
  · rw [htor₂, hS', nsmul_eq_mul, hZc, hfin, Nat.cast_mul, ← hn₁def, ← hn₂def, hn₁, hn₂]; ring

end Main

end Ws23NV3C7

open Polynomial CuspidalType in
theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q)) :
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) = ((q ^ 2 - 1 : ℕ) : K) ∧
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) * ρ.character (torus q α)⁻¹ =
      (((q - 1) * (q ^ 2 - 1) : ℕ) : K) :=
  Ws23NV3C7.main ρ hK1 hK2 hK3 hK4 hK5 hK6

end S_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv
end P2MW
export P2MW.S_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv (solution)
