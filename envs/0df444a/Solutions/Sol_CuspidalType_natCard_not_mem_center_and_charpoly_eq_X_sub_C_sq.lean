-- Prove2me | solution 1 for CuspidalType.natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/152e0d3f-a8aa-539e-8914-6115e5700cef

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq

set_option autoImplicit false

open Polynomial CuspidalType

namespace Ws23C2

open Polynomial Matrix

section Generic

variable {F : Type*} [Field F] [DecidableEq F]

theorem nil_rel (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    N 1 1 = -N 0 0 ∧ N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
  have h := fun i j => congrFun (congrFun hN i) j
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h01 h10 h11
  refine ⟨?_, h00⟩
  by_contra hne
  have hsum : N 0 0 + N 1 1 ≠ 0 := fun hs => hne (by linear_combination hs)
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have ha : N 0 0 = 0 := by
    rw [hb, zero_mul, add_zero] at h00
    exact mul_self_eq_zero.mp h00
  have hd : N 1 1 = 0 := by
    rw [hb, mul_zero, zero_add] at h11
    exact mul_self_eq_zero.mp h11
  exact hsum (by rw [ha, hd, add_zero])

def nilOf (s t : F) : Matrix (Fin 2) (Fin 2) F :=
  if s = 0 then !![0, 0; t, 0] else !![t, s; -(t * t) / s, -t]

theorem nilOf_mul_self (s t : F) : nilOf s t * nilOf s t = 0 := by
  unfold nilOf
  split_ifs with hs
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; field_simp; ring)

theorem nilOf_apply_01 (s t : F) : nilOf s t 0 1 = s := by
  unfold nilOf; split_ifs with hs <;> simp [hs]

theorem nilOf_eq_zero_iff (s t : F) : nilOf s t = 0 ↔ s = 0 ∧ t = 0 := by
  constructor
  · intro h
    have hs : s = 0 := by simpa [nilOf_apply_01] using congrFun (congrFun h 0) 1
    refine ⟨hs, ?_⟩
    have h10 := congrFun (congrFun h 1) 0
    simpa [nilOf, hs] using h10
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf]

theorem nilOf_injective : Function.Injective (fun p : F × F => nilOf p.1 p.2) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only at h
  have hs : s = s' := by
    have := congrFun (congrFun h 0) 1
    rwa [nilOf_apply_01, nilOf_apply_01] at this
  subst hs
  by_cases hs0 : s = 0
  · have h10 := congrFun (congrFun h 1) 0
    simp [nilOf, hs0] at h10
    simp [h10]
  · have h00 := congrFun (congrFun h 0) 0
    simp [nilOf, hs0] at h00
    simp [h00]

theorem exists_nilOf_eq (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    ∃ s t : F, nilOf s t = N := by
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  by_cases hb : N 0 1 = 0
  · have ha : N 0 0 = 0 := by
      rw [hb, zero_mul, add_zero] at hadbc
      exact mul_self_eq_zero.mp hadbc
    refine ⟨0, N 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf, ha, hb, hd]
  · refine ⟨N 0 1, N 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilOf, hb, hd]

    field_simp
    linear_combination -hadbc

theorem nilOf_bijective :
    Function.Bijective (fun p : {p : F × F // p ≠ 0} =>
      (⟨nilOf p.1.1 p.1.2, fun h => p.2 (Prod.ext ((nilOf_eq_zero_iff _ _).mp h).1 ((nilOf_eq_zero_iff _ _).mp h).2),
        nilOf_mul_self _ _⟩ : {N : Matrix (Fin 2) (Fin 2) F // N ≠ 0 ∧ N * N = 0})) := by
  constructor
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have := congrArg Subtype.val h
    exact Subtype.ext (nilOf_injective this)
  · rintro ⟨N, hN0, hN⟩
    obtain ⟨s, t, rfl⟩ := exists_nilOf_eq N hN
    refine ⟨⟨(s, t), fun h => hN0 ?_⟩, rfl⟩
    rw [Prod.mk_eq_zero] at h
    exact (nilOf_eq_zero_iff s t).mpr h

def glOf (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) : GL (Fin 2) F :=
  ⟨z • (1 + N), z⁻¹ • (1 - N),
    by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz, one_smul]
      simp [mul_sub, add_mul, hN],
    by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz, one_smul]
      simp [sub_mul, mul_add, hN]⟩

omit [DecidableEq F] in
@[scoped simp] theorem val_glOf (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    ((glOf z hz N hN : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = z • (1 + N) := rfl

theorem charpoly_smul_one_add (z : F) (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) :
    (z • (1 + N)).charpoly = (X - C z) ^ 2 := by
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  have htr : (z • (1 + N)).trace = 2 * z := by
    simp [Matrix.trace_fin_two, hd]; ring
  have hdet : (z • (1 + N)).det = z ^ 2 := by
    simp [Matrix.det_fin_two, hd]
    linear_combination (-(z ^ 2)) * hadbc
  rw [Matrix.charpoly_fin_two, htr, hdet, map_mul, map_pow, show C (2 : F) = (2 : F[X]) from map_ofNat C 2]
  ring

theorem smul_one_add_not_mem_range_scalar (z : F) (hz : z ≠ 0) (N : Matrix (Fin 2) (Fin 2) F)
    (hN : N * N = 0) (hN0 : N ≠ 0) : z • (1 + N) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  obtain ⟨hd, hadbc⟩ := nil_rel N hN
  have h := fun i j => congrFun (congrFun ha i) j
  have h01 := h 0 1
  have h10 := h 1 0
  simp [Matrix.scalar_apply, hz] at h01 h10

  have ha0 : N 0 0 = 0 := by
    rw [h01, zero_mul, add_zero] at hadbc
    exact mul_self_eq_zero.mp hadbc
  apply hN0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, ha0, hd]

abbrev S (F : Type*) [Field F] : Type _ :=
  {g : GL (Fin 2) F // g ∉ Subgroup.center (GL (Fin 2) F) ∧
      ∃ z : F, (g : Matrix (Fin 2) (Fin 2) F).charpoly = (X - C z) ^ 2}

def phi (x : Fˣ × {N : Matrix (Fin 2) (Fin 2) F // N ≠ 0 ∧ N * N = 0}) : S F :=
  ⟨glOf (x.1 : F) x.1.ne_zero x.2.1 x.2.2.2,
    by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, val_glOf]
      exact smul_one_add_not_mem_range_scalar _ x.1.ne_zero _ x.2.2.2 x.2.2.1,
    ⟨(x.1 : F), by rw [val_glOf]; exact charpoly_smul_one_add _ _ x.2.2.2⟩⟩

omit [DecidableEq F] in
theorem eq_of_X_sub_C_sq_eq {z z' : F} (h : (X - C z) ^ 2 = (X - C z') ^ 2) : z = z' := by
  have h1 := congrArg (Polynomial.eval z) h
  simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self] at h1
  have h2 : (z - z') ^ 2 = 0 := by
    rw [← h1]; norm_num
  have h3 : z - z' = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linear_combination h3

theorem phi_injective : Function.Injective (phi (F := F)) := by
  rintro ⟨z, N, hN0, hN⟩ ⟨z', N', hN0', hN'⟩ h
  have hval : (z : F) • (1 + N) = (z' : F) • (1 + N') := by
    have := congrArg (fun s : S F => ((s.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [phi] using this
  have hz : (z : F) = z' := by
    have h1 := charpoly_smul_one_add (z : F) N hN
    have h2 := charpoly_smul_one_add (z' : F) N' hN'
    rw [hval] at h1
    exact eq_of_X_sub_C_sq_eq (h1.symm.trans h2)
  have hzu : z = z' := Units.ext hz
  subst hzu
  have hN1 : 1 + N = 1 + N' := smul_right_injective _ z.ne_zero hval
  have : N = N' := add_left_cancel hN1
  subst this
  rfl

theorem phi_surjective : Function.Surjective (phi (F := F)) := by
  rintro ⟨g, hgc, z, hchar⟩

  have hCH : ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) * ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) = 0 := by
    have := Matrix.aeval_self_charpoly (g : Matrix (Fin 2) (Fin 2) F)
    rw [hchar] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sq] using this
  have hz : z ≠ 0 := by
    rintro rfl
    simp only [zero_smul, sub_zero] at hCH
    have h1 : ((g * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [Units.val_mul]; exact hCH
    exact (g * g).ne_zero h1
  set N : Matrix (Fin 2) (Fin 2) F := z⁻¹ • ((g : Matrix (Fin 2) (Fin 2) F) - z • 1) with hNdef
  have hN : N * N = 0 := by
    rw [hNdef, smul_mul_assoc, mul_smul_comm, hCH, smul_zero, smul_zero]
  have hgN : z • (1 + N) = (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [hNdef, smul_add, smul_smul, mul_inv_cancel₀ hz, one_smul]
    abel
  have hN0 : N ≠ 0 := by
    intro h0
    apply hgc
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨z, ?_⟩
    rw [← hgN, h0, add_zero, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  refine ⟨⟨Units.mk0 z hz, ⟨N, hN0, hN⟩⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp [phi, hgN]

theorem phi_bijective : Function.Bijective (phi (F := F)) := ⟨phi_injective, phi_surjective⟩

end Generic

theorem card_nil (q : ℕ) [Fact q.Prime] :
    Nat.card {N : Matrix (Fin 2) (Fin 2) (ZMod q) // N ≠ 0 ∧ N * N = 0} = q ^ 2 - 1 := by
  rw [← Nat.card_eq_of_bijective _ nilOf_bijective, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Fintype.card_subtype_eq, sq]

theorem card_S (q : ℕ) [Fact q.Prime] : Nat.card (S (ZMod q)) = (q - 1) * (q ^ 2 - 1) := by
  rw [← Nat.card_eq_of_bijective _ phi_bijective, Nat.card_prod, card_nil, Nat.card_eq_fintype_card,
    ZMod.card_units]

end Ws23C2
p2m_reactivate "P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq.Ws23C2"

theorem solution
    (q : ℕ) [Fact q.Prime]
    :
    Nat.card {g : GL2 q // g ∉ Subgroup.center (GL2 q) ∧
      ∃ z : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (X - C z) ^ 2} = (q - 1) * (q ^ 2 - 1) :=
  Ws23C2.card_S q

end S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq
end P2MW
export P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq (solution)
