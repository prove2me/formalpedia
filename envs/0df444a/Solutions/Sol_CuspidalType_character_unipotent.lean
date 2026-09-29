-- Prove2me | solution 1 for CuspidalType.character_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/61417f5f-f052-58ef-a21c-2e2c9ec9e985

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Theorems.Thm_CuspidalType_finrank_eq_of_irreducible_of_cuspidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_character_unipotent

set_option autoImplicit false

p2m_open "CuspidalType P2MW.S_CuspidalType_character_unipotent.CuspidalType"

namespace CuspidalType
p2m_export "CuspidalType" "GL2 unipotent diagElem diagElem_val unipotent_val torus finrank_eq_of_irreducible_of_cuspidal"
namespace K3
p2m_open "CuspidalType"

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext
  simp only [unipotent_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_unipotent (t x : ZMod q) : unipotent q t * unipotent q x = unipotent q (t + x) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem diagElem_mul_unipotent (c : (ZMod q)ˣ) (t : ZMod q) :
    diagElem q c * unipotent q t = unipotent q ((c : ZMod q) * t) * diagElem q c := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val, diagElem_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sum_unipotent_eq_zero {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    ∑ t : ZMod q, ρ (unipotent q t) = 0 := by
  classical
  apply LinearMap.ext
  intro v
  rw [LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
  apply hcusp
  intro t
  rw [map_sum]
  calc ∑ x : ZMod q, ρ (unipotent q t) (ρ (unipotent q x) v) = ∑ x : ZMod q, ρ (unipotent q (t + x)) v := by
        simp only [← unipotent_mul_unipotent, map_mul, Module.End.mul_apply]
    _ = ∑ x : ZMod q, ρ (unipotent q x) v := Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun x => rfl)

end CuspidalType.K3

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {t : ZMod q} (ht : t ≠ 0) :
    ρ.character (unipotent q t) = -1 := by
  classical
  have hdim : Module.finrank K V = q - 1 := CuspidalType.finrank_eq_of_irreducible_of_cuspidal ρ hirr hcusp
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le

  have hconst : ∀ x : ZMod q, x ≠ 0 → ρ.character (unipotent q x) = ρ.character (unipotent q t) := by
    intro x hx
    have hc : x * t⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero ht)
    have h := CuspidalType.K3.diagElem_mul_unipotent (Units.mk0 (x * t⁻¹) hc) t
    rw [Units.val_mk0, inv_mul_cancel_right₀ ht] at h
    rw [← Representation.char_conj ρ (unipotent q t) (diagElem q (Units.mk0 (x * t⁻¹) hc)), h, mul_inv_cancel_right]

  have hsum : ∑ x : ZMod q, ρ.character (unipotent q x) = 0 := by
    have : ∑ x : ZMod q, ρ.character (unipotent q x) = LinearMap.trace K V (∑ x : ZMod q, ρ (unipotent q x)) := by
      rw [map_sum]; rfl
    rw [this, CuspidalType.K3.sum_unipotent_eq_zero ρ hcusp, map_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), CuspidalType.K3.unipotent_zero,
    Representation.char_one, hdim, Finset.sum_congr rfl (fun x hx => hconst x (Finset.ne_of_mem_erase hx)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_sub hq1, Nat.cast_one] at hsum
  have hq : ((q : K) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (Fact.out : q.Prime).one_lt.ne'

  have : ((q : K) - 1) * (ρ.character (unipotent q t) + 1) = 0 := by rw [mul_add, mul_one, add_comm]; exact hsum
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 this).resolve_left hq)

end S_CuspidalType_character_unipotent
end P2MW
export P2MW.S_CuspidalType_character_unipotent (solution)
