-- Prove2me | solution 1 for CuspidalType.character_unipotent_mul_diagElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/59909d19-296e-5d97-991a-1d124dfbe728

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_character_unipotent_mul_diagElem

set_option autoImplicit false

p2m_open "CuspidalType P2MW.S_CuspidalType_character_unipotent_mul_diagElem.CuspidalType"

namespace CuspidalType
p2m_export "CuspidalType" "GL2 unipotent diagElem diagElem_val unipotent_val"
namespace K4
p2m_open "CuspidalType"

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_mul_unipotent (t x : ZMod q) : unipotent q t * unipotent q x = unipotent q (t + x) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_mul_unipotent_mul_diagElem (a : (ZMod q)ˣ) (s x : ZMod q) :
    unipotent q x * (unipotent q s * diagElem q a) =
      unipotent q (s + (1 - (a : ZMod q)) * x) * diagElem q a * unipotent q x := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val, diagElem_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

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

end CuspidalType.K4

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {a : (ZMod q)ˣ} (ha : a ≠ 1) (s : ZMod q) :
    ρ.character (unipotent q s * diagElem q a) = 0 := by
  classical

  have h3 : ∑ t : ZMod q, ρ.character (unipotent q t * diagElem q a) = 0 := by
    have : ∑ t : ZMod q, ρ.character (unipotent q t * diagElem q a) =
        LinearMap.trace K V ((∑ t : ZMod q, ρ (unipotent q t)) * ρ (diagElem q a)) := by
      rw [Finset.sum_mul, map_sum]
      simp only [Representation.character, map_mul]
    rw [this, CuspidalType.K4.sum_unipotent_eq_zero ρ hcusp, zero_mul, map_zero]

  have ha' : (1 - (a : ZMod q)) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact ha (Units.ext h.symm)
  have h2 : ∑ x : ZMod q, ρ.character (unipotent q x * (unipotent q s * diagElem q a) * (unipotent q x)⁻¹) =
      (q : K) * ρ.character (unipotent q s * diagElem q a) := by
    simp only [Representation.char_conj, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hbij : ∑ x : ZMod q, ρ.character (unipotent q x * (unipotent q s * diagElem q a) * (unipotent q x)⁻¹) =
      ∑ t : ZMod q, ρ.character (unipotent q t * diagElem q a) := by
    refine Fintype.sum_equiv ((Equiv.mulLeft₀ (1 - (a : ZMod q)) ha').trans (Equiv.addLeft s)) _ _ (fun x => ?_)
    rw [CuspidalType.K4.unipotent_mul_unipotent_mul_diagElem a s x, mul_inv_cancel_right]
    rfl
  have hq : (q : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  have := h2.symm.trans (hbij.trans h3)
  exact (mul_eq_zero.1 this).resolve_left hq

end S_CuspidalType_character_unipotent_mul_diagElem
end P2MW
export P2MW.S_CuspidalType_character_unipotent_mul_diagElem (solution)
