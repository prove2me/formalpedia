-- Prove2me | solution 1 for Garrido.injective_lift_rho_sigma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:07:58.249228+00:00
-- url     : https://prove2.me/submissions/4a2bcf97-9faf-4005-963b-74861e2c8678

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix

noncomputable def vec (a b c : ℤ) (k : ℕ) : Fin 3 → ℝ :=
  ![a / 3 ^ k, b * √2 / 3 ^ k, c / 3 ^ k]

noncomputable def act (g : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v

theorem sq2 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

theorem act_mul (g h : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    act (g * h) v = act g (act h v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 3 → ℝ) : act 1 v = v := by simp [act]

theorem act_inv_act (g : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem vec_nine (a b c : ℤ) (k : ℕ) :
    vec (9 * a) (9 * b) (9 * c) (k + 2) = vec a b c k := by
  funext i
  fin_cases i <;> simp [vec, pow_add] <;> field_simp <;> ring

theorem act_rho (a b c : ℤ) (k : ℕ) :
    act rho (vec a b c k) = vec (a - 4 * b) (2 * a + b) (3 * c) (k + 1) := by
  funext i
  fin_cases i <;>
    simp [act, vec, rho, mulVec, dotProduct, Fin.sum_univ_three, pow_succ] <;>
    field_simp <;> (try simp only [sq2]) <;> ring

theorem act_sigma (a b c : ℤ) (k : ℕ) :
    act sigma (vec a b c k) = vec (3 * a) (b - 2 * c) (c + 4 * b) (k + 1) := by
  funext i
  fin_cases i <;>
    simp [act, vec, sigma, mulVec, dotProduct, Fin.sum_univ_three, pow_succ] <;>
    field_simp <;> (try simp only [sq2]) <;> ring

theorem act_rho_inv (a b c : ℤ) (k : ℕ) :
    act rho⁻¹ (vec a b c k) = vec (a + 4 * b) (b - 2 * a) (3 * c) (k + 1) := by
  conv_lhs => rw [← vec_nine a b c k, show 9 * a = (a + 4 * b) - 4 * (b - 2 * a) by ring,
    show 9 * b = 2 * (a + 4 * b) + (b - 2 * a) by ring, show 9 * c = 3 * (3 * c) by ring,
    ← act_rho]
  exact act_inv_act _ _

theorem act_sigma_inv (a b c : ℤ) (k : ℕ) :
    act sigma⁻¹ (vec a b c k) = vec (3 * a) (b + 2 * c) (c - 4 * b) (k + 1) := by
  conv_lhs => rw [← vec_nine a b c k, show 9 * a = 3 * (3 * a) by ring,
    show 9 * b = (b + 2 * c) - 2 * (c - 4 * b) by ring,
    show 9 * c = (c - 4 * b) + 4 * (b + 2 * c) by ring, ← act_sigma]
  exact act_inv_act _ _


/-- The four residue patterns mod 3 (reduced words ending/starting with `ρ, ρ⁻¹, σ, σ⁻¹`). -/
def patB : Fin 2 × Bool → ZMod 3 → ZMod 3 → ZMod 3 → Bool
  | (0, true), x, y, z => decide (x ≠ 0 ∧ y = -x ∧ z = 0)
  | (0, false), x, y, z => decide (x ≠ 0 ∧ y = x ∧ z = 0)
  | (1, true), x, y, z => decide (x = 0 ∧ y ≠ 0 ∧ z = y)
  | (1, false), x, y, z => decide (x = 0 ∧ y ≠ 0 ∧ z = -y)

def InP (l : Fin 2 × Bool) (v : Fin 3 → ℝ) : Prop :=
  ∃ a b c : ℤ, ∃ k : ℕ, v = vec a b c k ∧ patB l a b c = true

noncomputable def gen (x : Fin 2 × Bool) : specialOrthogonalGroup (Fin 3) ℝ :=
  cond x.2 (![rho, sigma] x.1) (![rho, sigma] x.1)⁻¹

theorem step (l m : Fin 2 × Bool) (hlm : l.1 = m.1 → l.2 = m.2) (v : Fin 3 → ℝ)
    (hv : InP m v) : InP l (act (gen l) v) := by
  obtain ⟨a, b, c, k, rfl, h⟩ := hv
  rcases l with ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp only [gen, cond, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      act_rho, act_rho_inv, act_sigma, act_sigma_inv] <;>
    refine ⟨_, _, _, _, rfl, ?_⟩ <;> push_cast <;>
    generalize (a : ZMod 3) = x at * <;> generalize (b : ZMod 3) = y at * <;>
    generalize (c : ZMod 3) = z at * <;> revert h hlm <;> rcases m with ⟨j, t⟩ <;>
    revert x y z <;> revert j t <;> decide


/-- The base point `(1, 0, 1)`, whose residue pattern is in none of the four classes. -/
noncomputable def v0 : Fin 3 → ℝ := vec 1 0 1 0

theorem base (l : Fin 2 × Bool) : InP l (act (gen l) v0) := by
  rcases l with ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp only [v0, gen, cond, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, act_rho, act_rho_inv, act_sigma, act_sigma_inv] <;>
    refine ⟨_, _, _, _, rfl, ?_⟩ <;> decide

theorem not_InP_v0 (l : Fin 2 × Bool) : ¬ InP l v0 := by
  rintro ⟨a, b, c, k, h, hp⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [v0, vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Int.cast_zero, Int.cast_one, zero_mul,
    pow_zero, div_one] at h0 h1 h2
  have hk : (3 : ℝ) ^ k ≠ 0 := by positivity
  have ha : (a : ℝ) = 3 ^ k := by field_simp at h0; linarith
  have hc : (c : ℝ) = 3 ^ k := by field_simp at h2; linarith
  have ha' : a = 3 ^ k := by exact_mod_cast ha
  have hc' : c = 3 ^ k := by exact_mod_cast hc
  have hb' : b = 0 := by
    have h1' : (b : ℝ) * √2 = 0 := by
      rcases div_eq_zero_iff.mp h1.symm with h1 | h1
      · exact h1
      · exact absurd h1 hk
    rcases mul_eq_zero.mp h1' with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 (by positivity)
  subst ha' hc' hb'
  rcases k with _ | k
  · revert hp; rcases l with ⟨i, s⟩; revert i s; decide
  · have : ((3 ^ (k + 1) : ℤ) : ZMod 3) = 0 := by
      rw [Int.cast_pow, pow_succ, show ((3 : ℤ) : ZMod 3) = 0 from by decide, mul_zero]
    rw [this, Int.cast_zero] at hp; revert hp; rcases l with ⟨i, s⟩; revert i s; decide

theorem main (L : List (Fin 2 × Bool)) :
    ∀ l : Fin 2 × Bool, FreeGroup.IsReduced (l :: L) →
      InP l (act ((l :: L).map gen).prod v0) := by
  induction L with
  | nil => intro l _; simpa using base l
  | cons m L ih =>
    intro l hr
    rw [FreeGroup.isReduced_cons_cons] at hr
    rw [List.map_cons, List.prod_cons, act_mul]
    exact step l m hr.1 _ (ih m hr.2)


-- Proposition 1.6 (p. 2), the step: ρ and σ generate a free group (Wagon, Theorem 2.1)
theorem injective_lift_rho_sigma' :
    Function.Injective (FreeGroup.lift ![rho, sigma]) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  rcases hL : w.toWord with _ | ⟨l, L⟩
  · exact hne (FreeGroup.toWord_eq_nil_iff.mp hL)
  · have hr : FreeGroup.IsReduced (l :: L) := hL ▸ FreeGroup.isReduced_toWord
    have key := main L l hr
    have hprod : ((l :: L).map gen).prod = FreeGroup.lift ![rho, sigma] w := by
      rw [← FreeGroup.mk_toWord (x := w), hL, FreeGroup.lift_mk]
      rfl
    rw [hprod, hw, act_one] at key
    exact not_InP_v0 l key

-- Proposition 1.6 (p. 2)

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem injective_lift_rho_sigma : Function.Injective (FreeGroup.lift ![rho, sigma]) :=
  Garrido.BT.injective_lift_rho_sigma'

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    Function.Injective (FreeGroup.lift ![rho, sigma]) :=
  Garrido.BT.Final.injective_lift_rho_sigma
