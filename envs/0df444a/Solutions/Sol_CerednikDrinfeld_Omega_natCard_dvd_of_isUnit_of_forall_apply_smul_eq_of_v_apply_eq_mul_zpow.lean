-- Prove2me | solution 1 for CerednikDrinfeld.Omega.natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/687d916f-010e-584e-9bee-a3bd9479baac

import Mathlib
import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace TubeStab

section Basics

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

def IsUnif (ϖ : PseudoUniformizer K₀ K) : Prop :=
  ∀ a : K₀, Valued.v (ι a) ≤ Valued.v (ι ϖ.ϖ) ∨ 1 ≤ Valued.v (ι a)

variable (ϖ : PseudoUniformizer K₀ K)

def InV (r : Γ₀) : Prop := Valued.v (ι ϖ.ϖ) < r ∧ r < 1

def InA (z : K) : Prop := InV ϖ (Valued.v z)

theorem inA_iff (z : K) : InA ϖ z ↔ Valued.v (ι ϖ.ϖ) < Valued.v z ∧ Valued.v z < 1 := Iff.rfl

theorem inA_of_mem {z : K} (hz : z ∈ stdEdgeTube ϖ) : InA ϖ z := ⟨hz.2.1, hz.2.2⟩

theorem not_inV_algebraMap (hunif : IsUnif ϖ) (t : K₀) : ¬ InV ϖ (Valued.v (ι t)) := by
  rintro ⟨h1, h2⟩
  rcases hunif t with h | h
  · exact absurd h1 (not_lt.2 h)
  · exact absurd h2 (not_lt.2 h)

theorem mem_of_inA (hunif : IsUnif ϖ) {z : K} (hz : InA ϖ z) : z ∈ stdEdgeTube ϖ := by
  refine ⟨?_, hz.1, hz.2⟩
  rw [mem_upperHalfPlane_iff]
  intro a ha
  apply not_inV_algebraMap ϖ hunif a
  rw [ha]; exact hz

theorem InA.v_ne_zero {z : K} (hz : InA ϖ z) : Valued.v z ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hz.1)

theorem InA.ne_zero {z : K} (hz : InA ϖ z) : z ≠ 0 := fun h => hz.v_ne_zero ϖ (by rw [h, map_zero])

theorem q_pos : 0 < Valued.v (ι ϖ.ϖ) := ϖ.pos
theorem q_lt_one : Valued.v (ι ϖ.ϖ) < 1 := ϖ.lt_one
theorem q_ne_zero : Valued.v (ι ϖ.ϖ) ≠ 0 := ϖ.pos.ne'

theorem exists_basePoint [IsAlgClosed K] :
    ∃ s : K, InA ϖ s ∧ Valued.v s * Valued.v s ≠ Valued.v (ι ϖ.ϖ) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (ι ϖ.ϖ) (n := 3) (by norm_num)
  have hv : Valued.v s ^ 3 = Valued.v (ι ϖ.ϖ) := by rw [← map_pow, hs]
  have hq0 := q_pos ϖ
  have hq1 := q_lt_one ϖ
  have hs1 : Valued.v s < 1 := by
    by_contra h
    rw [not_lt] at h
    have : (1 : Γ₀) ≤ Valued.v s ^ 3 := one_le_pow₀ h
    rw [hv] at this
    exact absurd hq1 (not_lt.2 this)
  have hs0 : Valued.v (ι ϖ.ϖ) < Valued.v s := by
    by_contra h
    rw [not_lt] at h

    have h3 : Valued.v s ^ 3 ≤ Valued.v (ι ϖ.ϖ) ^ 3 := pow_le_pow_left₀ zero_le' h 3
    rw [hv] at h3
    have : Valued.v (ι ϖ.ϖ) ^ 3 < Valued.v (ι ϖ.ϖ) := by
      calc Valued.v (ι ϖ.ϖ) ^ 3 = Valued.v (ι ϖ.ϖ) * (Valued.v (ι ϖ.ϖ) * Valued.v (ι ϖ.ϖ)) := by
            rw [pow_succ, pow_two, mul_comm]
        _ < Valued.v (ι ϖ.ϖ) * 1 := by
          apply mul_lt_mul_of_pos_left _ hq0
          calc Valued.v (ι ϖ.ϖ) * Valued.v (ι ϖ.ϖ) < Valued.v (ι ϖ.ϖ) * 1 := mul_lt_mul_of_pos_left hq1 hq0
            _ = Valued.v (ι ϖ.ϖ) := mul_one _
            _ < 1 := hq1
        _ = Valued.v (ι ϖ.ϖ) := mul_one _
    exact absurd h3 (not_le.2 this)
  refine ⟨s, ⟨hs0, hs1⟩, fun h => ?_⟩

  have hne : Valued.v s ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hs0)
  have : Valued.v s ^ 3 = Valued.v s * Valued.v s * 1 := by rw [mul_one, h, hv]
  have : Valued.v s = 1 := by
    have h' : Valued.v s * Valued.v s * Valued.v s = Valued.v s * Valued.v s * 1 := by
      rw [← this, pow_succ, pow_two]
    exact mul_left_cancel₀ (mul_ne_zero hne hne) h'
  exact absurd hs1 (by rw [this]; exact lt_irrefl 1)

theorem unif_dichot (hunif : IsUnif ϖ) (a b : K₀) :
    Valued.v (ι b) ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι a) ∨ Valued.v (ι a) ≤ Valued.v (ι b) := by
  by_cases ha : a = 0
  · right; rw [ha, map_zero, map_zero]; exact zero_le'
  · have ha' : Valued.v (ι a) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact fun h => ha ((algebraMap K₀ K).injective (by rw [h, map_zero]))
    have hapos : 0 < Valued.v (ι a) := lt_of_le_of_ne zero_le' ha'.symm
    rcases hunif (b / a) with h | h
    · left
      rw [map_div₀, map_div₀, div_le_iff₀ hapos] at h
      exact h
    · right
      rw [map_div₀, map_div₀, le_div_iff₀ hapos, one_mul] at h
      exact h

theorem v_lin_eq_mul {a b : K₀} (h : Valued.v (ι b) ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι a)) {z : K}
    (hz : InA ϖ z) : Valued.v (ι a * z + ι b) = Valued.v (ι a) * Valued.v z := by
  by_cases ha : Valued.v (ι a) = 0
  · rw [ha, mul_zero, nonpos_iff_eq_zero] at h
    rw [Valuation.zero_iff] at ha h
    simp [ha, h]
  · have hapos : 0 < Valued.v (ι a) := lt_of_le_of_ne zero_le' (Ne.symm ha)
    have hlt : Valued.v (ι b) < Valued.v (ι a * z) := by
      rw [map_mul]
      calc Valued.v (ι b) ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι a) := h
        _ = Valued.v (ι a) * Valued.v (ι ϖ.ϖ) := mul_comm _ _
        _ < Valued.v (ι a) * Valued.v z := mul_lt_mul_of_pos_left hz.1 hapos
    rw [Valuation.map_add_eq_of_lt_left _ hlt, map_mul]

theorem v_lin_eq_const {a b : K₀} (h : Valued.v (ι a) ≤ Valued.v (ι b)) {z : K}
    (hz : InA ϖ z) : Valued.v (ι a * z + ι b) = Valued.v (ι b) := by
  by_cases ha : Valued.v (ι a) = 0
  · rw [Valuation.zero_iff] at ha
    rw [ha, zero_mul, zero_add]
  · have hapos : 0 < Valued.v (ι a) := lt_of_le_of_ne zero_le' (Ne.symm ha)
    have hlt : Valued.v (ι a * z) < Valued.v (ι b) := by
      rw [map_mul]
      calc Valued.v (ι a) * Valued.v z < Valued.v (ι a) * 1 := mul_lt_mul_of_pos_left hz.2 hapos
        _ = Valued.v (ι a) := mul_one _
        _ ≤ Valued.v (ι b) := h
    rw [Valuation.map_add_eq_of_lt_right _ hlt]

end Basics

section Dichotomy

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

variable (ϖ : PseudoUniformizer K₀ K)

theorem v_algebraMap_ne_zero {x : K₀} (hx : x ≠ 0) : Valued.v (ι x) ≠ 0 := by
  rw [Valuation.ne_zero_iff]; exact fun h => hx ((algebraMap K₀ K).injective (by rw [h, map_zero]))

theorem v_algebraMap_pos {x : K₀} (hx : x ≠ 0) : 0 < Valued.v (ι x) :=
  lt_of_le_of_ne zero_le' (v_algebraMap_ne_zero hx).symm

theorem eq_zero_of_v_algebraMap_le_zero {x : K₀} (hx : Valued.v (ι x) ≤ 0) : x = 0 := by
  rw [nonpos_iff_eq_zero, Valuation.zero_iff] at hx
  exact (algebraMap K₀ K).injective (by rw [hx, map_zero])

theorem eq_one_of_inV_mul (hunif : IsUnif ϖ) (t : K₀) {r : Γ₀} (hr : InV ϖ r)
    (h : InV ϖ (Valued.v (ι t) * r)) : Valued.v (ι t) = 1 := by
  have hq0 := q_pos ϖ
  rcases hunif t with h1 | h1
  · exfalso
    have : Valued.v (ι t) * r < Valued.v (ι ϖ.ϖ) :=
      calc Valued.v (ι t) * r ≤ Valued.v (ι ϖ.ϖ) * r := mul_le_mul_left h1 r
        _ < Valued.v (ι ϖ.ϖ) * 1 := mul_lt_mul_of_pos_left hr.2 hq0
        _ = Valued.v (ι ϖ.ϖ) := mul_one _
    exact absurd h.1 (not_lt.2 this.le)
  · have ht : t ≠ 0 := fun ht => by
      rw [ht, map_zero, map_zero] at h1; exact absurd h1 (not_le.2 zero_lt_one)
    have hu : Valued.v (ι t⁻¹) * Valued.v (ι t) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ ht, map_one, map_one]
    rcases hunif t⁻¹ with h2 | h2
    · exfalso
      have hr0 : 0 < r := lt_trans hq0 hr.1
      have : r < r :=
        calc r = Valued.v (ι t⁻¹) * (Valued.v (ι t) * r) := by rw [← mul_assoc, hu, one_mul]
          _ ≤ Valued.v (ι ϖ.ϖ) * (Valued.v (ι t) * r) := mul_le_mul_left h2 _
          _ < Valued.v (ι ϖ.ϖ) * 1 := mul_lt_mul_of_pos_left h.2 hq0
          _ = Valued.v (ι ϖ.ϖ) := mul_one _
          _ < r := hr.1
      exact lt_irrefl _ this
    · apply le_antisymm _ h1
      calc Valued.v (ι t) = 1 * Valued.v (ι t) := (one_mul _).symm
        _ ≤ Valued.v (ι t⁻¹) * Valued.v (ι t) := mul_le_mul_left h2 _
        _ = 1 := hu

theorem eq_q_of_inV_mul (hunif : IsUnif ϖ) (t : K₀) {r x : Γ₀} (hr : InV ϖ r) (hx : InV ϖ x)
    (h : x * r = Valued.v (ι t)) : Valued.v (ι t) = Valued.v (ι ϖ.ϖ) := by
  have hq0 := q_pos ϖ
  have hr0 : 0 < r := lt_trans hq0 hr.1
  have hx0 : 0 < x := lt_trans hq0 hx.1
  rcases hunif t with h1 | h1
  · rcases hunif (t / ϖ.ϖ) with h2 | h2
    · exfalso
      rw [map_div₀, map_div₀, div_le_iff₀ hq0] at h2
      have : Valued.v (ι ϖ.ϖ) * Valued.v (ι ϖ.ϖ) < x * r :=
        calc Valued.v (ι ϖ.ϖ) * Valued.v (ι ϖ.ϖ) < x * Valued.v (ι ϖ.ϖ) := mul_lt_mul_of_pos_right hx.1 hq0
          _ < x * r := mul_lt_mul_of_pos_left hr.1 hx0
      rw [h] at this
      exact absurd h2 (not_le.2 this)
    · rw [map_div₀, map_div₀, le_div_iff₀ hq0, one_mul] at h2
      exact le_antisymm h1 h2
  · exfalso
    have : x * r < 1 :=
      calc x * r < x * 1 := mul_lt_mul_of_pos_left hr.2 hx0
        _ = x := mul_one _
        _ < 1 := hx.2
    rw [h] at this
    exact absurd h1 (not_le.2 this)

def Direct (g : GL (Fin 2) K₀) : Prop :=
  Valued.v (ι (g 0 1)) ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι (g 0 0)) ∧
  Valued.v (ι (g 1 0)) ≤ Valued.v (ι (g 1 1)) ∧
  Valued.v (ι (g 0 0)) = Valued.v (ι (g 1 1)) ∧ g 1 1 ≠ 0

def Swap (g : GL (Fin 2) K₀) : Prop :=
  Valued.v (ι (g 0 0)) ≤ Valued.v (ι (g 0 1)) ∧
  Valued.v (ι (g 1 1)) ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι (g 1 0)) ∧
  Valued.v (ι (g 0 1)) = Valued.v (ι ϖ.ϖ) * Valued.v (ι (g 1 0)) ∧ g 1 0 ≠ 0

theorem moebius_def (g : GL (Fin 2) K₀) (z : K) :
    moebius K₀ K g z = (ι (g 0 0) * z + ι (g 0 1)) / (ι (g 1 0) * z + ι (g 1 1)) := rfl

theorem v_moebius_of_direct {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z) :
    Valued.v (moebius K₀ K g z) = Valued.v z := by
  rw [moebius_def, map_div₀, v_lin_eq_mul ϖ hd.1 hz, v_lin_eq_const ϖ hd.2.1 hz, hd.2.2.1,
    mul_div_cancel_left₀ _ (v_algebraMap_ne_zero hd.2.2.2)]

theorem v_moebius_mul_of_swap {g : GL (Fin 2) K₀} (hs : Swap ϖ g) {z : K} (hz : InA ϖ z) :
    Valued.v (moebius K₀ K g z) * Valued.v z = Valued.v (ι ϖ.ϖ) := by
  rw [moebius_def, map_div₀, v_lin_eq_const ϖ hs.1 hz, v_lin_eq_mul ϖ hs.2.1 hz, hs.2.2.1,
    div_mul_eq_mul_div, mul_assoc, mul_div_cancel_right₀ _ (mul_ne_zero (v_algebraMap_ne_zero hs.2.2.2) (hz.v_ne_zero ϖ))]

theorem direct_or_swap [IsAlgClosed K] (hunif : IsUnif ϖ) (g : GL (Fin 2) K₀)
    (hg : ∀ z : K, InA ϖ z → InA ϖ (moebius K₀ K g z)) : Direct ϖ g ∨ Swap ϖ g := by
  obtain ⟨s, hs, -⟩ := exists_basePoint ϖ
  have hgs := hg s hs
  have hdet : (g : Matrix (Fin 2) (Fin 2) K₀).det ≠ 0 := g.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  rcases unif_dichot ϖ hunif (g 0 0) (g 0 1) with hnum | hnum <;>
  rcases unif_dichot ϖ hunif (g 1 0) (g 1 1) with hden | hden
  ·
    exfalso
    have hv : Valued.v (moebius K₀ K g s) = Valued.v (ι (g 0 0 / g 1 0)) := by
      rw [moebius_def, map_div₀, v_lin_eq_mul ϖ hnum hs, v_lin_eq_mul ϖ hden hs, map_div₀, map_div₀,
        mul_div_mul_right _ _ (hs.v_ne_zero ϖ)]
    exact not_inV_algebraMap ϖ hunif _ (by rw [← hv]; exact hgs)
  ·
    left
    have hd : g 1 1 ≠ 0 := by
      intro hd; apply hdet
      have hc : g 1 0 = 0 := by
        apply eq_zero_of_v_algebraMap_le_zero (K := K)
        rw [hd, map_zero, map_zero] at hden; exact hden
      rw [hd, hc]; ring
    have hv : Valued.v (moebius K₀ K g s) = Valued.v (ι (g 0 0 / g 1 1)) * Valued.v s := by
      rw [moebius_def, map_div₀, v_lin_eq_mul ϖ hnum hs, v_lin_eq_const ϖ hden hs, map_div₀, map_div₀,
        div_mul_eq_mul_div]
    have h1 : Valued.v (ι (g 0 0 / g 1 1)) = 1 := eq_one_of_inV_mul ϖ hunif _ hs (hv ▸ hgs)
    rw [map_div₀, map_div₀, div_eq_one_iff_eq (v_algebraMap_ne_zero hd)] at h1
    exact ⟨hnum, hden, h1, hd⟩
  ·
    right
    have hc : g 1 0 ≠ 0 := by
      intro hc; apply hdet
      have hd : g 1 1 = 0 := by
        apply eq_zero_of_v_algebraMap_le_zero (K := K)
        rw [hc, map_zero, map_zero, mul_zero] at hden; exact hden
      rw [hd, hc]; ring
    have hv : Valued.v (moebius K₀ K g s) * Valued.v s = Valued.v (ι (g 0 1 / g 1 0)) := by
      rw [moebius_def, map_div₀, v_lin_eq_const ϖ hnum hs, v_lin_eq_mul ϖ hden hs, map_div₀, map_div₀,
        div_mul_eq_mul_div, mul_div_mul_right _ _ (hs.v_ne_zero ϖ)]
    have h1 := eq_q_of_inV_mul ϖ hunif _ hs hgs hv
    rw [map_div₀, map_div₀, div_eq_iff (v_algebraMap_ne_zero hc)] at h1
    exact ⟨hnum, hden, h1, hc⟩
  ·
    exfalso
    have hv : Valued.v (moebius K₀ K g s) = Valued.v (ι (g 0 1 / g 1 1)) := by
      rw [moebius_def, map_div₀, v_lin_eq_const ϖ hnum hs, v_lin_eq_const ϖ hden hs, map_div₀, map_div₀]
    exact not_inV_algebraMap ϖ hunif _ (by rw [← hv]; exact hgs)

variable [DecidableEq K]

theorem pmoebius_mk_of_inA (hunif : IsUnif ϖ) (g : GL (Fin 2) K₀) {z : K} (hz : InA ϖ z) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z = moebius K₀ K g z :=
  pmoebius_mk K₀ g z (moebius_denom_ne_zero_of_mem K₀ (mem_of_inA ϖ hunif hz).1 g)

end Dichotomy

theorem v_pmoebius_eq_or_mul_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (h : PGL(2, K₀)) (hh : ∀ z : K, z ∈ stdEdgeTube ϖ → pmoebius K₀ h z ∈ stdEdgeTube ϖ) :
    (∀ z : K, z ∈ stdEdgeTube ϖ → Valued.v (pmoebius K₀ h z) = Valued.v z) ∨
    (∀ z : K, z ∈ stdEdgeTube ϖ →
      Valued.v (pmoebius K₀ h z) * Valued.v z = Valued.v (algebraMap K₀ K ϖ.ϖ)) := by
  induction h using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    have hg : ∀ z : K, InA ϖ z → InA ϖ (moebius K₀ K g z) := fun z hz => by
      rw [← pmoebius_mk_of_inA ϖ hunif g hz]; exact inA_of_mem ϖ (hh z (mem_of_inA ϖ hunif hz))
    rcases direct_or_swap ϖ hunif g hg with hd | hs
    · left; intro z hz
      rw [pmoebius_mk_of_inA ϖ hunif g (inA_of_mem ϖ hz)]; exact v_moebius_of_direct ϖ hd (inA_of_mem ϖ hz)
    · right; intro z hz
      rw [pmoebius_mk_of_inA ϖ hunif g (inA_of_mem ϖ hz)]; exact v_moebius_mul_of_swap ϖ hs (inA_of_mem ϖ hz)

section DirectAnalysis

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

variable (ϖ : PseudoUniformizer K₀ K)

theorem div_lt_one_of_lt {a b : Γ₀} (h : a < b) : a / b < 1 := by
  rw [div_eq_mul_inv]; exact mul_inv_lt_of_lt_mul₀ (by rwa [one_mul])

theorem Direct.den_ne_zero {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z) :
    ι (g 1 0) * z + ι (g 1 1) ≠ 0 := by
  intro h
  have := v_lin_eq_const ϖ hd.2.1 hz
  rw [h, map_zero] at this
  exact v_algebraMap_ne_zero hd.2.2.2 this.symm

theorem Direct.inA_moebius {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z) :
    InA ϖ (moebius K₀ K g z) := by
  show InV ϖ _
  rw [v_moebius_of_direct ϖ hd hz]; exact hz

theorem v_ratio_sub_lt {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z) :
    Valued.v (moebius K₀ K g z / z - ι (g 0 0) / ι (g 1 1)) < 1 := by
  have hz0 := hz.ne_zero ϖ
  have hD := hd.den_ne_zero ϖ hz
  have hd0 : ι (g 1 1) ≠ 0 := fun h => hd.2.2.2 ((algebraMap K₀ K).injective (by rw [h, map_zero]))
  have key : moebius K₀ K g z / z - ι (g 0 0) / ι (g 1 1) =
      (ι (g 0 1) * ι (g 1 1) - ι (g 0 0) * ι (g 1 0) * z ^ 2) / (ι (g 1 1) * z * (ι (g 1 0) * z + ι (g 1 1))) := by
    rw [moebius_def, div_div, div_sub_div _ _ (mul_ne_zero hD hz0) hd0, mul_comm (ι (g 1 1)) z, mul_assoc, mul_comm]
    congr 1
    · ring
    · ring
  rw [key, map_div₀]
  have hdpos : 0 < Valued.v (ι (g 1 1)) := v_algebraMap_pos hd.2.2.2
  have hzpos : 0 < Valued.v z := lt_trans (q_pos ϖ) hz.1
  have hden : Valued.v (ι (g 1 1) * z * (ι (g 1 0) * z + ι (g 1 1))) =
      Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v z := by
    rw [map_mul, map_mul, v_lin_eq_const ϖ hd.2.1 hz]; ac_rfl
  rw [hden]
  apply div_lt_one_of_lt
  apply lt_of_le_of_lt (Valuation.map_sub _ _ _)
  apply max_lt
  · rw [map_mul]
    calc Valued.v (ι (g 0 1)) * Valued.v (ι (g 1 1))
        ≤ Valued.v (ι ϖ.ϖ) * Valued.v (ι (g 0 0)) * Valued.v (ι (g 1 1)) := mul_le_mul_left hd.1 _
      _ = Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v (ι ϖ.ϖ) := by rw [hd.2.2.1]; ac_rfl
      _ < Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v z :=
          mul_lt_mul_of_pos_left hz.1 (mul_pos hdpos hdpos)
  · rw [map_mul, map_mul, map_pow]
    calc Valued.v (ι (g 0 0)) * Valued.v (ι (g 1 0)) * Valued.v z ^ 2
        ≤ Valued.v (ι (g 0 0)) * Valued.v (ι (g 1 1)) * Valued.v z ^ 2 :=
          mul_le_mul_left (mul_le_mul_right hd.2.1 _) _
      _ = Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v z * Valued.v z := by rw [hd.2.2.1, pow_two]; ac_rfl
      _ < Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v z * 1 :=
          mul_lt_mul_of_pos_left hz.2 (mul_pos (mul_pos hdpos hdpos) hzpos)
      _ = Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v z := mul_one _

theorem v_ratio_sub_ratio_lt {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z w : K} (hz : InA ϖ z) (hw : InA ϖ w) :
    Valued.v (moebius K₀ K g z / z - moebius K₀ K g w / w) < 1 := by
  have : moebius K₀ K g z / z - moebius K₀ K g w / w =
      (moebius K₀ K g z / z - ι (g 0 0) / ι (g 1 1)) - (moebius K₀ K g w / w - ι (g 0 0) / ι (g 1 1)) := by ring
  rw [this]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (v_ratio_sub_lt ϖ hd hz) (v_ratio_sub_lt ϖ hd hw))

theorem v_ratio_eq_one {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z) :
    Valued.v (moebius K₀ K g z / z) = 1 := by
  rw [map_div₀, v_moebius_of_direct ϖ hd hz, div_self (hz.v_ne_zero ϖ)]

theorem disp_sub_disp_eq (g : GL (Fin 2) K₀) {u w : K}
    (hDu : ι (g 1 0) * u + ι (g 1 1) ≠ 0) (hDw : ι (g 1 0) * w + ι (g 1 1) ≠ 0) :
    (moebius K₀ K g u - u) - (moebius K₀ K g w - w) =
      (u - w) * (-(ι (g 1 0) ^ 2 * u * w) - ι (g 1 0) * ι (g 1 1) * (u + w)
        + (ι (g 0 0) - ι (g 1 1)) * ι (g 1 1) - ι (g 0 1) * ι (g 1 0)) /
      ((ι (g 1 0) * u + ι (g 1 1)) * (ι (g 1 0) * w + ι (g 1 1))) := by
  rw [moebius_def, moebius_def, eq_div_iff (mul_ne_zero hDu hDw), div_sub' hDu, div_sub' hDw,
    div_sub_div _ _ hDu hDw, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hDu hDw)]
  ring

theorem v_disp_sub_disp_le {g : GL (Fin 2) K₀} (hd : Direct ϖ g)
    {u w : K} (hu : InA ϖ u) (hw : InA ϖ w) (huw : Valued.v w = Valued.v u) :
    Valued.v ((moebius K₀ K g u - u) - (moebius K₀ K g w - w)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) * Valued.v (u - w) := by
  have hDu := hd.den_ne_zero ϖ hu
  have hDw := hd.den_ne_zero ϖ hw
  rw [disp_sub_disp_eq g hDu hDw, map_div₀, map_mul, map_mul, v_lin_eq_const ϖ hd.2.1 hu,
    v_lin_eq_const ϖ hd.2.1 hw]
  have hdpos : 0 < Valued.v (ι (g 1 1)) := v_algebraMap_pos hd.2.2.2
  have hd2 : 0 < Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) := mul_pos hdpos hdpos
  have hcd : Valued.v (ι (g 1 0)) ≤ Valued.v (ι (g 1 1)) := hd.2.1
  have hu1 : Valued.v u ≤ max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) :=
    le_max_right _ _

  have t1 : Valued.v (-(ι (g 1 0) ^ 2 * u * w)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
    rw [Valuation.map_neg, map_mul, map_mul, map_pow, huw]
    calc Valued.v (ι (g 1 0)) ^ 2 * Valued.v u * Valued.v u ≤ Valued.v (ι (g 1 1)) ^ 2 * Valued.v u * 1 :=
          mul_le_mul' (mul_le_mul_left (pow_le_pow_left₀ zero_le' hcd 2) _) hu.2.le
      _ = Valued.v u * (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by rw [mul_one, pow_two]; ac_rfl
      _ ≤ _ := mul_le_mul_left hu1 _
  have t2 : Valued.v (ι (g 1 0) * ι (g 1 1) * (u + w)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
    rw [map_mul, map_mul]
    have huw' : Valued.v (u + w) ≤ Valued.v u :=
      le_of_le_of_eq (Valuation.map_add _ _ _) (by rw [huw, max_self])
    calc Valued.v (ι (g 1 0)) * Valued.v (ι (g 1 1)) * Valued.v (u + w)
        ≤ Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)) * Valued.v u := mul_le_mul' (mul_le_mul_left hcd _) huw'
      _ = Valued.v u * (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by ac_rfl
      _ ≤ _ := mul_le_mul_left hu1 _
  have t3 : Valued.v ((ι (g 0 0) - ι (g 1 1)) * ι (g 1 1)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
    rw [map_mul]
    calc Valued.v (ι (g 0 0) - ι (g 1 1)) * Valued.v (ι (g 1 1))
        = (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) *
            (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hdpos.ne']
      _ ≤ _ := mul_le_mul_left (le_max_left _ _) _
  have t4 : Valued.v (ι (g 0 1) * ι (g 1 0)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
    rw [map_mul]
    calc Valued.v (ι (g 0 1)) * Valued.v (ι (g 1 0))
        ≤ (Valued.v (ι ϖ.ϖ) * Valued.v (ι (g 0 0))) * Valued.v (ι (g 1 1)) := mul_le_mul' hd.1 hcd
      _ = Valued.v (ι ϖ.ϖ) * (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by rw [hd.2.2.1, mul_assoc]
      _ ≤ Valued.v u * (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := mul_le_mul_left hu.1.le _
      _ ≤ _ := mul_le_mul_left hu1 _
  have hQ : Valued.v (-(ι (g 1 0) ^ 2 * u * w) - ι (g 1 0) * ι (g 1 1) * (u + w)
        + (ι (g 0 0) - ι (g 1 1)) * ι (g 1 1) - ι (g 0 1) * ι (g 1 0)) ≤
      max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ t4)
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ t3)
    exact le_trans (Valuation.map_sub _ _ _) (max_le t1 t2)
  calc Valued.v (u - w) * Valued.v (-(ι (g 1 0) ^ 2 * u * w) - ι (g 1 0) * ι (g 1 1) * (u + w)
          + (ι (g 0 0) - ι (g 1 1)) * ι (g 1 1) - ι (g 0 1) * ι (g 1 0)) /
        (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)))
      ≤ Valued.v (u - w) * (max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) *
          (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1)))) / (Valued.v (ι (g 1 1)) * Valued.v (ι (g 1 1))) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_left (mul_le_mul_right hQ _) _
      _ = max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) * Valued.v (u - w) := by
        rw [← mul_assoc, mul_div_cancel_right₀ _ hd2.ne', mul_comm]

theorem eps_lt_one {g : GL (Fin 2) K₀} (hd : Direct ϖ g)
    (hsmall : Valued.v (ι (g 0 0) - ι (g 1 1)) < Valued.v (ι (g 1 1))) {u : K} (hu : InA ϖ u) :
    max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v u) < 1 :=
  max_lt (div_lt_one_of_lt hsmall) hu.2

end DirectAnalysis

section Tame

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

theorem apply_eq_self_of_iterate_eq_self (F : K → K) (S : Set K) (hS : ∀ u ∈ S, F u ∈ S)
    (ε : Γ₀) (hε : ε < 1)
    (hcontr : ∀ u ∈ S, ∀ w ∈ S, Valued.v ((F u - u) - (F w - w)) ≤ ε * Valued.v (u - w))
    (n : ℕ) (hvn : Valued.v (n : K) = 1) {z : K} (hz : z ∈ S) (hn : F^[n] z = z) : F z = z := by
  have horb : ∀ k, F^[k] z ∈ S := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hn0 : n ≠ 0 := by rintro rfl; simp at hvn
  have hstep : ∀ k, F (F^[k] z) - F^[k] z = F^[k + 1] z - F^[k] z := fun k => by
    rw [Function.iterate_succ_apply']
  have hsum0 : ∑ k ∈ Finset.range n, (F (F^[k] z) - F^[k] z) = 0 := by
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_range_sub (fun k => F^[k] z) n, hn,
      Function.iterate_zero, id_eq, sub_self]
  have hne : (Finset.range n).Nonempty := ⟨0, by simp [Nat.pos_of_ne_zero hn0]⟩
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (Finset.range n) (fun k => Valued.v (F (F^[k] z) - F^[k] z)) hne
  have hpartial : ∀ k ∈ Finset.range n, Valued.v (F^[k] z - z) ≤ Valued.v (F (F^[k₀] z) - F^[k₀] z) := by
    intro k hk
    have : F^[k] z - z = ∑ i ∈ Finset.range k, (F (F^[i] z) - F^[i] z) := by
      rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_range_sub (fun i => F^[i] z) k,
        Function.iterate_zero, id_eq]
    rw [this]
    apply Valuation.map_sum_le
    intro i hi
    apply hmax i
    simp only [Finset.mem_range] at hk hi ⊢
    omega
  have hdiff : ∀ k ∈ Finset.range n,
      Valued.v (F^[k] z - F^[k₀] z) ≤ Valued.v (F (F^[k₀] z) - F^[k₀] z) := fun k hk => by
    have : F^[k] z - F^[k₀] z = (F^[k] z - z) - (F^[k₀] z - z) := by ring
    rw [this]; exact le_trans (Valuation.map_sub _ _ _) (max_le (hpartial k hk) (hpartial k₀ hk₀))
  by_contra hcon
  have hm0 : Valued.v (F (F^[k₀] z) - F^[k₀] z) ≠ 0 := by
    intro hm0
    apply hcon
    have h0 := hmax 0 (by simp [Nat.pos_of_ne_zero hn0])
    rw [hm0, le_zero_iff, Valuation.zero_iff, Function.iterate_zero, id_eq] at h0
    exact sub_eq_zero.mp h0
  have hmpos : 0 < Valued.v (F (F^[k₀] z) - F^[k₀] z) := lt_of_le_of_ne zero_le' hm0.symm
  have hsmallsum : Valued.v (∑ k ∈ Finset.range n,
      ((F (F^[k] z) - F^[k] z) - (F (F^[k₀] z) - F^[k₀] z))) < Valued.v (F (F^[k₀] z) - F^[k₀] z) := by
    apply Valuation.map_sum_lt _ hm0
    intro k hk
    calc Valued.v ((F (F^[k] z) - F^[k] z) - (F (F^[k₀] z) - F^[k₀] z))
        ≤ ε * Valued.v (F^[k] z - F^[k₀] z) := hcontr _ (horb k) _ (horb k₀)
      _ ≤ ε * Valued.v (F (F^[k₀] z) - F^[k₀] z) := mul_le_mul_right (hdiff k hk) _
      _ < 1 * Valued.v (F (F^[k₀] z) - F^[k₀] z) := mul_lt_mul_of_pos_right hε hmpos
      _ = _ := one_mul _
  have htotal : ∑ k ∈ Finset.range n, (F (F^[k] z) - F^[k] z) =
      (n : K) * (F (F^[k₀] z) - F^[k₀] z) +
        ∑ k ∈ Finset.range n, ((F (F^[k] z) - F^[k] z) - (F (F^[k₀] z) - F^[k₀] z)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hv1 : Valued.v ((n : K) * (F (F^[k₀] z) - F^[k₀] z)) = Valued.v (F (F^[k₀] z) - F^[k₀] z) := by
    rw [map_mul, hvn, one_mul]
  have : Valued.v (∑ k ∈ Finset.range n, (F (F^[k] z) - F^[k] z)) = Valued.v (F (F^[k₀] z) - F^[k₀] z) := by
    rw [htotal, Valuation.map_add_eq_of_lt_left _ (by rw [hv1]; exact hsmallsum), hv1]
  rw [hsum0, map_zero] at this
  exact hm0 this.symm

variable (ϖ : PseudoUniformizer K₀ K)

theorem moebius_eq_self_of_tame {g : GL (Fin 2) K₀} (hd : Direct ϖ g)
    (hsmall : Valued.v (ι (g 0 0) - ι (g 1 1)) < Valued.v (ι (g 1 1)))
    (n : ℕ) (hvn : Valued.v (n : K) = 1) {z : K} (hz : InA ϖ z) (hn : (moebius K₀ K g)^[n] z = z) :
    moebius K₀ K g z = z := by
  refine apply_eq_self_of_iterate_eq_self (moebius K₀ K g) {u | InA ϖ u ∧ Valued.v u = Valued.v z}
    (fun u hu => ⟨hd.inA_moebius ϖ hu.1, (v_moebius_of_direct ϖ hd hu.1).trans hu.2⟩)
    (max (Valued.v (ι (g 0 0) - ι (g 1 1)) / Valued.v (ι (g 1 1))) (Valued.v z)) (eps_lt_one ϖ hd hsmall hz)
    (fun u hu w hw => ?_) n hvn ⟨hz, rfl⟩ hn
  have := v_disp_sub_disp_le ϖ hd hu.1 hw.1 (hw.2.trans hu.2.symm)
  rw [hu.2] at this
  exact this

theorem exists_three [IsAlgClosed K] :
    ∃ z₁ z₂ z₃ : K, InA ϖ z₁ ∧ InA ϖ z₂ ∧ InA ϖ z₃ ∧ z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ := by
  obtain ⟨s, hs, -⟩ := exists_basePoint ϖ
  have hs0 := hs.ne_zero ϖ
  have hp0 : (ι ϖ.ϖ) ≠ 0 := fun h => (q_ne_zero ϖ) (by rw [h, map_zero])
  have hp1 : (ι ϖ.ϖ) ≠ 1 := fun h => (q_lt_one ϖ).ne (by rw [h, map_one])
  have hv1 : Valued.v (1 + ι ϖ.ϖ) = 1 := Valuation.map_one_add_of_lt _ (q_lt_one ϖ)
  have hv2 : Valued.v (1 + ι ϖ.ϖ ^ 2) = 1 :=
    Valuation.map_one_add_of_lt _ (by rw [map_pow]; exact pow_lt_one₀ zero_le' (q_lt_one ϖ) two_ne_zero)
  refine ⟨s, s * (1 + ι ϖ.ϖ), s * (1 + ι ϖ.ϖ ^ 2), hs, ?_, ?_, ?_, ?_, ?_⟩
  · show InV ϖ _; rw [map_mul, hv1, mul_one]; exact hs
  · show InV ϖ _; rw [map_mul, hv2, mul_one]; exact hs
  · intro h
    have : s * ι ϖ.ϖ = 0 := by linear_combination -h
    exact hp0 ((mul_eq_zero.mp this).resolve_left hs0)
  · intro h
    have : s * ι ϖ.ϖ ^ 2 = 0 := by linear_combination -h
    exact (pow_ne_zero 2 hp0) ((mul_eq_zero.mp this).resolve_left hs0)
  · intro h
    have : s * (ι ϖ.ϖ * (1 - ι ϖ.ϖ)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs0) with h' | h'
    · exact hp0 h'
    · exact hp1 (sub_eq_zero.mp h').symm

theorem mk_eq_one_of_forall_moebius_eq [IsAlgClosed K] (hunif : IsUnif ϖ) (g : GL (Fin 2) K₀)
    (hfix : ∀ z : K, InA ϖ z → moebius K₀ K g z = z) : Matrix.ProjGenLinGroup.mk g = 1 := by
  obtain ⟨z₁, z₂, z₃, h₁, h₂, h₃, h12, h13, h23⟩ := exists_three ϖ

  have P : ∀ z : K, InA ϖ z → ι (g 1 0) * z ^ 2 + (ι (g 1 1) - ι (g 0 0)) * z - ι (g 0 1) = 0 := by
    intro z hz
    have hD : ι (g 1 0) * z + ι (g 1 1) ≠ 0 := moebius_denom_ne_zero_of_mem K₀ (mem_of_inA ϖ hunif hz).1 g
    have h := hfix z hz
    rw [moebius_def, div_eq_iff hD] at h
    linear_combination -h
  have P1 := P z₁ h₁
  have P2 := P z₂ h₂
  have P3 := P z₃ h₃
  have Q12 : (z₁ - z₂) * (ι (g 1 0) * (z₁ + z₂) + (ι (g 1 1) - ι (g 0 0))) = 0 := by linear_combination P1 - P2
  have Q13 : (z₁ - z₃) * (ι (g 1 0) * (z₁ + z₃) + (ι (g 1 1) - ι (g 0 0))) = 0 := by linear_combination P1 - P3
  have R12 := (mul_eq_zero.mp Q12).resolve_left (sub_ne_zero.mpr h12)
  have R13 := (mul_eq_zero.mp Q13).resolve_left (sub_ne_zero.mpr h13)
  have hc0 : ι (g 1 0) * (z₂ - z₃) = 0 := by linear_combination R12 - R13
  have hc : ι (g 1 0) = 0 := (mul_eq_zero.mp hc0).resolve_right (sub_ne_zero.mpr h23)
  have hda : ι (g 1 1) - ι (g 0 0) = 0 := by rw [hc, zero_mul, zero_add] at R12; exact R12
  have hb : ι (g 0 1) = 0 := by
    have := P1; rw [hc, hda] at this; simpa using this
  have hc' : g 1 0 = 0 := (algebraMap K₀ K).injective (by rw [hc, map_zero])
  have hb' : g 0 1 = 0 := (algebraMap K₀ K).injective (by rw [hb, map_zero])
  have hda' : g 1 1 = g 0 0 := (algebraMap K₀ K).injective (sub_eq_zero.mp hda)
  have ha : g 0 0 ≠ 0 := by
    intro ha
    apply g.det_ne_zero
    rw [Matrix.det_fin_two, ha, hb']; ring
  have hg : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (g 0 0) ha) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, hb', hc', hda']
  rw [hg, Matrix.ProjGenLinGroup.mk_scalar]

end Tame

section Assembly

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

variable (ϖ : PseudoUniformizer K₀ K)

theorem lt_of_div_lt_one {a b : Γ₀} (hb : b ≠ 0) (h : a / b < 1) : a < b := by
  by_contra hab
  have : (1 : Γ₀) ≤ a / b :=
    (le_div_iff₀ (lt_of_le_of_ne zero_le' hb.symm)).2 (by rw [one_mul]; exact not_lt.1 hab)
  exact absurd h (not_lt.2 this)

theorem exists_direct_rep [IsAlgClosed K] (hunif : IsUnif ϖ) (h : PGL(2, K₀))
    (hh : ∀ z : K, z ∈ stdEdgeTube ϖ → pmoebius K₀ h z ∈ stdEdgeTube ϖ)
    (hdirh : ∀ z : K, z ∈ stdEdgeTube ϖ → Valued.v (pmoebius K₀ h z) = Valued.v z) :
    ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = h ∧ Direct ϖ g := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  refine ⟨g, rfl, ?_⟩
  have hg : ∀ z : K, InA ϖ z → InA ϖ (moebius K₀ K g z) := fun z hz => by
    rw [← pmoebius_mk_of_inA ϖ hunif g hz]; exact inA_of_mem ϖ (hh z (mem_of_inA ϖ hunif hz))
  rcases direct_or_swap ϖ hunif g hg with hd | hsw
  · exact hd
  · exfalso
    obtain ⟨s, hs, hss⟩ := exists_basePoint ϖ
    have h1 := v_moebius_mul_of_swap ϖ hsw hs
    have h2 := hdirh s (mem_of_inA ϖ hunif hs)
    rw [pmoebius_mk_of_inA ϖ hunif g hs] at h2
    rw [h2] at h1
    exact hss h1

theorem iterate_moebius_eq (hunif : IsUnif ϖ) {g : GL (Fin 2) K₀} (hd : Direct ϖ g) {z : K} (hz : InA ϖ z)
    (k : ℕ) : (moebius K₀ K g)^[k] z = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g ^ k) z ∧
      InA ϖ ((moebius K₀ K g)^[k] z) := by
  induction k with
  | zero => simp [hz]
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', pmoebius_mul K₀ (mem_of_inA ϖ hunif hz).1, ← ih.1,
      pmoebius_mk_of_inA ϖ hunif g ih.2]
    exact ⟨rfl, hd.inA_moebius ϖ ih.2⟩

theorem mk_eq_one_of_tame [IsAlgClosed K] (hunif : IsUnif ϖ) {g : GL (Fin 2) K₀} (hd : Direct ϖ g)
    (hsmall : Valued.v (ι (g 0 0) - ι (g 1 1)) < Valued.v (ι (g 1 1)))
    (n : ℕ) (hvn : Valued.v (n : K) = 1) (hn : Matrix.ProjGenLinGroup.mk g ^ n = 1) :
    Matrix.ProjGenLinGroup.mk g = 1 := by
  apply mk_eq_one_of_forall_moebius_eq ϖ hunif g
  intro z hz
  apply moebius_eq_self_of_tame ϖ hd hsmall n hvn hz
  rw [(iterate_moebius_eq ϖ hunif hd hz n).1, hn, pmoebius_one]

abbrev intRing (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] :
    ValuationSubring K := (Valued.v : Valuation K Γ₀).valuationSubring

theorem mem_intRing_iff (x : K) : x ∈ intRing K ↔ Valued.v x ≤ 1 := Valuation.mem_valuationSubring_iff _ _

theorem mem_maximalIdeal_intRing_iff (x : ↥(intRing K)) :
    x ∈ IsLocalRing.maximalIdeal ↥(intRing K) ↔ Valued.v (x : K) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one).symm

theorem residue_eq_residue_iff (x y : ↥(intRing K)) :
    IsLocalRing.residue ↥(intRing K) x = IsLocalRing.residue ↥(intRing K) y ↔ Valued.v ((x : K) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_intRing_iff]
  rfl

theorem moebiusK_injective {α β γ δ : K} (hdet : α * δ - β * γ ≠ 0) {y z : K} (hy : γ * y + δ ≠ 0)
    (hz : γ * z + δ ≠ 0) (h : (α * y + β) / (γ * y + δ) = (α * z + β) / (γ * z + δ)) : y = z := by
  rw [div_eq_div_iff hy hz] at h
  have : (α * δ - β * γ) * (y - z) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hdet)

end Assembly

section Coordinate

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

namespace Coord
private theorem _root_.TubeStab.Coord.v_sub_eq_of_lt {x y : K} (h : Valued.v y < Valued.v x) : Valued.v (x - y) = Valued.v x := by
  rw [sub_eq_add_neg]; apply Valuation.map_add_eq_of_lt_left; rwa [Valuation.map_neg]

end Coord
p2m_export "TubeStab" "Coord.v_sub_eq_of_lt"
theorem Coord.v_add_eq_of_lt {x y : K} (h : Valued.v y < Valued.v x) : Valued.v (x + y) = Valued.v x :=
  Valuation.map_add_eq_of_lt_left _ h

theorem Coord.fix_identity {a b c d ξ : K} (h : c * ξ ^ 2 + (d - a) * ξ - b = 0) (z : K) :
    (a * z + b) - ξ * (c * z + d) = (a - c * ξ) * (z - ξ) := by
  linear_combination (-1 : K) * h

variable (ϖ : PseudoUniformizer K₀ K)

theorem Coord.core [IsAlgClosed K] {a b c d : K} (hcne : c ≠ 0) (hdne : d ≠ 0)
    (hb : Valued.v b ≤ Valued.v (ι ϖ.ϖ) * Valued.v d) (hc : Valued.v c ≤ Valued.v d)
    (hsep : Valued.v (a - d) = Valued.v d)
    (hden : ∀ z : K, InA ϖ z → c * z + d ≠ 0)
    (ξ₁ ξ₂ : K) (h₁ : c * ξ₁ ^ 2 + (d - a) * ξ₁ - b = 0) (h₂ : c * ξ₂ ^ 2 + (d - a) * ξ₂ - b = 0)
    (hsum : ξ₁ + ξ₂ = (a - d) / c) (hprod : ξ₁ * ξ₂ = -b / c) (hle : Valued.v ξ₁ ≤ Valued.v ξ₂) :
    ∃ μ α β γ δ : K, α * δ - β * γ ≠ 0 ∧
      (∀ z : K, InA ϖ z → γ * z + δ ≠ 0 ∧ Valued.v ((α * z + β) / (γ * z + δ)) = Valued.v z) ∧
      (∀ w : K, InA ϖ w → ∃ z : K, InA ϖ z ∧ (α * z + β) / (γ * z + δ) = w) ∧
      (∀ z : K, InA ϖ z →
        (α * ((a * z + b) / (c * z + d)) + β) / (γ * ((a * z + b) / (c * z + d)) + δ) = μ * ((α * z + β) / (γ * z + δ))) := by
  have hq0 := q_pos ϖ
  have hq1 := q_lt_one ϖ
  have hvc : 0 < Valued.v c := (Valuation.pos_iff _).mpr hcne
  have hvd : 0 < Valued.v d := (Valuation.pos_iff _).mpr hdne
  set L : Γ₀ := Valued.v d / Valued.v c with hL
  have hL1 : 1 ≤ L := by rw [hL, le_div_iff₀ hvc, one_mul]; exact hc
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hvsum : Valued.v (ξ₁ + ξ₂) = L := by rw [hsum, map_div₀, hsep]
  have hvprod : Valued.v (ξ₁ * ξ₂) ≤ Valued.v (ι ϖ.ϖ) * L := by
    rw [hprod, map_div₀, Valuation.map_neg, hL, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hb zero_le'

  have hξ₂L : Valued.v ξ₂ = L := by
    refine le_antisymm ?_ ?_
    · by_contra hgt
      rw [not_le] at hgt
      have heq : Valued.v ξ₁ = Valued.v ξ₂ := by
        rcases hle.lt_or_eq with hlt | heq
        · exfalso
          have : Valued.v (ξ₁ + ξ₂) = Valued.v ξ₂ := by rw [add_comm]; exact Coord.v_add_eq_of_lt hlt
          rw [hvsum] at this; exact hgt.ne this
        · exact heq
      have h1 : L * L < Valued.v ξ₂ * Valued.v ξ₂ := mul_lt_mul'' hgt hgt zero_le' zero_le'
      have h2 : Valued.v (ι ϖ.ϖ) * L < L * L :=
        calc Valued.v (ι ϖ.ϖ) * L < 1 * L := mul_lt_mul_of_pos_right hq1 hL0
          _ ≤ L * L := mul_le_mul' hL1 le_rfl
      have : Valued.v (ξ₁ * ξ₂) = Valued.v ξ₂ * Valued.v ξ₂ := by rw [map_mul, heq]
      exact absurd hvprod (not_le.mpr (by rw [this]; exact h2.trans h1))
    · rw [← hvsum]
      exact (Valuation.map_add _ _ _).trans (max_le hle le_rfl)
  have hξ₁q : Valued.v ξ₁ ≤ Valued.v (ι ϖ.ϖ) := by
    have h : Valued.v ξ₁ * L ≤ Valued.v (ι ϖ.ϖ) * L := by
      have := hvprod; rw [map_mul, hξ₂L] at this; exact this
    calc Valued.v ξ₁ = Valued.v ξ₁ * L / L := by rw [mul_div_cancel_right₀ _ hL0.ne']
      _ ≤ Valued.v (ι ϖ.ϖ) * L / L := div_le_div_of_nonneg_right h zero_le'
      _ = Valued.v (ι ϖ.ϖ) := mul_div_cancel_right₀ _ hL0.ne'
  have hξ₂0 : ξ₂ ≠ 0 := (Valuation.pos_iff _).mp (by rw [hξ₂L]; exact hL0)
  have hξ₁₂ : ξ₁ ≠ ξ₂ := fun h => by
    have : Valued.v ξ₁ < Valued.v ξ₂ := (hξ₁q.trans_lt hq1).trans_le (by rw [hξ₂L]; exact hL1)
    rw [h] at this; exact lt_irrefl _ this
  have hacξ₂ : a - c * ξ₂ ≠ 0 := by
    intro h
    have hb' : d * ξ₂ - b = 0 := by linear_combination h₂ + ξ₂ * h
    have : Valued.v ξ₂ ≤ Valued.v (ι ϖ.ϖ) := by
      have : ξ₂ = b / d := by field_simp; linear_combination hb'
      rw [this, map_div₀, div_le_iff₀ hvd]; exact hb
    exact absurd (hL1.trans_eq hξ₂L.symm) (not_le.mpr (this.trans_lt hq1))

  have hzξ₁ : ∀ z : K, InA ϖ z → Valued.v (z - ξ₁) = Valued.v z := fun z hz =>
    Coord.v_sub_eq_of_lt (hξ₁q.trans_lt hz.1)
  have hzξ₂ : ∀ z : K, InA ϖ z → Valued.v (z - ξ₂) = Valued.v ξ₂ := fun z hz => by
    rw [Valuation.map_sub_swap]; exact Coord.v_sub_eq_of_lt (hz.2.trans_le (by rw [hξ₂L]; exact hL1))
  have hzne : ∀ z : K, InA ϖ z → z - ξ₂ ≠ 0 := fun z hz =>
    (Valuation.ne_zero_iff _).mp (by rw [hzξ₂ z hz, hξ₂L]; exact hL0.ne')
  refine ⟨(a - c * ξ₁) / (a - c * ξ₂), -ξ₂, ξ₁ * ξ₂, 1, -ξ₂, ?_, ?_, ?_, ?_⟩
  · rw [show -ξ₂ * -ξ₂ - ξ₁ * ξ₂ * 1 = ξ₂ * (ξ₂ - ξ₁) by ring]
    exact mul_ne_zero hξ₂0 (sub_ne_zero.mpr (Ne.symm hξ₁₂))
  · intro z hz
    have e1 : -ξ₂ * z + ξ₁ * ξ₂ = -ξ₂ * (z - ξ₁) := by ring
    have e2 : 1 * z + -ξ₂ = z - ξ₂ := by ring
    refine ⟨by rw [e2]; exact hzne z hz, ?_⟩
    rw [e1, e2, map_div₀, map_mul, Valuation.map_neg, hzξ₁ z hz, hzξ₂ z hz, mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).mpr hξ₂0)]
  · intro w hw
    have hwξ₂ : w + ξ₂ ≠ 0 := by
      intro h
      have : Valued.v w = Valued.v ξ₂ := by rw [show w = -ξ₂ by linear_combination h, Valuation.map_neg]
      exact absurd hw.2 (not_lt.mpr (by rw [this, hξ₂L]; exact hL1))
    refine ⟨ξ₂ * (w + ξ₁) / (w + ξ₂), ?_, ?_⟩
    · show InV ϖ (Valued.v (ξ₂ * (w + ξ₁) / (w + ξ₂)))
      have hv : Valued.v (ξ₂ * (w + ξ₁) / (w + ξ₂)) = Valued.v w := by
        rw [map_div₀, map_mul, Coord.v_add_eq_of_lt (hξ₁q.trans_lt hw.1),
          show w + ξ₂ = ξ₂ + w by ring, Coord.v_add_eq_of_lt (hw.2.trans_le (by rw [hξ₂L]; exact hL1)),
          mul_comm, mul_div_cancel_right₀ _ ((Valuation.ne_zero_iff _).mpr hξ₂0)]
      rw [hv]; exact hw
    · have hsub : ξ₁ - ξ₂ ≠ 0 := sub_ne_zero.mpr hξ₁₂
      have hsub' : -ξ₂ + ξ₁ ≠ 0 := by rw [neg_add_eq_sub]; exact hsub
      have hsub'' : ξ₂ - ξ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ₁₂)
      rw [div_eq_iff (by
        intro h0
        have : (1 : K) * (ξ₂ * (w + ξ₁) / (w + ξ₂)) + -ξ₂ = ξ₂ * (ξ₁ - ξ₂) / (w + ξ₂) := by field_simp; ring
        rw [this] at h0
        exact (div_ne_zero (mul_ne_zero hξ₂0 hsub) hwξ₂) h0)]
      field_simp
      ring
  · intro z hz
    have hD := hden z hz
    have hg1 : (a * z + b) / (c * z + d) - ξ₁ = (a - c * ξ₁) * (z - ξ₁) / (c * z + d) := by
      rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]; exact Coord.fix_identity h₁ z
    have hg2 : (a * z + b) / (c * z + d) - ξ₂ = (a - c * ξ₂) * (z - ξ₂) / (c * z + d) := by
      rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]; exact Coord.fix_identity h₂ z
    have e1 : ∀ u : K, -ξ₂ * u + ξ₁ * ξ₂ = -ξ₂ * (u - ξ₁) := fun u => by ring
    have e2 : ∀ u : K, 1 * u + -ξ₂ = u - ξ₂ := fun u => by ring
    rw [e1, e2, e1, e2, hg1, hg2]
    have hzξ := hzne z hz
    have hzξ₁ : z - ξ₁ ≠ 0 := fun h => by
      have := hzξ₁ z hz; rw [h, map_zero] at this; exact (InA.v_ne_zero ϖ hz) this.symm
    rw [mul_div_assoc, div_div_div_cancel_right₀ hD, mul_div_mul_comm, mul_div_assoc]
    ring

theorem exists_coordinate_of_direct [IsAlgClosed K] (hunif : IsUnif ϖ) {g : GL (Fin 2) K₀} (hd : Direct ϖ g)
    (hsep : Valued.v (ι (g 0 0) - ι (g 1 1)) = Valued.v (ι (g 1 1))) :
    ∃ μ α β γ δ : K, α * δ - β * γ ≠ 0 ∧
      (∀ z : K, InA ϖ z → γ * z + δ ≠ 0 ∧ Valued.v ((α * z + β) / (γ * z + δ)) = Valued.v z) ∧
      (∀ w : K, InA ϖ w → ∃ z : K, InA ϖ z ∧ (α * z + β) / (γ * z + δ) = w) ∧
      (∀ z : K, InA ϖ z → (α * moebius K₀ K g z + β) / (γ * moebius K₀ K g z + δ) = μ * ((α * z + β) / (γ * z + δ))) := by
  have hden : ∀ z : K, InA ϖ z → ι (g 1 0) * z + ι (g 1 1) ≠ 0 := fun z hz => Direct.den_ne_zero ϖ hd hz
  obtain ⟨hb, hc, had, hd0⟩ := hd
  set a : K := ι (g 0 0) with ha
  set b : K := ι (g 0 1) with hbK
  set c : K := ι (g 1 0) with hcK
  set d : K := ι (g 1 1) with hdK
  have hq0 := q_pos ϖ
  have hq1 := q_lt_one ϖ
  have hvd0 : Valued.v d ≠ 0 := v_algebraMap_ne_zero hd0
  have hvdpos : 0 < Valued.v d := lt_of_le_of_ne zero_le' hvd0.symm
  have hdne : d ≠ 0 := (Valuation.ne_zero_iff _).mp hvd0
  have hb' : Valued.v b ≤ Valued.v (ι ϖ.ϖ) * Valued.v d := by rw [← had]; exact hb
  have hgz : ∀ z : K, moebius K₀ K g z = (a * z + b) / (c * z + d) := fun z => moebius_def g z
  by_cases hc0 : g 1 0 = 0
  ·
    have hcz : c = 0 := by rw [hcK, hc0, map_zero]
    have hda : d - a ≠ 0 := by
      intro h
      have : Valued.v (a - d) = 0 := by rw [show a - d = -(d - a) by ring, h, neg_zero, map_zero]
      rw [this] at hsep; exact hvd0 hsep.symm
    set ξ₁ : K := b / (d - a) with hξ₁
    have hvξ₁ : Valued.v ξ₁ ≤ Valued.v (ι ϖ.ϖ) := by
      rw [hξ₁, map_div₀, show d - a = -(a - d) by ring, Valuation.map_neg, hsep, div_le_iff₀ hvdpos]
      exact hb'
    refine ⟨a / d, 1, -ξ₁, 0, 1, by norm_num, ?_, ?_, ?_⟩
    · intro z hz
      refine ⟨by norm_num, ?_⟩
      rw [zero_mul, zero_add, div_one, one_mul, ← sub_eq_add_neg, Coord.v_sub_eq_of_lt (hvξ₁.trans_lt hz.1)]
    · intro w hw
      refine ⟨w + ξ₁, ?_, by ring⟩
      show InV ϖ (Valued.v (w + ξ₁))
      rw [Coord.v_add_eq_of_lt (hvξ₁.trans_lt hw.1)]; exact hw
    · intro z hz
      rw [hgz, hcz, zero_mul, zero_add]
      simp only [zero_mul, zero_add, div_one, one_mul]
      rw [hξ₁]
      field_simp
      ring
  ·
    have hvc0 : Valued.v c ≠ 0 := v_algebraMap_ne_zero hc0
    have hcne : c ≠ 0 := (Valuation.ne_zero_iff _).mp hvc0
    obtain ⟨ξ, hξ⟩ : ∃ ξ : K, c * ξ ^ 2 + (d - a) * ξ - b = 0 := by
      have hdeg : (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C (d - a) * Polynomial.X + Polynomial.C (-b) :
          Polynomial K).degree ≠ 0 := by
        rw [Polynomial.degree_quadratic hcne]; decide
      obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root _ hdeg
      refine ⟨ξ, ?_⟩
      have := hξ
      rw [Polynomial.IsRoot] at this
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at this
      linear_combination this
    set s : K := (a - d) / c with hs
    have hcs : c * s = a - d := by rw [hs, ← mul_div_assoc, mul_div_cancel_left₀ _ hcne]
    set ξ' : K := s - ξ with hξ'
    have hξ'root : c * ξ' ^ 2 + (d - a) * ξ' - b = 0 := by
      rw [hξ']; linear_combination hξ + (s - 2 * ξ) * hcs
    have hsum : ξ + ξ' = (a - d) / c := by rw [hξ', ← hs]; ring
    have hsum' : ξ' + ξ = (a - d) / c := by rw [add_comm]; exact hsum
    have hprod : ξ * ξ' = -b / c := by
      rw [eq_div_iff hcne, hξ']; linear_combination (-1 : K) * hξ + ξ * hcs
    have hprod' : ξ' * ξ = -b / c := by rw [mul_comm]; exact hprod
    simp only [hgz]
    rcases le_total (Valued.v ξ) (Valued.v ξ') with hle | hle
    · exact Coord.core ϖ hcne hdne hb' hc hsep hden ξ ξ' hξ hξ'root hsum hprod hle
    · exact Coord.core ϖ hcne hdne hb' hc hsep hden ξ' ξ hξ'root hξ hsum' hprod' hle

end Coordinate

theorem exists_rotation_coordinate
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (H : Subgroup PGL(2, K₀)) [Finite H]
    (hH : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → pmoebius K₀ h z ∈ stdEdgeTube ϖ)
    (hdir : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → Valued.v (pmoebius K₀ h z) = Valued.v z)
    (htame : Valued.v ((Nat.card H : ℕ) : K) = 1) :
    ∃ (h₀ : PGL(2, K₀)) (μ α β γ δ : K),
      h₀ ∈ H ∧ (∀ h ∈ H, ∃ j : ℕ, h = h₀ ^ j) ∧ IsPrimitiveRoot μ (Nat.card H) ∧ α * δ - β * γ ≠ 0 ∧
      (∀ z : K, z ∈ stdEdgeTube ϖ → γ * z + δ ≠ 0 ∧ Valued.v ((α * z + β) / (γ * z + δ)) = Valued.v z) ∧
      (∀ w : K, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v w → Valued.v w < 1 →
          ∃ z : K, z ∈ stdEdgeTube ϖ ∧ (α * z + β) / (γ * z + δ) = w) ∧
      (∀ z : K, z ∈ stdEdgeTube ϖ →
          (α * pmoebius K₀ h₀ z + β) / (γ * pmoebius K₀ h₀ z + δ) = μ * ((α * z + β) / (γ * z + δ))) := by
  have hunif' : IsUnif ϖ := hunif
  obtain ⟨s, hs, -⟩ := exists_basePoint ϖ
  have hsT : s ∈ stdEdgeTube ϖ := mem_of_inA ϖ hunif' hs
  have hsΩ := hsT.1
  have hs0 := hs.ne_zero ϖ
  have hn0 : 0 < Nat.card H := Nat.card_pos
  have hpow : ∀ h ∈ H, h ^ Nat.card H = 1 := fun h hh => by
    have := congrArg Subtype.val (pow_card_eq_one' (G := ↥H) (x := ⟨h, hh⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    exact this

  have tame : ∀ h ∈ H, ∀ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = h → Direct ϖ g →
      Valued.v (algebraMap K₀ K (g 0 0) - algebraMap K₀ K (g 1 1)) < Valued.v (algebraMap K₀ K (g 1 1)) →
      h = 1 := by
    intro h hh g hg hd hsmall
    rw [← hg]
    exact mk_eq_one_of_tame ϖ hunif' hd hsmall (Nat.card H) htame (by rw [hg]; exact hpow h hh)

  have hratio_mem : ∀ h ∈ H, pmoebius K₀ h s / s ∈ intRing K := fun h hh => by
    rw [mem_intRing_iff, map_div₀, hdir h hh s hsT, div_self (hs.v_ne_zero ϖ)]
  set χf : ↥H → IsLocalRing.ResidueField ↥(intRing K) :=
    fun h => IsLocalRing.residue _ ⟨pmoebius K₀ (h : PGL(2, K₀)) s / s, hratio_mem h h.2⟩ with hχf
  have hχmul : ∀ a b : ↥H, χf (a * b) = χf a * χf b := by
    intro a b
    simp only [hχf]
    rw [← map_mul, residue_eq_residue_iff]
    obtain ⟨g, hg, hd⟩ := exists_direct_rep ϖ hunif' (a : PGL(2, K₀)) (hH _ a.2) (hdir _ a.2)
    have hbs : InA ϖ (pmoebius K₀ (b : PGL(2, K₀)) s) := inA_of_mem ϖ (hH _ b.2 s hsT)
    have hb0 := hbs.ne_zero ϖ
    have e : pmoebius K₀ ((a * b : ↥H) : PGL(2, K₀)) s / s -
        (pmoebius K₀ (a : PGL(2, K₀)) s / s) * (pmoebius K₀ (b : PGL(2, K₀)) s / s) =
        (pmoebius K₀ (b : PGL(2, K₀)) s / s) *
          (moebius K₀ K g (pmoebius K₀ (b : PGL(2, K₀)) s) / pmoebius K₀ (b : PGL(2, K₀)) s -
            moebius K₀ K g s / s) := by
      rw [Subgroup.coe_mul, pmoebius_mul K₀ hsΩ, ← hg, pmoebius_mk_of_inA ϖ hunif' g hbs,
        pmoebius_mk_of_inA ϖ hunif' g hs]
      field_simp
    show Valued.v (pmoebius K₀ ((a * b : ↥H) : PGL(2, K₀)) s / s -
        (pmoebius K₀ (a : PGL(2, K₀)) s / s) * (pmoebius K₀ (b : PGL(2, K₀)) s / s)) < 1
    rw [e, map_mul, map_div₀, hdir _ b.2 s hsT, div_self (hs.v_ne_zero ϖ), one_mul]
    exact v_ratio_sub_ratio_lt ϖ hd hbs hs
  set χ : ↥H →* IsLocalRing.ResidueField ↥(intRing K) :=
    { toFun := χf
      map_one' := by
        simp only [hχf]
        rw [← map_one (IsLocalRing.residue ↥(intRing K))]
        congr 1
        apply Subtype.ext
        show pmoebius K₀ ((1 : ↥H) : PGL(2, K₀)) s / s = 1
        rw [OneMemClass.coe_one, pmoebius_one, div_self hs0]
      map_mul' := hχmul } with hχ
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    change χf a = 1 at ha
    simp only [hχf] at ha
    rw [← map_one (IsLocalRing.residue ↥(intRing K)), residue_eq_residue_iff] at ha
    change Valued.v (pmoebius K₀ (a : PGL(2, K₀)) s / s - 1) < 1 at ha
    obtain ⟨g, hg, hd⟩ := exists_direct_rep ϖ hunif' (a : PGL(2, K₀)) (hH _ a.2) (hdir _ a.2)
    have hd0 : algebraMap K₀ K (g 1 1) ≠ 0 := fun h =>
      hd.2.2.2 ((algebraMap K₀ K).injective (by rw [h, map_zero]))
    have h1 := v_ratio_sub_lt ϖ hd hs
    rw [← pmoebius_mk_of_inA ϖ hunif' g hs, hg] at h1
    have h2 : Valued.v (algebraMap K₀ K (g 0 0) / algebraMap K₀ K (g 1 1) - 1) < 1 := by
      have : algebraMap K₀ K (g 0 0) / algebraMap K₀ K (g 1 1) - 1 =
          (pmoebius K₀ (a : PGL(2, K₀)) s / s - 1) -
            (pmoebius K₀ (a : PGL(2, K₀)) s / s - algebraMap K₀ K (g 0 0) / algebraMap K₀ K (g 1 1)) := by ring
      rw [this]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha h1)
    rw [div_sub_one hd0, map_div₀] at h2
    have hsmall := lt_of_div_lt_one (v_algebraMap_ne_zero hd.2.2.2) h2
    exact Subtype.ext (tame _ a.2 g hg hd hsmall)
  haveI : IsCyclic ↥H := isCyclic_of_injective_ringHom χ hinj
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := ↥H)
  have horder : orderOf g₀ = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hgen : ∀ h ∈ H, ∃ j : ℕ, h = (g₀ : PGL(2, K₀)) ^ j := by
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨h, hh⟩)
    refine ⟨(k % (orderOf g₀ : ℤ)).toNat, ?_⟩
    have hk' : g₀ ^ ((k % (orderOf g₀ : ℤ)).toNat : ℤ) = ⟨h, hh⟩ := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos g₀).ne')),
        zpow_mod_orderOf, hk]
    rw [zpow_natCast] at hk'
    have := congrArg Subtype.val hk'
    rw [Subgroup.coe_pow] at this
    exact this.symm
  by_cases h1 : Nat.card H = 1
  ·
    have hg1 : g₀ = 1 := orderOf_eq_one_iff.mp (horder.trans h1)
    refine ⟨(g₀ : PGL(2, K₀)), 1, 1, 0, 0, 1, g₀.2, hgen, ?_, by norm_num, ?_, ?_, ?_⟩
    · rw [h1]; exact IsPrimitiveRoot.one
    · intro z _; constructor <;> simp
    · intro w hw1 hw2; exact ⟨w, mem_of_inA ϖ hunif' ⟨hw1, hw2⟩, by simp⟩
    · intro z _; rw [hg1, OneMemClass.coe_one, pmoebius_one]; simp
  ·
    have hn2 : g₀ ≠ 1 := fun h => h1 (by rw [← horder, h, orderOf_one])
    obtain ⟨g, hg, hd⟩ := exists_direct_rep ϖ hunif' (g₀ : PGL(2, K₀)) (hH _ g₀.2) (hdir _ g₀.2)
    have hsep : Valued.v (algebraMap K₀ K (g 0 0) - algebraMap K₀ K (g 1 1)) =
        Valued.v (algebraMap K₀ K (g 1 1)) := by
      by_contra hne
      have hle : Valued.v (algebraMap K₀ K (g 0 0) - algebraMap K₀ K (g 1 1)) ≤
          Valued.v (algebraMap K₀ K (g 1 1)) :=
        le_trans (Valuation.map_sub _ _ _) (by rw [hd.2.2.1, max_self])
      exact hn2 (Subtype.ext (tame _ g₀.2 g hg hd (lt_of_le_of_ne hle hne)))
    obtain ⟨μ, α, β, γ, δ, hdet, hval, honto, hconj⟩ := exists_coordinate_of_direct ϖ hunif' hd hsep
    have hval' : ∀ z : K, z ∈ stdEdgeTube ϖ → γ * z + δ ≠ 0 ∧ Valued.v ((α * z + β) / (γ * z + δ)) = Valued.v z :=
      fun z hz => hval z (inA_of_mem ϖ hz)
    have hconj' : ∀ z : K, z ∈ stdEdgeTube ϖ →
        (α * pmoebius K₀ (g₀ : PGL(2, K₀)) z + β) / (γ * pmoebius K₀ (g₀ : PGL(2, K₀)) z + δ) =
          μ * ((α * z + β) / (γ * z + δ)) := by
      intro z hz
      rw [← hg, pmoebius_mk_of_inA ϖ hunif' g (inA_of_mem ϖ hz)]
      exact hconj z (inA_of_mem ϖ hz)
    have hiter : ∀ k : ℕ, ∀ z : K, z ∈ stdEdgeTube ϖ →
        (α * pmoebius K₀ ((g₀ : PGL(2, K₀)) ^ k) z + β) / (γ * pmoebius K₀ ((g₀ : PGL(2, K₀)) ^ k) z + δ) =
          μ ^ k * ((α * z + β) / (γ * z + δ)) := by
      intro k
      induction k with
      | zero => intro z _; simp
      | succ k ih =>
        intro z hz
        have hkz : pmoebius K₀ ((g₀ : PGL(2, K₀)) ^ k) z ∈ stdEdgeTube ϖ := hH _ (pow_mem g₀.2 k) z hz
        rw [pow_succ', pmoebius_mul K₀ hz.1, hconj' _ hkz, ih z hz, ← mul_assoc, ← pow_succ']
    refine ⟨(g₀ : PGL(2, K₀)), μ, α, β, γ, δ, g₀.2, hgen, ?_, hdet, hval', ?_, hconj'⟩
    · have hφs0 : (α * s + β) / (γ * s + δ) ≠ 0 := fun h0 => by
        have := (hval' s hsT).2
        rw [h0, map_zero] at this
        exact hs.v_ne_zero ϖ this.symm
      refine IsPrimitiveRoot.mk_of_lt μ hn0 ?_ ?_
      · have := hiter (Nat.card H) s hsT
        rw [hpow _ g₀.2, pmoebius_one] at this
        exact mul_right_cancel₀ hφs0 (by rw [one_mul]; exact this.symm)
      · intro l hl0 hln hμl
        have hfix : ∀ z : K, InA ϖ z → moebius K₀ K (g ^ l) z = z := by
          intro z hz
          have hzT := mem_of_inA ϖ hunif' hz
          have h := hiter l z hzT
          rw [hμl, one_mul] at h
          have hlz : pmoebius K₀ ((g₀ : PGL(2, K₀)) ^ l) z ∈ stdEdgeTube ϖ := hH _ (pow_mem g₀.2 l) z hzT
          have := moebiusK_injective hdet (hval' _ hlz).1 (hval' z hzT).1 h
          rw [← pmoebius_mk_of_inA ϖ hunif' (g ^ l) hz, map_pow, hg]
          exact this
        have h1 : (g₀ : PGL(2, K₀)) ^ l = 1 := by
          rw [← hg, ← map_pow]; exact mk_eq_one_of_forall_moebius_eq ϖ hunif' (g ^ l) hfix
        have : orderOf (g₀ : PGL(2, K₀)) ∣ l := orderOf_dvd_of_pow_eq_one h1
        rw [Subgroup.orderOf_coe, horder] at this
        exact absurd (Nat.le_of_dvd hl0 this) (not_le.2 hln)
    · intro w hw1 hw2
      obtain ⟨z, hz, hzw⟩ := honto w ⟨hw1, hw2⟩
      exact ⟨z, mem_of_inA ϖ hunif' hz, hzw⟩

end TubeStab

open Polynomial Finset

namespace TubeStab

variable {K : Type} [Field K]

noncomputable def rotProd (μ : K) (n : ℕ) (Q : K[X]) : K[X] := ∏ j ∈ Finset.range n, Q.comp (C (μ ^ j) * X)

noncomputable def rotSum (μ : K) (n : ℕ) (P Q : K[X]) : K[X] :=
  ∑ j ∈ Finset.range n, P.comp (C (μ ^ j) * X) * ∏ i ∈ (Finset.range n).erase j, Q.comp (C (μ ^ i) * X)

theorem comp_CX_ne_zero {a : K} (ha : a ≠ 0) {Q : K[X]} (hQ : Q ≠ 0) : Q.comp (C a * X) ≠ 0 := by
  rw [ne_eq, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero ha)]; exact hQ

theorem eval_comp_CX (a : K) (P : K[X]) (w : K) : (P.comp (C a * X)).eval w = P.eval (a * w) := by
  simp [eval_comp]

theorem comp_CX_comp_CX (a b : K) (P : K[X]) : (P.comp (C b * X)).comp (C a * X) = P.comp (C (b * a) * X) := by
  ext k; simp only [comp_C_mul_X_coeff, mul_pow, mul_assoc]

theorem prod_range_shift {M : Type} [CommMonoid M] (n : ℕ) (hn : 0 < n) (g : ℕ → M)
    (hg : ∀ j, g (j + n) = g j) : ∏ j ∈ range n, g (j + 1) = ∏ j ∈ range n, g j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prod_range_succ, prod_range_succ', show m + 1 = 0 + (m + 1) by ring, hg 0]

theorem sum_range_shift {M : Type} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (g : ℕ → M)
    (hg : ∀ j, g (j + n) = g j) : ∑ j ∈ range n, g (j + 1) = ∑ j ∈ range n, g j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ, sum_range_succ', show m + 1 = 0 + (m + 1) by ring, hg 0]

theorem pow_mod_of_pow_eq_one {μ : K} {n : ℕ} (hμ : μ ^ n = 1) (a : ℕ) : μ ^ (a % n) = μ ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, hμ, one_pow, mul_one]

theorem rotProd_ne_zero {μ : K} (hμ0 : μ ≠ 0) (n : ℕ) {Q : K[X]} (hQ : Q ≠ 0) : rotProd μ n Q ≠ 0 := by
  unfold rotProd
  exact prod_ne_zero_iff.2 fun j _ => comp_CX_ne_zero (pow_ne_zero _ hμ0) hQ

theorem eval_rotProd (μ : K) (n : ℕ) (Q : K[X]) (w : K) :
    (rotProd μ n Q).eval w = ∏ j ∈ Finset.range n, Q.eval (μ ^ j * w) := by
  unfold rotProd; rw [eval_prod]; simp only [eval_comp_CX]

theorem rotProd_eq_mul_erase (μ : K) (n : ℕ) (Q : K[X]) {j : ℕ} (hj : j ∈ range n) :
    rotProd μ n Q = Q.comp (C (μ ^ j) * X) * ∏ i ∈ (range n).erase j, Q.comp (C (μ ^ i) * X) := by
  unfold rotProd; exact (mul_prod_erase (range n) (fun i => Q.comp (C (μ ^ i) * X)) hj).symm

theorem eval_rotSum_div (μ : K) (n : ℕ) (P Q : K[X]) (w : K)
    (hQ : ∀ j ∈ Finset.range n, Q.eval (μ ^ j * w) ≠ 0) :
    (rotSum μ n P Q).eval w / (rotProd μ n Q).eval w =
      ∑ j ∈ Finset.range n, P.eval (μ ^ j * w) / Q.eval (μ ^ j * w) := by
  have hq0 : (rotProd μ n Q).eval w ≠ 0 := by rw [eval_rotProd]; exact prod_ne_zero_iff.2 hQ
  rw [div_eq_iff hq0, sum_mul]
  unfold rotSum
  rw [eval_finsetSum]
  refine sum_congr rfl fun j hj => ?_
  rw [rotProd_eq_mul_erase μ n Q hj, eval_mul, eval_mul, eval_prod, eval_comp_CX, eval_comp_CX]
  field_simp [hQ j hj]

theorem rotProd_comp (μ : K) {n : ℕ} (hn : 0 < n) (hμ : μ ^ n = 1) (Q : K[X]) :
    (rotProd μ n Q).comp (C μ * X) = rotProd μ n Q := by
  unfold rotProd
  rw [Polynomial.prod_comp]
  simp_rw [comp_CX_comp_CX, ← pow_succ]
  exact prod_range_shift n hn (fun j => Q.comp (C (μ ^ j) * X)) fun j => by
    show Q.comp (C (μ ^ (j + n)) * X) = Q.comp (C (μ ^ j) * X)
    rw [pow_add, hμ, mul_one]

theorem rotSum_comp (μ : K) {n : ℕ} (hn : 0 < n) (hμ : μ ^ n = 1) (hμ0 : μ ≠ 0) (P Q : K[X]) (hQ : Q ≠ 0) :
    (rotSum μ n P Q).comp (C μ * X) = rotSum μ n P Q := by
  classical

  set A : ℕ → K[X] := fun j => P.comp (C (μ ^ j) * X) with hA
  set B : ℕ → K[X] := fun j => Q.comp (C (μ ^ j) * X) with hB
  set E : ℕ → K[X] := fun j => ∏ i ∈ (range n).erase j, B i with hE
  have hAper : ∀ j, A (j % n) = A j := fun j => by simp only [hA, pow_mod_of_pow_eq_one hμ]
  have hBper : ∀ j, B (j % n) = B j := fun j => by simp only [hB, pow_mod_of_pow_eq_one hμ]
  have hBper' : ∀ j, B (j + n) = B j := fun j => by simp only [hB, pow_add, hμ, mul_one]
  have hB0 : ∀ j, B j ≠ 0 := fun j => comp_CX_ne_zero (pow_ne_zero _ hμ0) hQ
  have hBE : ∀ j ∈ range n, B j * E j = rotProd μ n Q := fun j hj => (rotProd_eq_mul_erase μ n Q hj).symm

  have hshift : ∀ j ∈ range n, ∏ i ∈ (range n).erase j, (B i).comp (C μ * X) = E ((j + 1) % n) := by
    intro j hj
    have hj' : (j + 1) % n ∈ range n := mem_range.2 (Nat.mod_lt _ hn)
    apply mul_left_cancel₀ (hB0 (j + 1))

    have e1 : B (j + 1) * ∏ i ∈ (range n).erase j, (B i).comp (C μ * X) = ∏ i ∈ range n, B (i + 1) := by
      have : ∀ i, (B i).comp (C μ * X) = B (i + 1) := fun i => by
        simp only [hB, comp_CX_comp_CX, ← pow_succ]
      simp_rw [this]
      exact mul_prod_erase (range n) (fun i => B (i + 1)) hj
    rw [e1, prod_range_shift n hn B hBper', ← hBper (j + 1), hBE _ hj', rotProd]

  unfold rotSum
  rw [Polynomial.sum_comp]
  simp_rw [mul_comp, Polynomial.prod_comp]
  change ∑ j ∈ range n, (A j).comp (C μ * X) * ∏ i ∈ (range n).erase j, (B i).comp (C μ * X) =
    ∑ j ∈ range n, A j * E j
  rw [sum_congr rfl fun j hj => by rw [hshift j hj, show (A j).comp (C μ * X) = A (j + 1) by
    simp only [hA, comp_CX_comp_CX, ← pow_succ]]]

  have : ∀ j ∈ range n, A (j + 1) * E ((j + 1) % n) = (fun k => A (k % n) * E (k % n)) (j + 1) := fun j _ => by
    simp only [hAper]
  rw [sum_congr rfl this, sum_range_shift n hn (fun k => A (k % n) * E (k % n)) fun k => by
    simp only [Nat.add_mod_right]]
  exact sum_congr rfl fun j hj => by simp only [Nat.mod_eq_of_lt (mem_range.1 hj)]

theorem eq_expand_of_comp_eq {μ : K} {n : ℕ} (hn : 0 < n) (hμ : IsPrimitiveRoot μ n) (R : K[X])
    (hR : R.comp (C μ * X) = R) : ∃ R₁ : K[X], R = Polynomial.expand K n R₁ := by
  refine ⟨Polynomial.contract n R, ?_⟩
  ext k
  by_cases hk : n ∣ k
  · obtain ⟨q, rfl⟩ := hk
    rw [mul_comm, coeff_expand_mul hn, coeff_contract hn.ne']
  · rw [coeff_expand hn, if_neg hk]

    have h1 : R.coeff k * μ ^ k = R.coeff k := by
      have := congrArg (fun S => S.coeff k) hR
      simpa only [comp_C_mul_X_coeff] using this
    have hμk : μ ^ k ≠ 1 := fun h => hk ((hμ.pow_eq_one_iff_dvd k).1 h)
    by_contra hc
    exact hμk (mul_left_cancel₀ hc (h1.trans (mul_one _).symm))

theorem exists_expand_of_isPrimitiveRoot {μ : K} {n : ℕ} (hn : 0 < n) (hμ : IsPrimitiveRoot μ n) (P Q : K[X]) :
    ∃ P₁ Q₁ : K[X], rotSum μ n P Q = Polynomial.expand K n P₁ ∧ rotProd μ n Q = Polynomial.expand K n Q₁ := by
  have hμn : μ ^ n = 1 := hμ.pow_eq_one
  have hμ0 : μ ≠ 0 := hμ.ne_zero hn.ne'
  obtain ⟨Q₁, hQ₁⟩ := eq_expand_of_comp_eq hn hμ _ (rotProd_comp μ hn hμn Q)
  by_cases hQ : Q = 0
  ·
    refine ⟨if n = 1 then P else 0, Q₁, ?_, hQ₁⟩
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos rfl]
      simp [rotSum, expand_one]
    · rw [if_neg h1, map_zero]
      unfold rotSum
      refine sum_eq_zero fun j hj => ?_

      obtain ⟨i, hi⟩ : ∃ i, i ∈ (range n).erase j := by
        have : 2 ≤ n := by have := mem_range.1 hj; omega
        by_cases hj0 : j = 0
        · exact ⟨1, by rw [mem_erase, mem_range]; omega⟩
        · exact ⟨0, by rw [mem_erase, mem_range]; omega⟩
      rw [prod_eq_zero hi (by rw [hQ, zero_comp]), mul_zero]
  obtain ⟨P₁, hP₁⟩ := eq_expand_of_comp_eq hn hμ _ (rotSum_comp μ hn hμn hμ0 P Q hQ)
  exact ⟨P₁, Q₁, hP₁, hQ₁⟩

theorem expand_ne_zero_iff {n : ℕ} (hn : 0 < n) (R₁ : K[X]) : Polynomial.expand K n R₁ ≠ 0 ↔ R₁ ≠ 0 := by
  exact (Polynomial.expand_injective hn).ne_iff' (map_zero _)

end TubeStab

namespace TubeSlope

open Polynomial

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

private theorem _root_.TubeSlope.v_sub_eq_of_lt {x y : K} (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg]; apply Valuation.map_add_eq_of_lt_left; rwa [Valuation.map_neg]

p2m_export "TubeSlope" "v_sub_eq_of_lt"
theorem v_sub_eq_max_of_ne {u β : K} (h : v β ≠ v u) : v (u - β) = max (v u) (v β) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [max_eq_left hlt.le, v_sub_eq_of_lt hlt]
  · rw [max_eq_right hgt.le, Valuation.map_sub_swap, v_sub_eq_of_lt hgt]

variable [IsAlgClosed K]

theorem eq_C_mul_prod (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem v_eval_eq_prod_max (P : K[X]) {u : K} (hgen : ∀ β ∈ P.roots, v β ≠ v u) :
    v (P.eval u) = v P.leadingCoeff * (P.roots.map fun β => max (v u) (v β)).prod := by
  conv_lhs => rw [eq_C_mul_prod P]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun β hβ => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  exact v_sub_eq_max_of_ne (hgen β hβ)

omit [IsAlgClosed K] in

theorem prod_max_eq (R : Multiset K) {a b s : Γ₀} (has : a < s) (hsb : s < b)
    (hR : ∀ β ∈ R, v β ≤ a ∨ b ≤ v β) :
    (R.map fun β => max s (v β)).prod =
      s ^ (R.filter fun β => v β ≤ a).card * ((R.filter fun β => ¬ v β ≤ a).map fun β => v β).prod := by
  classical
  induction R using Multiset.induction_on with
  | empty => simp
  | cons β R ih =>
    have hβ := hR β (Multiset.mem_cons_self _ _)
    have ih' := ih fun x hx => hR x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, ih']
    by_cases hle : v β ≤ a
    · rw [Multiset.filter_cons_of_pos (p := fun β => v β ≤ a) R hle,
        Multiset.filter_cons_of_neg (p := fun β => ¬ v β ≤ a) R (not_not_intro hle),
        Multiset.card_cons, pow_succ, max_eq_left (hle.trans has.le)]
      ac_rfl
    · have hb : b ≤ v β := hβ.resolve_left hle
      rw [Multiset.filter_cons_of_neg (p := fun β => v β ≤ a) R hle,
        Multiset.filter_cons_of_pos (p := fun β => ¬ v β ≤ a) R hle, Multiset.map_cons, Multiset.prod_cons,
        max_eq_right (hsb.le.trans hb)]
      ac_rfl

omit [IsAlgClosed K] in

theorem zpow_eq_one_imp {t : Γ₀} (ht0 : t ≠ 0) (ht1 : t < 1) {k : ℤ} (h : t ^ k = 1) : k = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    have hk' : 0 < -k := by omega
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hk'.le
    have hjpos : j ≠ 0 := by omega
    have : t ^ (-k) = 1 := by rw [zpow_neg, h, inv_one]
    rw [hj, zpow_natCast] at this
    exact absurd this (pow_lt_one₀ zero_le' ht1 hjpos).ne
  · exact hk
  · exfalso
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hk.le
    have hjpos : j ≠ 0 := by omega
    rw [hj, zpow_natCast] at h
    exact absurd h (pow_lt_one₀ zero_le' ht1 hjpos).ne

omit [IsAlgClosed K] in
private theorem _root_.TubeSlope.sq_between {a b s : Γ₀} (ha : 0 < a) (hab : a < b) (h : s * s = a * b) : a < s ∧ s < b := by
  constructor
  · by_contra hle; rw [not_lt] at hle
    have h2 : s * s ≤ a * a := mul_le_mul' hle hle
    have h3 : a * a < a * b := mul_lt_mul_of_pos_left hab ha
    exact absurd (h ▸ h2) (not_le.mpr h3)
  · by_contra hle; rw [not_lt] at hle
    have h2 : b * b ≤ s * s := mul_le_mul' hle hle
    have hb : 0 < b := lt_of_le_of_lt zero_le' hab
    have h3 : a * b < b * b := by rw [mul_comm a b]; exact mul_lt_mul_of_pos_left hab hb
    exact absurd (h ▸ h2) (not_le.mpr h3)

p2m_export "TubeSlope" "sq_between"

theorem dvd_of_v_eval_pow_eq (n : ℕ) (hn : 0 < n) (P₁ Q₁ : K[X]) (hP : P₁ ≠ 0) (hQ : Q₁ ≠ 0)
    (c : Γ₀) (m : ℤ) (x y : K) (hx : x ≠ 0) (hxy : v x < v y)
    (hval : ∀ w : K, v x < v w → v w < v y →
      Q₁.eval (w ^ n) ≠ 0 ∧ v (P₁.eval (w ^ n)) = c * v w ^ m * v (Q₁.eval (w ^ n))) :
    (n : ℤ) ∣ m := by
  classical
  have hvx : 0 < v x := (Valuation.pos_iff _).mpr hx
  have hvy : 0 < v y := hvx.trans hxy
  have hy : y ≠ 0 := (Valuation.pos_iff _).mp hvy
  have hn0 : n ≠ 0 := hn.ne'

  set a : Γ₀ := v x ^ n with ha
  have hab' : a < v y ^ n := pow_lt_pow_left₀ hxy zero_le' hn0
  let R : Multiset K := P₁.roots + Q₁.roots
  let Rad : Finset Γ₀ := ((R.map fun β => v β).filter fun r => a < r).toFinset
  let S : Finset Γ₀ := insert (v y ^ n) Rad
  have hSne : S.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
  set b : Γ₀ := S.min' hSne with hb
  have hbS : b ∈ S := Finset.min'_mem S hSne
  have hab : a < b := by
    rcases Finset.mem_insert.mp hbS with h | h
    · rw [h]; exact hab'
    · obtain ⟨r, hr, rfl⟩ : ∃ r ∈ (R.map fun β => v β).filter (fun r => a < r), r = b := ⟨b, Multiset.mem_toFinset.mp h, rfl⟩
      exact (Multiset.mem_filter.mp hr).2
  have hby : b ≤ v y ^ n := Finset.min'_le S _ (Finset.mem_insert_self _ _)
  have hgap : ∀ β ∈ R, v β ≤ a ∨ b ≤ v β := by
    intro β hβ
    by_cases h : v β ≤ a
    · exact Or.inl h
    · refine Or.inr (Finset.min'_le S _ (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ?_)))
      exact Multiset.mem_filter.mpr ⟨Multiset.mem_map_of_mem _ hβ, not_le.mp h⟩

  have heb : ∃ e : K, v e = b := by
    rcases Finset.mem_insert.mp hbS with h | h
    · exact ⟨y ^ n, by rw [map_pow, h]⟩
    · obtain ⟨hr, -⟩ := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp h)
      obtain ⟨β, -, hβ⟩ := Multiset.mem_map.mp hr
      exact ⟨β, hβ⟩
  obtain ⟨e, he⟩ := heb

  obtain ⟨u₁, hu₁⟩ := IsAlgClosed.exists_eq_mul_self (x ^ n * e)
  have hvu₁ : v u₁ * v u₁ = a * b := by rw [← map_mul, ← hu₁, map_mul, map_pow, he]
  have ha0 : 0 < a := by rw [ha]; exact pow_pos hvx _
  obtain ⟨h1a, h1b⟩ := sq_between ha0 hab hvu₁
  obtain ⟨u₂, hu₂⟩ := IsAlgClosed.exists_eq_mul_self (u₁ * e)
  have hvu₂ : v u₂ * v u₂ = v u₁ * b := by rw [← map_mul, ← hu₂, map_mul, he]
  obtain ⟨h2a, h2b⟩ := sq_between (ha0.trans h1a) h1b hvu₂

  obtain ⟨w₁, hw₁⟩ := IsAlgClosed.exists_pow_nat_eq u₁ hn
  obtain ⟨w₂, hw₂⟩ := IsAlgClosed.exists_pow_nat_eq u₂ hn
  have hvw₁ : v w₁ ^ n = v u₁ := by rw [← map_pow, hw₁]
  have hvw₂ : v w₂ ^ n = v u₂ := by rw [← map_pow, hw₂]
  have between : ∀ {w u : K}, v w ^ n = v u → a < v u → v u < b → v x < v w ∧ v w < v y := by
    intro w u hwu hau hub
    constructor
    · by_contra hle; rw [not_lt] at hle
      have : v w ^ n ≤ a := by rw [ha]; exact pow_le_pow_left₀ zero_le' hle n
      rw [hwu] at this; exact absurd hau (not_lt.mpr this)
    · by_contra hle; rw [not_lt] at hle
      have : v y ^ n ≤ v w ^ n := pow_le_pow_left₀ zero_le' hle n
      rw [hwu] at this; exact absurd (hub.trans_le hby) (not_lt.mpr this)
  obtain ⟨hxw₁, hw₁y⟩ := between hvw₁ h1a h1b
  obtain ⟨hxw₂, hw₂y⟩ := between hvw₂ (h1a.trans h2a) h2b
  have hw₁w₂ : v w₁ < v w₂ := by
    by_contra hle; rw [not_lt] at hle
    have : v w₂ ^ n ≤ v w₁ ^ n := pow_le_pow_left₀ zero_le' hle n
    rw [hvw₁, hvw₂] at this; exact absurd h2a (not_lt.mpr this)
  have hvw₁0 : v w₁ ≠ 0 := (hvx.trans hxw₁).ne'
  have hvw₂0 : v w₂ ≠ 0 := (hvx.trans hxw₂).ne'

  have hgenP : ∀ (u : K), a < v u → v u < b → ∀ β ∈ P₁.roots, v β ≠ v u := fun u hau hub β hβ heq =>
    (hgap β (Multiset.mem_add.mpr (Or.inl hβ))).elim (fun h => absurd hau (not_lt.mpr (heq ▸ h)))
      (fun h => absurd hub (not_lt.mpr (heq ▸ h)))
  have hgenQ : ∀ (u : K), a < v u → v u < b → ∀ β ∈ Q₁.roots, v β ≠ v u := fun u hau hub β hβ heq =>
    (hgap β (Multiset.mem_add.mpr (Or.inr hβ))).elim (fun h => absurd hau (not_lt.mpr (heq ▸ h)))
      (fun h => absurd hub (not_lt.mpr (heq ▸ h)))
  set kP : ℕ := (P₁.roots.filter fun β => v β ≤ a).card with hkP
  set kQ : ℕ := (Q₁.roots.filter fun β => v β ≤ a).card with hkQ
  set AP : Γ₀ := v P₁.leadingCoeff * ((P₁.roots.filter fun β => ¬ v β ≤ a).map fun β => v β).prod with hAP
  set AQ : Γ₀ := v Q₁.leadingCoeff * ((Q₁.roots.filter fun β => ¬ v β ≤ a).map fun β => v β).prod with hAQ
  have hPu : ∀ u : K, a < v u → v u < b → v (P₁.eval u) = AP * v u ^ kP := by
    intro u hau hub
    rw [v_eval_eq_prod_max P₁ (hgenP u hau hub),
      prod_max_eq P₁.roots hau hub (fun β hβ => hgap β (Multiset.mem_add.mpr (Or.inl hβ))), hAP, hkP]
    ac_rfl
  have hQu : ∀ u : K, a < v u → v u < b → v (Q₁.eval u) = AQ * v u ^ kQ := by
    intro u hau hub
    rw [v_eval_eq_prod_max Q₁ (hgenQ u hau hub),
      prod_max_eq Q₁.roots hau hub (fun β hβ => hgap β (Multiset.mem_add.mpr (Or.inr hβ))), hAQ, hkQ]
    ac_rfl
  have hApos : ∀ (L : K[X]), L ≠ 0 → v L.leadingCoeff * ((L.roots.filter fun β => ¬ v β ≤ a).map fun β => v β).prod ≠ 0 := by
    intro L hL
    refine mul_ne_zero ((Valuation.ne_zero_iff _).mpr (leadingCoeff_ne_zero.mpr hL)) (Multiset.prod_ne_zero fun h0 => ?_)
    obtain ⟨β, hβ, hβ0⟩ := Multiset.mem_map.mp h0
    have : ¬ v β ≤ a := (Multiset.mem_filter.mp hβ).2
    exact this (by rw [hβ0]; exact zero_le')
  have hAP0 : AP ≠ 0 := hApos P₁ hP
  have hAQ0 : AQ ≠ 0 := hApos Q₁ hQ

  have E : ∀ {w u : K}, w ^ n = u → a < v u → v u < b → v x < v w → v w < v y →
      AP * v w ^ (((n * kP : ℕ)) : ℤ) = c * v w ^ m * (AQ * v w ^ (((n * kQ : ℕ)) : ℤ)) := by
    intro w u hwu hau hub hxw hwy
    obtain ⟨-, hv⟩ := hval w hxw hwy
    rw [hwu, hPu u hau hub, hQu u hau hub, ← hwu, map_pow, ← pow_mul, ← pow_mul, ← zpow_natCast, ← zpow_natCast] at hv
    exact hv
  have E1 := E hw₁ h1a h1b hxw₁ hw₁y
  have E2 := E hw₂ (h1a.trans h2a) h2b hxw₂ hw₂y
  set A : ℤ := ((n * kP : ℕ) : ℤ) with hA
  set B : ℤ := ((n * kQ : ℕ) : ℤ) with hB
  set g₁ : Γ₀ := v w₁ with hg₁
  set g₂ : Γ₀ := v w₂ with hg₂
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at E1
    exact mul_ne_zero hAP0 (zpow_ne_zero _ hvw₁0) E1
  have key : g₁ ^ A * (g₂ ^ m * g₂ ^ B) = g₂ ^ A * (g₁ ^ m * g₁ ^ B) := by
    have h12 : (AP * g₁ ^ A) * (c * g₂ ^ m * (AQ * g₂ ^ B)) = (c * g₁ ^ m * (AQ * g₁ ^ B)) * (AP * g₂ ^ A) := by
      rw [E1, ← E2]
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hAP0 hc0) hAQ0)
    calc AP * c * AQ * (g₁ ^ A * (g₂ ^ m * g₂ ^ B)) = (AP * g₁ ^ A) * (c * g₂ ^ m * (AQ * g₂ ^ B)) := by ac_rfl
      _ = (c * g₁ ^ m * (AQ * g₁ ^ B)) * (AP * g₂ ^ A) := h12
      _ = AP * c * AQ * (g₂ ^ A * (g₁ ^ m * g₁ ^ B)) := by ac_rfl
  set D : ℤ := A - (m + B) with hD
  have hzD : ∀ {g : Γ₀}, g ≠ 0 → g ^ D = g ^ A / (g ^ m * g ^ B) := fun {g} hg => by
    rw [hD, zpow_sub₀ hg, zpow_add₀ hg]
  have ht : (g₁ / g₂) ^ D = 1 := by
    rw [div_zpow, hzD hvw₁0, hzD hvw₂0, div_div_div_eq, div_eq_one_iff_eq]
    · rw [key]; ac_rfl
    · exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hvw₁0) (zpow_ne_zero _ hvw₁0)) (zpow_ne_zero _ hvw₂0)
  have ht0 : g₁ / g₂ ≠ 0 := div_ne_zero hvw₁0 hvw₂0
  have ht1 : g₁ / g₂ < 1 := by rw [div_lt_iff₀ ((Valuation.pos_iff _).mpr ((Valuation.ne_zero_iff _).mp hvw₂0)), one_mul]; exact hw₁w₂
  have hD0 := zpow_eq_one_imp ht0 ht1 ht
  refine ⟨(kP : ℤ) - (kQ : ℤ), ?_⟩
  have hA' : (A : ℤ) = (n : ℤ) * kP := by rw [hA]; push_cast; ring
  have hB' : (B : ℤ) = (n : ℤ) * kQ := by rw [hB]; push_cast; ring
  have hD' : A - (m + B) = 0 := by rw [← hD]; exact hD0
  rw [hA', hB'] at hD'
  linarith

end TubeSlope

namespace TubeMoeb

open Polynomial

variable {K : Type} [Field K]

noncomputable def homog (a b c d : K) (N : ℕ) (P : K[X]) : K[X] :=
  ∑ i ∈ Finset.range (N + 1), C (P.coeff i) * (C a * X + C b) ^ i * (C c * X + C d) ^ (N - i)

theorem eval_homog (a b c d : K) (N : ℕ) (P : K[X]) (hN : P.natDegree ≤ N) (w : K) (hcw : c * w + d ≠ 0) :
    (homog a b c d N P).eval w = P.eval ((a * w + b) / (c * w + d)) * (c * w + d) ^ N := by
  rw [homog, eval_finset_sum, eval_eq_sum_range' (Nat.lt_succ_of_le hN), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [div_pow, mul_assoc, mul_assoc]
  congr 1
  rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hcw), mul_assoc, ← pow_add, Nat.sub_add_cancel hi']

noncomputable def compM (a b c d : K) (r : RatPair K) : RatPair K :=
  ⟨homog a b c d (max r.num.natDegree r.den.natDegree) r.num, homog a b c d (max r.num.natDegree r.den.natDegree) r.den⟩

theorem compM_den_eval (a b c d : K) (r : RatPair K) (w : K) (hcw : c * w + d ≠ 0) :
    (compM a b c d r).den.eval w = r.den.eval ((a * w + b) / (c * w + d)) * (c * w + d) ^ (max r.num.natDegree r.den.natDegree) :=
  eval_homog a b c d _ r.den (le_max_right _ _) w hcw

theorem compM_num_eval (a b c d : K) (r : RatPair K) (w : K) (hcw : c * w + d ≠ 0) :
    (compM a b c d r).num.eval w = r.num.eval ((a * w + b) / (c * w + d)) * (c * w + d) ^ (max r.num.natDegree r.den.natDegree) :=
  eval_homog a b c d _ r.num (le_max_left _ _) w hcw

theorem compM_den_ne_zero (a b c d : K) (r : RatPair K) (w : K) (hcw : c * w + d ≠ 0)
    (hden : r.den.eval ((a * w + b) / (c * w + d)) ≠ 0) : (compM a b c d r).den.eval w ≠ 0 := by
  rw [compM_den_eval a b c d r w hcw]; exact mul_ne_zero hden (pow_ne_zero _ hcw)

theorem compM_evalAt (a b c d : K) (r : RatPair K) (w : K) (hcw : c * w + d ≠ 0)
    (hden : r.den.eval ((a * w + b) / (c * w + d)) ≠ 0) :
    (compM a b c d r).num.eval w / (compM a b c d r).den.eval w = r.evalAt ((a * w + b) / (c * w + d)) := by
  rw [compM_num_eval a b c d r w hcw, compM_den_eval a b c d r w hcw, mul_div_mul_right _ _ (pow_ne_zero _ hcw)]
  rfl

end TubeMoeb

section Asm

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

theorem Asm.sq_between {a b s : Γ₀} (ha : 0 < a) (hab : a < b) (h : s * s = a * b) : a < s ∧ s < b := by
  constructor
  · by_contra hle; rw [not_lt] at hle
    have h2 : s * s ≤ a * a := mul_le_mul' hle hle
    have h3 : a * a < a * b := mul_lt_mul_of_pos_left hab ha
    exact absurd (h ▸ h2) (not_le.mpr h3)
  · by_contra hle; rw [not_lt] at hle
    have h2 : b * b ≤ s * s := mul_le_mul' hle hle
    have hb : 0 < b := lt_of_le_of_lt zero_le' hab
    have h3 : a * b < b * b := by rw [mul_comm a b]; exact mul_lt_mul_of_pos_left hab hb
    exact absurd (h ▸ h2) (not_le.mpr h3)

theorem Asm.eq_one_of_pow_eq_one {t : Γ₀} {n : ℕ} (hn : n ≠ 0) (h : t ^ n = 1) : t = 1 := by
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · exact absurd h (pow_lt_one₀ zero_le' hlt hn).ne
  · exact heq
  · exact absurd h (one_lt_pow₀ hgt hn).ne'

theorem Asm.zpow_between {x y t : Γ₀} (hx : 0 < x) (hxt : x ≤ t) (hty : t ≤ y) (m : ℤ) :
    x ^ m ≤ t ^ m ∨ y ^ m ≤ t ^ m := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    left; rw [zpow_natCast, zpow_natCast]; exact pow_le_pow_left₀ zero_le' hxt k
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -m)
    have hm' : m = -(k : ℤ) := by omega
    right; rw [hm', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    have ht : 0 < t := hx.trans_le hxt
    exact (inv_le_inv₀ (pow_pos (ht.trans_le hty) _) (pow_pos ht _)).2 (pow_le_pow_left₀ zero_le' hty k)

end Asm

open Polynomial in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (H : Subgroup PGL(2, K₀)) [Finite H]
    (hH : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → pmoebius K₀ h z ∈ stdEdgeTube ϖ)
    (hdir : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ → Valued.v (pmoebius K₀ h z) = Valued.v z)
    (htame : Valued.v ((Nat.card H : ℕ) : K) = 1)
    (f : ↥(holRing ϖ)) (hf : IsUnit f)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ stdEdgeTube ϖ →
      (f : ↥(upperHalfPlane K₀ K) → K) (h • z) = (f : ↥(upperHalfPlane K₀ K) → K) z)
    (c : Γ₀) (m : ℤ)
    (hcm : ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ m) :
    ((Nat.card H : ℕ) : ℤ) ∣ m := by
  classical
  set p : K := algebraMap K₀ K ϖ.ϖ with hp
  have hvp : 0 < Valued.v p := ϖ.pos
  have hp1 : Valued.v p < 1 := ϖ.lt_one
  have hp0 : p ≠ 0 := (Valuation.pos_iff _).mp hvp
  set n : ℕ := Nat.card H with hn
  have hn0 : 0 < n := Nat.card_pos

  have memTube : ∀ z : K, Valued.v p < Valued.v z → Valued.v z < 1 → z ∈ stdEdgeTube ϖ := by
    intro z h1 h2
    refine ⟨?_, h1, h2⟩
    rw [mem_upperHalfPlane_iff]
    rintro a rfl
    rcases hunif a with h | h
    · exact absurd h1 (not_lt.mpr h)
    · exact absurd h2 (not_lt.mpr h)
  have tubeAff : ∀ z : K, z ∈ stdEdgeTube ϖ → z ∈ affinoid ϖ 1 := by
    intro z hz
    rw [mem_affinoid_iff']
    refine ⟨?_, fun a => ?_⟩
    · rw [pow_one]; exact hz.2.2.le.trans ((one_le_inv₀ hvp).2 hp1.le)
    · rw [pow_one]
      rcases hunif a with h | h
      · rw [TubeSlope.v_sub_eq_of_lt (h.trans_lt hz.2.1)]; exact hz.2.1.le
      · rw [Valuation.map_sub_swap, TubeSlope.v_sub_eq_of_lt (hz.2.2.trans_le h)]; exact hp1.le.trans h

  have hf0 : ∀ z : ↥(upperHalfPlane K₀ K), (f : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
    intro z
    obtain ⟨g, hg⟩ := hf.exists_right_inv
    have := congrArg (fun u : ↥(holRing ϖ) => (u : ↥(upperHalfPlane K₀ K) → K) z) hg
    simp only [Subring.coe_mul, Subring.coe_one, Pi.mul_apply, Pi.one_apply] at this
    exact left_ne_zero_of_mul_eq_one this

  obtain ⟨h₀, μ, α, β, γ, δ, hh₀, -, hμ, hdet, hφ, honto, hrot⟩ :=
    TubeStab.exists_rotation_coordinate K₀ K ϖ hunif H hH hdir htame
  have hμn : μ ^ n = 1 := hμ.pow_eq_one
  have hvμ : Valued.v μ = 1 := Asm.eq_one_of_pow_eq_one hn0.ne' (by rw [← map_pow, hμn, map_one])
  have hμ0 : μ ≠ 0 := fun h => by rw [h, map_zero] at hvμ; exact zero_ne_one hvμ

  have hψφ : ∀ z : K, z ∈ stdEdgeTube ϖ → (δ * ((α * z + β) / (γ * z + δ)) + -β) / (-γ * ((α * z + β) / (γ * z + δ)) + α) = z ∧
      -γ * ((α * z + β) / (γ * z + δ)) + α ≠ 0 := by
    intro z hz
    have hD := (hφ z hz).1
    have e2 : -γ * ((α * z + β) / (γ * z + δ)) + α = (α * δ - β * γ) / (γ * z + δ) := by
      rw [← mul_div_assoc, div_add' _ _ _ hD]; congr 1; ring
    have e1 : δ * ((α * z + β) / (γ * z + δ)) + -β = (α * δ - β * γ) * z / (γ * z + δ) := by
      rw [← mul_div_assoc, div_add' _ _ _ hD]; congr 1; ring
    refine ⟨?_, by rw [e2]; exact div_ne_zero hdet hD⟩
    rw [e1, e2, div_div_div_cancel_right₀ hD, mul_div_cancel_left₀ _ hdet]
  have hann : ∀ w : K, Valued.v p < Valued.v w → Valued.v w < 1 →
      (δ * w + -β) / (-γ * w + α) ∈ stdEdgeTube ϖ ∧ (α * ((δ * w + -β) / (-γ * w + α)) + β) / (γ * ((δ * w + -β) / (-γ * w + α)) + δ) = w ∧
      -γ * w + α ≠ 0 ∧ Valued.v ((δ * w + -β) / (-γ * w + α)) = Valued.v w := by
    intro w h1 h2
    obtain ⟨z, hz, hzw⟩ := honto w h1 h2
    obtain ⟨hψz, hden⟩ := hψφ z hz
    rw [hzw] at hψz hden
    refine ⟨by rw [hψz]; exact hz, by rw [hψz]; exact hzw, hden, ?_⟩
    rw [hψz, ← hzw]; exact ((hφ z hz).2).symm

  have hrotj : ∀ (j : ℕ) (z : K), z ∈ stdEdgeTube ϖ →
      (α * pmoebius K₀ (h₀ ^ j) z + β) / (γ * pmoebius K₀ (h₀ ^ j) z + δ) = μ ^ j * ((α * z + β) / (γ * z + δ)) := by
    intro j
    induction j with
    | zero => intro z hz; rw [pow_zero, pow_zero, one_mul, pmoebius_one]
    | succ j ih =>
      intro z hz
      have hz' : pmoebius K₀ (h₀ ^ j) z ∈ stdEdgeTube ϖ := hH _ (pow_mem hh₀ j) z hz
      rw [pow_succ', pmoebius_mul K₀ hz.1, hrot _ hz', ih z hz, pow_succ']; ring

  obtain ⟨r, hpf, -, hlim⟩ := f.2 1
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have happ : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ (z : K) (hz : z ∈ affinoid ϖ 1),
      Valued.v ((r k).evalAt z - (f : ↥(upperHalfPlane K₀ K) → K) ⟨z, affinoid_subset_upperHalfPlane ϖ 1 hz⟩) < Valued.v e := by
    intro e he
    have hm0 : vRestrict K e ≠ 0 := (Valuation.ne_zero_iff _).mpr he
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hm0))
    refine ⟨N, fun k hk z hz => (v_lt_iff_vRestrict_lt K _ _).2 ?_⟩
    have h__af := hN k hk ⟨z, hz⟩
    simp only [Units.val_mk0] at h__af
    exact h__af

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self p
  have hvs := Asm.sq_between hvp hp1 (by rw [← map_mul, ← hs, mul_one] : Valued.v s * Valued.v s = Valued.v p * 1)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_eq_mul_self (p * s)
  have hvx := Asm.sq_between hvp hvs.1 (by rw [← map_mul, ← hx, map_mul] : Valued.v x * Valued.v x = Valued.v p * Valued.v s)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_eq_mul_self s
  have hvy := Asm.sq_between (hvp.trans hvs.1) hvs.2 (by rw [← map_mul, ← hy, mul_one] : Valued.v y * Valued.v y = Valued.v s * 1)
  have hxy : Valued.v x < Valued.v y := hvx.2.trans hvy.1
  have hx0 : x ≠ 0 := (Valuation.pos_iff _).mp (hvp.trans hvx.1)
  have hwann : ∀ w : K, Valued.v x < Valued.v w → Valued.v w < Valued.v y → Valued.v p < Valued.v w ∧ Valued.v w < 1 :=
    fun w h1 h2 => ⟨hvx.1.trans h1, h2.trans hvy.2⟩

  have hfψ : ∀ (w : K) (h1 : Valued.v p < Valued.v w) (h2 : Valued.v w < 1),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * w + -β) / (-γ * w + α), (hann w h1 h2).1.1⟩) = c * Valued.v w ^ m := by
    intro w h1 h2
    rw [hcm _ (hann w h1 h2).1, (hann w h1 h2).2.2.2]
  have hc0 : c ≠ 0 := by
    intro h0
    have := hfψ x hvx.1 (hvx.2.trans hvs.2)
    rw [h0, zero_mul] at this
    exact hf0 _ ((Valuation.zero_iff _).mp this)
  obtain ⟨e, he0, hex, hey⟩ : ∃ e : K, e ≠ 0 ∧ Valued.v e ≤ c * Valued.v x ^ m ∧ Valued.v e ≤ c * Valued.v y ^ m := by
    set e₁ := (f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * x + -β) / (-γ * x + α), (hann x hvx.1 (hvx.2.trans hvs.2)).1.1⟩
    set e₂ := (f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * y + -β) / (-γ * y + α), (hann y (hvx.1.trans hxy) hvy.2).1.1⟩
    have h₁ : Valued.v e₁ = c * Valued.v x ^ m := hfψ x hvx.1 (hvx.2.trans hvs.2)
    have h₂ : Valued.v e₂ = c * Valued.v y ^ m := hfψ y (hvx.1.trans hxy) hvy.2
    rcases le_total (Valued.v e₁) (Valued.v e₂) with h | h
    · exact ⟨e₁, hf0 _, h₁.le, h.trans h₂.le⟩
    · exact ⟨e₂, hf0 _, h.trans h₁.le, h₂.le⟩
  have hbound : ∀ w : K, Valued.v x < Valued.v w → Valued.v w < Valued.v y → Valued.v e ≤ c * Valued.v w ^ m := by
    intro w h1 h2
    rcases Asm.zpow_between (hvp.trans hvx.1) h1.le h2.le m with h | h
    · exact hex.trans (mul_le_mul' le_rfl h)
    · exact hey.trans (mul_le_mul' le_rfl h)

  obtain ⟨N, hN⟩ := happ e he0
  set R : RatPair K := r N with hR
  set Rt : RatPair K := TubeMoeb.compM δ (-β) (-γ) α R with hRt

  have hkey : ∀ (w : K) (h1 : Valued.v p < Valued.v w) (h2 : Valued.v w < 1) (j : ℕ),
      Rt.den.eval (μ ^ j * w) ≠ 0 ∧
      Valued.v (Rt.num.eval (μ ^ j * w) / Rt.den.eval (μ ^ j * w) -
        (f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * w + -β) / (-γ * w + α), (hann w h1 h2).1.1⟩) < Valued.v e := by
    intro w h1 h2 j
    have hvw' : Valued.v (μ ^ j * w) = Valued.v w := by rw [map_mul, map_pow, hvμ, one_pow, one_mul]
    obtain ⟨hzj, -, hdenj, -⟩ := hann (μ ^ j * w) (by rw [hvw']; exact h1) (by rw [hvw']; exact h2)
    set zj : K := (δ * (μ ^ j * w) + -β) / (-γ * (μ ^ j * w) + α) with hzjdef
    have hzjA : zj ∈ affinoid ϖ 1 := tubeAff zj hzj
    have hQzj : R.den.eval zj ≠ 0 := hpf N zj hzjA
    refine ⟨TubeMoeb.compM_den_ne_zero δ (-β) (-γ) α R _ hdenj hQzj, ?_⟩
    rw [TubeMoeb.compM_evalAt δ (-β) (-γ) α R _ hdenj hQzj]

    obtain ⟨hz0, hφψ, -, -⟩ := hann w h1 h2
    have hzj_eq : zj = pmoebius K₀ (h₀ ^ j) ((δ * w + -β) / (-γ * w + α)) := by
      have h' := hrotj j _ hz0
      rw [hφψ] at h'

      have hmem := hH _ (pow_mem hh₀ j) _ hz0
      rw [hzjdef, ← h', (hψφ _ hmem).1]
    have hfj : (f : ↥(upperHalfPlane K₀ K) → K) ⟨zj, hzj.1⟩ =
        (f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * w + -β) / (-γ * w + α), hz0.1⟩ := by
      have := hinv (h₀ ^ j) (pow_mem hh₀ j) ⟨(δ * w + -β) / (-γ * w + α), hz0.1⟩ hz0
      have harg : (⟨zj, hzj.1⟩ : ↥(upperHalfPlane K₀ K)) =
          (h₀ ^ j) • (⟨(δ * w + -β) / (-γ * w + α), hz0.1⟩ : ↥(upperHalfPlane K₀ K)) := Subtype.ext hzj_eq
      rw [harg]; exact this
    rw [← hfj]
    exact hN N le_rfl zj hzjA

  have hsum : ∀ (w : K) (hw1 : Valued.v x < Valued.v w) (hw2 : Valued.v w < Valued.v y),
      (TubeStab.rotProd μ n Rt.den).eval w ≠ 0 ∧
      Valued.v ((TubeStab.rotSum μ n Rt.num Rt.den).eval w / (TubeStab.rotProd μ n Rt.den).eval w) = c * Valued.v w ^ m := by
    intro w hw1 hw2
    obtain ⟨h1, h2⟩ := hwann w hw1 hw2
    have hQj : ∀ j ∈ Finset.range n, Rt.den.eval (μ ^ j * w) ≠ 0 := fun j _ => (hkey w h1 h2 j).1
    refine ⟨by rw [TubeStab.eval_rotProd]; exact Finset.prod_ne_zero_iff.mpr hQj, ?_⟩
    rw [TubeStab.eval_rotSum_div μ n Rt.num Rt.den w hQj]
    set F : K := (f : ↥(upperHalfPlane K₀ K) → K) ⟨(δ * w + -β) / (-γ * w + α), (hann w h1 h2).1.1⟩ with hF
    have hvF : Valued.v F = c * Valued.v w ^ m := hfψ w h1 h2
    have hvnF : Valued.v ((n : K) * F) = c * Valued.v w ^ m := by rw [map_mul, hn, htame, one_mul, hvF]
    have hsplit : ∑ j ∈ Finset.range n, Rt.num.eval (μ ^ j * w) / Rt.den.eval (μ ^ j * w) =
        (n : K) * F + ∑ j ∈ Finset.range n, (Rt.num.eval (μ ^ j * w) / Rt.den.eval (μ ^ j * w) - F) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [hsplit]
    have hlt : Valued.v (∑ j ∈ Finset.range n, (Rt.num.eval (μ ^ j * w) / Rt.den.eval (μ ^ j * w) - F)) <
        Valued.v ((n : K) * F) := by
      rw [hvnF]
      exact Valuation.map_sum_lt _ (mul_ne_zero hc0 (zpow_ne_zero _ ((hvp.trans h1).ne')))
        (fun j _ => (hkey w h1 h2 j).2.trans_le (hbound w hw1 hw2))
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hvnF]

  obtain ⟨P₁, Q₁, hP₁, hQ₁⟩ := TubeStab.exists_expand_of_isPrimitiveRoot hn0 hμ Rt.num Rt.den
  have hval : ∀ w : K, Valued.v x < Valued.v w → Valued.v w < Valued.v y →
      Q₁.eval (w ^ n) ≠ 0 ∧ Valued.v (P₁.eval (w ^ n)) = c * Valued.v w ^ m * Valued.v (Q₁.eval (w ^ n)) := by
    intro w hw1 hw2
    obtain ⟨hden, hv⟩ := hsum w hw1 hw2
    rw [hQ₁, Polynomial.expand_eval] at hden
    rw [hP₁, hQ₁, Polynomial.expand_eval, Polynomial.expand_eval] at hv
    refine ⟨hden, ?_⟩
    rw [map_div₀, div_eq_iff ((Valuation.ne_zero_iff _).mpr hden)] at hv
    exact hv

  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_eq_mul_self (x * y)
  have hvw₀ := Asm.sq_between (hvp.trans hvx.1) hxy
    (by rw [← map_mul, ← hw₀, map_mul] : Valued.v w₀ * Valued.v w₀ = Valued.v x * Valued.v y)
  have hQ₁0 : Q₁ ≠ 0 := by
    intro h0
    have := (hsum w₀ hvw₀.1 hvw₀.2).1
    rw [hQ₁, h0, map_zero, eval_zero] at this
    exact this rfl
  have hP₁0 : P₁ ≠ 0 := by
    intro h0
    have := (hsum w₀ hvw₀.1 hvw₀.2).2
    rw [hP₁, h0, map_zero, eval_zero, zero_div, map_zero] at this
    exact mul_ne_zero hc0 (zpow_ne_zero _ ((hvp.trans (hvx.1.trans hvw₀.1)).ne')) this.symm
  exact TubeSlope.dvd_of_v_eval_pow_eq n hn0 P₁ Q₁ hP₁0 hQ₁0 c m x y hx0 hxy hval

end S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow (solution)
