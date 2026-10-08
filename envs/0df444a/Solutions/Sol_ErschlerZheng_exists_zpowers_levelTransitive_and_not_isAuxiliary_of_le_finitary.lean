-- Prove2me | solution 1 for ErschlerZheng.exists_zpowers_levelTransitive_and_not_isAuxiliary_of_le_finitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.446482+00:00
-- url     : https://prove2.me/submissions/894a874e-fcd7-4fc5-a80d-593889b945fe

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

theorem ray_ext {x y : Ray} (h : ∀ n, rayPrefix x n = rayPrefix y n) : x = y := by
  funext i
  have hx : i < (rayPrefix x (i + 1)).length := by simp [length_rayPrefix]
  rw [← getElem_rayPrefix x (i + 1) i hx, List.getElem_of_eq (h (i + 1)), getElem_rayPrefix]

end RayBasic

end ErschlerZheng
end

section
/-!
# The binary odometer: level transitive, yet no finitary group is auxiliary for it

Erschler–Zheng, p. 18, as printed, fails. The binary odometer `τ`, `τ(0w) = 1w`,
`τ(1w) = 0τ(w)` (digits `false` = 0, `true` = 1, least significant digit first), adds `1` to a
vertex read as a binary number. The cyclic group `G = ⟨τ⟩` acts transitively on every level, and
`τ(1^∞) = 0^∞`, so `0^∞ ∈ 1^∞·G`; but a subgroup `K` of the finitary automorphisms moves a ray
only within its cofinality class (the milestone
`ErschlerZheng.isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary`), and `0^∞` is not
cofinal with `1^∞`. Hence `1^∞·K ≠ 1^∞·G` and `K` is not an auxiliary group for `G`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace A2FOdometer

/-- The binary odometer `τ` on vertices: `τ(0w) = 1w`, `τ(1w) = 0τ(w)`. -/
def odoFun : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: odoFun w

/-- The inverse of the odometer: `τ⁻¹(1w) = 0w`, `τ⁻¹(0w) = 1τ⁻¹(w)`. -/
def odoInvFun : List Bool → List Bool
  | [] => []
  | true :: w => false :: w
  | false :: w => true :: odoInvFun w

theorem odoInvFun_odoFun (w : List Bool) : odoInvFun (odoFun w) = w := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [odoFun, odoInvFun, ih]

theorem odoFun_odoInvFun (w : List Bool) : odoFun (odoInvFun w) = w := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [odoFun, odoInvFun, ih]

theorem length_odoFun (w : List Bool) : (odoFun w).length = w.length := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [odoFun, ih]

theorem odoFun_prefix {v w : List Bool} (h : v <+: w) : odoFun v <+: odoFun w := by
  induction v generalizing w with
  | nil => exact List.nil_prefix
  | cons x v ih =>
    obtain ⟨t, rfl⟩ := h
    cases x
    · exact ⟨t, by simp [odoFun]⟩
    · simp only [List.cons_append, odoFun, List.cons_prefix_cons, true_and]
      exact ih ⟨t, rfl⟩

theorem odoInvFun_prefix {v w : List Bool} (h : v <+: w) : odoInvFun v <+: odoInvFun w := by
  induction v generalizing w with
  | nil => exact List.nil_prefix
  | cons x v ih =>
    obtain ⟨t, rfl⟩ := h
    cases x
    · simp only [List.cons_append, odoInvFun, List.cons_prefix_cons, true_and]
      exact ih ⟨t, rfl⟩
    · exact ⟨t, by simp [odoInvFun]⟩

theorem odoFun_prefix_iff (v w : List Bool) : v <+: w ↔ odoFun v <+: odoFun w :=
  ⟨odoFun_prefix, fun h => by simpa [odoInvFun_odoFun] using odoInvFun_prefix h⟩

/-- The odometer as a permutation of the vertices. -/
def odoPerm : Equiv.Perm (List Bool) :=
  ⟨odoFun, odoInvFun, odoInvFun_odoFun, odoFun_odoInvFun⟩

/-- The binary odometer `τ` as an automorphism of the binary tree. -/
def odometer : BinaryTreeAut := ⟨odoPerm, length_odoFun, odoFun_prefix_iff⟩

theorem odometer_pow_apply (k : ℕ) (w : List Bool) :
    ((odometer ^ k : BinaryTreeAut) : Equiv.Perm (List Bool)) w = odoFun^[k] w := by
  rw [Subgroup.coe_pow, Equiv.Perm.coe_pow]; rfl

/-- `τ²(bw) = bτ(w)`. -/
theorem odoFun_odoFun_cons (b : Bool) (w : List Bool) :
    odoFun (odoFun (b :: w)) = b :: odoFun w := by
  cases b <;> rfl

theorem iterate_odoFun_cons (b : Bool) (w : List Bool) (k : ℕ) :
    odoFun^[2 * k] (b :: w) = b :: odoFun^[k] w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, Function.iterate_add_apply, ih,
      Function.iterate_succ_apply' odoFun k w]
    exact odoFun_odoFun_cons b _

/-- Any two vertices of the same level are joined by a power of the odometer. -/
theorem exists_iterate_eq (n : ℕ) : ∀ u v : List Bool, u.length = n → v.length = n →
    ∃ k : ℕ, odoFun^[k] u = v := by
  induction n with
  | zero =>
    intro u v hu hv
    exact ⟨0, by rw [List.length_eq_zero_iff.mp hu, List.length_eq_zero_iff.mp hv]; rfl⟩
  | succ n ih =>
    intro u v hu hv
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_length_eq_add_one hu
    obtain ⟨b, v', rfl⟩ := List.exists_cons_of_length_eq_add_one hv
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hu hv
    obtain ⟨j, u'', hj, hu''⟩ :
        ∃ (j : ℕ) (u'' : List Bool), odoFun^[j] (a :: u') = b :: u'' ∧ u''.length = n := by
      by_cases hab : a = b
      · exact ⟨0, u', by rw [hab]; rfl, hu⟩
      · refine ⟨1, ?_⟩
        cases a <;> cases b
        · exact absurd rfl hab
        · exact ⟨u', rfl, hu⟩
        · exact ⟨odoFun u', rfl, by rw [length_odoFun, hu]⟩
        · exact absurd rfl hab
    obtain ⟨k, hk⟩ := ih u'' v' hu'' hv
    refine ⟨2 * k + j, ?_⟩
    rw [Function.iterate_add_apply, hj, iterate_odoFun_cons, hk]

/-- `⟨τ⟩` acts transitively on each level, for the right action `u·g = g⁻¹(u)`. -/
theorem levelTransitive (u v : List Bool) (h : u.length = v.length) :
    ∃ g ∈ Subgroup.zpowers odometer, u <• g = v := by
  obtain ⟨k, hk⟩ := exists_iterate_eq u.length u v rfl h.symm
  refine ⟨(odometer ^ k)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k), ?_⟩
  rw [vertex_smul_def, inv_inv, odometer_pow_apply, hk]

/-- The ray `0^∞`. -/
def zeroRay : Ray := fun _ => false

theorem odoFun_replicate_true (n : ℕ) :
    odoFun (List.replicate n true) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, odoFun, ih]

/-- `1^∞·τ⁻¹ = τ(1^∞) = 0^∞`. -/
theorem oneRay_smul_odometer_inv : oneRay <• odometer⁻¹ = zeroRay := by
  apply RayBasic.ray_ext
  intro n
  rw [rayPrefix_smul, vertex_smul_def, inv_inv]
  have h1 : rayPrefix oneRay n = List.replicate n true := by
    simp [rayPrefix, oneRay, List.ofFn_const]
  have h0 : rayPrefix zeroRay n = List.replicate n false := by
    simp [rayPrefix, zeroRay, List.ofFn_const]
  rw [h1, h0]
  exact odoFun_replicate_true n

/-- `0^∞` lies in the `⟨τ⟩`-orbit of `1^∞`. -/
theorem zeroRay_mem_rightOrbit : zeroRay ∈ rightOrbit (Subgroup.zpowers odometer) oneRay :=
  ⟨odometer⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers _), oneRay_smul_odometer_inv.symm⟩

/-- `0^∞` is not in the orbit of `1^∞` under any group of finitary automorphisms. -/
theorem zeroRay_not_mem_rightOrbit (K : Subgroup BinaryTreeAut) (hK : K ≤ finitary) :
    zeroRay ∉ rightOrbit K oneRay := by
  rintro ⟨k, hk, hkx⟩
  have h2 : zeroRay ∈ rightOrbit finitary oneRay := ⟨k, hK hk, hkx⟩
  rw [(isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 (fun _ => 0) oneRay).2]
    at h2
  obtain ⟨n, hn⟩ := (h2 : ∀ᶠ n in Filter.atTop, zeroRay n = oneRay n).exists
  simp [zeroRay, oneRay] at hn

end A2FOdometer

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open A2FOdometer in
theorem solution :
    ∃ τ : Garrido.BinaryTreeAut,
      (∀ u v : List Bool, u.length = v.length → ∃ g ∈ Subgroup.zpowers τ, u <• g = v) ∧
      ∀ K : Subgroup Garrido.BinaryTreeAut, K ≤ finitary →
        ¬ IsAuxiliary (X := Ray) (Subgroup.zpowers τ) K := by
  refine ⟨odometer, levelTransitive, fun K hK hAux => ?_⟩
  have h1 := zeroRay_mem_rightOrbit
  rw [← hAux.1 oneRay] at h1
  exact zeroRay_not_mem_rightOrbit K hK h1
end
