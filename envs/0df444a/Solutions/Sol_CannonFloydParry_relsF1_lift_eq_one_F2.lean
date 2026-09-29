-- Prove2me | solution 1 for CannonFloydParry.relsF1_lift_eq_one_F2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-17T22:02:09.653719+00:00
-- url     : https://prove2.me/submissions/79942661-5fbe-4a3c-8ec8-96679aa24674

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations

/-! # Section 3, generic algebra

The three groups of CFP §3 — `F₁`, `F₂` and `F` itself — each carry a family
`y₀ = a`, `yₙ = a^{-(n-1)} b a^{n-1}` (n ≥ 1), and in each the relations
`yₖ⁻¹ yₙ yₖ = y_{n+1}` (k < n) follow from the two instances `(k, n) = (1, 2), (1, 3)`.
This module proves that once, for an arbitrary group. -/

namespace CannonFloydParry
namespace S3

variable {G : Type*} [Group G]

/-- `genY a b n`: `a` for `n = 0`, and `a^{-(n-1)} b a^{n-1}` for `n ≥ 1`. -/
def genY (a b : G) : ℕ → G
  | 0 => a
  | n + 1 => (a ^ n)⁻¹ * b * a ^ n

@[simp] lemma genY_zero (a b : G) : genY a b 0 = a := rfl

lemma genY_succ (a b : G) (n : ℕ) : genY a b (n + 1) = (a ^ n)⁻¹ * b * a ^ n := rfl

@[simp] lemma genY_one (a b : G) : genY a b 1 = b := by
  rw [genY_succ]; simp

lemma genY_two (a b : G) : genY a b 2 = a⁻¹ * b * a := by
  rw [genY_succ]; simp

lemma genY_three (a b : G) : genY a b 3 = a⁻¹ ^ 2 * b * a ^ 2 := by
  rw [genY_succ, inv_pow]

lemma genY_succ_succ (a b : G) (n : ℕ) :
    genY a b (n + 2) = a⁻¹ * genY a b (n + 1) * a := by
  rw [genY_succ, genY_succ, pow_succ, mul_inv_rev]; group

/-- Conjugating the relation for `(k+1, n+1)` by `a` gives the relation for `(k+2, n+2)`. -/
lemma genY_step (a b : G) {k n : ℕ}
    (h : (genY a b (k + 1))⁻¹ * genY a b (n + 1) * genY a b (k + 1) = genY a b (n + 2)) :
    (genY a b (k + 2))⁻¹ * genY a b (n + 2) * genY a b (k + 2) = genY a b (n + 3) := by
  have e : genY a b (n + 3) = a⁻¹ * genY a b (n + 2) * a := genY_succ_succ a b (n + 1)
  rw [e, genY_succ_succ a b k]
  conv_lhs => rw [genY_succ_succ a b n]
  rw [← h]
  group

/-- From `y₁⁻¹ y₂ y₁ = y₃` and `y₁⁻¹ y₃ y₁ = y₄`, all relations `yₖ⁻¹ yₙ yₖ = y_{n+1}`, `k < n`. -/
theorem genY_conj (a b : G)
    (h2 : b⁻¹ * genY a b 2 * b = genY a b 3)
    (h3 : b⁻¹ * genY a b 3 * b = genY a b 4) :
    ∀ k n, k < n → (genY a b k)⁻¹ * genY a b n * genY a b k = genY a b (n + 1) := by
  -- the case `k = 1`, by strong induction on `n`
  have h1 : ∀ n, 2 ≤ n → b⁻¹ * genY a b n * b = genY a b (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 4 with h | h
      · interval_cases n
        · exact h2
        · exact h3
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        -- (1, m+2)
        have r1 : b⁻¹ * genY a b (m + 2) * b = genY a b (m + 3) := ih (m + 2) (by omega) (by omega)
        -- (2, m+3), by conjugating (1, m+2)
        have r2 : (genY a b 2)⁻¹ * genY a b (m + 3) * genY a b 2 = genY a b (m + 4) :=
          genY_step a b (k := 0) (n := m + 1) (by simpa using r1)
        -- (1, m+3)
        have r3 : b⁻¹ * genY a b (m + 3) * b = genY a b (m + 4) := ih (m + 3) (by omega) (by omega)
        -- (3, m+4), by conjugating (2, m+3)
        have r4 : (genY a b 3)⁻¹ * genY a b (m + 4) * genY a b 3 = genY a b (m + 5) :=
          genY_step a b (k := 1) (n := m + 2) r2
        rw [← r2]
        calc b⁻¹ * ((genY a b 2)⁻¹ * genY a b (m + 3) * genY a b 2) * b
            = (b⁻¹ * genY a b 2 * b)⁻¹ * (b⁻¹ * genY a b (m + 3) * b) * (b⁻¹ * genY a b 2 * b) := by
              group
          _ = genY a b (m + 5) := by rw [h2, r3, r4]
  intro k
  induction k with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [genY_zero, genY_succ, genY_succ, pow_succ, mul_inv_rev]; group
  | succ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rcases k with _ | k
    · simpa using h1 (m + 2) (by omega)
    · exact genY_step a b (ih (m + 1) (by omega))

/-- A relator `[a b⁻¹, y] = 1` says exactly that `b` and `a` conjugate `y` alike. -/
lemma conj_eq_of_comm_relator (a b y : G)
    (h : (a * b⁻¹) * y * (a * b⁻¹)⁻¹ * y⁻¹ = 1) : b⁻¹ * y * b = a⁻¹ * y * a := by
  have h' : (a * b⁻¹) * y * (a * b⁻¹)⁻¹ = y := mul_inv_eq_one.mp h
  calc b⁻¹ * y * b = a⁻¹ * ((a * b⁻¹) * y * (a * b⁻¹)⁻¹) * a := by group
    _ = a⁻¹ * y * a := by rw [h']

/-- Converse of `conj_eq_of_comm_relator`. -/
lemma comm_relator_of_conj_eq (a b y : G) (h : b⁻¹ * y * b = a⁻¹ * y * a) :
    (a * b⁻¹) * y * (a * b⁻¹)⁻¹ * y⁻¹ = 1 := by
  calc (a * b⁻¹) * y * (a * b⁻¹)⁻¹ * y⁻¹ = a * (b⁻¹ * y * b) * a⁻¹ * y⁻¹ := by group
    _ = a * (a⁻¹ * y * a) * a⁻¹ * y⁻¹ := by rw [h]
    _ = 1 := by group

/-- If `y₂ = a⁻¹ b a` conjugates `y` to `a⁻¹ y a`, then `a⁻¹ b` commutes with `y`. -/
lemma comm_relator_invA_B (a b y : G)
    (h : (a⁻¹ * b * a)⁻¹ * y * (a⁻¹ * b * a) = a⁻¹ * y * a) :
    (a⁻¹ * b) * y * (a⁻¹ * b)⁻¹ * y⁻¹ = 1 := by
  have h' : y * (a⁻¹ * b * a) = (a⁻¹ * b * a) * (a⁻¹ * y * a) := by rw [← h]; group
  calc (a⁻¹ * b) * y * (a⁻¹ * b)⁻¹ * y⁻¹
      = ((a⁻¹ * b * a) * (a⁻¹ * y * a)) * a⁻¹ * (a⁻¹ * b)⁻¹ * y⁻¹ := by group
    _ = (y * (a⁻¹ * b * a)) * a⁻¹ * (a⁻¹ * b)⁻¹ * y⁻¹ := by rw [h']
    _ = 1 := by group

end S3
end CannonFloydParry

/-! # Section 3: the relations in `F₁`

`Yₙ = genY A B n`; the two defining relators of `F₁` are the instances `(1,2)`, `(1,3)` of
`Yₖ⁻¹ Yₙ Yₖ = Y_{n+1}`, and `S3_gen` supplies the rest: line (3.2) and, from it, line (3.3). -/

namespace CannonFloydParry
namespace S3

open PresentedGroup

/-- `Y` is the generic family for `a = A`, `b = B`. -/
lemma Y_eq_genY : Y = genY (of FormalAB.A : F1) (of FormalAB.B) := by
  funext n; cases n <;> rfl

/-- The first relator of `F₁`, in `F₁`. -/
lemma F1_rel1 :
    ((of FormalAB.A : F1) * (of FormalAB.B)⁻¹) * ((of FormalAB.A)⁻¹ * of FormalAB.B * of FormalAB.A)
      * ((of FormalAB.A : F1) * (of FormalAB.B)⁻¹)⁻¹
      * ((of FormalAB.A : F1)⁻¹ * of FormalAB.B * of FormalAB.A)⁻¹ = 1 := by
  have h := one_of_mem (rels := relsF1)
    (x := (FreeGroup.of FormalAB.A * (FreeGroup.of FormalAB.B)⁻¹)
      * ((FreeGroup.of FormalAB.A)⁻¹ * FreeGroup.of FormalAB.B * FreeGroup.of FormalAB.A)
      * (FreeGroup.of FormalAB.A * (FreeGroup.of FormalAB.B)⁻¹)⁻¹
      * ((FreeGroup.of FormalAB.A)⁻¹ * FreeGroup.of FormalAB.B * FreeGroup.of FormalAB.A)⁻¹)
    (Set.mem_insert _ _)
  simp only [map_mul, map_inv] at h
  exact h

/-- The second relator of `F₁`, in `F₁`. -/
lemma F1_rel2 :
    ((of FormalAB.A : F1) * (of FormalAB.B)⁻¹)
      * ((of FormalAB.A)⁻¹ ^ 2 * of FormalAB.B * of FormalAB.A ^ 2)
      * ((of FormalAB.A : F1) * (of FormalAB.B)⁻¹)⁻¹
      * ((of FormalAB.A : F1)⁻¹ ^ 2 * of FormalAB.B * of FormalAB.A ^ 2)⁻¹ = 1 := by
  have h := one_of_mem (rels := relsF1)
    (x := (FreeGroup.of FormalAB.A * (FreeGroup.of FormalAB.B)⁻¹)
      * ((FreeGroup.of FormalAB.A)⁻¹ ^ 2 * FreeGroup.of FormalAB.B * FreeGroup.of FormalAB.A ^ 2)
      * (FreeGroup.of FormalAB.A * (FreeGroup.of FormalAB.B)⁻¹)⁻¹
      * ((FreeGroup.of FormalAB.A)⁻¹ ^ 2 * FreeGroup.of FormalAB.B * FreeGroup.of FormalAB.A ^ 2)⁻¹)
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [map_mul, map_inv, map_pow] at h
  exact h

lemma Y_h2 : (of FormalAB.B : F1)⁻¹ * Y 2 * of FormalAB.B = Y 3 := by
  rw [Y_eq_genY, genY_two, genY_succ_succ _ _ 1, genY_two]
  exact conj_eq_of_comm_relator _ _ _ F1_rel1

lemma Y_h3 : (of FormalAB.B : F1)⁻¹ * Y 3 * of FormalAB.B = Y 4 := by
  rw [Y_eq_genY, genY_three, genY_succ_succ _ _ 2, genY_three]
  exact conj_eq_of_comm_relator _ _ _ F1_rel2

/-- Line (3.2): `Yₖ⁻¹ Yₙ Yₖ = Y_{n+1}` for `k < n`. -/
theorem Y_conj_eq_Y_succ' (k n : ℕ) (hkn : k < n) : (Y k)⁻¹ * Y n * Y k = Y (n + 1) := by
  rw [Y_eq_genY]
  exact genY_conj _ _ (by rw [← Y_eq_genY]; exact Y_h2) (by rw [← Y_eq_genY]; exact Y_h3) k n hkn

/-- Line (3.3): `[A⁻¹B, Yₘ] = 1` for `m ≥ 3`. -/
theorem commutator_invA_B_Y_eq_one' (m : ℕ) (hm : 3 ≤ m) :
    ((of FormalAB.A : F1)⁻¹ * of FormalAB.B) * Y m
      * ((of FormalAB.A : F1)⁻¹ * of FormalAB.B)⁻¹ * (Y m)⁻¹ = 1 := by
  apply comm_relator_invA_B
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := Y_conj_eq_Y_succ' 2 (m' + 1) (by omega)
  rw [Y_eq_genY, genY_two, genY_succ_succ] at h
  rw [Y_eq_genY]
  exact h

end S3
end CannonFloydParry

/-! # Section 3: `F₂`, and Theorem 3.1 (`F₁ ≅ F₂`) -/

namespace CannonFloydParry
namespace S3

open PresentedGroup

/-- The defining relations of `F₂`. -/
lemma F2_rel (k n : ℕ) (hkn : k < n) : (of k : F2)⁻¹ * of n * of k = of (n + 1) := by
  have h := one_of_mem (rels := relsF2)
    (x := (FreeGroup.of k)⁻¹ * FreeGroup.of n * FreeGroup.of k * (FreeGroup.of (n + 1))⁻¹)
    ⟨k, n, hkn, rfl⟩
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- `Xₙ = X₀^{-(n-1)} X₁ X₀^{n-1}` in `F₂`, so `X₀` and `X₁` generate. -/
theorem of_succ_eq_conj_F2' (n : ℕ) :
    (of (n + 1) : F2) = (of 0 ^ n)⁻¹ * of 1 * of 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← F2_rel 0 (n + 1) (by omega), ih, pow_succ, mul_inv_rev]; group

/-- The generators of `F₂` form the generic family for `a = X₀`, `b = X₁`. -/
lemma of_eq_genY_F2 : (of : ℕ → F2) = genY (of 0) (of 1) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show of (n + 1) = genY (of 0) (of 1) (n + 1)
    rw [genY_succ]; exact of_succ_eq_conj_F2' n

/-- `X₀⁻¹ X₁ X₀ = X₂` in `F₂`. -/
lemma F2_two : ((of 0 : F2)⁻¹ * of 1 * of 0) = of 2 := by
  have := of_succ_eq_conj_F2' 1
  rw [pow_one] at this
  exact this.symm

/-- `X₀⁻² X₁ X₀² = X₃` in `F₂`. -/
lemma F2_three : ((of 0 : F2)⁻¹ ^ 2 * of 1 * of 0 ^ 2) = of 3 := by
  rw [inv_pow]; exact (of_succ_eq_conj_F2' 2).symm

/-- Theorem 3.1, first step: the relators of `F₁` hold in `F₂` under `A ↦ X₀`, `B ↦ X₁`. -/
theorem relsF1_lift_eq_one_F2' : ∀ r ∈ relsF1, FreeGroup.lift symF2 r = 1 := by
  intro r hr
  simp only [relsF1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, symF2]
    rw [F2_two]
    exact comm_relator_of_conj_eq _ _ _
      (by rw [F2_rel 1 2 (by norm_num), F2_rel 0 2 (by norm_num)])
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, symF2]
    rw [F2_three]
    exact comm_relator_of_conj_eq _ _ _
      (by rw [F2_rel 1 3 (by norm_num), F2_rel 0 3 (by norm_num)])

/-- The relators of `F₂` hold in `F₁` under `Xₙ ↦ Yₙ`. -/
theorem relsF2_lift_eq_one_Y : ∀ r ∈ relsF2, FreeGroup.lift Y r = 1 := by
  rintro r ⟨k, n, hkn, rfl⟩
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [Y_conj_eq_Y_succ' k n hkn, mul_inv_cancel]

/-- The homomorphism `F₁ → F₂`, `A ↦ X₀`, `B ↦ X₁`. -/
noncomputable def φ12 : F1 →* F2 := toGroup relsF1_lift_eq_one_F2'

/-- The homomorphism `F₂ → F₁`, `Xₙ ↦ Yₙ`. -/
noncomputable def φ21 : F2 →* F1 := toGroup relsF2_lift_eq_one_Y

lemma φ12_A : φ12 (of FormalAB.A) = of 0 := toGroup.of _
lemma φ12_B : φ12 (of FormalAB.B) = of 1 := toGroup.of _
lemma φ21_of (n : ℕ) : φ21 (of n) = Y n := toGroup.of _

lemma φ12_Y (n : ℕ) : φ12 (Y n) = of n := by
  cases n with
  | zero => exact φ12_A
  | succ n =>
    show φ12 ((of FormalAB.A ^ n)⁻¹ * of FormalAB.B * of FormalAB.A ^ n) = _
    rw [map_mul, map_mul, map_inv, map_pow, φ12_A, φ12_B]
    exact (of_succ_eq_conj_F2' n).symm

/-- Theorem 3.1: `F₁ ≅ F₂` with `A ↦ X₀`, `B ↦ X₁`. -/
theorem exists_mulEquiv_F1_F2' :
    ∃ e : F1 ≃* F2, e (of FormalAB.A) = of 0 ∧ e (of FormalAB.B) = of 1 := by
  refine ⟨MonoidHom.toMulEquiv φ12 φ21 ?_ ?_, φ12_A, φ12_B⟩
  · apply PresentedGroup.ext
    intro x
    cases x
    · simp [MonoidHom.comp_apply, φ12_A, φ21_of, Y]
    · simp [MonoidHom.comp_apply, φ12_B, φ21_of, Y]
  · apply PresentedGroup.ext
    intro n
    simp [MonoidHom.comp_apply, φ21_of, φ12_Y]

end S3
end CannonFloydParry

open CannonFloydParry

theorem solution : ∀ r ∈ relsF1, FreeGroup.lift symF2 r = 1 :=
  S3.relsF1_lift_eq_one_F2'
