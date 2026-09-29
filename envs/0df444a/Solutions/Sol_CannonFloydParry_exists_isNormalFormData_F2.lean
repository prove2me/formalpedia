-- Prove2me | solution 1 for CannonFloydParry.exists_isNormalFormData_F2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-17T22:14:18.292876+00:00
-- url     : https://prove2.me/submissions/f27e60b4-e535-4850-85fa-9ceae5f757c0

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

/-! # Section 3: positive words in `F₂`

Every element of `F₂` is `P N⁻¹` with `P`, `N` positive words (CFP p. 226): a generator or an
inverse generator multiplied into such a product is absorbed, using only the defining relations
`xₖ⁻¹ xₙ xₖ = x_{n+1}`. -/

namespace CannonFloydParry
namespace S3

open PresentedGroup

/-! ### Words -/

lemma wordF2_eq (cs : List ℕ) : wordF2 cs = wordFromF2 0 cs := rfl

lemma wordFromF2_nil (i : ℕ) : wordFromF2 i [] = 1 := rfl

lemma wordFromF2_cons (i c : ℕ) (cs : List ℕ) :
    wordFromF2 i (c :: cs) = (of i : F2) ^ c * wordFromF2 (i + 1) cs := rfl

lemma wordFromF2_replicate_zero : ∀ (n i : ℕ), wordFromF2 i (List.replicate n 0) = 1
  | 0, _ => rfl
  | n + 1, i => by
    rw [List.replicate_succ, wordFromF2_cons, pow_zero, one_mul]
    exact wordFromF2_replicate_zero n (i + 1)

lemma wordFromF2_append : ∀ (cs : List ℕ) (i : ℕ) (ds : List ℕ),
    wordFromF2 i (cs ++ ds) = wordFromF2 i cs * wordFromF2 (i + cs.length) ds := by
  intro cs
  induction cs with
  | nil => intro i ds; simp [wordFromF2_nil]
  | cons c cs ih =>
    intro i ds
    rw [List.cons_append, wordFromF2_cons, wordFromF2_cons, ih, mul_assoc, List.length_cons,
      show i + 1 + cs.length = i + (cs.length + 1) by omega]

lemma wordFromF2_pad {a b : ℕ} (hab : a ≤ b) (es : List ℕ) :
    wordFromF2 b es = wordFromF2 a (List.replicate (b - a) 0 ++ es) := by
  rw [wordFromF2_append, wordFromF2_replicate_zero, one_mul, List.length_replicate,
    show a + (b - a) = b by omega]

lemma of_eq_wordF2 (m : ℕ) : (of m : F2) = wordF2 (List.replicate m 0 ++ [1]) := by
  rw [wordF2_eq, wordFromF2_append, wordFromF2_replicate_zero, one_mul, List.length_replicate,
    zero_add, wordFromF2_cons, wordFromF2_nil, pow_one, mul_one]

/-! ### Pushing a generator through a positive word -/

lemma x_comm {k n : ℕ} (hkn : k < n) : (of n : F2) * of k = of k * of (n + 1) := by
  rw [← F2_rel k n hkn]; group

lemma x_pow_comm {i k : ℕ} (hik : i < k) :
    ∀ d : ℕ, (of k : F2) * of i ^ d = of i ^ d * of (k + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, x_comm (by omega), ← mul_assoc, ← pow_succ,
      show k + d + 1 = k + (d + 1) by omega]

lemma x_mul_wordFrom : ∀ (ds : List ℕ) (k i : ℕ),
    ∃ es, (of k : F2) * wordFromF2 i ds = wordFromF2 (min i k) es := by
  intro ds
  induction ds with
  | nil =>
    intro k i
    refine ⟨List.replicate (k - min i k) 0 ++ [1], ?_⟩
    rw [wordFromF2_nil, mul_one, ← wordFromF2_pad (by omega), wordFromF2_cons, wordFromF2_nil,
      pow_one, mul_one]
  | cons d ds ih =>
    intro k i
    rcases Nat.lt_or_ge i k with hik | hki
    · -- `k > i`: commute past `xᵢ ^ d`, raising the index
      obtain ⟨es', hes'⟩ := ih (k + d) (i + 1)
      rw [show min (i + 1) (k + d) = i + 1 by omega] at hes'
      refine ⟨d :: es', ?_⟩
      rw [wordFromF2_cons, ← mul_assoc, x_pow_comm hik, mul_assoc, hes', wordFromF2_cons,
        show min i k = i by omega]
    · rcases Nat.eq_or_lt_of_le hki with rfl | hki'
      · -- `k = i`: absorbed into the leading power
        refine ⟨(d + 1) :: ds, ?_⟩
        rw [wordFromF2_cons, ← mul_assoc, ← pow_succ', wordFromF2_cons, min_self]
      · -- `k < i`: the generator becomes a new leading letter, with zero padding
        refine ⟨1 :: (List.replicate (i - (k + 1)) 0 ++ d :: ds), ?_⟩
        rw [wordFromF2_pad (show k + 1 ≤ i by omega) (d :: ds), wordFromF2_cons, pow_one,
          show min i k = k by omega]

lemma x_pow_mul_wordFrom : ∀ (c k m : ℕ) (es : List ℕ),
    ∃ es', (of k : F2) ^ c * wordFromF2 m es = wordFromF2 (min m k) es' := by
  intro c
  induction c with
  | zero =>
    intro k m es
    exact ⟨_, by rw [pow_zero, one_mul, wordFromF2_pad (Nat.min_le_left m k)]⟩
  | succ c ih =>
    intro k m es
    obtain ⟨es₁, h₁⟩ := ih k m es
    obtain ⟨es₂, h₂⟩ := x_mul_wordFrom es₁ k (min m k)
    refine ⟨es₂, ?_⟩
    rw [pow_succ', mul_assoc, h₁, h₂, show min (min m k) k = min m k by omega]

lemma wordFrom_mul_wordFrom : ∀ (cs : List ℕ) (i j : ℕ) (ds : List ℕ),
    ∃ es, wordFromF2 i cs * wordFromF2 j ds = wordFromF2 (min i j) es := by
  intro cs
  induction cs with
  | nil =>
    intro i j ds
    exact ⟨_, by rw [wordFromF2_nil, one_mul, wordFromF2_pad (Nat.min_le_right i j)]⟩
  | cons c cs ih =>
    intro i j ds
    obtain ⟨es₁, h₁⟩ := ih (i + 1) j ds
    obtain ⟨es₂, h₂⟩ := x_pow_mul_wordFrom c i (min (i + 1) j) es₁
    refine ⟨es₂, ?_⟩
    rw [wordFromF2_cons, mul_assoc, h₁, h₂, show min (min (i + 1) j) i = min i j by omega]

/-- Positive words are closed under multiplication. -/
lemma pos_mul_pos (cs ds : List ℕ) : ∃ es, wordF2 cs * wordF2 ds = wordF2 es := by
  obtain ⟨es, hes⟩ := wordFrom_mul_wordFrom cs 0 0 ds
  exact ⟨es, by rw [wordF2_eq, wordF2_eq, wordF2_eq, hes, min_self]⟩

/-! ### Pushing an inverse generator through a positive word -/

lemma x_inv_comm_lt {i j : ℕ} (hij : i < j) : (of i : F2)⁻¹ * of j = of (j + 1) * (of i)⁻¹ := by
  rw [← F2_rel i j hij]; group

lemma x_inv_comm_pow_lt {i j : ℕ} (hij : i < j) :
    ∀ c : ℕ, (of i : F2)⁻¹ * of j ^ c = of (j + 1) ^ c * (of i)⁻¹ := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, x_inv_comm_lt hij, ← mul_assoc, ← pow_succ]

lemma x_inv_mul_wordFrom_of_lt : ∀ (cs : List ℕ) (i j : ℕ), i < j →
    (of i : F2)⁻¹ * wordFromF2 j cs = wordFromF2 (j + 1) cs * (of i)⁻¹ := by
  intro cs
  induction cs with
  | nil => intro i j _; simp [wordFromF2_nil]
  | cons c cs ih =>
    intro i j hij
    rw [wordFromF2_cons, wordFromF2_cons, ← mul_assoc, x_inv_comm_pow_lt hij, mul_assoc,
      ih i (j + 1) (by omega), mul_assoc]

lemma x_inv_mul_x_pow_gt {i j : ℕ} (hji : j < i) (c : ℕ) :
    (of i : F2)⁻¹ * of j ^ c = of j ^ c * (of (i + c))⁻¹ := by
  calc (of i : F2)⁻¹ * of j ^ c
      = (of i)⁻¹ * (of j ^ c * of (i + c)) * (of (i + c))⁻¹ := by group
    _ = (of i)⁻¹ * (of i * of j ^ c) * (of (i + c))⁻¹ := by rw [x_pow_comm hji c]
    _ = of j ^ c * (of (i + c))⁻¹ := by group

/-- An inverse generator times a positive word is a positive word times `1` or an inverse
generator. -/
lemma x_inv_mul_wordFrom : ∀ (cs : List ℕ) (i j : ℕ),
    ∃ (cs' : List ℕ) (q : F2), (q = 1 ∨ ∃ m, q = (of m)⁻¹) ∧
      (of i : F2)⁻¹ * wordFromF2 j cs = wordFromF2 j cs' * q := by
  intro cs
  induction cs with
  | nil =>
    intro i j
    exact ⟨[], (of i)⁻¹, Or.inr ⟨i, rfl⟩, by simp [wordFromF2_nil]⟩
  | cons c cs ih =>
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · refine ⟨0 :: c :: cs, (of i)⁻¹, Or.inr ⟨i, rfl⟩, ?_⟩
      rw [x_inv_mul_wordFrom_of_lt _ _ _ hij, wordFromF2_cons j 0, pow_zero, one_mul]
    · rcases c with _ | c
      · refine ⟨0 :: 0 :: cs, (of i)⁻¹, Or.inr ⟨i, rfl⟩, ?_⟩
        rw [wordFromF2_cons, pow_zero, one_mul, x_inv_mul_wordFrom_of_lt _ _ _ (by omega),
          wordFromF2_cons i 0, pow_zero, one_mul, wordFromF2_cons (i + 1) 0, pow_zero, one_mul]
      · refine ⟨c :: cs, 1, Or.inl rfl, ?_⟩
        rw [wordFromF2_cons, pow_succ', ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
          wordFromF2_cons, mul_one]
    · obtain ⟨cs', q, hq, h⟩ := ih (i + c) (j + 1)
      refine ⟨c :: cs', q, hq, ?_⟩
      rw [wordFromF2_cons, ← mul_assoc, x_inv_mul_x_pow_gt hji c, mul_assoc, h, wordFromF2_cons,
        mul_assoc]

/-- Every element of `F₂` is a positive word times the inverse of a positive word. -/
theorem exists_wordF2_pair (g : F2) : ∃ as bs : List ℕ, g = wordF2 bs * (wordF2 as)⁻¹ := by
  have hg : g ∈ Subgroup.closure (Set.range (of : ℕ → F2)) := by
    rw [closure_range_of]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨[], [], by simp [wordF2_eq, wordFromF2_nil]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨as, bs, rfl⟩ := ih
    obtain ⟨es, hes⟩ := pos_mul_pos (List.replicate n 0 ++ [1]) bs
    exact ⟨as, es, by rw [← mul_assoc, ← hes, ← of_eq_wordF2]⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨as, bs, rfl⟩ := ih
    obtain ⟨cs', q, hq, h⟩ := x_inv_mul_wordFrom bs n 0
    rw [← wordF2_eq, ← wordF2_eq] at h
    rcases hq with rfl | ⟨m, rfl⟩
    · exact ⟨as, cs', by rw [← mul_assoc, h, mul_one]⟩
    · obtain ⟨es, hes⟩ := pos_mul_pos as (List.replicate m 0 ++ [1])
      refine ⟨es, cs', ?_⟩
      rw [← mul_assoc, h, ← hes, ← of_eq_wordF2, mul_inv_rev, mul_assoc]

end S3
end CannonFloydParry

/-! # Section 3: normal forms in `F₂` (Theorem 3.4, existence)

Starting from `P N⁻¹` (`S3_pos`), pad to equal length and then reduce: a common trailing zero is
dropped; a common positive last exponent is cancelled; and an interior pair `aₖ, bₖ > 0` with
`a_{k+1} = b_{k+1} = 0` is shortened by conjugating the tail by `xₖ`, which lowers every index
`≥ k+2` by one (CFP p. 226).  Each step lowers `Σaᵢ + Σbᵢ + length`, so the process stops at a
normal form unless the element is `1`. -/

namespace CannonFloydParry
namespace S3

open PresentedGroup

/-! ### Conjugating a tail by `xₖ` -/

lemma x_conj_x {k j : ℕ} (h : k + 1 ≤ j) : (of k : F2) * of (j + 1) * (of k)⁻¹ = of j := by
  rw [← F2_rel k j (by omega)]; group

lemma x_conj_x_pow {k j : ℕ} (h : k + 1 ≤ j) (c : ℕ) :
    (of k : F2) * of (j + 1) ^ c * (of k)⁻¹ = of j ^ c := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, pow_succ, ← ih, ← x_conj_x h]; group

lemma x_conj_wordFrom : ∀ (cs : List ℕ) (k j : ℕ), k + 1 ≤ j →
    (of k : F2) * wordFromF2 (j + 1) cs * (of k)⁻¹ = wordFromF2 j cs := by
  intro cs
  induction cs with
  | nil => intro k j _; simp [wordFromF2_nil]
  | cons c cs ih =>
    intro k j h
    rw [wordFromF2_cons, wordFromF2_cons, ← x_conj_x_pow h c, ← ih k (j + 1) (by omega)]
    group

/-! ### List bookkeeping -/

lemma getD_eq_getElem' (l : List ℕ) (i : ℕ) (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

lemma eq_take_append_cons_cons (l : List ℕ) (i : ℕ) (h : i + 1 < l.length) :
    l = l.take i ++ l.getD i 0 :: l.getD (i + 1) 0 :: l.drop (i + 1 + 1) := by
  rw [getD_eq_getElem' l i (by omega), getD_eq_getElem' l (i + 1) h,
    ← List.drop_eq_getElem_cons h, ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]

lemma getD_append_singleton : ∀ (l : List ℕ) (a : ℕ), (l ++ [a]).getD l.length 0 = a
  | [], a => rfl
  | x :: l, a => by
    simp only [List.cons_append, List.length_cons, List.getD_cons_succ]
    exact getD_append_singleton l a

lemma tail_word (bs₁ : List ℕ) (n b : ℕ) (h : bs₁.length = n) :
    wordFromF2 0 (bs₁ ++ [b]) = wordFromF2 0 bs₁ * (of n : F2) ^ b := by
  rw [wordFromF2_append, h, zero_add, wordFromF2_cons, wordFromF2_nil, mul_one]

/-! ### The three reductions -/

/-- Cancelling an interior pair `aₖ, bₖ > 0` with `a_{k+1} = b_{k+1} = 0`. -/
lemma surgery (as bs : List ℕ) (k : ℕ) (hlen : as.length = bs.length) (hk : k + 1 < as.length)
    (hak : 0 < as.getD k 0) (hbk : 0 < bs.getD k 0)
    (hak1 : as.getD (k + 1) 0 = 0) (hbk1 : bs.getD (k + 1) 0 = 0) :
    ∃ as' bs' : List ℕ, as'.length = bs'.length ∧
      as'.sum + bs'.sum + as'.length + 1 ≤ as.sum + bs.sum + as.length ∧
      wordFromF2 0 bs * (wordFromF2 0 as)⁻¹ = wordFromF2 0 bs' * (wordFromF2 0 as')⁻¹ := by
  have hdA := eq_take_append_cons_cons as k hk
  have hdB := eq_take_append_cons_cons bs k (by omega)
  obtain ⟨a', ha'⟩ : ∃ a', as.getD k 0 = a' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hak).symm⟩
  obtain ⟨b', hb'⟩ : ∃ b', bs.getD k 0 = b' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hbk).symm⟩
  rw [ha', hak1] at hdA
  rw [hb', hbk1] at hdB
  have hA1 : (as.take k).length = k := by simp; omega
  have hB1 : (bs.take k).length = k := by simp; omega
  generalize as.take k = as₁ at hdA hA1
  generalize bs.take k = bs₁ at hdB hB1
  generalize as.drop (k + 1 + 1) = as₂ at hdA
  generalize bs.drop (k + 1 + 1) = bs₂ at hdB
  refine ⟨as₁ ++ a' :: as₂, bs₁ ++ b' :: bs₂, ?_, ?_, ?_⟩
  · have := congrArg List.length hdA
    have := congrArg List.length hdB
    simp only [List.length_append, List.length_cons] at *
    omega
  · have := congrArg List.length hdA
    have := congrArg List.sum hdA
    have := congrArg List.sum hdB
    simp only [List.length_append, List.length_cons, List.sum_append, List.sum_cons] at *
    omega
  · rw [hdA, hdB]
    simp only [wordFromF2_append, wordFromF2_cons, hA1, hB1, zero_add, pow_zero, one_mul]
    rw [← x_conj_wordFrom as₂ k (k + 1) (by omega), ← x_conj_wordFrom bs₂ k (k + 1) (by omega)]
    group

/-- The reduction, with `μ` as fuel bounding `Σaᵢ + Σbᵢ + length`. -/
theorem reduce : ∀ (μ : ℕ) (as bs : List ℕ), as.length = bs.length →
    as.sum + bs.sum + as.length ≤ μ →
    wordFromF2 0 bs * (wordFromF2 0 as)⁻¹ ≠ 1 →
    ∃ as' bs', IsNormalFormData as' bs' ∧
      wordFromF2 0 bs * (wordFromF2 0 as)⁻¹ = wordFromF2 0 bs' * (wordFromF2 0 as')⁻¹ := by
  intro μ
  induction μ with
  | zero =>
    intro as bs hlen hμ hne
    have ha : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha; subst hb
    exact absurd (by simp [wordFromF2_nil]) hne
  | succ μ ih =>
    intro as bs hlen hμ hne
    rcases List.eq_nil_or_concat as with rfl | ⟨as₁, a, rfl⟩
    · have hb : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst hb
      exact absurd (by simp [wordFromF2_nil]) hne
    rw [List.concat_eq_append] at *
    rcases List.eq_nil_or_concat bs with rfl | ⟨bs₁, b, rfl⟩
    · simp at hlen
    rw [List.concat_eq_append] at *
    have hlen1 : as₁.length = bs₁.length := by simpa using hlen
    have hwa := tail_word as₁ as₁.length a rfl
    have hwb := tail_word bs₁ as₁.length b hlen1.symm
    -- interior violation first
    by_cases hv : ∃ k, k + 1 < (as₁ ++ [a]).length ∧ 0 < (as₁ ++ [a]).getD k 0 ∧
        0 < (bs₁ ++ [b]).getD k 0 ∧ (as₁ ++ [a]).getD (k + 1) 0 = 0 ∧
        (bs₁ ++ [b]).getD (k + 1) 0 = 0
    · obtain ⟨k, hk, hak, hbk, hak1, hbk1⟩ := hv
      obtain ⟨as', bs', hlen', hμ', heq⟩ := surgery _ _ k hlen hk hak hbk hak1 hbk1
      obtain ⟨as'', bs'', hnf, heq'⟩ := ih as' bs' hlen' (by omega) (by rw [← heq]; exact hne)
      exact ⟨as'', bs'', hnf, heq.trans heq'⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb
    · -- both last entries zero: drop them
      have heq : wordFromF2 0 (bs₁ ++ [0]) * (wordFromF2 0 (as₁ ++ [0]))⁻¹
          = wordFromF2 0 bs₁ * (wordFromF2 0 as₁)⁻¹ := by
        rw [hwa, hwb, pow_zero, mul_one, mul_one]
      obtain ⟨as'', bs'', hnf, heq'⟩ := ih as₁ bs₁ hlen1
        (by simp only [List.length_append, List.length_singleton, List.sum_append,
              List.sum_singleton] at hμ; omega)
        (by rw [← heq]; exact hne)
      exact ⟨as'', bs'', hnf, heq.trans heq'⟩
    · -- `a = 0 < b`, no interior violation: already a normal form
      refine ⟨as₁ ++ [0], bs₁ ++ [b], ⟨by simp, by simpa using hlen, ?_, ?_⟩, rfl⟩
      · left
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        rw [getD_append_singleton, hlen1, getD_append_singleton]
        exact ⟨rfl, hb⟩
      · intro k hk hak hbk
        by_contra hcon
        exact hv ⟨k, hk, hak, hbk, by omega, by omega⟩
    · -- `b = 0 < a`
      refine ⟨as₁ ++ [a], bs₁ ++ [0], ⟨by simp, by simpa using hlen, ?_, ?_⟩, rfl⟩
      · right
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        rw [getD_append_singleton, hlen1, getD_append_singleton]
        exact ⟨ha, rfl⟩
      · intro k hk hak hbk
        by_contra hcon
        exact hv ⟨k, hk, hak, hbk, by omega, by omega⟩
    · -- both positive: cancel one from each
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have heq : wordFromF2 0 (bs₁ ++ [b' + 1]) * (wordFromF2 0 (as₁ ++ [a' + 1]))⁻¹
          = wordFromF2 0 (bs₁ ++ [b']) * (wordFromF2 0 (as₁ ++ [a']))⁻¹ := by
        rw [hwa, hwb, tail_word as₁ as₁.length a' rfl, tail_word bs₁ as₁.length b' hlen1.symm]
        group
      obtain ⟨as'', bs'', hnf, heq'⟩ := ih (as₁ ++ [a']) (bs₁ ++ [b']) (by simpa using hlen)
        (by simp only [List.length_append, List.length_singleton, List.sum_append,
              List.sum_singleton] at hμ ⊢; omega)
        (by rw [← heq]; exact hne)
      exact ⟨as'', bs'', hnf, heq.trans heq'⟩

/-- Theorem 3.4 for `F₂`, existence half: every nontrivial element has a normal form. -/
theorem exists_isNormalFormData_F2' (x : F2) (hx : x ≠ 1) :
    ∃ as bs : List ℕ, IsNormalFormData as bs ∧ x = wordF2 bs * (wordF2 as)⁻¹ := by
  obtain ⟨as, bs, rfl⟩ := exists_wordF2_pair x
  have e1 : wordF2 as = wordFromF2 0 (as ++ List.replicate (max as.length bs.length - as.length) 0) := by
    rw [wordF2_eq, wordFromF2_append, wordFromF2_replicate_zero, mul_one]
  have e2 : wordF2 bs = wordFromF2 0 (bs ++ List.replicate (max as.length bs.length - bs.length) 0) := by
    rw [wordF2_eq, wordFromF2_append, wordFromF2_replicate_zero, mul_one]
  rw [e1, e2] at hx ⊢
  obtain ⟨as', bs', hnf, heq⟩ := reduce _ _ _ (by simp only [List.length_append, List.length_replicate]; omega) le_rfl hx
  exact ⟨as', bs', hnf, heq⟩

end S3
end CannonFloydParry

open CannonFloydParry

theorem solution (x : F2) (hx : x ≠ 1) :
    ∃ as bs : List ℕ, IsNormalFormData as bs ∧ x = wordF2 bs * (wordF2 as)⁻¹ :=
  S3.exists_isNormalFormData_F2' x hx
