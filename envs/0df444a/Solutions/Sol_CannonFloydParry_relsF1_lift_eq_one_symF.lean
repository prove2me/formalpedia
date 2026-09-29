-- Prove2me | solution 1 for CannonFloydParry.relsF1_lift_eq_one_symF
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-17T22:11:59.292041+00:00
-- url     : https://prove2.me/submissions/83074442-57d3-4cc2-9950-b27c4119a734

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

/-! # Section 3: the relators of `F₁` hold in `F`

`A B⁻¹` is the identity on `[3/4, 1]`, while `A⁻¹ B A` and `A⁻² B A²` are the identity on
`[0, 3/4]`; maps fixing complementary intervals pointwise commute.  From the two relators,
`S3_gen` gives all the relations `Xₖ⁻¹ Xₙ Xₖ = X_{n+1}` in `F`. -/

namespace CannonFloydParry
namespace S3

lemma coe_mapA' (z : UI) : (mapA z : ℝ) = aFun (z : ℝ) := by
  rw [mapA, restrict_coe]; rfl

lemma coe_mapB' (z : UI) : (mapB z : ℝ) = bFun (z : ℝ) := by
  rw [mapB, restrict_coe]; rfl

lemma mul_apply' (f g : UI ≃o UI) (z : UI) : (f * g) z = f (g z) := rfl

lemma inv_apply' (f : UI ≃o UI) (z : UI) : f⁻¹ z = f.symm z := rfl

/-- Order automorphisms of `[0,1]` fixing `[c, 1]` and `[0, c]` pointwise, respectively, commute. -/
lemma comm_of_fixed (c : UI) (f g : UI ≃o UI)
    (hf : ∀ z, c ≤ z → f z = z) (hg : ∀ z, z ≤ c → g z = z) : f * g = g * f := by
  refine OrderIso.ext (funext fun z => ?_)
  rw [mul_apply', mul_apply']
  rcases le_total z c with hz | hz
  · have hfz : f z ≤ c := by
      have := f.monotone hz
      rwa [hf c le_rfl] at this
    rw [hg z hz, hg (f z) hfz]
  · have hgz : c ≤ g z := by
      have := g.monotone hz
      rwa [hg c le_rfl] at this
    rw [hf z hz, hf (g z) hgz]

lemma mapB_fix {z : UI} (h : (z : ℝ) ≤ 1 / 2) : mapB z = z := by
  ext1
  rw [coe_mapB', bFun_of_le_half h]

lemma mapA_le_half {z : UI} (h : (z : ℝ) ≤ 3 / 4) : (mapA z : ℝ) ≤ 1 / 2 := by
  rw [coe_mapA']
  rcases le_or_gt (z : ℝ) (1 / 2) with h1 | h1
  · rw [aFun_of_mem1 z.2.1 h1]; linarith
  · rw [aFun_of_mem2 h1.le h]; linarith

/-- `A⁻¹ B A` fixes `[0, 3/4]` pointwise. -/
lemma conj1_fix {z : UI} (h : (z : ℝ) ≤ 3 / 4) : (mapA⁻¹ * mapB * mapA) z = z := by
  rw [mul_apply', mul_apply', mapB_fix (mapA_le_half h), inv_apply', OrderIso.symm_apply_apply]

/-- `A⁻² B A²` fixes `[0, 3/4]` pointwise. -/
lemma conj2_fix {z : UI} (h : (z : ℝ) ≤ 3 / 4) : (mapA⁻¹ ^ 2 * mapB * mapA ^ 2) z = z := by
  have h1 : (mapA z : ℝ) ≤ 3 / 4 := by linarith [mapA_le_half h]
  have e : (mapA⁻¹ ^ 2 * mapB * mapA ^ 2 : UI ≃o UI) = mapA⁻¹ * (mapA⁻¹ * mapB * mapA) * mapA := by
    rw [inv_pow, pow_two, mul_inv_rev]; simp only [mul_assoc]
  rw [e, mul_apply', mul_apply', conj1_fix h1, inv_apply', OrderIso.symm_apply_apply]

/-- `A B⁻¹` fixes `[3/4, 1]` pointwise. -/
lemma AB_fix {z : UI} (h : 3 / 4 ≤ (z : ℝ)) : (mapA * mapB⁻¹) z = z := by
  rw [mul_apply']
  set w := mapB⁻¹ z with hw
  have hBw : mapB w = z := by
    rw [hw, inv_apply', OrderIso.apply_symm_apply]
  have hw78 : 7 / 8 ≤ (w : ℝ) := by
    by_contra hlt
    have hlt' : (w : ℝ) < 7 / 8 := not_le.mp hlt
    have h1 : bFun (w : ℝ) < bFun (7 / 8) := strictMono_bFun hlt'
    rw [bFun_of_mem2 (z := 7 / 8) (by norm_num) (by norm_num)] at h1
    have h2 : (mapB w : ℝ) = bFun (w : ℝ) := coe_mapB' w
    rw [hBw] at h2
    linarith
  have hz : (z : ℝ) = 2 * (w : ℝ) - 1 := by
    rw [← hBw, coe_mapB', bFun_of_mem3 hw78 w.2.2]
  ext1
  rw [coe_mapA', aFun_of_mem3 (by linarith) w.2.2, hz]

/-- The relators of `F₁` hold in `F` under `A ↦ mapA`, `B ↦ mapB`. -/
theorem relsF1_lift_eq_one_symF' : ∀ r ∈ relsF1, FreeGroup.lift symF r = 1 := by
  intro r hr
  simp only [relsF1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, symF]
    have hc : (mapA * mapB⁻¹) * (mapA⁻¹ * mapB * mapA) = (mapA⁻¹ * mapB * mapA) * (mapA * mapB⁻¹) :=
      comm_of_fixed ⟨3 / 4, by norm_num, by norm_num⟩ _ _
        (fun z hz => AB_fix (Subtype.coe_le_coe.mpr hz)) (fun z hz => conj1_fix (Subtype.coe_le_coe.mpr hz))
    rw [hc]; group
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, symF]
    have hc : (mapA * mapB⁻¹) * (mapA⁻¹ ^ 2 * mapB * mapA ^ 2)
        = (mapA⁻¹ ^ 2 * mapB * mapA ^ 2) * (mapA * mapB⁻¹) :=
      comm_of_fixed ⟨3 / 4, by norm_num, by norm_num⟩ _ _
        (fun z hz => AB_fix (Subtype.coe_le_coe.mpr hz)) (fun z hz => conj2_fix (Subtype.coe_le_coe.mpr hz))
    rw [hc]; group

/-- `X` is the generic family for `a = mapA`, `b = mapB`. -/
lemma X_eq_genY : X = genY mapA mapB := by
  funext n; cases n <;> rfl

lemma X_h2 : mapB⁻¹ * X 2 * mapB = X 3 := by
  rw [X_eq_genY, genY_two, genY_succ_succ _ _ 1, genY_two]
  apply conj_eq_of_comm_relator
  have h := relsF1_lift_eq_one_symF' _ (Set.mem_insert _ _)
  simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, symF] using h

lemma X_h3 : mapB⁻¹ * X 3 * mapB = X 4 := by
  rw [X_eq_genY, genY_three, genY_succ_succ _ _ 2, genY_three]
  apply conj_eq_of_comm_relator
  have h := relsF1_lift_eq_one_symF' _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simpa only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, symF] using h

/-- The relations `Xₖ⁻¹ Xₙ Xₖ = X_{n+1}` (`k < n`) in `F`. -/
theorem X_conj (k n : ℕ) (hkn : k < n) : (X k)⁻¹ * X n * X k = X (n + 1) := by
  rw [X_eq_genY]
  exact genY_conj _ _ (by rw [← X_eq_genY]; exact X_h2) (by rw [← X_eq_genY]; exact X_h3) k n hkn

end S3
end CannonFloydParry

open CannonFloydParry

theorem solution : ∀ r ∈ relsF1, FreeGroup.lift symF r = 1 :=
  S3.relsF1_lift_eq_one_symF'
