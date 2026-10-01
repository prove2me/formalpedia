-- Prove2me | solution 3 for CannonFloydParry.not_elementaryAmenable_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-01T08:45:48.588345+00:00
-- url     : https://prove2.me/submissions/146f3fcb-4379-4040-856c-908e84d54ec4

import Theorems.Thm_CannonFloydParry_mul_comm_quotient_of_ne_bot
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Definitions.Def_Chou_ElementaryAmenable
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_mem_commutator_iff
import Theorems.Thm_CannonFloydParry_center_eq_bot

namespace CannonFloydParry

/-! ### `extend` of the two generators is the underlying function on the line -/

/-! ### Marks lie strictly inside, and `marksAux` is natural for affine maps -/

/-! ### `A` is the rotation at the root

`A` carries `[0,1/2]`, `[1/2,3/4]`, `[3/4,1]` affinely onto `[0,1/4]`, `[1/4,1/2]`, `[1/2,1]`.
Reading those as the three blocks of `node l (node x y)` and of `node (node l x) y`, `A` carries
the marks of the first tree to the marks of the second, whatever `l`, `x`, `y` are. -/

/-! ### `B` is the rotation one step down the right side -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Chains from a uniform relation -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The marks of a tree increase -/

/-! ### Every point of `[0,1]` lies in one of the pieces -/

/-! ### An element is determined by its diagram -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The two generators lie in `F` -/

lemma coe_mapA (z : UI) : (mapA z : ℝ) = aFun (z : ℝ) := by
  rw [mapA, restrict_coe]; rfl

lemma coe_mapB (z : UI) : (mapB z : ℝ) = bFun (z : ℝ) := by
  rw [mapB, restrict_coe]; rfl

lemma isThompson_mapA : IsThompson mapA := by
  refine ⟨{0, 1/2, 3/4, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 1} : Finset ℝ) →
        b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hbm
      by_contra hc
      push_neg at hc
      exact hgap b ⟨⟨hc.1, hc.2⟩, by exact_mod_cast hbm⟩
    have h0 := hb 0 (by simp)
    have h1 := hb (1/2) (by simp)
    have h2 := hb (3/4) (by simp)
    have h3 := hb 1 (by simp)
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · rcases h3 with h3 | h3
          · refine ⟨0, 0, fun z hz => ?_⟩
            rw [coe_mapA, aFun_of_one_le (by linarith [hz.1])]; norm_num
          · refine ⟨1, -1, fun z hz => ?_⟩
            rw [coe_mapA, aFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
            ring
        · refine ⟨0, -(1/4), fun z hz => ?_⟩
          rw [coe_mapA, aFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
          ring
      · refine ⟨-1, 0, fun z hz => ?_⟩
        rw [coe_mapA, aFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
          zpow_neg, zpow_one]
        ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [coe_mapA, aFun_of_le_zero (by linarith [hz.2])]; norm_num

lemma isThompson_mapB : IsThompson mapB := by
  refine ⟨{0, 1/2, 3/4, 7/8, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨7, 3, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 7/8, 1} : Finset ℝ) →
        b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hbm
      by_contra hc
      push_neg at hc
      exact hgap b ⟨⟨hc.1, hc.2⟩, by exact_mod_cast hbm⟩
    have h0 := hb 0 (by simp)
    have h1 := hb (1/2) (by simp)
    have h2 := hb (3/4) (by simp)
    have h3 := hb (7/8) (by simp)
    have h4 := hb 1 (by simp)
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · rcases h3 with h3 | h3
          · rcases h4 with h4 | h4
            · refine ⟨0, 0, fun z hz => ?_⟩
              rw [coe_mapB, bFun_of_one_le (by linarith [hz.1])]; norm_num
            · refine ⟨1, -1, fun z hz => ?_⟩
              rw [coe_mapB, bFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
              ring
          · refine ⟨0, -(1/8), fun z hz => ?_⟩
            rw [coe_mapB, bFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
            ring
        · refine ⟨-1, 1/4, fun z hz => ?_⟩
          rw [coe_mapB, bFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
            zpow_neg, zpow_one]
          ring
      · refine ⟨0, 0, fun z hz => ?_⟩
        rw [coe_mapB, bFun_of_le_half (by linarith [hz.2]), zpow_zero]; ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [coe_mapB, bFun_of_le_half (by linarith [hz.2]), zpow_zero]; ring

lemma mapA_mem_F : mapA ∈ F := mem_F_of_isThompson isThompson_mapA

lemma mapB_mem_F : mapB ∈ F := mem_F_of_isThompson isThompson_mapB

/-! ### Affineness on the pieces, for the two rotations -/

/-! ### The two rotations, as tree diagrams -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The identity and inverses, as tree diagrams -/

/-! ### Spines: a sequence of left subtrees hanging off the right side -/

/-! ### Words -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Composition of tree diagrams (the source's rule on p. 222) -/


/-! ### `Xₘ` is the rotation `m` steps down the right side

`X₀ = A` rotates at the root and `X₁ = B` one step down; the recursion
`X_{m+2} = A⁻¹ X_{m+1} A` then pushes the rotation one step further each time, because `A` itself
turns a spine `w₀, w₁, …` into the spine `⟨w₀,w₁⟩, …`, one shorter. -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Exponents of a spine, and of a rotation -/

/-! ### Trees with all exponents zero are the right combs -/

/-! ### A tree with a positive exponent is a spine over a rotatable node -/

/-! ### Words with total exponent zero are trivial -/

/-! ### The identity, on a diagram whose two trees happen to coincide -/

/-! ### The induction of the source's proof: peel one rotation at a time -/


end CannonFloydParry

namespace CannonFloydParry

lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push_neg at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    push_cast
    field_simp
    ring

/-- An order isomorphism of `[0,1]` fixes the left endpoint. -/
lemma coe_apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  set b : UI := ⟨0, zero_mem_UI⟩ with hb
  have hge : (0:ℝ) ≤ (f b : ℝ) := (f b).2.1
  have hle : (f b : ℝ) ≤ 0 := by
    have h1 : b ≤ f.symm b := by
      show (0:ℝ) ≤ ((f.symm b : UI) : ℝ)
      exact (f.symm b).2.1
    have h2 := (OrderIso.le_iff_le f).mpr h1
    rw [f.apply_symm_apply] at h2
    exact h2
  linarith

/-- An order isomorphism of `[0,1]` fixes the right endpoint. -/
lemma coe_apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  set t : UI := ⟨1, one_mem_UI⟩ with ht
  have hle : (f t : ℝ) ≤ 1 := (f t).2.2
  have hge : (1:ℝ) ≤ (f t : ℝ) := by
    have h1 : f.symm t ≤ t := by
      show ((f.symm t : UI) : ℝ) ≤ (1:ℝ)
      exact (f.symm t).2.2
    have h2 := (OrderIso.le_iff_le f).mpr h1
    rw [f.apply_symm_apply] at h2
    exact h2
  linarith

lemma extend_eq_self_of_le_zero (f : UI ≃o UI) {x : ℝ} (hx : x ≤ 0) : extend f x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extendFun_of_notMem f (fun hm => absurd hm.1 (not_le.mpr h))
  · subst h
    rw [extend_apply, extendFun_of_mem f zero_mem_UI, coe_apply_zero f]

lemma extend_eq_self_of_one_le (f : UI ≃o UI) {x : ℝ} (hx : 1 ≤ x) : extend f x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extendFun_of_notMem f (fun hm => absurd hm.2 (not_le.mpr h))
  · subst h
    rw [extend_apply, extendFun_of_mem f one_mem_UI, coe_apply_one f]

lemma extend_coe (f : UI ≃o UI) (z : UI) : extend f (z : ℝ) = (f z : ℝ) := by
  rw [extend_apply, extendFun_of_mem f z.2]

/-- The two models agree on membership: `f` satisfies the textbook condition on `[0,1]` exactly
when its extension by the identity satisfies the line condition.  This is a statement about the
two predicates; that the groups they cut out are isomorphic is `F_mulEquiv_Fline`. -/
theorem isThompsonLine_extend_iff (f : UI ≃o UI) : IsThompsonLine (extend f) ↔ IsThompson f := by
  constructor
  · rintro ⟨-, -, B, hBd, hB⟩
    refine ⟨B, hBd, fun x y hxy hgap => ?_⟩
    obtain ⟨n, c, haff⟩ := hB (x:ℝ) (y:ℝ) hxy hgap
    refine ⟨n, c, fun z hz => ?_⟩
    rw [← extend_coe f z]
    exact haff (z:ℝ) hz
  · rintro ⟨B, hBd, hB⟩
    refine ⟨fun x hx => extend_eq_self_of_le_zero f hx,
      fun x hx => extend_eq_self_of_one_le f hx,
      insert 0 (insert 1 B), ?_, fun x y hxy hgap => ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨0, 0, by norm_num⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨1, 0, by norm_num⟩
      · exact hBd b hb
    · rw [Set.eq_empty_iff_forall_notMem] at hgap
      have h0 : (0:ℝ) ∉ Set.Ioo x y := fun h => hgap 0 ⟨h, by simp⟩
      have h1 : (1:ℝ) ∉ Set.Ioo x y := fun h => hgap 1 ⟨h, by simp⟩
      simp only [Set.mem_Ioo, not_and, not_lt] at h0 h1
      by_cases hx0 : (0:ℝ) ≤ x <;> by_cases hy1 : y ≤ (1:ℝ)
      · -- the interval sits inside `[0,1]`: use the hypothesis on `f`
        have hxm : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0, le_trans (le_of_lt hxy) hy1⟩
        have hym : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0 (le_of_lt hxy), hy1⟩
        have hgap' : Set.Ioo (x:ℝ) (y:ℝ) ∩ (B : Set ℝ) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro b hb
          exact hgap b ⟨hb.1, by simp [hb.2]⟩
        obtain ⟨n, c, haff⟩ :=
          hB ⟨x, hxm⟩ ⟨y, hym⟩ hxy hgap'
        refine ⟨n, c, fun z hz => ?_⟩
        have hzm : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0 hz.1, le_trans hz.2 hy1⟩
        rw [show z = ((⟨z, hzm⟩ : UI) : ℝ) from rfl, extend_coe f]
        exact haff ⟨z, hzm⟩ hz
      · -- `y > 1`, so `x ≥ 1` and the whole interval is fixed
        have hx1 : (1:ℝ) ≤ x := not_lt.mp (fun hc => absurd (h1 hc) hy1)
        exact ⟨0, 0, fun z hz => by
          rw [extend_eq_self_of_one_le f (le_trans hx1 hz.1)]; norm_num⟩
      · -- `x < 0`, so `y ≤ 0` and the whole interval is fixed
        have hy0 : y ≤ (0:ℝ) := h0 (lt_of_not_ge hx0)
        exact ⟨0, 0, fun z hz => by
          rw [extend_eq_self_of_le_zero f (le_trans hz.2 hy0)]; norm_num⟩
      · exact absurd (h0 (lt_of_not_ge hx0)) (not_le.mpr (lt_trans one_pos (lt_of_not_ge hy1)))

@[simp] lemma extend_one : extend (1 : UI ≃o UI) = 1 := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]; rfl

lemma extend_mul (f g : UI ≃o UI) : extend (f * g) = extend f * extend g := by
  ext x
  show extend (f * g) x = extend f (extend g x)
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_mem _ h,
      extendFun_of_mem g h, extendFun_of_mem f (g ⟨x, h⟩).2]
    rfl
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_notMem _ h,
      extendFun_of_notMem g h, extendFun_of_notMem f h]

lemma extend_injective : Function.Injective extend := by
  intro f g h
  ext z
  have hz : extend f (z : ℝ) = extend g (z : ℝ) := congrArg (fun L : ℝ ≃o ℝ => L (z : ℝ)) h
  rw [extend_coe, extend_coe] at hz
  exact hz

lemma extend_restrict (L : ℝ ≃o ℝ) (hlo : ∀ x ≤ (0:ℝ), L x = x)
    (hhi : ∀ x, (1:ℝ) ≤ x → L x = x) : extend (restrict L hlo hhi) = L := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]
    rcases not_and_or.mp h with hc | hc
    · exact (hlo x (le_of_lt (lt_of_not_ge hc))).symm
    · exact (hhi x (le_of_lt (lt_of_not_ge hc))).symm


end CannonFloydParry

namespace CannonFloydParry

end CannonFloydParry

namespace CannonFloydParry

/-! ### Small tools -/

/-! ### One piece of the uniform partition -/

/-! ### Every Thompson map has a tree diagram -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The generators `Xₙ` lie in the subgroup generated by `A` and `B` -/

lemma mapA_mem_closure : mapA ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

lemma mapB_mem_closure : mapB ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

lemma X_mem_closure : ∀ n : ℕ, X n ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI))
  | 0 => mapA_mem_closure
  | n + 1 => by
      show (mapA ^ n)⁻¹ * mapB * mapA ^ n ∈ _
      exact mul_mem (mul_mem (inv_mem (pow_mem mapA_mem_closure n)) mapB_mem_closure)
        (pow_mem mapA_mem_closure n)

lemma wordFrom_mem_closure : ∀ (cs : List ℕ) (i : ℕ),
    wordFrom i cs ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
  intro cs
  induction cs with
  | nil => intro i; rw [wordFrom]; exact one_mem _
  | cons c cs ih =>
      intro i
      rw [wordFrom]
      exact mul_mem (pow_mem (X_mem_closure i) c) (ih (i + 1))

/-- **Corollary 2.6**: `F` is generated by `A` and `B`. -/
theorem closure_mapA_mapB_eq_F' : Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) = F :=
  by
  first
    | exact CannonFloydParry.closure_mapA_mapB_eq_F
    | exact CannonFloydParry.closure_mapA_mapB_eq_F ..
    | (apply CannonFloydParry.closure_mapA_mapB_eq_F <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.closure_mapA_mapB_eq_F


end CannonFloydParry

namespace CannonFloydParry

/-! ### The relation `Xₙ Xₖ = Xₖ Xₙ₊₁` for `k < n`, read off the rotation diagrams -/

/-! ### Pushing a generator through a positive word -/

end CannonFloydParry

open CannonFloydParry

namespace CannonFloydParry

/-! ### Lengths -/

/-! ### Unfolding `caretAt` and `endsInCaret`

Both are defined by overlapping pattern matches, so they are unfolded here through `rfl`
equations rather than by rewriting with the definitions. -/

/-! ### `incrHead` touches only the head -/

/-! ### The first and last left-runs

The leftmost leaf of a node is a left child, so its run is positive; the rightmost leaf of any
tree is a right child (or the whole tree), so its run is zero. -/

/-! ### Carets and left-runs

The `k`th and `(k+1)`th leaves are siblings exactly when the left-run from the `k`th is positive
and the run from the `(k+1)`th is zero: the first says the `k`th leaf is a left child, the second
that the `(k+1)`th is a right child, and adjacency then forces them to share a parent. -/

/-! ### The exponent at the last pair, and carets read off the exponents -/

/-! ### `endsInCaret` is the caret at the last pair -/

end CannonFloydParry

namespace CannonFloydParry

open Function


end CannonFloydParry

namespace CannonFloydParry

/-! ### The slope of a Thompson map at the two endpoints

An element of `F` is affine on some `[0, ε]`, with slope a power of two and, since it fixes `0`,
no intercept: `f z = 2 ^ n z` there. Likewise near `1`: `1 - f z = 2 ^ m (1 - z)`. The exponents
`n`, `m` are the source's "right derivative at `0`" and "left derivative at `1`", and
`f ↦ (n, m)` is the homomorphism `φ` of Theorem 4.1. -/

def HasSlope0 (f : UI ≃o UI) (n : ℤ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z : UI, (z : ℝ) ≤ ε → (f z : ℝ) = 2 ^ n * (z : ℝ)

def HasSlope1 (f : UI ≃o UI) (n : ℤ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z : UI, 1 - ε ≤ (z : ℝ) → 1 - (f z : ℝ) = 2 ^ n * (1 - (z : ℝ))

lemma two_zpow_injective {n m : ℤ} (h : (2 : ℝ) ^ n = 2 ^ m) : n = m :=
  zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h

lemma hasSlope0_unique {f : UI ≃o UI} {n m : ℤ} (hn : HasSlope0 f n) (hm : HasSlope0 f m) :
    n = m := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨ε', hε', hm⟩ := hm
  set z : ℝ := min (min ε ε') 1 with hz
  have hz0 : 0 < z := lt_min (lt_min hε hε') one_pos
  have hz1 : z ≤ 1 := min_le_right _ _
  have hzε : z ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hzε' : z ≤ ε' := le_trans (min_le_left _ _) (min_le_right _ _)
  have h1 := hn ⟨z, le_of_lt hz0, hz1⟩ hzε
  have h2 := hm ⟨z, le_of_lt hz0, hz1⟩ hzε'
  have : (2 : ℝ) ^ n * z = 2 ^ m * z := by rw [← h1, ← h2]
  exact two_zpow_injective (mul_right_cancel₀ (ne_of_gt hz0) this)

lemma hasSlope1_unique {f : UI ≃o UI} {n m : ℤ} (hn : HasSlope1 f n) (hm : HasSlope1 f m) :
    n = m := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨ε', hε', hm⟩ := hm
  set d : ℝ := min (min ε ε') 1 with hd
  have hd0 : 0 < d := lt_min (lt_min hε hε') one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdε : d ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hdε' : d ≤ ε' := le_trans (min_le_left _ _) (min_le_right _ _)
  have hz : (1 - d) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1 := hn ⟨1 - d, hz⟩ (by simp; linarith)
  have h2 := hm ⟨1 - d, hz⟩ (by simp; linarith)
  simp only [Subtype.coe_mk, sub_sub_cancel] at h1 h2
  have : (2 : ℝ) ^ n * d = 2 ^ m * d := by rw [← h1, ← h2]
  exact two_zpow_injective (mul_right_cancel₀ (ne_of_gt hd0) this)

/-- A point of `(0, 1]` below every positive breakpoint. -/
lemma exists_gap_above_zero (B : Finset ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ Set.Ioo (0 : ℝ) y ∩ (B : Set ℝ) = ∅ := by
  classical
  set P := B.filter (fun b => 0 < b) with hP
  by_cases hne : P.Nonempty
  · refine ⟨min (P.min' hne) 1, lt_min ?_ one_pos, min_le_right _ _, ?_⟩
    · have := Finset.min'_mem P hne
      exact (Finset.mem_filter.mp this).2
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb0, hb1⟩, hbB⟩
      have hbP : b ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb0⟩
      have := Finset.min'_le P b hbP
      have := min_le_left (P.min' hne) 1
      linarith
  · refine ⟨1, one_pos, le_refl _, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro b ⟨⟨hb0, -⟩, hbB⟩
    exact hne ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb0⟩⟩

/-- A point of `[0, 1)` above every breakpoint below `1`. -/
lemma exists_gap_below_one (B : Finset ℝ) :
    ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧ Set.Ioo x (1 : ℝ) ∩ (B : Set ℝ) = ∅ := by
  classical
  set P := B.filter (fun b => b < 1) with hP
  by_cases hne : P.Nonempty
  · refine ⟨max (P.max' hne) 0, le_max_right _ _, max_lt ?_ one_pos, ?_⟩
    · have := Finset.max'_mem P hne
      exact (Finset.mem_filter.mp this).2
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb0, hb1⟩, hbB⟩
      have hbP : b ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb1⟩
      have := Finset.le_max' P b hbP
      have := le_max_left (P.max' hne) 0
      linarith
  · refine ⟨0, le_refl _, one_pos, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro b ⟨⟨-, hb1⟩, hbB⟩
    exact hne ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb1⟩⟩

lemma exists_hasSlope0 {f : UI ≃o UI} (hf : IsThompson f) : ∃ n, HasSlope0 f n := by
  obtain ⟨B, -, hB⟩ := hf
  obtain ⟨y, hy0, hy1, hgap⟩ := exists_gap_above_zero B
  obtain ⟨n, c, h⟩ := hB ⟨0, zero_mem_UI⟩ ⟨y, le_of_lt hy0, hy1⟩ hy0 hgap
  have h0 := h ⟨0, zero_mem_UI⟩ ⟨le_refl _, le_of_lt hy0⟩
  rw [coe_apply_zero] at h0
  have hc : c = 0 := by simpa using h0.symm
  refine ⟨n, y, hy0, fun z hz => ?_⟩
  have := h z ⟨z.2.1, hz⟩
  rw [this, hc, add_zero]

lemma exists_hasSlope1 {f : UI ≃o UI} (hf : IsThompson f) : ∃ n, HasSlope1 f n := by
  obtain ⟨B, -, hB⟩ := hf
  obtain ⟨x, hx0, hx1, hgap⟩ := exists_gap_below_one B
  obtain ⟨n, c, h⟩ := hB ⟨x, hx0, le_of_lt hx1⟩ ⟨1, one_mem_UI⟩ hx1 hgap
  have h1 := h ⟨1, one_mem_UI⟩ ⟨le_of_lt hx1, le_refl _⟩
  rw [coe_apply_one] at h1
  refine ⟨n, 1 - x, by linarith, fun z hz => ?_⟩
  have := h z ⟨by simp at hz; linarith, z.2.2⟩
  rw [this]
  simp only [Subtype.coe_mk] at h1
  linarith

lemma hasSlope0_mul {f g : UI ≃o UI} {n m : ℤ} (hf : HasSlope0 f n) (hg : HasSlope0 g m) :
    HasSlope0 (f * g) (n + m) := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨δ, hδ, hg⟩ := hg
  have hm : (0 : ℝ) < 2 ^ m := zpow_pos (by norm_num) _
  refine ⟨min δ (ε / 2 ^ m), lt_min hδ (div_pos hε hm), fun z hz => ?_⟩
  have hzδ : (z : ℝ) ≤ δ := le_trans hz (min_le_left _ _)
  have hzε : (z : ℝ) ≤ ε / 2 ^ m := le_trans hz (min_le_right _ _)
  have hgz : (g z : ℝ) = 2 ^ m * z := hg z hzδ
  have hgz' : (g z : ℝ) ≤ ε := by
    rw [hgz]; rw [le_div_iff₀ hm] at hzε; linarith
  show (f (g z) : ℝ) = 2 ^ (n + m) * z
  rw [hf (g z) hgz', hgz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma hasSlope1_mul {f g : UI ≃o UI} {n m : ℤ} (hf : HasSlope1 f n) (hg : HasSlope1 g m) :
    HasSlope1 (f * g) (n + m) := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨δ, hδ, hg⟩ := hg
  have hm : (0 : ℝ) < 2 ^ m := zpow_pos (by norm_num) _
  refine ⟨min δ (ε / 2 ^ m), lt_min hδ (div_pos hε hm), fun z hz => ?_⟩
  have hmin1 := min_le_left δ (ε / 2 ^ m)
  have hmin2 := min_le_right δ (ε / 2 ^ m)
  have hzδ : 1 - δ ≤ (z : ℝ) := by linarith
  have hzε : 1 - ε / 2 ^ m ≤ (z : ℝ) := by linarith
  have hgz : 1 - (g z : ℝ) = 2 ^ m * (1 - z) := hg z hzδ
  have hgz' : 1 - ε ≤ (g z : ℝ) := by
    have : (1 : ℝ) - z ≤ ε / 2 ^ m := by linarith
    rw [le_div_iff₀ hm] at this
    linarith
  show 1 - (f (g z) : ℝ) = 2 ^ (n + m) * (1 - z)
  rw [hf (g z) hgz', hgz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-! ### The homomorphism `φ` -/

noncomputable def slope0 (f : F) : ℤ :=
  Classical.choose (exists_hasSlope0 (mem_F_iff_isThompson.mp f.2))

noncomputable def slope1 (f : F) : ℤ :=
  Classical.choose (exists_hasSlope1 (mem_F_iff_isThompson.mp f.2))

lemma hasSlope0_slope0 (f : F) : HasSlope0 (f : UI ≃o UI) (slope0 f) :=
  Classical.choose_spec (exists_hasSlope0 (mem_F_iff_isThompson.mp f.2))

lemma hasSlope1_slope1 (f : F) : HasSlope1 (f : UI ≃o UI) (slope1 f) :=
  Classical.choose_spec (exists_hasSlope1 (mem_F_iff_isThompson.mp f.2))

lemma slope0_eq {f : F} {n : ℤ} (h : HasSlope0 (f : UI ≃o UI) n) : slope0 f = n :=
  hasSlope0_unique (hasSlope0_slope0 f) h

lemma slope1_eq {f : F} {n : ℤ} (h : HasSlope1 (f : UI ≃o UI) n) : slope1 f = n :=
  hasSlope1_unique (hasSlope1_slope1 f) h

lemma hasSlope0_one : HasSlope0 (1 : UI ≃o UI) 0 :=
  ⟨1, one_pos, fun z _ => by simp⟩

lemma hasSlope1_one : HasSlope1 (1 : UI ≃o UI) 0 :=
  ⟨1, one_pos, fun z _ => by simp⟩

noncomputable def φ : F →* Multiplicative (ℤ × ℤ) where
  toFun f := Multiplicative.ofAdd (slope0 f, slope1 f)
  map_one' := by
    have h0 : slope0 (1 : F) = 0 := slope0_eq hasSlope0_one
    have h1 : slope1 (1 : F) = 0 := slope1_eq hasSlope1_one
    rw [h0, h1]; rfl
  map_mul' f g := by
    have h0 : slope0 (f * g) = slope0 f + slope0 g :=
      slope0_eq (hasSlope0_mul (hasSlope0_slope0 f) (hasSlope0_slope0 g))
    have h1 : slope1 (f * g) = slope1 f + slope1 g :=
      slope1_eq (hasSlope1_mul (hasSlope1_slope1 f) (hasSlope1_slope1 g))
    rw [h0, h1]; rfl

lemma φ_apply (f : F) : φ f = Multiplicative.ofAdd (slope0 f, slope1 f) := rfl

/-! ### Values on the generators, and surjectivity -/

lemma hasSlope0_mapA : HasSlope0 mapA (-1) :=
  ⟨1 / 2, by norm_num, fun z hz => by
    rw [coe_mapA, aFun_of_mem1 z.2.1 hz, zpow_neg_one]; ring⟩

lemma hasSlope1_mapA : HasSlope1 mapA 1 :=
  ⟨1 / 4, by norm_num, fun z hz => by
    rw [coe_mapA, aFun_of_mem3 (by linarith) z.2.2, zpow_one]; ring⟩

/-- `A` and `B` as elements of the subgroup `F`. -/
noncomputable def genA : F := ⟨mapA, mapA_mem_F⟩
noncomputable def genB : F := ⟨mapB, mapB_mem_F⟩

lemma φ_genA : φ genA = Multiplicative.ofAdd (-1, 1) := by
  rw [φ_apply, slope0_eq hasSlope0_mapA, slope1_eq hasSlope1_mapA]

/-- `F` is generated by `A` and `B`, as elements of `F` (Corollary 2.6 lifted to the subtype). -/
lemma closure_genA_genB : Subgroup.closure ({genA, genB} : Set F) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : UI ≃o UI) ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [closure_mapA_mapB_eq_F']; exact x.2
  have hmap : (Subgroup.closure ({genA, genB} : Set F)).map F.subtype
      = Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, genA, genB]
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have : y = x := Subtype.ext hyx
  rw [← this]; exact hy

/-! ### Slope zero is triviality near the endpoint -/

/-! ### Theorem 4.1 -/

end CannonFloydParry

/-!
# Dyadic piecewise-linear machinery for Cannon–Floyd–Parry Lemma 4.2

Shared development, kept as its own file while it is being built.  It is concatenated into the
self-contained solution files that are submitted to the platform.

Two independent parts:

* `SumPow` — the arithmetic core: a positive integer `q` is a sum of *exactly* `k` integer
  powers of two whenever `q < 2 ^ k`.
* the piecewise-linear constructor — from strictly monotone dyadic breakpoint data `s` and
  target data `t` whose consecutive gaps have power-of-two ratios, an order isomorphism of `ℝ`
  that is the identity off `[0,1]` and carries `s j` to `t j`.
-/

open CannonFloydParry

namespace CFPLib

/-! ### Sums of exactly `k` powers of two -/

/-- `SumPow k q`: the real number `q` is a sum of exactly `k` integer powers of two. -/
def SumPow (k : ℕ) (q : ℝ) : Prop :=
  ∃ l : List ℤ, l.length = k ∧ (l.map fun e => (2 : ℝ) ^ e).sum = q

lemma two_ne_zero' : (2 : ℝ) ≠ 0 := by norm_num

lemma SumPow.one (e : ℤ) : SumPow 1 ((2 : ℝ) ^ e) := ⟨[e], rfl, by simp⟩

lemma SumPow.cons {k : ℕ} {q : ℝ} (e : ℤ) (h : SumPow k q) :
    SumPow (k + 1) ((2 : ℝ) ^ e + q) := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨e :: l, by simp [hl], by simp [hs]⟩

lemma halves (e : ℤ) : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ e := by
  have h : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (e - 1) := by
    rw [zpow_one]; ring
  rw [h, ← zpow_add₀ two_ne_zero']
  congr 1
  ring

/-- Splitting one summand in half increases the number of summands by one. -/
lemma SumPow.split {k : ℕ} {q : ℝ} (h : SumPow k q) (hk : 1 ≤ k) : SumPow (k + 1) q := by
  obtain ⟨l, hl, hs⟩ := h
  cases l with
  | nil => simp at hl; omega
  | cons e rest =>
      refine ⟨(e - 1) :: (e - 1) :: rest, by simpa using hl, ?_⟩
      simp only [List.map_cons, List.sum_cons] at hs ⊢
      rw [← add_assoc, halves, hs]

/-! ### Dyadic arithmetic -/

/-! ### Assembling the exponent list -/

/-! ### The clamp ("ramp") function -/

/-- `ramp a b z` is the length of `[a, b] ∩ (-∞, z]`, for `a ≤ b`. -/
noncomputable def ramp (a b z : ℝ) : ℝ := min (max z a) b - a

lemma ramp_of_le_left {a b z : ℝ} (h : z ≤ a) (hab : a ≤ b) : ramp a b z = 0 := by
  unfold ramp
  rw [max_eq_right h, min_eq_left hab]
  ring

lemma ramp_of_right_le {a b z : ℝ} (h : b ≤ z) (hab : a ≤ b) : ramp a b z = b - a := by
  unfold ramp
  rw [max_eq_left (hab.trans h), min_eq_right h]

lemma ramp_of_mem {a b z : ℝ} (h1 : a ≤ z) (h2 : z ≤ b) : ramp a b z = z - a := by
  unfold ramp
  rw [max_eq_left h1, min_eq_left h2]

lemma ramp_mono (a b : ℝ) : Monotone (ramp a b) := by
  intro z w h
  unfold ramp
  have : max z a ≤ max w a := max_le_max h le_rfl
  exact sub_le_sub_right (min_le_min this le_rfl) a

/-! ### Piecewise-linear data -/

/-- The data of a dyadic piecewise-linear order isomorphism of `[0,1]`: breakpoints `s`,
targets `t`, and slope exponents `e`. -/
structure PLData where
  N : ℕ
  s : ℕ → ℝ
  t : ℕ → ℝ
  e : ℕ → ℤ
  hN : 1 ≤ N
  hs0 : s 0 = 0
  hsN : s N = 1
  ht0 : t 0 = 0
  htN : t N = 1
  hsmono : ∀ j, j < N → s j < s (j + 1)
  hslope : ∀ j, j < N → t (j + 1) - t j = (2 : ℝ) ^ (e j) * (s (j + 1) - s j)
  hsdy : ∀ j, j ≤ N → IsDyadic (s j)
  htdy : ∀ j, j ≤ N → IsDyadic (t j)

namespace PLData

variable (D : PLData)

lemma s_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.N) : D.s i ≤ D.s j := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (le_of_lt (D.hsmono j (by omega)))
      · have : i = j + 1 := by omega
        simp [this]

lemma s_nonneg {j : ℕ} (hj : j ≤ D.N) : 0 ≤ D.s j := by
  have := D.s_le (Nat.zero_le j) hj
  rwa [D.hs0] at this

lemma s_le_one {j : ℕ} (hj : j ≤ D.N) : D.s j ≤ 1 := by
  have := D.s_le hj le_rfl
  rwa [D.hsN] at this

lemma t_sub {j : ℕ} (hj : j < D.N) : D.t j < D.t (j + 1) := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (D.e j) := zpow_pos (by norm_num) _
  have h2 : 0 < D.s (j + 1) - D.s j := sub_pos.mpr (D.hsmono j hj)
  have := D.hslope j hj
  nlinarith

/-- Partial sums of the target gaps: `∑_{j < k} (t (j+1) - t j) = t k`. -/
lemma sum_gaps (k : ℕ) : ∑ j ∈ Finset.range k, (D.t (j + 1) - D.t j) = D.t k - D.t 0 :=
  Finset.sum_range_sub (fun j => D.t j) k

/-- The underlying function. -/
noncomputable def fn (z : ℝ) : ℝ :=
  min z 0 + (∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
    + max (z - 1) 0

lemma fn_monotone : Monotone D.fn := by
  intro z w hzw
  unfold fn
  have h1 : min z 0 ≤ min w 0 := min_le_min hzw le_rfl
  have h2 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        ≤ (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) w := fun j _ =>
    mul_le_mul_of_nonneg_left (ramp_mono _ _ hzw) (le_of_lt (zpow_pos (by norm_num) _))
  have h3 : max (z - 1) 0 ≤ max (w - 1) 0 := max_le_max (sub_le_sub_right hzw 1) le_rfl
  exact add_le_add (add_le_add h1 (Finset.sum_le_sum h2)) h3

lemma fn_of_nonpos {z : ℝ} (hz : z ≤ 0) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = z := min_eq_left hz
  have h2 : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_le_left (hz.trans (D.s_nonneg (by omega)))
      (le_of_lt (D.hsmono j hj)), mul_zero]
  rw [h1, h2, Finset.sum_congr rfl h3]
  simp

lemma total_mass : ∑ j ∈ Finset.range D.N,
    (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = 1 := by
  have h : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = D.t (j + 1) - D.t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (D.hslope j hj).symm
  rw [Finset.sum_congr rfl h, D.sum_gaps D.N, D.ht0, D.htN]
  ring

lemma fn_of_one_le {z : ℝ} (hz : 1 ≤ z) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = 0 := min_eq_right (by linarith)
  have h2 : max (z - 1) 0 = z - 1 := max_eq_left (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_right_le ((D.s_le_one (by omega)).trans hz) (le_of_lt (D.hsmono j hj))]
  rw [h1, h2, Finset.sum_congr rfl h3, D.total_mass]
  ring

/-- The affine formula on the `k`-th piece. -/
lemma fn_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.fn z = D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) := by
  have hz0 : 0 ≤ z := (D.s_nonneg (by omega)).trans hz1
  have hz1' : z ≤ 1 := hz2.trans (D.s_le_one (by omega))
  unfold fn
  have hmin : min z 0 = 0 := min_eq_right hz0
  have hmax : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  rw [hmin, hmax]
  -- split the sum at `k`
  have hsplit : ∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
        + ∑ j ∈ Finset.Ico (k + 1) D.N,
            (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (by omega)]
  have htail : ∑ j ∈ Finset.Ico (k + 1) D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hzs : z ≤ D.s j := hz2.trans (D.s_le (by omega) (by omega))
    rw [ramp_of_le_left hzs (le_of_lt (D.hsmono j (by omega))), mul_zero]
  have hhead : ∑ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = D.t k := by
    have h : ∀ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = D.t (j + 1) - D.t j := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hsj : D.s (j + 1) ≤ z := (D.s_le (by omega) (by omega)).trans hz1
      rw [ramp_of_right_le hsj (le_of_lt (D.hsmono j (by omega)))]
      exact (D.hslope j (by omega)).symm
    rw [Finset.sum_congr rfl h, D.sum_gaps k, D.ht0]
    ring
  rw [hsplit, htail, Finset.sum_range_succ, hhead, ramp_of_mem hz1 hz2]
  ring

/-- The largest breakpoint index at or below a point of `[0,1]`. -/
lemma exists_max_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k ≤ D.N ∧ D.s k ≤ z ∧ ∀ j, j ≤ D.N → D.s j ≤ z → j ≤ k := by
  classical
  have hN := D.hN
  set S : Finset ℕ := (Finset.range (D.N + 1)).filter (fun j => D.s j ≤ z) with hS
  have h0 : 0 ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [D.hs0]; exact hz0⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  refine ⟨S.max' hne, ?_, ?_, ?_⟩
  · have := (Finset.mem_filter.mp (S.max'_mem hne)).1
    rw [Finset.mem_range] at this
    omega
  · exact (Finset.mem_filter.mp (S.max'_mem hne)).2
  · intro j hj hjz
    refine S.le_max' _ ?_
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hjz⟩

/-- Every point of `[0,1]` lies on some piece. -/
lemma exists_piece_c {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k < D.N ∧ D.s k ≤ z ∧ z ≤ D.s (k + 1) := by
  have hN := D.hN
  obtain ⟨k, hkN, hkz, hmax⟩ := D.exists_max_le hz0 hz1
  rcases Nat.lt_or_ge k D.N with hlt | hge
  · refine ⟨k, hlt, hkz, ?_⟩
    by_contra hc
    push_neg at hc
    have := hmax (k + 1) (by omega) (le_of_lt hc)
    omega
  · -- `k = N`, so `z = 1`; use the last piece
    have hkN' : k = D.N := by omega
    have hz : z = 1 := by
      have h : D.s D.N ≤ z := by rw [← hkN']; exact hkz
      rw [D.hsN] at h
      linarith
    refine ⟨D.N - 1, by omega, ?_, ?_⟩
    · have h : D.s (D.N - 1) ≤ D.s D.N := D.s_le (by omega) le_rfl
      rw [D.hsN] at h
      linarith
    · have h : D.N - 1 + 1 = D.N := by omega
      rw [h, D.hsN, hz]

/-! ### The inverse -/

/-- The inverse data: swap breakpoints and targets, negate the slope exponents. -/
def symm : PLData where
  N := D.N
  s := D.t
  t := D.s
  e := fun j => -(D.e j)
  hN := D.hN
  hs0 := D.ht0
  hsN := D.htN
  ht0 := D.hs0
  htN := D.hsN
  hsmono := fun j hj => D.t_sub hj
  hslope := by
    intro j hj
    have hne : ((2 : ℝ) ^ (D.e j)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    rw [zpow_neg, D.hslope j hj, inv_mul_cancel_left₀ hne]
  hsdy := D.htdy
  htdy := D.hsdy

@[simp] lemma symm_N : D.symm.N = D.N := rfl
@[simp] lemma symm_s : D.symm.s = D.t := rfl
@[simp] lemma symm_t : D.symm.t = D.s := rfl
@[simp] lemma symm_e (j : ℕ) : D.symm.e j = -(D.e j) := rfl

/-- The image of a piece is the corresponding target piece. -/
lemma fn_mem_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.t k ≤ D.fn z ∧ D.fn z ≤ D.t (k + 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (D.e k) := zpow_pos (by norm_num) _
  have hsl := D.hslope k hk
  rw [D.fn_piece hk hz1 hz2]
  constructor
  · nlinarith [sub_nonneg.mpr hz1]
  · nlinarith [sub_nonneg.mpr hz2]

lemma symm_fn_fn (z : ℝ) : D.symm.fn (D.fn z) = z := by
  rcases le_or_gt z 0 with hz | hz
  · rw [D.fn_of_nonpos hz, D.symm.fn_of_nonpos hz]
  rcases le_or_gt 1 z with hz1 | hz1
  · rw [D.fn_of_one_le hz1, D.symm.fn_of_one_le hz1]
  obtain ⟨k, hk, h1, h2⟩ := D.exists_piece_c (le_of_lt hz) (le_of_lt hz1)
  obtain ⟨ha, hb⟩ := D.fn_mem_piece hk h1 h2
  have hne : ((2 : ℝ) ^ (D.e k)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  rw [D.symm.fn_piece (show k < D.symm.N from hk) ha hb, D.fn_piece hk h1 h2]
  simp only [symm_t, symm_s, symm_e]
  have hcollapse : D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) - D.t k
      = (2 : ℝ) ^ (D.e k) * (z - D.s k) := by ring
  rw [hcollapse, zpow_neg, inv_mul_cancel_left₀ hne]
  ring

lemma symm_symm_fn : D.symm.symm.fn = D.fn := by
  funext z
  simp [fn, symm]

lemma fn_symm_fn (y : ℝ) : D.fn (D.symm.fn y) = y := by
  have h := D.symm.symm_fn_fn y
  rwa [D.symm_symm_fn] at h

lemma fn_injective : Function.Injective D.fn :=
  Function.LeftInverse.injective D.symm_fn_fn

lemma fn_surjective : Function.Surjective D.fn := fun y => ⟨D.symm.fn y, D.fn_symm_fn y⟩

lemma fn_strictMono : StrictMono D.fn :=
  D.fn_monotone.strictMono_of_injective D.fn_injective

/-- The order isomorphism of the line determined by the data. -/
noncomputable def iso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective D.fn D.fn_strictMono D.fn_surjective

@[simp] lemma iso_apply (z : ℝ) : D.iso z = D.fn z := rfl

/-! ### The data defines an element of the line model -/

/-! ### Stretches where the data is already the identity -/

lemma iso_of_le_zero : ∀ x ≤ (0 : ℝ), D.iso x = x := fun x hx => D.fn_of_nonpos hx

lemma iso_of_one_le : ∀ x, (1 : ℝ) ≤ x → D.iso x = x := fun x hx => D.fn_of_one_le hx

end PLData

/-! ### Transfer to the unit-interval model -/

/-- The interval-model element determined by piecewise-linear data. -/
noncomputable def PLData.uiMap (D : PLData) : UI ≃o UI :=
  restrict D.iso D.iso_of_le_zero D.iso_of_one_le

@[simp] lemma PLData.uiMap_coe (D : PLData) (z : UI) : ((D.uiMap z : UI) : ℝ) = D.fn (z : ℝ) :=
  rfl

/-! ### From a pair of integer partitions to the data -/

end CFPLib
open CannonFloydParry CFPLib

namespace CFPCenter

/-! ### Dyadic rationals are order-dense

Cannon–Floyd–Parry's argument needs a supply of dyadic breakpoints strictly between two given
reals; that is all this section provides. -/

/-! ### A element of `F` whose fixed set is exactly `[0,c] ∪ {1}`

For a dyadic `c ∈ (0,1)`, rescale the shape of the generator `A` to `[c,1]`: the three pieces
have slopes `1/2`, `1`, `2`, so the map is the identity on `[0,c]` and strictly decreasing
away from the diagonal on `(c,1)`. -/

variable {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hcd : IsDyadic c)

end CFPCenter

namespace CannonFloydParry

open CFPCenter

end CannonFloydParry

namespace CannonFloydParry
open CFPCenter


end CannonFloydParry

namespace CannonFloydParry

/-! ### The generators, as elements of `F`, and the relations among them -/

noncomputable def XF (n : ℕ) : F :=
  ⟨X n, by rw [← closure_mapA_mapB_eq_F']; exact X_mem_closure n⟩

noncomputable def wordFromF (i : ℕ) (l : List ℕ) : F :=
  ⟨wordFrom i l, by rw [← closure_mapA_mapB_eq_F']; exact wordFrom_mem_closure l i⟩

@[simp] lemma coe_XF (n : ℕ) : ((XF n : F) : UI ≃o UI) = X n := rfl

@[simp] lemma coe_wordFromF (i : ℕ) (l : List ℕ) :
    ((wordFromF i l : F) : UI ≃o UI) = wordFrom i l := rfl

/-! ### The slope at `0` of a word -/

/-! ### The commutator `[B, A⁻¹]` lies in any normal subgroup containing a suitable word -/

/-! ### Theorem 4.3 -/

theorem mul_comm_quotient_of_ne_bot' (N : Subgroup F) [hN : N.Normal] (hne : N ≠ ⊥)
    (x y : F ⧸ N) : x * y = y * x :=
  by
  try haveI := N; try haveI := hne; try haveI := x; try haveI := y; first
    | exact CannonFloydParry.mul_comm_quotient_of_ne_bot N x y
    | exact CannonFloydParry.mul_comm_quotient_of_ne_bot
    | exact CannonFloydParry.mul_comm_quotient_of_ne_bot ..
    | (apply CannonFloydParry.mul_comm_quotient_of_ne_bot <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.mul_comm_quotient_of_ne_bot


end CannonFloydParry

namespace CannonFloydParry






















/-! ## Lemma 4.4

The subgroup of `F` consisting of the elements supported in a dyadic interval `[a,b]` of length
a power of two is isomorphic to `F`, by conjugation with the increasing affine bijection
`x ↦ a + 2 ^ k * x`.  Everything is done on the line model, where that conjugation is just a
product of three order isomorphisms of `ℝ`; the interval model is reached at the end by
`restrict`. -/

lemma two_zpow_pos (k : ℤ) : (0:ℝ) < 2 ^ k := zpow_pos (by norm_num) k

/-! ### The rescaling -/

/-- The increasing affine bijection of `ℝ` sending `0` to `a` and `1` to `a + 2 ^ k`. -/
noncomputable def aff (a : ℝ) (k : ℤ) : ℝ ≃o ℝ where
  toFun := fun x => a + 2 ^ k * x
  invFun := fun y => (y - a) / 2 ^ k
  left_inv := by
    intro x
    have h := (two_zpow_pos k).ne'
    show (a + 2 ^ k * x - a) / 2 ^ k = x
    field_simp
    ring
  right_inv := by
    intro y
    have h := (two_zpow_pos k).ne'
    show a + 2 ^ k * ((y - a) / 2 ^ k) = y
    field_simp
    ring
  map_rel_iff' := by
    intro x y
    have hp := two_zpow_pos k
    show a + 2 ^ k * x ≤ a + 2 ^ k * y ↔ x ≤ y
    refine ⟨fun h => le_of_mul_le_mul_left (by linarith) hp, fun h => ?_⟩
    have := mul_le_mul_of_nonneg_left h (le_of_lt hp)
    linarith

@[simp] lemma aff_apply (a : ℝ) (k : ℤ) (x : ℝ) : aff a k x = a + 2 ^ k * x := rfl

@[simp] lemma aff_symm_apply (a : ℝ) (k : ℤ) (y : ℝ) :
    (aff a k).symm y = (y - a) / 2 ^ k := rfl

lemma aff_inv_apply (a : ℝ) (k : ℤ) (y : ℝ) : (aff a k)⁻¹ y = (y - a) / 2 ^ k := rfl

/-- The inverse rescaling is again a rescaling, with dyadic data when `a` is dyadic. -/
lemma aff_inv_eq (a : ℝ) (k : ℤ) : (aff a k)⁻¹ = aff (-(a * 2 ^ (-k))) (-k) := by
  apply RelIso.ext
  intro x
  rw [aff_inv_apply, aff_apply, zpow_neg]
  have h := (two_zpow_pos k).ne'
  field_simp
  ring

/-! ### Four arithmetic transfers between the two sides of the rescaling -/

lemma aff_lt_iff (a : ℝ) (k : ℤ) (x u : ℝ) : (x - a) / 2 ^ k < u ↔ x < a + 2 ^ k * u := by
  have hp := two_zpow_pos k
  rw [div_lt_iff₀ hp, mul_comm u ((2:ℝ) ^ k)]
  constructor <;> intro h <;> linarith

lemma lt_aff_iff (a : ℝ) (k : ℤ) (u y : ℝ) : u < (y - a) / 2 ^ k ↔ a + 2 ^ k * u < y := by
  have hp := two_zpow_pos k
  rw [lt_div_iff₀ hp, mul_comm u ((2:ℝ) ^ k)]
  constructor <;> intro h <;> linarith

lemma aff_le_iff (a : ℝ) (k : ℤ) (x u : ℝ) : (x - a) / 2 ^ k ≤ u ↔ x ≤ a + 2 ^ k * u := by
  have hp := two_zpow_pos k
  rw [div_le_iff₀ hp, mul_comm u ((2:ℝ) ^ k)]
  constructor <;> intro h <;> linarith

lemma le_aff_iff (a : ℝ) (k : ℤ) (u y : ℝ) : u ≤ (y - a) / 2 ^ k ↔ a + 2 ^ k * u ≤ y := by
  have hp := two_zpow_pos k
  rw [le_div_iff₀ hp, mul_comm u ((2:ℝ) ^ k)]
  constructor <;> intro h <;> linarith

lemma aff_symm_self (a : ℝ) (k : ℤ) (z : ℝ) : a + 2 ^ k * ((z - a) / 2 ^ k) = z := by
  have h := (two_zpow_pos k).ne'
  field_simp
  ring

/-! ### Conjugation -/

/-- Conjugating a line-model map into `[a, a + 2 ^ k]`. -/
noncomputable def cj (a : ℝ) (k : ℤ) (L : ℝ ≃o ℝ) : ℝ ≃o ℝ := aff a k * L * (aff a k)⁻¹

/-- Conjugating a line-model map supported in `[a, a + 2 ^ k]` back to `[0,1]`. -/
noncomputable def cjInv (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) : ℝ ≃o ℝ := (aff a k)⁻¹ * M * aff a k

lemma cj_apply (a : ℝ) (k : ℤ) (L : ℝ ≃o ℝ) (x : ℝ) :
    cj a k L x = a + 2 ^ k * L ((x - a) / 2 ^ k) := rfl

lemma cjInv_apply (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) (x : ℝ) :
    cjInv a k M x = (M (a + 2 ^ k * x) - a) / 2 ^ k := rfl

lemma cjInv_cj (a : ℝ) (k : ℤ) (L : ℝ ≃o ℝ) : cjInv a k (cj a k L) = L := by
  simp only [cj, cjInv]
  group

lemma cj_cjInv (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) : cj a k (cjInv a k M) = M := by
  simp only [cj, cjInv]
  group

lemma cjInv_eq_cj (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) :
    cjInv a k M = cj (-(a * 2 ^ (-k))) (-k) M := by
  simp only [cj, cjInv, ← aff_inv_eq, inv_inv]

/-- Off `[a, a + 2 ^ k]` the conjugate is the identity: below. -/
lemma cj_eq_self_of_le {a : ℝ} {k : ℤ} {L : ℝ ≃o ℝ} (hlo : ∀ x ≤ (0:ℝ), L x = x)
    {x : ℝ} (hx : x ≤ a) : cj a k L x = x := by
  have hp := two_zpow_pos k
  have h : (x - a) / 2 ^ k ≤ 0 := by
    rw [div_le_iff₀ hp]
    ring_nf
    linarith
  rw [cj_apply, hlo _ h, aff_symm_self]

/-- Off `[a, a + 2 ^ k]` the conjugate is the identity: above. -/
lemma cj_eq_self_of_ge {a : ℝ} {k : ℤ} {L : ℝ ≃o ℝ} (hhi : ∀ x, (1:ℝ) ≤ x → L x = x)
    {x : ℝ} (hx : a + 2 ^ k ≤ x) : cj a k L x = x := by
  have hp := two_zpow_pos k
  have h : (1:ℝ) ≤ (x - a) / 2 ^ k := by
    rw [le_div_iff₀ hp]
    ring_nf
    linarith
  rw [cj_apply, hhi _ h, aff_symm_self]

/-- The piecewise-affine data transports through the conjugation: breakpoints move by the
rescaling, which keeps them dyadic, and the slope exponents are unchanged. -/
lemma cj_affine {a : ℝ} {k : ℤ} (ha : IsDyadic a) {L : ℝ ≃o ℝ}
    {B : Finset ℝ} (hBd : ∀ t ∈ B, IsDyadic t)
    (hBa : ∀ x y : ℝ, x < y → Set.Ioo x y ∩ (B : Set ℝ) = ∅ →
      ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c) :
    ∃ B' : Finset ℝ, (∀ t ∈ B', IsDyadic t) ∧
      ∀ x y : ℝ, x < y → Set.Ioo x y ∩ (B' : Set ℝ) = ∅ →
        ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, cj a k L z = 2 ^ n * z + c := by
  classical
  have hp := two_zpow_pos k
  refine ⟨B.image (fun t => a + 2 ^ k * t), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact isDyadic_add ha (isDyadic_zpow_mul (hBd u hu))
  · intro x y hxy hgap
    have hxy' : (x - a) / 2 ^ k < (y - a) / 2 ^ k := by
      rw [aff_lt_iff, aff_symm_self]
      exact hxy
    have hgap' : Set.Ioo ((x - a) / 2 ^ k) ((y - a) / 2 ^ k) ∩ (B : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨⟨hu1, hu2⟩, huB⟩ := hu
      have hmem : a + 2 ^ k * u ∈
          Set.Ioo x y ∩ ((B.image (fun t => a + 2 ^ k * t) : Finset ℝ) : Set ℝ) := by
        refine ⟨⟨(aff_lt_iff a k x u).mp hu1, (lt_aff_iff a k u y).mp hu2⟩, ?_⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u, huB, rfl⟩)
      rw [hgap] at hmem
      exact hmem
    obtain ⟨n, c, hc⟩ := hBa _ _ hxy' hgap'
    refine ⟨n, a + 2 ^ k * c - 2 ^ n * a, ?_⟩
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : (x - a) / 2 ^ k ≤ (z - a) / 2 ^ k := by
      rw [aff_le_iff, aff_symm_self]; exact hz1
    have hz2' : (z - a) / 2 ^ k ≤ (y - a) / 2 ^ k := by
      rw [le_aff_iff, aff_symm_self]; exact hz2
    rw [cj_apply, hc _ ⟨hz1', hz2'⟩]
    have h := (two_zpow_pos k).ne'
    field_simp
    ring

/-! ### An order isomorphism of `ℝ` fixing a half-line fixes its endpoint -/

lemma eq_self_of_forall_lt {M : ℝ ≃o ℝ} {a : ℝ} (h : ∀ x < a, M x = x) : M a = a := by
  rcases lt_trichotomy (M a) a with hlt | heq | hgt
  · have hfix : M (M a) = M a := h _ hlt
    have : M a = a := M.injective hfix
    linarith [this, hlt]
  · exact heq
  · obtain ⟨y, hy1, hy2⟩ : ∃ y, a < y ∧ y < M a := ⟨(a + M a) / 2, by linarith, by linarith⟩
    set w := M.symm y with hw
    have hMw : M w = y := M.apply_symm_apply y
    rcases lt_or_ge w a with hwa | hwa
    · rw [h w hwa] at hMw
      linarith [hMw, hy1, hw]
    · have : M a ≤ M w := M.monotone hwa
      rw [hMw] at this
      linarith

lemma eq_self_of_forall_gt {M : ℝ ≃o ℝ} {b : ℝ} (h : ∀ x, b < x → M x = x) : M b = b := by
  rcases lt_trichotomy (M b) b with hlt | heq | hgt
  · obtain ⟨y, hy1, hy2⟩ : ∃ y, M b < y ∧ y < b := ⟨(M b + b) / 2, by linarith, by linarith⟩
    set w := M.symm y with hw
    have hMw : M w = y := M.apply_symm_apply y
    rcases lt_or_ge b w with hbw | hbw
    · rw [h w hbw] at hMw
      linarith [hMw, hy2]
    · have : M w ≤ M b := M.monotone hbw
      rw [hMw] at this
      linarith
  · exact heq
  · have hfix : M (M b) = M b := h _ hgt
    have : M b = b := M.injective hfix
    linarith

/-! ### Support -/

lemma mem_supp_iff {f : UI ≃o UI} {z : UI} : ((z : ℝ)) ∈ supp f ↔ f z ≠ z := by
  constructor
  · intro ht hfz
    obtain ⟨w, hw, hne⟩ := ht
    have hwz : w = z := Subtype.ext hw
    rw [hwz, hfz] at hne
    exact hne rfl
  · intro h
    exact ⟨z, rfl, fun hc => h (Subtype.ext hc)⟩

lemma inv_fix_iff {f : UI ≃o UI} {z : UI} : f⁻¹ z = z ↔ f z = z := by
  show f.symm z = z ↔ f z = z
  rw [f.symm_apply_eq]
  exact eq_comm

lemma supp_one : supp (1 : UI ≃o UI) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨z, hz, hne⟩ := ht
  rw [← hz] at hne
  exact hne rfl

lemma supp_mul_subset (f g : UI ≃o UI) : supp (f * g) ⊆ supp f ∪ supp g := by
  intro t ht
  obtain ⟨z, hz, hne⟩ := ht
  by_contra hc
  rw [Set.mem_union] at hc
  push_neg at hc
  obtain ⟨hf, hg⟩ := hc
  rw [← hz] at hf hg hne
  have hgz : g z = z := by
    by_contra h
    exact hg (mem_supp_iff.mpr h)
  have hfz : f z = z := by
    by_contra h
    exact hf (mem_supp_iff.mpr h)
  apply hne
  show ((f (g z) : UI) : ℝ) = ((z : UI) : ℝ)
  rw [hgz, hfz]

lemma supp_inv (f : UI ≃o UI) : supp f⁻¹ = supp f := by
  ext t
  constructor
  · intro ht
    obtain ⟨z, hz, hne⟩ := ht
    rw [← hz] at hne ⊢
    refine mem_supp_iff.mpr (fun h => hne ?_)
    rw [inv_fix_iff.mpr h]
  · intro ht
    obtain ⟨z, hz, hne⟩ := ht
    rw [← hz] at hne ⊢
    refine mem_supp_iff.mpr (fun h => hne ?_)
    rw [inv_fix_iff.mp h]

/-- The elements of `F` supported in `[a,b]`. -/
def suppSubgroup (a b : ℝ) : Subgroup ↥F where
  carrier := {g : ↥F | supp ((g : ↥F) : UI ≃o UI) ⊆ Set.Icc a b}
  one_mem' := by
    intro t ht
    rw [show ((1 : ↥F) : UI ≃o UI) = 1 from rfl, supp_one] at ht
    exact absurd ht (Set.notMem_empty t)
  mul_mem' := by
    intro x y hx hy t ht
    rw [show ((x * y : ↥F) : UI ≃o UI) = (x : UI ≃o UI) * (y : UI ≃o UI) from rfl] at ht
    rcases supp_mul_subset _ _ ht with h | h
    · exact hx h
    · exact hy h
  inv_mem' := by
    intro x hx t ht
    rw [show ((x⁻¹ : ↥F) : UI ≃o UI) = (x : UI ≃o UI)⁻¹ from rfl, supp_inv] at ht
    exact hx ht

/-! ### The two conjugations on the interval model -/

/-- Conjugate an element of the interval model into `[a, a + 2 ^ k]`. -/
noncomputable def resize (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (f : UI ≃o UI) :
    UI ≃o UI :=
  restrict (cj a k (extend f))
    (fun x hx => cj_eq_self_of_le (fun w hw => extend_eq_self_of_le_zero f hw) (le_trans hx h0))
    (fun x hx => cj_eq_self_of_ge (fun w hw => extend_eq_self_of_one_le f hw) (le_trans h1 hx))

lemma extend_resize (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (f : UI ≃o UI) :
    extend (resize a k h0 h1 f) = cj a k (extend f) := extend_restrict _ _ _

lemma cjInv_eq_self_of_le {a : ℝ} {k : ℤ} {M : ℝ ≃o ℝ} (hM : ∀ x ≤ a, M x = x)
    {x : ℝ} (hx : x ≤ 0) : cjInv a k M x = x := by
  have hp := two_zpow_pos k
  have h2 : 2 ^ k * x ≤ 2 ^ k * 0 := mul_le_mul_of_nonneg_left hx (le_of_lt hp)
  have h : a + 2 ^ k * x ≤ a := by simp only [mul_zero] at h2; linarith
  rw [cjInv_apply, hM _ h]
  have hne := hp.ne'
  field_simp
  ring

lemma cjInv_eq_self_of_ge {a : ℝ} {k : ℤ} {M : ℝ ≃o ℝ} (hM : ∀ x, a + 2 ^ k ≤ x → M x = x)
    {x : ℝ} (hx : (1:ℝ) ≤ x) : cjInv a k M x = x := by
  have hp := two_zpow_pos k
  have h2 : 2 ^ k * 1 ≤ 2 ^ k * x := mul_le_mul_of_nonneg_left hx (le_of_lt hp)
  have h : a + 2 ^ k ≤ a + 2 ^ k * x := by simp only [mul_one] at h2; linarith
  rw [cjInv_apply, hM _ h]
  have hne := hp.ne'
  field_simp
  ring

/-- Conjugate a line-model map supported in `[a, a + 2 ^ k]` back onto `[0,1]`. -/
noncomputable def unresize (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) (hlo : ∀ x ≤ a, M x = x)
    (hhi : ∀ x, a + 2 ^ k ≤ x → M x = x) : UI ≃o UI :=
  restrict (cjInv a k M) (fun _ hx => cjInv_eq_self_of_le hlo hx)
    (fun _ hx => cjInv_eq_self_of_ge hhi hx)

lemma extend_unresize (a : ℝ) (k : ℤ) (M : ℝ ≃o ℝ) (hlo : ∀ x ≤ a, M x = x)
    (hhi : ∀ x, a + 2 ^ k ≤ x → M x = x) :
    extend (unresize a k M hlo hhi) = cjInv a k M := extend_restrict _ _ _

/-! ### Both directions land in `F` -/

lemma isThompson_resize (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (ha : IsDyadic a)
    {f : UI ≃o UI} (hf : IsThompson f) : IsThompson (resize a k h0 h1 f) := by
  rw [← isThompsonLine_extend_iff, extend_resize]
  obtain ⟨hlo, hhi, B, hBd, hBa⟩ := (isThompsonLine_extend_iff f).mpr hf
  exact ⟨fun x hx => cj_eq_self_of_le hlo (le_trans hx h0),
    fun x hx => cj_eq_self_of_ge hhi (le_trans h1 hx), cj_affine ha hBd hBa⟩

lemma isThompson_unresize (a : ℝ) (k : ℤ) (ha : IsDyadic a) {M : ℝ ≃o ℝ}
    (hlo : ∀ x ≤ a, M x = x) (hhi : ∀ x, a + 2 ^ k ≤ x → M x = x)
    (hM : IsThompsonLine M) : IsThompson (unresize a k M hlo hhi) := by
  rw [← isThompsonLine_extend_iff, extend_unresize]
  obtain ⟨_, _, B, hBd, hBa⟩ := hM
  refine ⟨fun _ hx => cjInv_eq_self_of_le hlo hx, fun _ hx => cjInv_eq_self_of_ge hhi hx, ?_⟩
  rw [cjInv_eq_cj]
  have ha' : IsDyadic (-(a * 2 ^ (-k))) := by
    refine isDyadic_neg ?_
    rw [mul_comm]
    exact isDyadic_zpow_mul ha
  exact cj_affine ha' hBd hBa

/-! ### `resize` and `unresize` are mutually inverse group homomorphisms -/

lemma cjInv_mul (a : ℝ) (k : ℤ) (M N : ℝ ≃o ℝ) :
    cjInv a k (M * N) = cjInv a k M * cjInv a k N := by
  simp only [cjInv]
  group

/-! ### The support condition says exactly "fixes everything outside `[a,b]`" -/

lemma extend_eq_self_of_lt_of_supp {g : UI ≃o UI} {a b : ℝ}
    (hs : supp g ⊆ Set.Icc a b) {x : ℝ} (hx : x < a) : extend g x = x := by
  by_cases hm : x ∈ Set.Icc (0:ℝ) 1
  · by_contra hne
    have hcoe : extend g x = ((g ⟨x, hm⟩ : UI) : ℝ) := extend_coe g ⟨x, hm⟩
    have hne' : ((g ⟨x, hm⟩ : UI) : ℝ) ≠ x := by rw [← hcoe]; exact hne
    have hmem : x ∈ supp g := ⟨⟨x, hm⟩, rfl, hne'⟩
    have hax : a ≤ x := (hs hmem).1
    linarith
  · rw [extend_apply, extendFun_of_notMem _ hm]

lemma extend_eq_self_of_gt_of_supp {g : UI ≃o UI} {a b : ℝ}
    (hs : supp g ⊆ Set.Icc a b) {x : ℝ} (hx : b < x) : extend g x = x := by
  by_cases hm : x ∈ Set.Icc (0:ℝ) 1
  · by_contra hne
    have hcoe : extend g x = ((g ⟨x, hm⟩ : UI) : ℝ) := extend_coe g ⟨x, hm⟩
    have hne' : ((g ⟨x, hm⟩ : UI) : ℝ) ≠ x := by rw [← hcoe]; exact hne
    have hmem : x ∈ supp g := ⟨⟨x, hm⟩, rfl, hne'⟩
    have hxb : x ≤ b := (hs hmem).2
    linarith
  · rw [extend_apply, extendFun_of_notMem _ hm]

lemma extend_eq_self_of_le_of_supp {g : UI ≃o UI} {a b : ℝ}
    (hs : supp g ⊆ Set.Icc a b) {x : ℝ} (hx : x ≤ a) : extend g x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extend_eq_self_of_lt_of_supp hs h
  · rw [h]
    exact eq_self_of_forall_lt (fun w hw => extend_eq_self_of_lt_of_supp hs hw)

lemma extend_eq_self_of_ge_of_supp {g : UI ≃o UI} {a b : ℝ}
    (hs : supp g ⊆ Set.Icc a b) {x : ℝ} (hx : b ≤ x) : extend g x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extend_eq_self_of_gt_of_supp hs h
  · rw [← h]
    exact eq_self_of_forall_gt (fun w hw => extend_eq_self_of_gt_of_supp hs hw)

lemma supp_resize_subset (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (f : UI ≃o UI) :
    supp (resize a k h0 h1 f) ⊆ Set.Icc a (a + 2 ^ k) := by
  intro t ht
  obtain ⟨z, hz, hne⟩ := ht
  have hcoe : ((resize a k h0 h1 f z : UI) : ℝ) = cj a k (extend f) t := by
    rw [← hz, ← extend_coe (resize a k h0 h1 f) z, extend_resize]
  rw [hcoe] at hne
  constructor
  · by_contra hc
    push_neg at hc
    exact hne (cj_eq_self_of_le (fun w hw => extend_eq_self_of_le_zero f hw) (le_of_lt hc))
  · by_contra hc
    push_neg at hc
    exact hne (cj_eq_self_of_ge (fun w hw => extend_eq_self_of_one_le f hw) (le_of_lt hc))

/-! ### The isomorphism -/

/-- Conjugating an element of `F` into `[a, a + 2 ^ k]`. -/
noncomputable def toSupp (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (ha : IsDyadic a)
    (f : ↥F) : ↥(suppSubgroup a (a + 2 ^ k)) :=
  ⟨⟨resize a k h0 h1 ((f : ↥F) : UI ≃o UI),
    mem_F_of_isThompson (isThompson_resize a k h0 h1 ha (mem_F_iff_isThompson.mp f.2))⟩,
   supp_resize_subset a k h0 h1 _⟩

/-- Conjugating an element supported in `[a, a + 2 ^ k]` back to `F`. -/
noncomputable def ofSupp (a : ℝ) (k : ℤ) (ha : IsDyadic a)
    (g : ↥(suppSubgroup a (a + 2 ^ k))) : ↥F :=
  ⟨unresize a k (extend ((g : ↥F) : UI ≃o UI))
      (fun _ hx => extend_eq_self_of_le_of_supp g.2 hx)
      (fun _ hx => extend_eq_self_of_ge_of_supp g.2 hx),
   mem_F_of_isThompson (isThompson_unresize a k ha _ _
      ((isThompsonLine_extend_iff _).mpr (mem_F_iff_isThompson.mp (g : ↥F).2)))⟩

end CannonFloydParry

namespace CannonFloydParry

/-! ### The Lemma 4.4 isomorphism, concretely, and how it moves supports -/

/-- The linear conjugation of Lemma 4.4 as an explicit multiplicative equivalence. -/
noncomputable def suppEquiv (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (ha : IsDyadic a) :
    ↥(suppSubgroup a (a + 2 ^ k)) ≃* ↥F where
  toFun := ofSupp a k ha
  invFun := toSupp a k h0 h1 ha
  left_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply extend_injective
    simp only [toSupp, ofSupp, extend_resize, extend_unresize, cj_cjInv]
  right_inv := by
    intro f
    apply Subtype.ext
    apply extend_injective
    simp only [toSupp, ofSupp, extend_resize, extend_unresize, cjInv_cj]
  map_mul' := by
    intro x y
    apply Subtype.ext
    apply extend_injective
    simp only [ofSupp, Subgroup.coe_mul, extend_mul, cjInv_mul, extend_unresize]

end CannonFloydParry

namespace CannonFloydParry
open CFPLib


end CannonFloydParry

namespace CannonFloydParry

/-! ### Supports under conjugation -/

/-! ### Two copies of `A`, squeezed into `[0, 1/8]` and `[7/8, 1]`, to adjust the slopes -/
lemma isDyadic_quarter : IsDyadic (1 / 4 : ℝ) := ⟨1, 2, by norm_num⟩
lemma quarter_nonneg : (0 : ℝ) ≤ 1 / 4 := by norm_num
lemma quarter_bound : (1 / 4 : ℝ) + 2 ^ (-1 : ℤ) ≤ 1 := by norm_num [zpow_neg]
lemma two_zpow_neg_one : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num [zpow_neg]

/-! ### Conjugating an element of `[F,F]` into `[3/8, 5/8]` -/

/-! ### Theorem 4.5 -/

end CannonFloydParry

namespace CannonFloydParry

/-- Theorem 4.3, read as an inclusion: a nontrivial normal subgroup of `F` contains `[F,F]`. -/
lemma commutator_le_of_normal_ne_bot (N : Subgroup ↥F) [N.Normal] (hN : N ≠ ⊥) :
    commutator ↥F ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    ← commutatorElement_def, commutatorElement_eq_one_iff_commute]
  exact mul_comm_quotient_of_ne_bot' N hN _ _

/-- The subgroup of elements supported in `[1/4, 3/4]` lies in `[F,F]` (Theorem 4.1). -/
lemma suppSubgroup_quarter_le_commutator :
    suppSubgroup (1 / 4) (1 / 4 + 2 ^ (-1 : ℤ)) ≤ commutator ↥F := by
  intro u hu
  have hq : (1 / 4 : ℝ) + 2 ^ (-1 : ℤ) = 3 / 4 := by rw [two_zpow_neg_one]; norm_num
  rw [mem_commutator_iff]
  constructor
  · refine ⟨1 / 4, by norm_num, fun z hz => ?_⟩
    by_contra hne
    have := (hu ⟨z, rfl, hne⟩).1
    linarith
  · refine ⟨1 / 4, by norm_num, fun z hz => ?_⟩
    by_contra hne
    have := (hu ⟨z, rfl, hne⟩).2
    rw [hq] at this
    linarith

/-- Theorem 4.10, the step the source states in words: every nontrivial normal subgroup of
`F` contains a subgroup isomorphic to `F`. -/
theorem exists_subgroup_le_mulEquiv_of_normal_ne_bot' (N : Subgroup ↥F) [N.Normal]
    (hN : N ≠ ⊥) : ∃ H : Subgroup ↥F, H ≤ N ∧ Nonempty (↥H ≃* ↥F) :=
  ⟨suppSubgroup (1 / 4) (1 / 4 + 2 ^ (-1 : ℤ)),
    suppSubgroup_quarter_le_commutator.trans (commutator_le_of_normal_ne_bot N hN),
    ⟨suppEquiv (1 / 4) (-1) quarter_nonneg quarter_bound isDyadic_quarter⟩⟩

end CannonFloydParry

namespace CannonFloydParry

/-! ### `F` is a subquotient: the invariant of the induction -/

/-- `F` is a quotient of a subgroup of `G`: there is a group `K` with an injective homomorphism
into `G` and a surjective homomorphism onto `F`. -/
def HasSubquotientF (G : Type) [Group G] : Prop :=
  ∃ (K : Type) (_ : Group K) (ι : K →* G) (φ : K →* ↥F),
    Function.Injective ι ∧ Function.Surjective φ

lemma hasSubquotientF_self : HasSubquotientF ↥F :=
  ⟨↥F, inferInstance, MonoidHom.id _, MonoidHom.id _, fun _ _ h => h, fun x => ⟨x, rfl⟩⟩

lemma hasSubquotientF_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : HasSubquotientF G) : HasSubquotientF H := by
  obtain ⟨K, _, ι, φ, hι, hφ⟩ := h
  exact ⟨K, ‹_›, e.toMonoidHom.comp ι, φ, e.injective.comp hι, hφ⟩

lemma hasSubquotientF_of_subgroup {G : Type} [Group G] (H : Subgroup G)
    (h : HasSubquotientF ↥H) : HasSubquotientF G := by
  obtain ⟨K, _, ι, φ, hι, hφ⟩ := h
  exact ⟨K, ‹_›, H.subtype.comp ι, φ, H.subtype_injective.comp hι, hφ⟩

lemma hasSubquotientF_of_quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (h : HasSubquotientF (G ⧸ N)) : HasSubquotientF G := by
  obtain ⟨K, _, ι, φ, hι, hφ⟩ := h
  -- the preimage in `G` of the image of `K`
  let K' : Subgroup G := ι.range.comap (QuotientGroup.mk' N)
  have hmem : ∀ x : ↥K', (QuotientGroup.mk' N) (x : G) ∈ ι.range := fun x => x.2
  let ψ : ↥K' →* K :=
    (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
      (((QuotientGroup.mk' N).comp K'.subtype).codRestrict ι.range hmem)
  refine ⟨↥K', inferInstance, K'.subtype, φ.comp ψ, K'.subtype_injective, ?_⟩
  intro f
  obtain ⟨k, rfl⟩ := hφ f
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (ι k)
  have hgK : g ∈ K' := by
    show (QuotientGroup.mk' N) g ∈ ι.range
    rw [hg]; exact ⟨k, rfl⟩
  refine ⟨⟨g, hgK⟩, ?_⟩
  show φ ((MonoidHom.ofInjective hι).symm ⟨(QuotientGroup.mk' N) g, hmem ⟨g, hgK⟩⟩) = φ k
  congr 1
  have hx : (⟨(QuotientGroup.mk' N) g, hmem ⟨g, hgK⟩⟩ : ι.range) = MonoidHom.ofInjective hι k := by
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply]
    exact hg
  rw [hx, MulEquiv.symm_apply_apply]

/-! ### Facts about `F` used at the leaves -/

lemma genA_ne_one : genA ≠ 1 := by
  intro h
  have := φ_genA
  rw [h, map_one] at this
  have h2 := congrArg (fun w => (Multiplicative.toAdd w).1) this
  norm_num at h2

lemma genA_pow_injective : Function.Injective (fun n : ℕ => genA ^ n) := by
  intro n m h
  have := congrArg (fun w => (Multiplicative.toAdd (φ w)).2) h
  simp only [map_pow, φ_genA, toAdd_pow, toAdd_ofAdd, Prod.smul_snd] at this
  rw [nsmul_one, nsmul_one] at this
  exact_mod_cast this

lemma infinite_F : Infinite ↥F := Infinite.of_injective _ genA_pow_injective

lemma not_comm_F : ¬ ∀ x y : ↥F, x * y = y * x := by
  intro h
  have hAc : genA ∉ Subgroup.center ↥F := by
    rw [center_eq_bot, Subgroup.mem_bot]; exact genA_ne_one
  exact hAc (Subgroup.mem_center_iff.mpr fun g => h g genA)

lemma not_hasSubquotientF_of_finite {G : Type} [Group G] [Finite G] : ¬ HasSubquotientF G := by
  rintro ⟨K, _, ι, φ, hι, hφ⟩
  have : Finite K := Finite.of_injective ι hι
  have : Finite ↥F := Finite.of_surjective φ hφ
  have := infinite_F
  exact not_finite ↥F

lemma not_hasSubquotientF_of_comm {G : Type} [CommGroup G] : ¬ HasSubquotientF G := by
  rintro ⟨K, _, ι, φ, hι, hφ⟩
  apply not_comm_F
  intro x y
  obtain ⟨a, rfl⟩ := hφ x
  obtain ⟨b, rfl⟩ := hφ y
  rw [← map_mul, ← map_mul]
  congr 1
  apply hι
  rw [map_mul, map_mul, mul_comm]

/-! ### The two closure cases with content -/

set_option maxHeartbeats 1000000 in
/-- An extension: if `F` is a subquotient of `G` and `N ⊴ G`, then `F` is a subquotient of
`N` or of `G ⧸ N`.  Theorem 4.3 decides which: the image in `F` of the part of `K` lying in
`N` is normal, hence trivial or containing `[F,F]`, and `[F,F]` contains a copy of `F`. -/
lemma hasSubquotientF_extension {G : Type} [Group G] (N : Subgroup G) [hN : N.Normal]
    (h : HasSubquotientF G) : HasSubquotientF ↥N ∨ HasSubquotientF (G ⧸ N) := by
  obtain ⟨K, _, ι, φ, hι, hφ⟩ := h
  obtain ⟨KN, hKNdef⟩ : ∃ KN : Subgroup K, KN = N.comap ι := ⟨_, rfl⟩
  have memKN : ∀ k, k ∈ KN ↔ ι k ∈ N := fun k => by rw [hKNdef]; exact Subgroup.mem_comap
  have hKNn : KN.Normal := by rw [hKNdef]; exact hN.comap ι
  have hmapn : (KN.map φ).Normal := hKNn.map φ hφ
  rcases eq_or_ne (KN.map φ) ⊥ with hbot | hne
  · right
    have hker : KN ≤ φ.ker := by
      intro k hk
      rw [MonoidHom.mem_ker]
      have : φ k ∈ KN.map φ := Subgroup.mem_map_of_mem φ hk
      rwa [hbot, Subgroup.mem_bot] at this
    have hKN : KN = ((QuotientGroup.mk' N).comp ι).ker := by
      ext k
      rw [memKN, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    haveI := hKNn
    refine ⟨K ⧸ KN, inferInstance,
      (QuotientGroup.kerLift ((QuotientGroup.mk' N).comp ι)).comp
        (QuotientGroup.quotientMulEquivOfEq hKN).toMonoidHom,
      QuotientGroup.lift KN φ hker, ?_, ?_⟩
    · exact (QuotientGroup.kerLift_injective _).comp
        (QuotientGroup.quotientMulEquivOfEq hKN).injective
    · intro f
      obtain ⟨k, rfl⟩ := hφ f
      exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk' KN hker k⟩
  · left
    haveI := hmapn
    obtain ⟨H', hH'le, ⟨e⟩⟩ := exists_subgroup_le_mulEquiv_of_normal_ne_bot' (KN.map φ) hne
    obtain ⟨K'', hK''def⟩ : ∃ K'' : Subgroup K, K'' = (H'.comap φ) ⊓ KN := ⟨_, rfl⟩
    have memK'' : ∀ k, k ∈ K'' ↔ φ k ∈ H' ∧ k ∈ KN := fun k => by
      rw [hK''def, Subgroup.mem_inf, Subgroup.mem_comap]
    have hιN : ∀ x : ↥K'', ι (x : K) ∈ N := fun x => (memKN _).mp ((memK'' _).mp x.2).2
    have hφH : ∀ x : ↥K'', φ (x : K) ∈ H' := fun x => ((memK'' _).mp x.2).1
    refine ⟨↥K'', inferInstance, (ι.comp K''.subtype).codRestrict N hιN,
      e.toMonoidHom.comp ((φ.comp K''.subtype).codRestrict H' hφH), ?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply hι
      exact congrArg Subtype.val hxy
    · intro f
      obtain ⟨h', rfl⟩ := e.surjective f
      have hmem : (h' : ↥F) ∈ KN.map φ := hH'le h'.2
      obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.mp hmem
      have hk'' : k ∈ K'' := (memK'' k).mpr ⟨by rw [hkh]; exact h'.2, hk⟩
      refine ⟨⟨k, hk''⟩, ?_⟩
      show e ⟨φ k, hφH ⟨k, hk''⟩⟩ = e h'
      congr 1
      exact Subtype.ext hkh

/-- A directed union: `F` is two-generated, so lifts of its generators lie in one member of
the family, and the subgroup they generate maps onto `F`. -/
lemma hasSubquotientF_directedUnion {G : Type} [Group G] {ι : Type} (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) (h : HasSubquotientF G) :
    ∃ i, HasSubquotientF ↥(H i) := by
  obtain ⟨K, _, emb, φ, hemb, hφ⟩ := h
  obtain ⟨a, ha⟩ := hφ genA
  obtain ⟨b, hb⟩ := hφ genB
  rcases isEmpty_or_nonempty ι with hempty | hne
  · exfalso
    have hbot : (⨆ i, H i) = ⊥ := by simp
    rw [hbot] at hsup
    have hK : ∀ x : K, x = 1 := by
      intro x
      apply hemb
      have : emb x ∈ (⊥ : Subgroup G) := by rw [hsup]; trivial
      rw [Subgroup.mem_bot] at this
      rw [this, map_one]
    apply genA_ne_one
    rw [← ha, hK a, map_one]
  · have hmemA : emb a ∈ ⨆ i, H i := by rw [hsup]; trivial
    have hmemB : emb b ∈ ⨆ i, H i := by rw [hsup]; trivial
    obtain ⟨i, hi⟩ := (Subgroup.mem_iSup_of_directed hdir).mp hmemA
    obtain ⟨j, hj⟩ := (Subgroup.mem_iSup_of_directed hdir).mp hmemB
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_⟩
    let K' : Subgroup K := Subgroup.closure {a, b}
    have hK'H : ∀ x : ↥K', emb (x : K) ∈ H k := by
      intro x
      have hle : K' ≤ (H k).comap emb := by
        apply (Subgroup.closure_le _).mpr
        intro z hz
        rcases hz with rfl | rfl
        · exact hik hi
        · exact hjk hj
      exact hle x.2
    refine ⟨↥K', inferInstance, (emb.comp K'.subtype).codRestrict (H k) hK'H,
      φ.comp K'.subtype, ?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply hemb
      exact congrArg Subtype.val hxy
    · intro f
      have hf : f ∈ Subgroup.closure ({genA, genB} : Set ↥F) := by
        rw [closure_genA_genB]; trivial
      have hmap : K'.map φ = Subgroup.closure ({genA, genB} : Set ↥F) := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb]
      rw [← hmap] at hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
      exact ⟨⟨x, hx⟩, rfl⟩

/-! ### The induction, and Theorem 4.10 -/

theorem not_hasSubquotientF_of_elementaryAmenable {G : Type} [Group G]
    (h : Chou.ElementaryAmenable G) : ¬ HasSubquotientF G := by
  induction h with
  | of_finite G => exact not_hasSubquotientF_of_finite
  | of_commGroup G => exact not_hasSubquotientF_of_comm
  | of_mulEquiv e _ ih => exact fun h => ih (hasSubquotientF_of_mulEquiv e.symm h)
  | subgroup H _ ih => exact fun h => ih (hasSubquotientF_of_subgroup H h)
  | quotient N _ ih => exact fun h => ih (hasSubquotientF_of_quotient N h)
  | extension N _ _ ihN ihQ => exact fun h => (hasSubquotientF_extension N h).elim ihN ihQ
  | directedUnion H hdir hsup _ ih =>
      exact fun h => let ⟨i, hi⟩ := hasSubquotientF_directedUnion H hdir hsup h; ih i hi

/-- Theorem 4.10: Thompson's group `F` is not elementary amenable. -/
theorem not_elementaryAmenable_F' : ¬ Chou.ElementaryAmenable ↥F :=
  fun h => not_hasSubquotientF_of_elementaryAmenable h hasSubquotientF_self

end CannonFloydParry

open CannonFloydParry

theorem solution : ¬ Chou.ElementaryAmenable F :=
  not_elementaryAmenable_F'
