-- Prove2me | solution 2 for CannonFloydParry.mem_commutator_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:47:36.545991+00:00
-- url     : https://prove2.me/submissions/e43eb8a5-1782-4332-840b-901fe8ee7ba2

import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_ker_eq_commutator_of_two_generators_of_surjective

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

@[simp] lemma extend_one : extend (1 : UI ≃o UI) = 1 := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]; rfl


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

lemma hasSlope0_mapB : HasSlope0 mapB 0 :=
  ⟨1 / 2, by norm_num, fun z hz => by
    rw [coe_mapB, bFun_of_le_half hz, zpow_zero]; ring⟩

lemma hasSlope1_mapB : HasSlope1 mapB 1 :=
  ⟨1 / 8, by norm_num, fun z hz => by
    rw [coe_mapB, bFun_of_mem3 (by linarith) z.2.2, zpow_one]; ring⟩

/-- `A` and `B` as elements of the subgroup `F`. -/
noncomputable def genA : F := ⟨mapA, mapA_mem_F⟩
noncomputable def genB : F := ⟨mapB, mapB_mem_F⟩

lemma φ_genA : φ genA = Multiplicative.ofAdd (-1, 1) := by
  rw [φ_apply, slope0_eq hasSlope0_mapA, slope1_eq hasSlope1_mapA]

lemma φ_genB : φ genB = Multiplicative.ofAdd (0, 1) := by
  rw [φ_apply, slope0_eq hasSlope0_mapB, slope1_eq hasSlope1_mapB]

lemma φ_surjective : Function.Surjective φ := by
  intro w
  refine ⟨genA ^ (-(Multiplicative.toAdd w).1) * genB ^ ((Multiplicative.toAdd w).1 + (Multiplicative.toAdd w).2), ?_⟩
  rw [map_mul, map_zpow, map_zpow, φ_genA, φ_genB, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
  conv_rhs => rw [← ofAdd_toAdd w]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring

/-- `F` is generated by `A` and `B`, as elements of `F` (Corollary 2.6 lifted to the subtype). -/
lemma closure_genA_genB : Subgroup.closure ({genA, genB} : Set F) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : UI ≃o UI) ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [CannonFloydParry.closure_mapA_mapB_eq_F]; exact x.2
  have hmap : (Subgroup.closure ({genA, genB} : Set F)).map F.subtype
      = Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, genA, genB]
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have : y = x := Subtype.ext hyx
  rw [← this]; exact hy

lemma ker_φ : φ.ker = commutator F :=
  ker_eq_commutator_of_two_generators_of_surjective genA genB closure_genA_genB φ φ_surjective

/-! ### Slope zero is triviality near the endpoint -/

lemma trivialNearZero_iff_slope0 (f : F) : TrivialNearZero (f : UI ≃o UI) ↔ slope0 f = 0 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine slope0_eq ⟨ε / 2, half_pos hε, fun z hz => ?_⟩
    rw [h z (by linarith), zpow_zero, one_mul]
  · intro h0
    obtain ⟨ε, hε, h⟩ := hasSlope0_slope0 f
    rw [h0] at h
    exact ⟨ε, hε, fun z hz => by rw [h z (le_of_lt hz), zpow_zero, one_mul]⟩

lemma trivialNearOne_iff_slope1 (f : F) : TrivialNearOne (f : UI ≃o UI) ↔ slope1 f = 0 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine slope1_eq ⟨ε / 2, half_pos hε, fun z hz => ?_⟩
    rw [h z (by linarith), zpow_zero, one_mul]
  · intro h0
    obtain ⟨ε, hε, h⟩ := hasSlope1_slope1 f
    rw [h0] at h
    exact ⟨ε, hε, fun z hz => by
      have := h z (le_of_lt hz)
      rw [zpow_zero, one_mul] at this
      linarith⟩

/-! ### Theorem 4.1 -/

theorem mem_commutator_iff' (g : F) :
    g ∈ commutator F ↔ TrivialNearZero (g : UI ≃o UI) ∧ TrivialNearOne (g : UI ≃o UI) := by
  rw [← ker_φ, MonoidHom.mem_ker, φ_apply, trivialNearZero_iff_slope0, trivialNearOne_iff_slope1]
  constructor
  · intro h
    have h' : (slope0 g, slope1 g) = ((0 : ℤ), (0 : ℤ)) := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    exact ⟨(Prod.mk.injEq _ _ _ _).mp h' |>.1, (Prod.mk.injEq _ _ _ _).mp h' |>.2⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]; rfl

end CannonFloydParry

open CannonFloydParry

theorem solution (g : F) :
    g ∈ commutator F ↔ TrivialNearZero (g : UI ≃o UI) ∧ TrivialNearOne (g : UI ≃o UI) :=
  mem_commutator_iff' g
