-- Prove2me | solution 3 for CannonFloydParry.closure_mapA_mapB_eq_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T17:54:03.130965+00:00
-- url     : https://prove2.me/submissions/7b9b3f99-6459-44d0-9c16-4972b17dbf39

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_represents_word_exponents
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson

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

lemma getD_chain {R : ℝ → ℝ → Prop} : ∀ (xs : List ℝ),
    (∀ j, j + 1 < xs.length → R (xs.getD j 0) (xs.getD (j + 1) 0)) → List.IsChain R xs := by
  intro xs
  induction xs with
  | nil => intro _; exact List.isChain_nil
  | cons x rest ih =>
      intro h
      refine List.isChain_cons.mpr ⟨?_, ih ?_⟩
      · intro y hy
        cases rest with
        | nil => simp at hy
        | cons z t =>
            have hyz : z = y := by simpa using hy
            subst hyz
            have := h 0 (by simp)
            simpa using this
      · intro j hj
        have := h (j + 1) (by simpa using hj)
        simpa using this

end CannonFloydParry

namespace CannonFloydParry

/-! ### The marks of a tree increase -/

lemma marks_length_eq (t : TTree) : t.marks.length = t.leafCount + 1 := by
  have haux : ∀ (u : TTree) (a b : ℝ), (u.marksAux a b).length + 1 = u.leafCount := by
    intro u
    induction u with
    | leaf => intro a b; simp [TTree.marksAux, TTree.leafCount]
    | node l r ihl ihr =>
        intro a b
        rw [TTree.marksAux, TTree.leafCount]
        have h1 := ihl a ((a + b) / 2)
        have h2 := ihr ((a + b) / 2) b
        simp only [List.length_append, List.length_cons]
        omega
  show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).length = t.leafCount + 1
  have := haux t 0 1
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

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

lemma getD_map {l : List ℝ} {g : ℝ → ℝ} {i : ℕ} (hi : i < l.length) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]


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


/-- **An element of the line model carries dyadic rationals to dyadic rationals.**

This is Cannon–Floyd–Parry's own argument, immediately following their definition: `f(0) = 0`,
so on the first piece `f x = 2 ^ n * x` with dyadic intercept `0`; since the right endpoint of a
piece is dyadic and its image is therefore dyadic, the next piece's intercept is dyadic too; and
so on inductively along the breakpoints.  Note that dyadic intercepts are *derived* here, not
assumed — the definition asks only that breakpoints be dyadic and slopes be powers of two. -/
theorem isDyadic_apply {f : ℝ ≃o ℝ} (hf : IsThompsonLine f) {x : ℝ} (hx : IsDyadic x) :
    IsDyadic (f x) := by
  obtain ⟨hlo, hhi, B, hBd, hB⟩ := hf
  -- adjoin `0`, so that every point of `[0, ∞)` has a breakpoint of the enlarged set below it
  set B' : Finset ℝ := insert 0 B with hB'def
  have hB'd : ∀ b ∈ B', IsDyadic b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    · exact hBd b hb
  have hzero : (0:ℝ) ∈ B' := Finset.mem_insert_self _ _
  -- induction along the breakpoints, on how many of them lie below the point
  have key : ∀ n : ℕ, ∀ y : ℝ, (B'.filter (fun b => b < y)).card = n → 0 ≤ y →
      IsDyadic y → IsDyadic (f y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hcard hy0 hyd
      rcases eq_or_lt_of_le hy0 with hy | hy
      · rw [← hy, hlo 0 le_rfl]; exact ⟨0, 0, by norm_num⟩
      · -- `p` is the last breakpoint strictly below `y`
        have hmem0 : (0:ℝ) ∈ B'.filter (fun b => b < y) := Finset.mem_filter.mpr ⟨hzero, hy⟩
        have hne : (B'.filter (fun b => b < y)).Nonempty := ⟨0, hmem0⟩
        set p := (B'.filter (fun b => b < y)).max' hne with hpdef
        have hpmem : p ∈ B'.filter (fun b => b < y) := Finset.max'_mem _ _
        have hpB' : p ∈ B' := (Finset.mem_filter.mp hpmem).1
        have hpy : p < y := by
          have := (Finset.mem_filter.mp hpmem).2
          simpa using this
        have hp0 : 0 ≤ p := Finset.le_max' _ 0 hmem0
        -- nothing of `B` lies strictly between `p` and `y`
        have hgap : Set.Ioo p y ∩ (B : Set ℝ) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro b ⟨⟨hb1, hb2⟩, hbB⟩
          have hbf : b ∈ B'.filter (fun b => b < y) :=
            Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hbB, by simpa using hb2⟩
          exact absurd (Finset.le_max' _ b hbf) (not_le.mpr hb1)
        obtain ⟨m, c, haff⟩ := hB p y hpy hgap
        -- the induction hypothesis applies at `p`, which has strictly fewer breakpoints below it
        have hsub : B'.filter (fun b => b < p) ⊆ B'.filter (fun b => b < y) := by
          intro b hb
          obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨hb1, lt_trans hb2 hpy⟩
        have hssub : B'.filter (fun b => b < p) ⊂ B'.filter (fun b => b < y) :=
          (Finset.ssubset_iff_of_subset hsub).mpr ⟨p, hpmem, by simp⟩
        have hlt : (B'.filter (fun b => b < p)).card < n := by
          rw [← hcard]; exact Finset.card_lt_card hssub
        have hfp : IsDyadic (f p) := ih _ hlt p rfl hp0 (hB'd p hpB')
        -- hence the intercept of this piece is dyadic
        have hcp : f p = 2 ^ m * p + c := haff p ⟨le_rfl, le_of_lt hpy⟩
        have hcd : IsDyadic c := by
          have hc : c = f p + -(2 ^ m * p) := by linarith
          rw [hc]
          exact isDyadic_add hfp (isDyadic_neg (isDyadic_zpow_mul (hB'd p hpB')))
        rw [haff y ⟨le_of_lt hpy, le_rfl⟩]
        exact isDyadic_add (isDyadic_zpow_mul hyd) hcd
  rcases le_or_gt 0 x with hx0 | hx0
  · exact key _ x rfl hx0 hx
  · rw [hlo x (le_of_lt hx0)]; exact hx

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


end CannonFloydParry

namespace CannonFloydParry

/-- The midpoint of the standard dyadic interval `[c/2^k, (c+1)/2^k]`, written so that it is
visibly a dyadic rational of level `k+1`. -/
noncomputable def md (c k : ℕ) : ℝ := (2 * (c : ℝ) + 1) / 2 ^ (k + 1)

lemma md_eq (c k : ℕ) :
    md c k = ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 := by
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [md]
  field_simp
  ring

lemma lt_md (c k : ℕ) : (c : ℝ) / 2 ^ k < md c k := by
  have h : (0 : ℝ) < 2 ^ k := by positivity
  have e : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
  have hp : (0 : ℝ) < 1 / 2 ^ k := by positivity
  rw [md_eq]
  linarith

lemma md_lt (c k : ℕ) : md c k < ((c : ℝ) + 1) / 2 ^ k := by
  have h : (0 : ℝ) < 2 ^ k := by positivity
  have e : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
  have hp : (0 : ℝ) < 1 / 2 ^ k := by positivity
  rw [md_eq]
  linarith

/-- A standard dyadic interval is a genuine interval: its left endpoint is below its right one. -/
lemma sdi_lt {x y : ℝ} (h : IsStandardDyadicInterval x y) : x < y := by
  obtain ⟨a, n, -, rfl, rfl⟩ := h
  have hp : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have e : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
  linarith

/-- **No straddling.** A standard dyadic interval sitting inside `[c/2^k, (c+1)/2^k]` cannot
contain the midpoint `md c k` in its interior unless it *is* `[c/2^k, (c+1)/2^k]`. -/
lemma no_straddle {x y : ℝ} (h : IsStandardDyadicInterval x y) {c k : ℕ}
    (hlo : (c : ℝ) / 2 ^ k ≤ x) (hhi : y ≤ ((c : ℝ) + 1) / 2 ^ k)
    (h1 : x < md c k) (h2 : md c k < y) :
    x = (c : ℝ) / 2 ^ k ∧ y = ((c : ℝ) + 1) / 2 ^ k := by
  obtain ⟨a, n, han, rfl, rfl⟩ := h
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- the interval is no longer than the ambient one, so `k ≤ n`
  have hd : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ k := by
    have e1 : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
    have e2 : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
    linarith
  have hkn : k ≤ n := by
    rcases Nat.lt_or_ge n k with hcon | hle
    · exfalso
      have hnat : (2 : ℕ) ^ n < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hcon
      have hlt : (2 : ℝ) ^ n < 2 ^ k := by exact_mod_cast hnat
      have : (1 : ℝ) / 2 ^ k < 1 / 2 ^ n := one_div_lt_one_div_of_lt h2n hlt
      linarith
    · exact hle
  rcases eq_or_lt_of_le hkn with rfl | hlt
  · -- same level: the numerators must agree
    have hca : (c : ℝ) ≤ (a : ℝ) := by
      have := (div_le_div_iff_of_pos_right h2k).mp hlo
      exact this
    have hac : (a : ℝ) + 1 ≤ (c : ℝ) + 1 := (div_le_div_iff_of_pos_right h2k).mp hhi
    have : (a : ℝ) = (c : ℝ) := le_antisymm (by linarith) hca
    rw [this]
    exact ⟨rfl, rfl⟩
  · -- strictly deeper level: the midpoint is itself a multiple of `1/2^n`, so it cannot lie
    -- strictly between two consecutive multiples
    exfalso
    obtain ⟨d, hd'⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    set M : ℕ := (2 * c + 1) * 2 ^ d with hM
    have hmd : md c k = (M : ℝ) / 2 ^ n := by
      have hk : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
      have hdd : (2 : ℝ) ^ d ≠ 0 := by positivity
      have hsplit : (2 : ℝ) ^ n = 2 ^ (k + 1) * 2 ^ d := by rw [hd', pow_add]
      rw [md, hM, hsplit]
      push_cast
      field_simp
    rw [hmd] at h1 h2
    have hlt1 : (a : ℝ) < (M : ℝ) := (div_lt_div_iff_of_pos_right h2n).mp h1
    have hlt2 : (M : ℝ) < (a : ℝ) + 1 := (div_lt_div_iff_of_pos_right h2n).mp h2
    have n1 : a < M := by exact_mod_cast hlt1
    have n2 : M < a + 1 := by
      have : (M : ℝ) < ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega

/-- In a chain of standard dyadic intervals with at least two entries, the head is strictly
below the last entry. -/
lemma chain_lt_getLast : ∀ (l : List ℝ) (x v : ℝ),
    List.IsChain IsStandardDyadicInterval (x :: l) → (x :: l).getLast? = some v → l ≠ [] →
    x < v := by
  intro l
  induction l with
  | nil => intro x v _ _ h; exact absurd rfl h
  | cons y t ih =>
      intro x v hch hlast _
      have hxy : IsStandardDyadicInterval x y :=
        (List.isChain_cons.mp hch).1 y (by simp)
      have hch' : List.IsChain IsStandardDyadicInterval (y :: t) := (List.isChain_cons.mp hch).2
      have hlast' : (y :: t).getLast? = some v := by
        rw [List.getLast?_cons_cons] at hlast; exact hlast
      rcases eq_or_ne t [] with rfl | ht
      · have : v = y := by simpa using hlast'.symm
        subst this; exact sdi_lt hxy
      · exact lt_trans (sdi_lt hxy) (ih y v hch' hlast' ht)

/-- **The midpoint is a mark.** A chain of standard dyadic intervals running from `c/2^k` up to
`(c+1)/2^k` must contain the midpoint, unless it is the two-element chain consisting of the
ambient interval itself. -/
lemma md_mem (c k : ℕ) : ∀ (xs : List ℝ), List.IsChain IsStandardDyadicInterval xs →
    ∀ u, xs.head? = some u → (c : ℝ) / 2 ^ k ≤ u →
    xs.getLast? = some (((c : ℝ) + 1) / 2 ^ k) → u < md c k →
    md c k ∈ xs ∨ (u = (c : ℝ) / 2 ^ k ∧ xs.length = 2) := by
  intro xs
  induction xs with
  | nil => intro _ u hh; simp at hh
  | cons x rest ih =>
      intro hch u hh hlo hlast hu
      have hux : u = x := by simpa using hh.symm
      subst hux
      cases rest with
      | nil =>
          exfalso
          have : u = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast
          have := md_lt c k
          linarith
      | cons y t =>
          have hxy : IsStandardDyadicInterval u y :=
            (List.isChain_cons.mp hch).1 y (by simp)
          have hch' : List.IsChain IsStandardDyadicInterval (y :: t) := (List.isChain_cons.mp hch).2
          have hlast' : (y :: t).getLast? = some (((c : ℝ) + 1) / 2 ^ k) := by
            rw [List.getLast?_cons_cons] at hlast; exact hlast
          have hy_le : y ≤ ((c : ℝ) + 1) / 2 ^ k := by
            rcases eq_or_ne t [] with rfl | ht
            · have : y = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast'
              exact le_of_eq this
            · exact le_of_lt (chain_lt_getLast t y _ hch' hlast' ht)
          rcases lt_trichotomy (md c k) y with hmy | hmy | hmy
          · -- straddle: forced to be the whole interval, hence a two-element chain
            obtain ⟨hx, hy⟩ := no_straddle hxy hlo hy_le hu hmy
            refine Or.inr ⟨hx, ?_⟩
            have ht : t = [] := by
              by_contra ht
              have := chain_lt_getLast t y _ hch' hlast' ht
              rw [hy] at this
              exact absurd this (lt_irrefl _)
            subst ht
            simp
          · exact Or.inl (by simp [hmy])
          · have hlo' : (c : ℝ) / 2 ^ k ≤ y := le_of_lt (lt_of_le_of_lt hlo (sdi_lt hxy))
            rcases ih hch' y (by simp) hlo' hlast' hmy with hmem | ⟨hyc, -⟩
            · exact Or.inl (by simp [hmem])
            · exfalso
              have := sdi_lt hxy
              rw [hyc] at this
              linarith

/-- **Existence.** Every chain of standard dyadic intervals from `c/2^k` to `(c+1)/2^k` is the
mark list of a tree placed on that interval. Strong induction on the length: the chain is split
at the midpoint, and each half is a chain one level deeper. -/
lemma exists_tree : ∀ (N : ℕ) (xs : List ℝ), xs.length ≤ N →
    List.IsChain IsStandardDyadicInterval xs →
    ∀ c k : ℕ, c + 1 ≤ 2 ^ k →
    xs.head? = some ((c : ℝ) / 2 ^ k) → xs.getLast? = some (((c : ℝ) + 1) / 2 ^ k) →
    ∃ t : TTree, xs = (c : ℝ) / 2 ^ k ::
      (t.marksAux ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k) ++ [((c : ℝ) + 1) / 2 ^ k]) := by
  intro N
  induction N with
  | zero =>
      intro xs hlen _ c k _ hh _
      exfalso
      have : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this
      simp at hh
  | succ N ih =>
      intro xs hlen hch c k hc hh hlast
      -- the two halves live at level `k+1`
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hlow : ((2 * c : ℕ) : ℝ) / 2 ^ (k + 1) = (c : ℝ) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast; field_simp; ring
      have hmidL : (((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = md c k := by
        rw [md]; push_cast; ring
      have hmidR : ((2 * c + 1 : ℕ) : ℝ) / 2 ^ (k + 1) = md c k := by
        rw [md]; push_cast; ring
      have htop : (((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((c : ℝ) + 1) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast; field_simp; ring
      -- length two is the leaf case
      rcases eq_or_ne xs.length 2 with hlen2 | hlen2
      · match xs, hlen2 with
        | [p, q], _ =>
            refine ⟨TTree.leaf, ?_⟩
            have hp : p = (c : ℝ) / 2 ^ k := by simpa using hh
            have hq : q = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast
            subst hp; subst hq
            simp [TTree.marksAux]
      · -- otherwise the midpoint is one of the marks
        have hmem : md c k ∈ xs := by
          rcases md_mem c k xs hch _ hh le_rfl hlast (lt_md c k) with h | ⟨-, h2⟩
          · exact h
          · exact absurd h2 hlen2
        obtain ⟨xs₁, xs₂, rfl⟩ := List.append_of_mem hmem
        have hne1 : xs₁ ≠ [] := by
          intro h; subst h
          simp at hh
          have := lt_md c k
          rw [← hh] at this
          exact absurd this (lt_irrefl _)
        have hne2 : xs₂ ≠ [] := by
          intro h; subst h
          rw [List.getLast?_append_of_ne_nil _ (by simp)] at hlast
          simp at hlast
          have := md_lt c k
          rw [hlast] at this
          exact absurd this (lt_irrefl _)
        -- the two halves, as lists
        have hsplit : xs₁ ++ md c k :: xs₂ = (xs₁ ++ [md c k]) ++ xs₂ := by simp
        have hchL : List.IsChain IsStandardDyadicInterval (xs₁ ++ [md c k]) := by
          refine hch.prefix ⟨xs₂, ?_⟩
          simp
        have hchR : List.IsChain IsStandardDyadicInterval (md c k :: xs₂) :=
          hch.right_of_append
        -- heads and last entries of the two halves
        have hhL : (xs₁ ++ [md c k]).head? = some (((2 * c : ℕ) : ℝ) / 2 ^ (k + 1)) := by
          rw [hlow]
          rw [List.head?_append_of_ne_nil _ hne1]
          rw [List.head?_append_of_ne_nil _ hne1] at hh
          exact hh
        have hlastL : (xs₁ ++ [md c k]).getLast? = some ((((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1)) := by
          rw [hmidL, List.getLast?_append_of_ne_nil _ (by simp)]
          simp
        have hhR : (md c k :: xs₂).head? = some (((2 * c + 1 : ℕ) : ℝ) / 2 ^ (k + 1)) := by
          rw [hmidR]; simp
        have hlastR :
            (md c k :: xs₂).getLast? = some ((((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1)) := by
          rw [htop]
          rw [List.getLast?_cons_of_ne_nil hne2]
          rw [hsplit, List.getLast?_append_of_ne_nil _ hne2] at hlast
          exact hlast
        -- lengths shrink
        have hl1 : 1 ≤ xs₁.length := List.length_pos_iff.mpr hne1
        have hl2 : 1 ≤ xs₂.length := List.length_pos_iff.mpr hne2
        have hlenAll : xs₁.length + 1 + xs₂.length ≤ N + 1 := by
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
        have hlenL : (xs₁ ++ [md c k]).length ≤ N := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hlenR : (md c k :: xs₂).length ≤ N := by
          simp only [List.length_cons]
          omega
        obtain ⟨l, hlEq⟩ := ih _ hlenL hchL (2 * c) (k + 1) (by omega) hhL hlastL
        obtain ⟨r, hrEq⟩ := ih _ hlenR hchR (2 * c + 1) (k + 1) (by omega) hhR hlastR
        rw [hlow, hmidL] at hlEq
        rw [hmidR, htop] at hrEq
        -- read the two halves off and reassemble
        have hxs1 : xs₁ = (c : ℝ) / 2 ^ k :: l.marksAux ((c : ℝ) / 2 ^ k) (md c k) := by
          have : xs₁ ++ [md c k] =
              ((c : ℝ) / 2 ^ k :: l.marksAux ((c : ℝ) / 2 ^ k) (md c k)) ++ [md c k] := by
            rw [hlEq]; simp
          exact List.append_cancel_right this
        have hxs2 : xs₂ = r.marksAux (md c k) (((c : ℝ) + 1) / 2 ^ k) ++ [((c : ℝ) + 1) / 2 ^ k] := by
          have := hrEq
          simpa using this
        refine ⟨TTree.node l r, ?_⟩
        rw [hxs1, hxs2, TTree.marksAux, ← md_eq]
        simp [List.append_assoc]

end CannonFloydParry

namespace CannonFloydParry

/-! ### Small tools -/

/-- A uniform bound over a finite set of eventually-true properties. -/
lemma finset_uniform (S : Finset ℝ) (P : ℝ → ℕ → Prop)
    (h : ∀ b ∈ S, ∃ K : ℕ, ∀ M, K ≤ M → P b M) :
    ∃ K : ℕ, ∀ b ∈ S, ∀ M, K ≤ M → P b M := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun b hb => absurd hb (Finset.notMem_empty b)⟩
  | insert a s _ ih =>
      obtain ⟨Ka, hKa⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨Ks, hKs⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      refine ⟨max Ka Ks, fun b hb M hM => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hKa M (le_trans (le_max_left _ _) hM)
      · exact hKs b hb M (le_trans (le_max_right _ _) hM)

lemma isDyadic_den' {v : ℝ} (h : IsDyadic v) :
    ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, v = (a : ℝ) / 2 ^ M := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨k, fun M hM => ⟨m * 2 ^ (M - k), ?_⟩⟩
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hd : ((2 : ℝ) ^ (M - k)) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ M = 2 ^ k * 2 ^ (M - k) := by
    rw [← pow_add]; congr 1; omega
  rw [h2]
  push_cast
  field_simp

lemma getD_range_map {g : ℕ → ℝ} {n k : ℕ} (hk : k < n) :
    ((List.range n).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

lemma head?_eq_getD {l : List ℝ} (h : l ≠ []) : l.head? = some (l.getD 0 0) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

lemma getLast?_eq_getD : ∀ (l : List ℝ), l ≠ [] →
    l.getLast? = some (l.getD (l.length - 1) 0) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
      intro _
      cases t with
      | nil => rfl
      | cons b t' =>
          rw [List.getLast?_cons_cons, ih (by simp)]
          show some ((b :: t').getD (t'.length) 0) = some ((a :: b :: t').getD (t'.length + 1) 0)
          rw [List.getD_cons_succ]

lemma two_zpow_div_pow {e : ℤ} {p q : ℕ} (hq : (q : ℤ) = p - e) :
    (2 : ℝ) ^ e / 2 ^ p = 1 / 2 ^ q := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [← zpow_natCast (2 : ℝ) p, ← zpow_sub₀ h2, ← zpow_natCast (2 : ℝ) q, hq, one_div,
    ← zpow_neg, neg_sub]

/-- The tree whose marks are a given standard dyadic partition (existence half of
`existsUnique_tree_marks_eq`). -/
lemma exists_tree_marks {xs : List ℝ} (h : IsStandardDyadicPartition xs) :
    ∃ t : TTree, t.marks = xs := by
  obtain ⟨hh, hl, hc⟩ := h
  have hh' : xs.head? = some ((0 : ℕ) / (2 : ℝ) ^ (0 : ℕ)) := by norm_num [hh]
  have hl' : xs.getLast? = some ((((0 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (0 : ℕ)) := by norm_num [hl]
  obtain ⟨t, ht⟩ := exists_tree xs.length xs le_rfl hc 0 0 (by norm_num) hh' hl'
  refine ⟨t, ?_⟩
  show (0 : ℝ) :: (t.marksAux 0 1 ++ [1]) = xs
  rw [ht]
  norm_num

/-! ### One piece of the uniform partition -/

/-- On a piece `[k/2^p, (k+1)/2^p]` of the uniform partition with `p = 2K`, where `K` bounds the
dyadic denominators of the breakpoints and of their images: `f` is affine on the piece, and the
image of the piece is a standard dyadic interval. -/
lemma piece_spec {f : UI ≃o UI} {B' : Finset ℝ}
    (hB'01 : ∀ b ∈ B', b ∈ Set.Icc (0 : ℝ) 1)
    (hform : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → u < v →
      Set.Ioo u v ∩ (B' : Set ℝ) = ∅ →
      ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc u v, extend f z = 2 ^ n * z + c)
    (hrange : ∀ z ∈ Set.Icc (0 : ℝ) 1, extend f z ∈ Set.Icc (0 : ℝ) 1)
    (K : ℕ)
    (hK : ∀ b ∈ insert (0 : ℝ) (insert 1 B'), ∀ M, K ≤ M →
      (∃ a : ℤ, b = (a : ℝ) / 2 ^ M) ∧ (∃ a : ℤ, extend f b = (a : ℝ) / 2 ^ M))
    (k : ℕ) (hk : k < 2 ^ (2 * K)) :
    (∃ (a c : ℝ), ∀ z ∈ Set.Icc ((k : ℝ) / 2 ^ (2 * K)) (((k : ℝ) + 1) / 2 ^ (2 * K)),
      extend f z = a * z + c) ∧
    IsStandardDyadicInterval (extend f ((k : ℝ) / 2 ^ (2 * K)))
      (extend f (((k : ℝ) + 1) / 2 ^ (2 * K))) := by
  classical
  set p := 2 * K with hp
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  set xk : ℝ := (k : ℝ) / 2 ^ p with hxk
  set xk1 : ℝ := ((k : ℝ) + 1) / 2 ^ p with hxk1
  have hk' : (k : ℝ) + 1 ≤ 2 ^ p := by exact_mod_cast hk
  have hxk0 : 0 ≤ xk := by positivity
  have hxklt : xk < xk1 := by
    rw [hxk, hxk1, div_lt_div_iff_of_pos_right hpos]; linarith
  have hxk1le : xk1 ≤ 1 := by
    rw [hxk1, div_le_one hpos]; exact hk'
  have hxk_lt1 : xk < 1 := lt_of_lt_of_le hxklt hxk1le
  -- the nearest breakpoint at or below the piece
  set S₀ : Finset ℝ := (insert (0 : ℝ) B').filter (fun b => b ≤ xk) with hS₀
  have hS₀ne : S₀.Nonempty := ⟨0, by simp [hS₀, hxk0]⟩
  set b : ℝ := S₀.max' hS₀ne with hb
  have hb_mem : b ∈ S₀ := Finset.max'_mem _ _
  have hb_le : b ≤ xk := (Finset.mem_filter.mp hb_mem).2
  have hb_in : b ∈ insert (0 : ℝ) B' := (Finset.mem_filter.mp hb_mem).1
  have hb01 : b ∈ Set.Icc (0 : ℝ) 1 := by
    rcases Finset.mem_insert.mp hb_in with h0 | hb'
    · rw [h0]; exact ⟨le_refl _, by norm_num⟩
    · exact hB'01 b hb'
  -- the nearest breakpoint strictly above it
  set S₁ : Finset ℝ := (insert (1 : ℝ) B').filter (fun c => b < c) with hS₁
  have hS₁ne : S₁.Nonempty := ⟨1, by simp [hS₁]; linarith⟩
  set bp : ℝ := S₁.min' hS₁ne with hbp
  have hbp_mem : bp ∈ S₁ := Finset.min'_mem _ _
  have hbp_gt : b < bp := (Finset.mem_filter.mp hbp_mem).2
  have hbp_in : bp ∈ insert (1 : ℝ) B' := (Finset.mem_filter.mp hbp_mem).1
  have hbp01 : bp ∈ Set.Icc (0 : ℝ) 1 := by
    rcases Finset.mem_insert.mp hbp_in with h1 | hbp'
    · rw [h1]; exact ⟨by norm_num, le_refl _⟩
    · exact hB'01 bp hbp'
  -- no breakpoint strictly between them
  have hgap : Set.Ioo b bp ∩ (B' : Set ℝ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro c ⟨hc, hcB⟩
    have hcS₁ : c ∈ S₁ := by
      simp only [hS₁, Finset.mem_filter, Finset.mem_insert]
      exact ⟨Or.inr hcB, hc.1⟩
    have := Finset.min'_le S₁ c hcS₁
    linarith [hc.2]
  obtain ⟨e, c₀, hform'⟩ := hform b bp hb01 hbp01 hbp_gt hgap
  -- the piece lies inside the gap
  have hbp_gt_xk : xk < bp := by
    by_contra hcon
    push_neg at hcon
    have hbp_ne1 : bp ≠ 1 := by intro h1; rw [h1] at hcon; linarith
    have hbpB : bp ∈ B' := by
      rcases Finset.mem_insert.mp hbp_in with h1 | h
      · exact absurd h1 hbp_ne1
      · exact h
    have hbpS₀ : bp ∈ S₀ := by
      simp only [hS₀, Finset.mem_filter, Finset.mem_insert]
      exact ⟨Or.inr hbpB, hcon⟩
    have := Finset.le_max' S₀ bp hbpS₀
    linarith
  have hKp : K ≤ p := by omega
  have hbp_in' : bp ∈ insert (0 : ℝ) (insert 1 B') := by
    rcases Finset.mem_insert.mp hbp_in with h1 | h
    · rw [h1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  have hb_in' : b ∈ insert (0 : ℝ) (insert 1 B') := by
    rcases Finset.mem_insert.mp hb_in with h0 | h
    · rw [h0]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  obtain ⟨⟨abp, habp⟩, -⟩ := hK bp hbp_in' p hKp
  have hxk1_le_bp : xk1 ≤ bp := by
    rw [habp] at hbp_gt_xk ⊢
    rw [hxk, div_lt_div_iff_of_pos_right hpos] at hbp_gt_xk
    rw [hxk1, div_le_div_iff_of_pos_right hpos]
    have : (k : ℤ) < abp := by exact_mod_cast hbp_gt_xk
    have : (k : ℤ) + 1 ≤ abp := this
    exact_mod_cast this
  have hsub : ∀ z ∈ Set.Icc xk xk1, z ∈ Set.Icc b bp := fun z hz =>
    ⟨le_trans hb_le hz.1, le_trans hz.2 hxk1_le_bp⟩
  refine ⟨⟨2 ^ e, c₀, fun z hz => hform' z (hsub z hz)⟩, ?_⟩
  -- the values at the two ends of the piece
  have hy := hform' xk (hsub xk ⟨le_refl _, le_of_lt hxklt⟩)
  have hy1 := hform' xk1 (hsub xk1 ⟨le_of_lt hxklt, le_refl _⟩)
  have hfb := hform' b ⟨le_refl _, le_of_lt hbp_gt⟩
  have hfbp := hform' bp ⟨le_of_lt hbp_gt, le_refl _⟩
  -- dyadic data for `b`, `bp`, `f b` at level `K` and at level `p`
  obtain ⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩ := hK b hb_in' K le_rfl
  obtain ⟨⟨βp, hβp⟩, -⟩ := hK b hb_in' p hKp
  obtain ⟨⟨β', hβ'⟩, -⟩ := hK bp hbp_in' K le_rfl
  -- the slope exponent is at most `K`: the gap is at least `2^{-K}` long and maps into `[0,1]`
  have hKpos : (0 : ℝ) < 2 ^ K := by positivity
  have hgaplen : (1 : ℝ) / 2 ^ K ≤ bp - b := by
    rw [hβ, hβ'] at hbp_gt ⊢
    rw [div_lt_div_iff_of_pos_right hKpos] at hbp_gt
    have h1 : β + 1 ≤ β' := by exact_mod_cast hbp_gt
    have h2 : (β : ℝ) + 1 ≤ β' := by exact_mod_cast h1
    rw [← sub_div, div_le_div_iff_of_pos_right hKpos]
    linarith
  have hfb0 : 0 ≤ extend f b := (hrange b hb01).1
  have hfbp1 : extend f bp ≤ 1 := (hrange bp hbp01).2
  have hslope : (2 : ℝ) ^ e * (bp - b) ≤ 1 := by
    have : extend f bp - extend f b = 2 ^ e * (bp - b) := by rw [hfbp, hfb]; ring
    linarith
  have heK : e ≤ (K : ℤ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (2 : ℝ) ^ ((K : ℤ) + 1) ≤ 2 ^ e :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ ((K : ℤ) + 1) = 2 * 2 ^ K := by
      rw [zpow_add_one₀ (by norm_num), zpow_natCast]; ring
    have h3 : (2 : ℝ) ^ e * (bp - b) ≥ 2 * 2 ^ K * (1 / 2 ^ K) := by
      rw [← h2]
      exact mul_le_mul h1 hgaplen (by positivity) (by positivity)
    have h4 : (2 : ℝ) * 2 ^ K * (1 / 2 ^ K) = 2 := by field_simp
    linarith
  -- the level of the image piece
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = (p : ℤ) - e :=
    ⟨((p : ℤ) - e).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hKq : K ≤ q := by omega
  have hqpos : (0 : ℝ) < 2 ^ q := by positivity
  have hzp : (2 : ℝ) ^ e / 2 ^ p = 1 / 2 ^ q := two_zpow_div_pow hq
  have h2q : (2 : ℝ) ^ q = 2 ^ K * 2 ^ (q - K) := by
    rw [← pow_add]; congr 1; omega
  -- the numerator of the left endpoint of the image piece
  set m : ℤ := (k : ℤ) - βp + γ * 2 ^ (q - K) with hm
  have hy_eq : extend f xk = (m : ℝ) / 2 ^ q := by
    have hc₀ : c₀ = extend f b - 2 ^ e * b := by linarith [hfb]
    rw [hy, hc₀, hγ, hβp, hxk, hm]
    push_cast
    have e1 : (2 : ℝ) ^ e * ((k : ℝ) / 2 ^ p) = (k : ℝ) * (1 / 2 ^ q) := by
      rw [← hzp]; ring
    have e2 : (2 : ℝ) ^ e * ((βp : ℝ) / 2 ^ p) = (βp : ℝ) * (1 / 2 ^ q) := by
      rw [← hzp]; ring
    have e3 : (γ : ℝ) / 2 ^ K = (γ : ℝ) * 2 ^ (q - K) / 2 ^ q := by
      rw [h2q]; field_simp
    rw [e1, e2, e3]
    field_simp
    ring
  have hy1_eq : extend f xk1 = ((m : ℝ) + 1) / 2 ^ q := by
    have hd : extend f xk1 = extend f xk + 2 ^ e / 2 ^ p := by
      rw [hy1, hy, hxk1, hxk]; ring
    rw [hd, hy_eq, hzp]
    field_simp
  -- the numerator is nonnegative and the right endpoint is at most `1`
  have hy0 : 0 ≤ extend f xk := (hrange xk ⟨hxk0, le_of_lt hxk_lt1⟩).1
  have hy11 : extend f xk1 ≤ 1 := (hrange xk1 ⟨by positivity, hxk1le⟩).2
  have hm0 : 0 ≤ m := by
    rw [hy_eq] at hy0
    have : (0 : ℝ) ≤ (m : ℝ) := by
      by_contra hcon; push_neg at hcon
      have : (m : ℝ) / 2 ^ q < 0 := div_neg_of_neg_of_pos hcon hqpos
      linarith
    exact_mod_cast this
  have hm1 : m + 1 ≤ 2 ^ q := by
    rw [hy1_eq, div_le_one hqpos] at hy11
    exact_mod_cast hy11
  refine ⟨m.toNat, q, ?_, ?_, ?_⟩
  · have hcast : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg hm0
    have h : (m.toNat : ℤ) + 1 ≤ ((2 ^ q : ℕ) : ℤ) := by
      rw [hcast]; push_cast; exact hm1
    exact_mod_cast h
  · rw [hy_eq]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hm0).symm
  · rw [hy1_eq]
    congr 1
    have : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    rw [← this]
    push_cast
    ring

/-! ### Every Thompson map has a tree diagram -/

/-- **CFP Lemma 2.2**, in tree form: a map satisfying the Thompson condition is represented by
some tree diagram.  The domain tree cuts `[0,1]` into `2 ^ p` equal parts with `p` large. -/
theorem exists_represents_of_isThompson {f : UI ≃o UI} (hf : IsThompson f) :
    ∃ d : TreeDiagram, Represents d f := by
  classical
  obtain ⟨B, hBd, hB⟩ := hf
  have hL : IsThompsonLine (extend f) := (isThompsonLine_extend_iff f).mpr ⟨B, hBd, hB⟩
  have hf0 : extend f 0 = 0 := extend_eq_self_of_le_zero f (le_refl 0)
  have hf1 : extend f 1 = 1 := extend_eq_self_of_one_le f (le_refl 1)
  have hmono : Monotone (extend f) := (extend f).monotone
  have hrange : ∀ z ∈ Set.Icc (0 : ℝ) 1, extend f z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨by rw [← hf0]; exact hmono hz.1, by rw [← hf1]; exact hmono hz.2⟩
  -- the breakpoints inside `[0,1]`
  set B' : Finset ℝ := B.filter (fun b => b ∈ Set.Icc (0 : ℝ) 1) with hB'
  have hB'01 : ∀ b ∈ B', b ∈ Set.Icc (0 : ℝ) 1 := fun b hb => (Finset.mem_filter.mp hb).2
  have hform : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → u < v →
      Set.Ioo u v ∩ (B' : Set ℝ) = ∅ →
      ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc u v, extend f z = 2 ^ n * z + c := by
    intro u v hu hv huv hgap
    have hgapB : Set.Ioo (u : ℝ) v ∩ (B : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem] at hgap ⊢
      intro c ⟨hc, hcB⟩
      refine hgap c ⟨hc, ?_⟩
      rw [Finset.mem_coe, hB', Finset.mem_filter]
      exact ⟨Finset.mem_coe.mp hcB, ⟨le_trans hu.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hv.2⟩⟩
    obtain ⟨n, c, h⟩ := hB ⟨u, hu⟩ ⟨v, hv⟩ huv hgapB
    refine ⟨n, c, fun z hz => ?_⟩
    have hz01 : z ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hu.1 hz.1, le_trans hz.2 hv.2⟩
    rw [extend_apply, extendFun_of_mem _ hz01]
    exact h ⟨z, hz01⟩ hz
  -- a uniform dyadic denominator for the breakpoints, the endpoints, and their images
  set S : Finset ℝ := insert 0 (insert 1 B') with hS
  have hSd : ∀ b ∈ S, IsDyadic b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨1, 0, by norm_num⟩
    exact hBd b (Finset.mem_filter.mp hb).1
  obtain ⟨K, hK⟩ := finset_uniform S
    (fun b M => (∃ a : ℤ, b = (a : ℝ) / 2 ^ M) ∧ (∃ a : ℤ, extend f b = (a : ℝ) / 2 ^ M))
    (by
      intro b hb
      obtain ⟨K₁, hK₁⟩ := isDyadic_den' (hSd b hb)
      obtain ⟨K₂, hK₂⟩ := isDyadic_den' (isDyadic_apply hL (hSd b hb))
      exact ⟨max K₁ K₂, fun M hM =>
        ⟨hK₁ M (le_trans (le_max_left _ _) hM), hK₂ M (le_trans (le_max_right _ _) hM)⟩⟩)
  have hpieces := fun k hk => piece_spec hB'01 hform hrange K hK k hk
  set p := 2 * K with hp
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  -- the uniform partition and its image
  set xs : List ℝ := (List.range (2 ^ p + 1)).map (fun k : ℕ => (k : ℝ) / 2 ^ p) with hxs
  have hxs_len : xs.length = 2 ^ p + 1 := by simp [hxs]
  have hxs_ne : xs ≠ [] := by
    intro h; rw [h] at hxs_len; simp at hxs_len
  have hxs_getD : ∀ k, k ≤ 2 ^ p → xs.getD k 0 = (k : ℝ) / 2 ^ p := fun k hk =>
    getD_range_map (Nat.lt_succ_of_le hk)
  have hxs0 : xs.getD 0 0 = 0 := by rw [hxs_getD 0 (Nat.zero_le _)]; simp
  have hxs1 : xs.getD (xs.length - 1) 0 = 1 := by
    rw [hxs_len, Nat.add_sub_cancel, hxs_getD _ le_rfl]
    push_cast
    field_simp
  set ys : List ℝ := xs.map (extend f) with hys
  have hys_len : ys.length = 2 ^ p + 1 := by rw [hys, List.length_map, hxs_len]
  have hys_ne : ys ≠ [] := by
    intro h; rw [h] at hys_len; simp at hys_len
  have hys_getD : ∀ k, k ≤ 2 ^ p → ys.getD k 0 = extend f ((k : ℝ) / 2 ^ p) := by
    intro k hk
    rw [hys, getD_map (by rw [hxs_len]; exact Nat.lt_succ_of_le hk), hxs_getD k hk]
  have hxs_sdp : IsStandardDyadicPartition xs := by
    refine ⟨?_, ?_, ?_⟩
    · rw [head?_eq_getD hxs_ne, hxs0]
    · rw [getLast?_eq_getD xs hxs_ne, hxs1]
    · refine getD_chain _ ?_
      intro j hj
      rw [hxs_len] at hj
      rw [hxs_getD j (by omega), hxs_getD (j + 1) (by omega)]
      exact ⟨j, p, by omega, rfl, by push_cast; rfl⟩
  have hys_sdp : IsStandardDyadicPartition ys := by
    refine ⟨?_, ?_, ?_⟩
    · rw [head?_eq_getD hys_ne, hys_getD 0 (Nat.zero_le _)]
      simp [hf0]
    · rw [getLast?_eq_getD ys hys_ne, hys_len, Nat.add_sub_cancel, hys_getD _ le_rfl]
      have : ((2 ^ p : ℕ) : ℝ) / 2 ^ p = 1 := by push_cast; field_simp
      rw [this, hf1]
    · refine getD_chain _ ?_
      intro j hj
      rw [hys_len] at hj
      rw [hys_getD j (by omega), hys_getD (j + 1) (by omega)]
      have := (hpieces j (by omega)).2
      push_cast
      exact this
  obtain ⟨R, hR⟩ := exists_tree_marks hxs_sdp
  obtain ⟨T, hT⟩ := exists_tree_marks hys_sdp
  have hlc : R.leafCount = T.leafCount := by
    have h1 := marks_length_eq R
    have h2 := marks_length_eq T
    rw [hR, hxs_len] at h1
    rw [hT, hys_len] at h2
    omega
  refine ⟨⟨R, T, hlc⟩, mem_F_of_isThompson ⟨B, hBd, hB⟩, ?_, ?_⟩
  · show AffineOnPieces (extend f) R.marks
    rw [hR]
    refine getD_chain _ ?_
    intro j hj
    rw [hxs_len] at hj
    rw [hxs_getD j (by omega), hxs_getD (j + 1) (by omega)]
    have := (hpieces j (by omega)).1
    push_cast
    exact this
  · show R.marks.map (extend f) = T.marks
    rw [hR, hT]

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
theorem closure_mapA_mapB_eq_F' : Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) = F := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact mapA_mem_F
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact mapB_mem_F
  · intro f hf
    have hT : IsThompson f := mem_F_iff_isThompson.mp hf
    obtain ⟨d, hd⟩ := exists_represents_of_isThompson hT
    rw [represents_word_exponents hd]
    exact mul_mem (wordFrom_mem_closure _ _) (inv_mem (wordFrom_mem_closure _ _))

end CannonFloydParry

open CannonFloydParry

theorem solution : Subgroup.closure {mapA, mapB} = F := closure_mapA_mapB_eq_F'
