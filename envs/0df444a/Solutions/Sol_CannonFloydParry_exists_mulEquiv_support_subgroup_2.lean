-- Prove2me | solution 2 for CannonFloydParry.exists_mulEquiv_support_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-22T13:38:58.949688+00:00
-- url     : https://prove2.me/submissions/954f67a8-66a1-4d4f-9852-4aeda346aa27

import Definitions.Def_CannonFloydParry
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson

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

/-- Around any point outside a finite set there is a two-sided interval missing the set. -/
lemma exists_gap_around {B : Finset ℝ} {x : ℝ} (hx : x ∉ (B : Set ℝ)) :
    ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ∩ (B : Set ℝ) = ∅ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp B.finite_toSet.isClosed.isOpen_compl x hx
  refine ⟨ε, hε, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨hz1, hz2⟩ hzB
  exact hball (by rw [Real.ball_eq_Ioo]; exact ⟨hz1, hz2⟩) hzB


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

theorem isThompsonLine_one : IsThompsonLine (1 : ℝ ≃o ℝ) := by
  refine ⟨fun x _ => rfl, fun x _ => rfl, ∅, by simp, fun x y _ _ => ?_⟩
  exact ⟨0, 0, fun z _ => by norm_num⟩

theorem isThompsonLine_inv {f : ℝ ≃o ℝ} (hf : IsThompsonLine f) : IsThompsonLine f⁻¹ := by
  obtain ⟨h0, h1, B, hBd, hB⟩ := hf
  have hinv : ∀ x : ℝ, (f⁻¹ : ℝ ≃o ℝ) x = f.symm x := fun _ => rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, B.image f, ?_, fun x y hxy hgap => ?_⟩
  · rw [hinv, f.symm_apply_eq]; exact (h0 x hx).symm
  · rw [hinv, f.symm_apply_eq]; exact (h1 x hx).symm
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact isDyadic_apply ⟨h0, h1, B, hBd, hB⟩ (hBd b' hb')
  · have hlt : f.symm x < f.symm y := by simpa using hxy
    have hgap' : Set.Ioo (f.symm x) (f.symm y) ∩ (B : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb1, hb2⟩, hbB⟩
      have h1' : x < f b := by simpa using (OrderIso.lt_iff_lt f).mpr hb1
      have h2' : f b < y := by simpa using (OrderIso.lt_iff_lt f).mpr hb2
      rw [Set.eq_empty_iff_forall_notMem] at hgap
      exact hgap (f b) ⟨⟨h1', h2'⟩, by exact_mod_cast Finset.mem_image_of_mem f hbB⟩
    obtain ⟨n, c, haff⟩ := hB _ _ hlt hgap'
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine ⟨-n, -(2 ^ (-n) * c), fun w hw => ?_⟩
    have hmem : f.symm w ∈ Set.Icc (f.symm x) (f.symm y) :=
      ⟨(OrderIso.le_iff_le f.symm).mpr hw.1, (OrderIso.le_iff_le f.symm).mpr hw.2⟩
    have hkey : w = 2 ^ n * f.symm w + c := by
      have := haff _ hmem
      rwa [f.apply_symm_apply] at this
    rw [hinv, zpow_neg]
    field_simp
    linarith [hkey]

theorem isThompsonLine_mul {f g : ℝ ≃o ℝ} (hf : IsThompsonLine f) (hg : IsThompsonLine g) :
    IsThompsonLine (f * g) := by
  have hginv := isThompsonLine_inv hg
  obtain ⟨hf0, hf1, Bf, hBfd, hBf⟩ := hf
  obtain ⟨hg0, hg1, Bg, hBgd, hBg⟩ := hg
  have hmul : ∀ x : ℝ, (f * g : ℝ ≃o ℝ) x = f (g x) := fun _ => rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, Bg ∪ Bf.image (fun b => g.symm b), ?_,
    fun x y hxy hgap => ?_⟩
  · rw [hmul, hg0 x hx, hf0 x hx]
  · rw [hmul, hg1 x hx, hf1 x hx]
  · intro b hb
    rcases Finset.mem_union.mp hb with h | h
    · exact hBgd b h
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp h
      exact isDyadic_apply hginv (hBfd b' hb')
  · rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hgapg : Set.Ioo x y ∩ (Bg : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨hb1, hb2⟩
      exact hgap b ⟨hb1, by simp [Finset.mem_union, hb2]⟩
    obtain ⟨m, d, haffg⟩ := hBg _ _ hxy hgapg
    have hgxy : g x < g y := by simpa using hxy
    have hgapf : Set.Ioo (g x) (g y) ∩ (Bf : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb1, hb2⟩, hbB⟩
      have h1' : x < g.symm b := by simpa using (OrderIso.lt_iff_lt g.symm).mpr hb1
      have h2' : g.symm b < y := by simpa using (OrderIso.lt_iff_lt g.symm).mpr hb2
      refine hgap (g.symm b) ⟨⟨h1', h2'⟩, ?_⟩
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ hbB)
    obtain ⟨n, e, hafff⟩ := hBf _ _ hgxy hgapf
    refine ⟨n + m, 2 ^ n * d + e, fun z hz => ?_⟩
    have hgz : g z ∈ Set.Icc (g x) (g y) :=
      ⟨(OrderIso.le_iff_le g).mpr hz.1, (OrderIso.le_iff_le g).mpr hz.2⟩
    rw [hmul, hafff _ hgz, haffg z hz, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
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

/-- Extension by the identity, as a group homomorphism. -/
noncomputable def extendHom : (UI ≃o UI) →* (ℝ ≃o ℝ) where
  toFun := extend
  map_one' := extend_one
  map_mul' := extend_mul

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





/-- `A` lies in the line model of `F`. -/
theorem isThompsonLine_lineA : IsThompsonLine lineA := by
  refine ⟨fun x hx => aFun_of_le_zero hx, fun x hx => aFun_of_one_le hx,
    {0, 1/2, 3/4, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 1} : Finset ℝ) → b ≤ x ∨ y ≤ b := by
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
            rw [lineA_apply, aFun_of_one_le (by linarith [hz.1])]; norm_num
          · refine ⟨1, -1, fun z hz => ?_⟩
            rw [lineA_apply, aFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
            ring
        · refine ⟨0, -(1/4), fun z hz => ?_⟩
          rw [lineA_apply, aFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
          ring
      · refine ⟨-1, 0, fun z hz => ?_⟩
        rw [lineA_apply, aFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
          zpow_neg, zpow_one]
        ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [lineA_apply, aFun_of_le_zero (by linarith [hz.2])]; norm_num

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

lemma cj_mul (a : ℝ) (k : ℤ) (L M : ℝ ≃o ℝ) : cj a k (L * M) = cj a k L * cj a k M := by
  simp only [cj]
  group

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

lemma resize_mul (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (f g : UI ≃o UI) :
    resize a k h0 h1 (f * g) = resize a k h0 h1 f * resize a k h0 h1 g := by
  apply extend_injective
  simp only [extend_resize, extend_mul, cj_mul]

lemma unresize_resize (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (f : UI ≃o UI)
    (hlo : ∀ x ≤ a, extend (resize a k h0 h1 f) x = x)
    (hhi : ∀ x, a + 2 ^ k ≤ x → extend (resize a k h0 h1 f) x = x) :
    unresize a k (extend (resize a k h0 h1 f)) hlo hhi = f := by
  apply extend_injective
  rw [extend_unresize, extend_resize, cjInv_cj]

lemma resize_unresize (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (M : ℝ ≃o ℝ)
    (hlo : ∀ x ≤ a, M x = x) (hhi : ∀ x, a + 2 ^ k ≤ x → M x = x) :
    extend (resize a k h0 h1 (unresize a k M hlo hhi)) = M := by
  rw [extend_resize, extend_unresize, cj_cjInv]

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

theorem suppSubgroup_equiv (a : ℝ) (k : ℤ) (h0 : 0 ≤ a) (h1 : a + 2 ^ k ≤ 1) (ha : IsDyadic a) :
    Nonempty (↥(suppSubgroup a (a + 2 ^ k)) ≃* ↥F) := by
  refine ⟨{ toFun := ofSupp a k ha, invFun := toSupp a k h0 h1 ha,
            left_inv := ?_, right_inv := ?_, map_mul' := ?_ }⟩
  · intro g
    apply Subtype.ext
    apply Subtype.ext
    apply extend_injective
    simp only [toSupp, ofSupp, extend_resize, extend_unresize, cj_cjInv]
  · intro f
    apply Subtype.ext
    apply extend_injective
    simp only [toSupp, ofSupp, extend_resize, extend_unresize, cjInv_cj]
  · intro x y
    apply Subtype.ext
    apply extend_injective
    simp only [ofSupp, Subgroup.coe_mul, extend_mul, cjInv_mul, extend_unresize]

end CannonFloydParry

open CannonFloydParry

theorem solution {a b : ℝ} (h0 : 0 ≤ a) (hab : a < b) (h1 : b ≤ 1)
    (ha : IsDyadic a) (hb : IsDyadic b) (k : ℤ) (hk : b - a = 2 ^ k) :
    ∃ H : Subgroup F, (∀ g : F, g ∈ H ↔ supp (g : UI ≃o UI) ⊆ Set.Icc a b) ∧
      Nonempty (H ≃* F) := by
  have hb' : b = a + 2 ^ k := by linarith
  subst hb'
  exact ⟨suppSubgroup a (a + 2 ^ k), fun g => Iff.rfl, suppSubgroup_equiv a k h0 h1 ha⟩
