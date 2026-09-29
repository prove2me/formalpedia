-- Prove2me | solution 1 for CannonFloydParry.exists_biInvariant_linearOrder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-16T09:15:52.596579+00:00
-- url     : https://prove2.me/submissions/1fffc8a7-65c1-430a-8013-cca20e957780

import Definitions.Def_CannonFloydParry
import Mathlib

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
theorem mem_F_iff_isThompson {f : UI ≃o UI} : f ∈ F ↔ IsThompson f := by
  refine ⟨fun hf => ?_, mem_F_of_isThompson⟩
  induction hf using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact (isThompsonLine_extend_iff 1).mp (by rw [extend_one]; exact isThompsonLine_one)
  | mul x y _ _ hx hy =>
      refine (isThompsonLine_extend_iff _).mp ?_
      rw [extend_mul]
      exact isThompsonLine_mul ((isThompsonLine_extend_iff x).mpr hx)
        ((isThompsonLine_extend_iff y).mpr hy)
  | inv x _ hx =>
      refine (isThompsonLine_extend_iff _).mp ?_
      rw [show extend x⁻¹ = (extend x)⁻¹ from map_inv extendHom x]
      exact isThompsonLine_inv ((isThompsonLine_extend_iff x).mpr hx)

/-! ## Theorem 4.11: `F` is a totally ordered group

Cannon–Floyd–Parry's *order positive* elements (p. 232) are those that are the identity to the
left of some point and have derivative less than `1` on an interval just to the right of it — in
other words, the first point an element moves, it moves down.  That set is a positive cone: it
misses `1`, it is closed under multiplication, it is closed under conjugation, and every element
other than `1` lies in it or has its inverse in it.  Those four facts make
`f < g ↔ f⁻¹ g` order positive a bi-invariant strict total order. -/

lemma eq_self_of_forall_lt {M : ℝ ≃o ℝ} {a : ℝ} (h : ∀ x < a, M x = x) : M a = a := by
  rcases lt_trichotomy (M a) a with hlt | heq | hgt
  · have hfix : M (M a) = M a := h _ hlt
    have : M a = a := M.injective hfix
    linarith
  · exact heq
  · obtain ⟨y, hy1, hy2⟩ : ∃ y, a < y ∧ y < M a := ⟨(a + M a) / 2, by linarith, by linarith⟩
    have hMw : M (M.symm y) = y := M.apply_symm_apply y
    rcases lt_or_ge (M.symm y) a with hwa | hwa
    · rw [h _ hwa] at hMw
      linarith
    · have : M a ≤ M (M.symm y) := M.monotone hwa
      rw [hMw] at this
      linarith

/-! ### The line-model image of an element of `F` -/

/-- Each element of `F`, as an order isomorphism of the whole line. -/
noncomputable def line (f : ↥F) : ℝ ≃o ℝ := extend ((f : ↥F) : UI ≃o UI)

lemma isThompsonLine_line (f : ↥F) : IsThompsonLine (line f) :=
  (isThompsonLine_extend_iff _).mpr (mem_F_iff_isThompson.mp f.2)

lemma line_one : line (1 : ↥F) = 1 := extend_one

lemma line_mul (f g : ↥F) : line (f * g) = line f * line g := extend_mul _ _

lemma line_inv (f : ↥F) : line f⁻¹ = (line f)⁻¹ := map_inv extendHom _

lemma line_apply_mul (f g : ↥F) (x : ℝ) : line (f * g) x = line f (line g x) := by
  rw [line_mul]
  rfl

lemma line_injective : Function.Injective line := fun _ _ h => Subtype.ext (extend_injective h)

/-! ### The positive cone -/

/-- `f` is **order positive**: it is the identity to the left of some `t`, and lies strictly
below the diagonal on an interval immediately to the right of `t`. -/
def cone (f : ↥F) : Prop :=
  ∃ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ (∀ x, x < t → line f x = x) ∧
    (∀ x, t < x → x < t + δ → line f x < x)

lemma cone_fix {f : ↥F} {t : ℝ} (h : ∀ x, x < t → line f x = x) : line f t = t :=
  eq_self_of_forall_lt (fun x hx => h x hx)

lemma not_cone_one : ¬ cone (1 : ↥F) := by
  rintro ⟨t, δ, hδ, -, h2⟩
  have h := h2 (t + δ / 2) (by linarith) (by linarith)
  rw [line_one] at h
  have hid : (1 : ℝ ≃o ℝ) (t + δ / 2) = t + δ / 2 := rfl
  rw [hid] at h
  exact absurd h (lt_irrefl _)

lemma cone_mul {f g : ↥F} (hf : cone f) (hg : cone g) : cone (f * g) := by
  obtain ⟨t₁, δ₁, hδ₁, hid₁, hlt₁⟩ := hf
  obtain ⟨t₂, δ₂, hδ₂, hid₂, hlt₂⟩ := hg
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · refine ⟨t₁, min δ₁ (t₂ - t₁), lt_min hδ₁ (by linarith), ?_, ?_⟩
    · intro x hx
      rw [line_apply_mul, hid₂ x (by linarith), hid₁ x hx]
    · intro x hx1 hx2
      have hm1 := min_le_left δ₁ (t₂ - t₁)
      have hm2 := min_le_right δ₁ (t₂ - t₁)
      rw [line_apply_mul, hid₂ x (by linarith)]
      exact hlt₁ x hx1 (by linarith)
  · subst h
    refine ⟨t₁, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_⟩
    · intro x hx
      rw [line_apply_mul, hid₂ x hx, hid₁ x hx]
    · intro x hx1 hx2
      have hm1 := min_le_left δ₁ δ₂
      have hm2 := min_le_right δ₁ δ₂
      have hgt : t₁ < line g x := by
        have hfx := cone_fix hid₂
        have hmono : line g t₁ < line g x := (line g).lt_iff_lt.mpr hx1
        rw [hfx] at hmono
        exact hmono
      have hglt : line g x < x := hlt₂ x hx1 (by linarith)
      have hflt : line f (line g x) < line g x := hlt₁ _ hgt (by linarith)
      rw [line_apply_mul]
      linarith
  · refine ⟨t₂, min δ₂ (t₁ - t₂), lt_min hδ₂ (by linarith), ?_, ?_⟩
    · intro x hx
      rw [line_apply_mul, hid₂ x (by linarith), hid₁ x (by linarith)]
    · intro x hx1 hx2
      have hm1 := min_le_left δ₂ (t₁ - t₂)
      have hm2 := min_le_right δ₂ (t₁ - t₂)
      have hglt : line g x < x := hlt₂ x hx1 (by linarith)
      rw [line_apply_mul, hid₁ (line g x) (by linarith)]
      exact hglt

lemma cone_conj {f : ↥F} (hf : cone f) (c : ↥F) : cone (c⁻¹ * f * c) := by
  obtain ⟨t, δ, hδ, hid, hlt⟩ := hf
  have hkey : ∀ x : ℝ, line (c⁻¹ * f * c) x = (line c).symm (line f (line c x)) := by
    intro x
    rw [line_apply_mul, line_apply_mul, line_inv]
    rfl
  have hpos : (line c).symm t < (line c).symm (t + δ) :=
    (line c).symm.lt_iff_lt.mpr (by linarith)
  refine ⟨(line c).symm t, (line c).symm (t + δ) - (line c).symm t, by linarith, ?_, ?_⟩
  · intro x hx
    have hHx : line c x < t := by
      have h := (line c).lt_iff_lt.mpr hx
      rwa [(line c).apply_symm_apply] at h
    rw [hkey x, hid _ hHx, (line c).symm_apply_apply]
  · intro x hx1 hx2
    have hHx1 : t < line c x := by
      have h := (line c).lt_iff_lt.mpr hx1
      rwa [(line c).apply_symm_apply] at h
    have hHx2 : line c x < t + δ := by
      have hx2' : x < (line c).symm (t + δ) := by linarith
      have h := (line c).lt_iff_lt.mpr hx2'
      rwa [(line c).apply_symm_apply] at h
    rw [hkey x]
    have h := (line c).symm.lt_iff_lt.mpr (hlt _ hHx1 hHx2)
    rwa [(line c).symm_apply_apply] at h

/-- A gap to the right of any point: the breakpoint set is finite. -/
lemma exists_gap_right (B : Finset ℝ) (t : ℝ) :
    ∃ δ > 0, Set.Ioo t (t + δ) ∩ (B : Set ℝ) = ∅ := by
  classical
  rcases (B.filter (fun u => t < u)).eq_empty_or_nonempty with hE | hN
  · refine ⟨1, one_pos, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨⟨hu1, _⟩, huB⟩ := hu
    have hmem : u ∈ B.filter (fun u => t < u) :=
      Finset.mem_filter.mpr ⟨Finset.mem_coe.mp huB, hu1⟩
    rw [hE] at hmem
    exact absurd hmem (Finset.notMem_empty u)
  · have hmin := Finset.mem_filter.mp ((B.filter (fun u => t < u)).min'_mem hN)
    refine ⟨(B.filter (fun u => t < u)).min' hN - t, by linarith [hmin.2], ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨⟨hu1, hu2⟩, huB⟩ := hu
    have hmem : u ∈ B.filter (fun u => t < u) :=
      Finset.mem_filter.mpr ⟨Finset.mem_coe.mp huB, hu1⟩
    have := (B.filter (fun u => t < u)).min'_le u hmem
    linarith

lemma cone_trichotomy (f : ↥F) (hf : f ≠ 1) : cone f ∨ cone f⁻¹ := by
  classical
  obtain ⟨hlo, hhi, B, hBd, hBa⟩ := isThompsonLine_line f
  have hSne : {x : ℝ | line f x ≠ x}.Nonempty := by
    rcases Set.eq_empty_or_nonempty {x : ℝ | line f x ≠ x} with hE | hN
    · exfalso
      apply hf
      apply line_injective
      rw [line_one]
      apply RelIso.ext
      intro x
      show line f x = x
      have hx : x ∉ {x : ℝ | line f x ≠ x} := by rw [hE]; exact Set.notMem_empty x
      by_contra hc
      exact hx hc
    · exact hN
  have hbdd : BddBelow {x : ℝ | line f x ≠ x} := by
    refine ⟨0, fun x hx => ?_⟩
    by_contra hneg
    push_neg at hneg
    exact hx (hlo x (le_of_lt hneg))
  set t := sInf {x : ℝ | line f x ≠ x} with ht
  have hid : ∀ x, x < t → line f x = x := by
    intro x hx
    by_contra hne
    have hge : t ≤ x := csInf_le hbdd hne
    linarith
  have hft : line f t = t := eq_self_of_forall_lt hid
  obtain ⟨δ₀, hδ₀, hgap⟩ := exists_gap_right B t
  obtain ⟨n, c, hc⟩ := hBa t (t + δ₀) (by linarith) hgap
  have hcval : c = t - 2 ^ n * t := by
    have h := hc t ⟨le_rfl, by linarith⟩
    rw [hft] at h
    linarith
  have hform : ∀ z, t ≤ z → z ≤ t + δ₀ → line f z - z = (2 ^ n - 1) * (z - t) := by
    intro z h1 h2
    have h := hc z ⟨h1, h2⟩
    rw [hcval] at h
    rw [h]
    ring
  rcases lt_trichotomy n 0 with hn | hn | hn
  · left
    refine ⟨t, δ₀, hδ₀, hid, ?_⟩
    intro x hx1 hx2
    have h := hform x (le_of_lt hx1) (le_of_lt hx2)
    have h2n : (2:ℝ) ^ n < 1 := by
      rw [zpow_lt_one_iff_right₀ (by norm_num : (1:ℝ) < 2)]
      exact hn
    nlinarith [h, h2n, hx1]
  · exfalso
    subst hn
    have hfix : ∀ z, t ≤ z → z ≤ t + δ₀ → line f z = z := by
      intro z h1 h2
      have h := hform z h1 h2
      simp only [zpow_zero] at h
      linarith
    have hlb : ∀ x ∈ {x : ℝ | line f x ≠ x}, t + δ₀ ≤ x := by
      intro x hx
      by_contra hxl
      push_neg at hxl
      rcases lt_or_ge x t with h | h
      · exact hx (hid x h)
      · exact hx (hfix x h (le_of_lt hxl))
    have hle : t + δ₀ ≤ t := le_csInf hSne hlb
    linarith
  · right
    have h2n : (1:ℝ) < 2 ^ n := by
      rw [one_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)]
      exact hn
    have hup : ∀ z, t < z → z ≤ t + δ₀ → z < line f z := by
      intro z h1 h2
      have h := hform z (le_of_lt h1) h2
      nlinarith [h, h2n, h1]
    have hLpos : t + δ₀ < line f (t + δ₀) := hup (t + δ₀) (by linarith) le_rfl
    refine ⟨t, min δ₀ (line f (t + δ₀) - t), lt_min hδ₀ (by linarith), ?_, ?_⟩
    · intro x hx
      rw [line_inv]
      show (line f).symm x = x
      rw [(line f).symm_apply_eq]
      exact (hid x hx).symm
    · intro x hx1 hx2
      have hm1 := min_le_left δ₀ (line f (t + δ₀) - t)
      have hm2 := min_le_right δ₀ (line f (t + δ₀) - t)
      rw [line_inv]
      show (line f).symm x < x
      have hxy : line f ((line f).symm x) = x := (line f).apply_symm_apply x
      have hyt : t < (line f).symm x := by
        by_contra hc2
        push_neg at hc2
        have hmono : line f ((line f).symm x) ≤ line f t := (line f).monotone hc2
        rw [hxy, hft] at hmono
        linarith
      have hyd : (line f).symm x < t + δ₀ := by
        by_contra hc2
        push_neg at hc2
        have hmono : line f (t + δ₀) ≤ line f ((line f).symm x) := (line f).monotone hc2
        rw [hxy] at hmono
        linarith
      have h := hup _ hyt (le_of_lt hyd)
      rw [hxy] at h
      exact h

/-- The strict relation of Theorem 4.11. -/
def coneLt (f g : ↥F) : Prop := cone (f⁻¹ * g)

instance : IsStrictTotalOrder ↥F coneLt where
  trichotomous := by
    intro a b hab hba
    by_contra hne
    have h : a⁻¹ * b ≠ 1 := fun hc => hne (inv_mul_eq_one.mp hc)
    rcases cone_trichotomy _ h with hc | hc
    · exact hab hc
    · refine hba ?_
      show cone (b⁻¹ * a)
      have hrw : (a⁻¹ * b)⁻¹ = b⁻¹ * a := by group
      rwa [hrw] at hc
  irrefl := by
    intro a
    show ¬ cone (a⁻¹ * a)
    rw [inv_mul_cancel]
    exact not_cone_one
  trans := by
    intro a b c hab hbc
    show cone (a⁻¹ * c)
    have hrw : a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) := by group
    rw [hrw]
    exact cone_mul hab hbc

end CannonFloydParry

open CannonFloydParry

theorem solution :
    ∃ l : LinearOrder F, ∀ a b c : F, l.le a b → l.le (c * a) (c * b) ∧ l.le (a * c) (b * c) := by
  classical
  refine ⟨linearOrderOfSTO coneLt, ?_⟩
  intro a b c hab
  have hab' : a = b ∨ coneLt a b := hab
  refine ⟨?_, ?_⟩
  · rcases hab' with rfl | h
    · exact Or.inl rfl
    · refine Or.inr ?_
      show cone ((c * a)⁻¹ * (c * b))
      have hrw : (c * a)⁻¹ * (c * b) = a⁻¹ * b := by group
      rw [hrw]
      exact h
  · rcases hab' with rfl | h
    · exact Or.inl rfl
    · refine Or.inr ?_
      show cone ((a * c)⁻¹ * (b * c))
      have hrw : (a * c)⁻¹ * (b * c) = c⁻¹ * (a⁻¹ * b) * c := by group
      rw [hrw]
      exact cone_conj h c
