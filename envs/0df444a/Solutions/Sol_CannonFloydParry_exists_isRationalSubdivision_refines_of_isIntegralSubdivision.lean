-- Prove2me | solution 1 for CannonFloydParry.exists_isRationalSubdivision_refines_of_isIntegralSubdivision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:09:29.128255+00:00
-- url     : https://prove2.me/submissions/4c51d659-85b4-41dd-9e18-3558ea7ebac2

import Definitions.Def_CannonFloydParry_PIP
import Mathlib

/-!
# Common rational refinements, part 1: integer linear forms and rational points of cells

For an integer vector `a`, `ell a` is the linear form `x ↦ ∑ aᵢ xᵢ`. The main result here is that
for a finite set of integer forms, every point of `Δₙ` can be replaced by a rational point of
`Δₙ` on which every form has the same sign.
-/

namespace CannonFloydParry.S7

open Set

variable {n : ℕ}

/-- The linear form with integer coefficients `a`. -/
noncomputable def ell (a : Fin (n + 1) → ℤ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, (a i : ℝ) • LinearMap.proj i

lemma ell_apply (a : Fin (n + 1) → ℤ) (x : Fin (n + 1) → ℝ) :
    ell a x = ∑ i, (a i : ℝ) * x i := by
  simp [ell]

lemma ell_neg (a : Fin (n + 1) → ℤ) (x : Fin (n + 1) → ℝ) : ell (-a) x = -ell a x := by
  simp [ell_apply, Finset.sum_neg_distrib]

lemma ell_single (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ell (Pi.single i 1) x = x i := by
  rw [ell_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- Rational approximation keeping all signs of finitely many integer forms. -/
lemma exists_rat_same_sign (L : Finset (Fin (n + 1) → ℤ)) {x : Fin (n + 1) → ℝ}
    (hx : ∑ i, x i = 1) :
    ∃ y : Fin (n + 1) → ℝ, (∀ i, ∃ q : ℚ, y i = q) ∧ ∑ i, y i = 1 ∧
      ∀ a ∈ L, (ell a x = 0 → ell a y = 0) ∧ (ell a x ≠ 0 → 0 < ell a x * ell a y) := by
  classical
  set V : Submodule ℚ ℝ := Submodule.span ℚ (Set.range x) with hV
  have : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  set β := Module.finBasis ℚ V
  set k := Module.finrank ℚ V
  let e : Fin k → ℝ := fun α => (β α : ℝ)
  have hli : LinearIndependent ℚ e :=
    β.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  let c : Fin (n + 1) → Fin k → ℚ := fun i α =>
    β.repr ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩ α
  have hxc : ∀ i, x i = ∑ α, (c i α : ℝ) * e α := by
    intro i
    have h := congrArg Subtype.val (β.sum_repr ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun α _ => ?_)
    rw [Submodule.coe_smul, Rat.smul_def]
  let F : (Fin k → ℝ) → Fin (n + 1) → ℝ := fun r i => ∑ α, (c i α : ℝ) * r α
  let m : (Fin (n + 1) → ℤ) → Fin k → ℚ := fun a α => ∑ i, (a i : ℚ) * c i α
  have hF : ∀ a r, ell a (F r) = ∑ α, (m a α : ℝ) * r α := by
    intro a r
    simp only [ell_apply, F, m, Finset.mul_sum, Finset.sum_mul, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_intCast]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hFe : F e = x := funext fun i => (hxc i).symm
  have hzero : ∀ a, ell a x = 0 → ∀ r, ell a (F r) = 0 := by
    intro a ha r
    have h0 : ∀ α, m a α = 0 := by
      refine Fintype.linearIndependent_iff.mp hli (m a) ?_
      rw [← hFe, hF] at ha
      simpa [Rat.smul_def] using ha
    rw [hF]; simp [h0]
  set L' := L.filter (fun a => ell a x ≠ 0)
  set U : Set (Fin k → ℝ) :=
    (⋂ a ∈ L', {r | 0 < ell a x * ∑ α, (m a α : ℝ) * r α}) ∩ {r | 0 < ∑ i, F r i} with hU
  have hUo : IsOpen U := by
    refine IsOpen.inter (isOpen_biInter_finset fun a _ => ?_) ?_
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  have heU : e ∈ U := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro a ha
      rw [← hF, hFe]
      exact mul_self_pos.mpr (Finset.mem_filter.mp ha).2
    · show 0 < ∑ i, F e i
      rw [hFe, hx]; norm_num
  have hd : DenseRange (fun q : Fin k → ℚ => fun α => (q α : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q, hqU⟩ := hd.exists_mem_open hUo ⟨e, heU⟩
  set r : Fin k → ℝ := fun α => (q α : ℝ)
  set y₀ := F r
  set s := ∑ i, y₀ i
  have hs : 0 < s := hqU.2
  refine ⟨s⁻¹ • y₀, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(∑ j, ∑ α, c j α * q α)⁻¹ * ∑ α, c i α * q α, ?_⟩
    simp [s, y₀, F, r]
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro a ha
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [map_smul, hzero a h0, smul_zero]
    · have h1 : a ∈ L' := Finset.mem_filter.mpr ⟨ha, h0⟩
      have h2 := hqU.1
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h2
      have h3 := h2 a h1
      rw [← hF] at h3
      rw [map_smul, smul_eq_mul]
      have : ell a x * (s⁻¹ * ell a y₀) = s⁻¹ * (ell a x * ell a y₀) := by ring
      rw [this]
      exact mul_pos (inv_pos.mpr hs) h3

/-- A rational point of `Δₙ` in the same cell as `x`, provided the coordinate forms are among
the forms considered. -/
lemma exists_rationalPoint_same_sign (L : Finset (Fin (n + 1) → ℤ))
    (hcoord : ∀ i, Pi.single i 1 ∈ L) {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) :
    ∃ y, IsRationalPoint y ∧
      ∀ a ∈ L, (ell a x = 0 → ell a y = 0) ∧ (ell a x ≠ 0 → 0 < ell a x * ell a y) := by
  obtain ⟨y, hyq, hy1, hy⟩ := exists_rat_same_sign L hx.2
  refine ⟨y, ⟨⟨fun i => ?_, hy1⟩, hyq⟩, hy⟩
  have h := hy _ (hcoord i)
  rw [ell_single, ell_single] at h
  rcases (hx.1 i).eq_or_lt with h0 | h0
  · exact (h.1 h0.symm).ge
  · exact (pos_of_mul_pos_right (h.2 h0.ne') h0.le).le

end CannonFloydParry.S7

/-!
# Common rational refinements, part 2: cells of an arrangement of integer forms

Fix a finite set `L` of integer linear forms, closed under negation and containing the
coordinate forms. The *cell* of a point `x` is the set of forms of `L` that are nonnegative at
`x`. Cells are ordered by reverse inclusion (a smaller cell set is a bigger face). Every cell of a
point of `Δₙ` has a rational representative `bary L σ`. Chains of cells give simplices
(the barycentric-type subdivision of the arrangement). Here we prove the key combinatorial facts:
positive combinations along a chain land in the top cell, chains give affinely independent
points, the chain and support of a positive combination are unique, and every point of `Δₙ` is a
positive combination along a chain.
-/

namespace CannonFloydParry.S7

open Set

variable {n : ℕ}

section Cells

variable (L : Finset (Fin (n + 1) → ℤ))

/-- The cell of `x`: the forms of `L` nonnegative at `x`. -/
noncomputable def cellOf (x : Fin (n + 1) → ℝ) : Finset (Fin (n + 1) → ℤ) :=
  L.filter (fun a => 0 ≤ ell a x)

omit L in
lemma mem_cellOf {L : Finset (Fin (n + 1) → ℤ)} {x : Fin (n + 1) → ℝ} {a : Fin (n + 1) → ℤ} :
    a ∈ cellOf L x ↔ a ∈ L ∧ 0 ≤ ell a x := Finset.mem_filter

/-- A cell with a rational representative in `Δₙ`. -/
def Good (σ : Finset (Fin (n + 1) → ℤ)) : Prop :=
  ∃ y, IsRationalPoint y ∧ cellOf L y = σ

/-- A chosen rational representative of a good cell. -/
noncomputable def bary (σ : Finset (Fin (n + 1) → ℤ)) : Fin (n + 1) → ℝ := by
  classical exact if h : Good L σ then h.choose else 0

variable {L}

lemma bary_spec {σ : Finset (Fin (n + 1) → ℤ)} (h : Good L σ) :
    IsRationalPoint (bary L σ) ∧ cellOf L (bary L σ) = σ := by
  unfold bary; rw [dif_pos h]; exact h.choose_spec

lemma mem_iff_of_good {σ : Finset (Fin (n + 1) → ℤ)} (h : Good L σ) (a : Fin (n + 1) → ℤ) :
    a ∈ σ ↔ a ∈ L ∧ 0 ≤ ell a (bary L σ) := by
  rw [← mem_cellOf, (bary_spec h).2]

lemma ell_neg_of_not_mem {σ : Finset (Fin (n + 1) → ℤ)} (h : Good L σ)
    {a : Fin (n + 1) → ℤ} (haL : a ∈ L) (ha : a ∉ σ) : ell a (bary L σ) < 0 := by
  by_contra h'
  exact ha ((mem_iff_of_good h a).2 ⟨haL, not_lt.mp h'⟩)

lemma neg_mem_of_not_mem (hneg : ∀ a ∈ L, -a ∈ L) {σ : Finset (Fin (n + 1) → ℤ)} (h : Good L σ)
    {a : Fin (n + 1) → ℤ} (haL : a ∈ L) (ha : a ∉ σ) : -a ∈ σ := by
  refine (mem_iff_of_good h _).2 ⟨hneg a haL, ?_⟩
  rw [ell_neg]; linarith [ell_neg_of_not_mem h haL ha]

lemma good_cellOf (hcoord : ∀ i, Pi.single i 1 ∈ L) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ Simplex n) : Good L (cellOf L x) := by
  obtain ⟨y, hy, hs⟩ := exists_rationalPoint_same_sign L hcoord hx
  refine ⟨y, hy, Finset.filter_congr fun a ha => ?_⟩
  obtain ⟨h1, h2⟩ := hs a ha
  by_cases h0 : ell a x = 0
  · simp [h0, h1 h0]
  · have := h2 h0
    constructor <;> intro h <;> nlinarith

lemma ell_sum {ι : Type*} (a : Fin (n + 1) → ℤ) (C : Finset ι) (w : ι → ℝ)
    (f : ι → Fin (n + 1) → ℝ) :
    ell a (∑ σ ∈ C, w σ • f σ) = ∑ σ ∈ C, w σ * ell a (f σ) := by
  rw [map_sum]; simp [map_smul]

/-- The chain condition on a finite set of cells. -/
abbrev IsCh (C : Finset (Finset (Fin (n + 1) → ℤ))) : Prop :=
  IsChain (· ⊆ ·) (C : Set (Finset (Fin (n + 1) → ℤ)))

lemma exists_top {C : Finset (Finset (Fin (n + 1) → ℤ))} (hC : IsCh C) (hne : C.Nonempty) :
    ∃ τ ∈ C, ∀ σ ∈ C, τ ⊆ σ := by
  obtain ⟨τ, hτ, hmin⟩ := C.exists_min_image Finset.card hne
  refine ⟨τ, hτ, fun σ hσ => ?_⟩
  by_cases h : σ = τ
  · rw [h]
  rcases hC hσ hτ h with h1 | h1
  · exact absurd (Finset.eq_of_subset_of_card_le h1 (hmin σ hσ)) h
  · exact h1

lemma IsCh.erase {C : Finset (Finset (Fin (n + 1) → ℤ))} (hC : IsCh C) (τ) : IsCh (C.erase τ) :=
  hC.mono (Finset.coe_subset.mpr (Finset.erase_subset τ C))

/-- A positive combination along a chain lies in the top cell. -/
lemma cellOf_sum (hneg : ∀ a ∈ L, -a ∈ L) {C : Finset (Finset (Fin (n + 1) → ℤ))}
    (hg : ∀ σ ∈ C, Good L σ) {τ : Finset (Fin (n + 1) → ℤ)} (hτC : τ ∈ C)
    (hτ : ∀ σ ∈ C, τ ⊆ σ) {w : Finset (Fin (n + 1) → ℤ) → ℝ} (hw : ∀ σ ∈ C, 0 ≤ w σ)
    (hwτ : 0 < w τ) : cellOf L (∑ σ ∈ C, w σ • bary L σ) = τ := by
  ext a
  rw [mem_cellOf, ell_sum]
  constructor
  · rintro ⟨haL, hpos⟩
    by_contra haτ
    have h1 := ell_neg_of_not_mem (hg τ hτC) haL haτ
    have hna := neg_mem_of_not_mem hneg (hg τ hτC) haL haτ
    have h2 : ∀ σ ∈ C, ell a (bary L σ) ≤ 0 := by
      intro σ hσ
      have := ((mem_iff_of_good (hg σ hσ) (-a)).1 (hτ σ hσ hna)).2
      rw [ell_neg] at this; linarith
    rw [← Finset.add_sum_erase C _ hτC] at hpos
    have h3 : ∑ σ ∈ C.erase τ, w σ * ell a (bary L σ) ≤ 0 :=
      Finset.sum_nonpos fun σ hσ => mul_nonpos_of_nonneg_of_nonpos
        (hw σ (Finset.mem_of_mem_erase hσ)) (h2 σ (Finset.mem_of_mem_erase hσ))
    nlinarith [mul_neg_of_pos_of_neg hwτ h1]
  · intro ha
    exact ⟨((mem_iff_of_good (hg τ hτC) a).1 ha).1, Finset.sum_nonneg fun σ hσ =>
      mul_nonneg (hw σ hσ) ((mem_iff_of_good (hg σ hσ) a).1 (hτ σ hσ ha)).2⟩

/-- A form negative on the top cell and vanishing on the rest of the chain. -/
lemma exists_sep (hneg : ∀ a ∈ L, -a ∈ L) {C : Finset (Finset (Fin (n + 1) → ℤ))}
    (hC : IsCh C) (hg : ∀ σ ∈ C, Good L σ) {τ : Finset (Fin (n + 1) → ℤ)} (hτC : τ ∈ C)
    (hτ : ∀ σ ∈ C, τ ⊆ σ) (hne : (C.erase τ).Nonempty) :
    ∃ a ∈ L, ell a (bary L τ) < 0 ∧ -a ∈ τ ∧ ∀ σ ∈ C.erase τ, ell a (bary L σ) = 0 := by
  obtain ⟨ρ, hρC, hρ⟩ := exists_top (hC.erase τ) hne
  have hρC' := Finset.mem_of_mem_erase hρC
  have hρne : ρ ≠ τ := Finset.ne_of_mem_erase hρC
  obtain ⟨a, haρ, haτ⟩ : ∃ a ∈ ρ, a ∉ τ := by
    by_contra h; push Not at h; exact hρne (Finset.Subset.antisymm h (hτ ρ hρC'))
  have haL := ((mem_iff_of_good (hg ρ hρC') a).1 haρ).1
  have hna := neg_mem_of_not_mem hneg (hg τ hτC) haL haτ
  refine ⟨a, haL, ell_neg_of_not_mem (hg τ hτC) haL haτ, hna, fun σ hσ => ?_⟩
  have hσC := Finset.mem_of_mem_erase hσ
  have e1 := ((mem_iff_of_good (hg σ hσC) a).1 (hρ σ hσ haρ)).2
  have e2 := ((mem_iff_of_good (hg σ hσC) (-a)).1 (hτ σ hσC hna)).2
  rw [ell_neg] at e2; linarith

/-- Points along a chain satisfy no nontrivial affine relation. -/
lemma eq_zero_of_chain (hneg : ∀ a ∈ L, -a ∈ L) :
    ∀ (k : ℕ) (C : Finset (Finset (Fin (n + 1) → ℤ))), C.card = k → IsCh C →
      (∀ σ ∈ C, Good L σ) → ∀ v : Finset (Fin (n + 1) → ℤ) → ℝ, ∑ σ ∈ C, v σ = 0 →
        ∑ σ ∈ C, v σ • bary L σ = 0 → ∀ σ ∈ C, v σ = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro C hk hC hg v hv0 hv1
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨τ, hτC, hτ⟩ := exists_top hC hne
  have hs0 := Finset.add_sum_erase C v hτC
  have hs1 := Finset.add_sum_erase C (fun σ => v σ • bary L σ) hτC
  have hvτ : v τ = 0 := by
    rcases (C.erase τ).eq_empty_or_nonempty with he | hne'
    · rw [he, Finset.sum_empty, add_zero] at hs0; linarith
    · obtain ⟨a, _, h1, _, h0⟩ := exists_sep hneg hC hg hτC hτ hne'
      have := congrArg (ell a) hv1
      rw [← hs1, map_add, ell_sum, Finset.sum_eq_zero (fun σ hσ => by rw [h0 σ hσ, mul_zero]),
        map_smul, smul_eq_mul, add_zero, map_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
  have hrest := ih _ (hk ▸ Finset.card_erase_lt_of_mem hτC) (C.erase τ) rfl (hC.erase τ)
    (fun σ hσ => hg σ (Finset.mem_of_mem_erase hσ)) v (by rw [hvτ] at hs0; linarith)
    (by rw [hvτ, zero_smul, zero_add] at hs1; rw [hs1, hv1])
  intro σ hσ
  by_cases h : σ = τ
  · rw [h]; exact hvτ
  · exact hrest σ (Finset.mem_erase.2 ⟨h, hσ⟩)

lemma le_ell_sum {C : Finset (Finset (Fin (n + 1) → ℤ))} (hg : ∀ σ ∈ C, Good L σ)
    {τ : Finset (Fin (n + 1) → ℤ)} (hτC : τ ∈ C) (hτ : ∀ σ ∈ C, τ ⊆ σ)
    {w : Finset (Fin (n + 1) → ℤ) → ℝ} (hw : ∀ σ ∈ C, 0 ≤ w σ) {a : Fin (n + 1) → ℤ}
    (ha : a ∈ τ) : w τ * ell a (bary L τ) ≤ ell a (∑ σ ∈ C, w σ • bary L σ) := by
  rw [ell_sum, ← Finset.add_sum_erase C _ hτC]
  have : 0 ≤ ∑ σ ∈ C.erase τ, w σ * ell a (bary L σ) :=
    Finset.sum_nonneg fun σ hσ => mul_nonneg (hw σ (Finset.mem_of_mem_erase hσ))
      ((mem_iff_of_good (hg σ (Finset.mem_of_mem_erase hσ)) a).1
        (hτ σ (Finset.mem_of_mem_erase hσ) ha)).2
  linarith

lemma exists_eq_ell_sum (hneg : ∀ a ∈ L, -a ∈ L) {C : Finset (Finset (Fin (n + 1) → ℤ))}
    (hC : IsCh C) (hg : ∀ σ ∈ C, Good L σ) {τ : Finset (Fin (n + 1) → ℤ)} (hτC : τ ∈ C)
    (hτ : ∀ σ ∈ C, τ ⊆ σ) (hne : (C.erase τ).Nonempty) :
    ∃ a ∈ τ, 0 < ell a (bary L τ) ∧ ∀ w : Finset (Fin (n + 1) → ℤ) → ℝ,
      ell a (∑ σ ∈ C, w σ • bary L σ) = w τ * ell a (bary L τ) := by
  obtain ⟨a, _, h1, hna, h0⟩ := exists_sep hneg hC hg hτC hτ hne
  refine ⟨-a, hna, by rw [ell_neg]; linarith, fun w => ?_⟩
  rw [ell_sum, ← Finset.add_sum_erase C _ hτC, Finset.sum_eq_zero, add_zero]
  intro σ hσ
  rw [ell_neg, h0 σ hσ, neg_zero, mul_zero]

lemma weight_le (hneg : ∀ a ∈ L, -a ∈ L) {C D : Finset (Finset (Fin (n + 1) → ℤ))}
    (hC : IsCh C) (hgC : ∀ σ ∈ C, Good L σ) (hgD : ∀ σ ∈ D, Good L σ)
    {τ : Finset (Fin (n + 1) → ℤ)} (hτC : τ ∈ C) (hτ : ∀ σ ∈ C, τ ⊆ σ) (hτD : τ ∈ D)
    (hτ' : ∀ σ ∈ D, τ ⊆ σ) {w w' : Finset (Fin (n + 1) → ℤ) → ℝ} (hw' : ∀ σ ∈ D, 0 ≤ w' σ)
    (hvec : ∑ σ ∈ C, w σ • bary L σ = ∑ σ ∈ D, w' σ • bary L σ) (hne : (C.erase τ).Nonempty) :
    w' τ ≤ w τ := by
  obtain ⟨a, ha, hpos, heq⟩ := exists_eq_ell_sum hneg hC hgC hτC hτ hne
  have h1 := le_ell_sum hgD hτD hτ' hw' ha
  rw [← hvec, heq] at h1
  exact le_of_mul_le_mul_right h1 hpos

/-- Uniqueness of the chain carrying a positive combination. -/
lemma chain_unique (hneg : ∀ a ∈ L, -a ∈ L) (w w' : Finset (Fin (n + 1) → ℤ) → ℝ) :
    ∀ (k : ℕ) (C D : Finset (Finset (Fin (n + 1) → ℤ))), C.card = k → IsCh C → IsCh D →
      (∀ σ ∈ C, Good L σ) → (∀ σ ∈ D, Good L σ) → C.Nonempty → D.Nonempty →
      (∀ σ ∈ C, 0 < w σ) → (∀ σ ∈ D, 0 < w' σ) → ∑ σ ∈ C, w σ = ∑ σ ∈ D, w' σ →
      ∑ σ ∈ C, w σ • bary L σ = ∑ σ ∈ D, w' σ • bary L σ → C = D := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro C D hk hC hD hgC hgD hneC hneD hw hw' hsum hvec
  obtain ⟨τ, hτC, hτ⟩ := exists_top hC hneC
  obtain ⟨τ', hτD, hτ'⟩ := exists_top hD hneD
  have e1 := cellOf_sum hneg hgC hτC hτ (fun σ hσ => (hw σ hσ).le) (hw τ hτC)
  have e2 := cellOf_sum hneg hgD hτD hτ' (fun σ hσ => (hw' σ hσ).le) (hw' τ' hτD)
  rw [hvec, e2] at e1
  subst e1
  have hsC := Finset.add_sum_erase C w hτC
  have hsD := Finset.add_sum_erase D w' hτD
  have hvC := Finset.add_sum_erase C (fun σ => w σ • bary L σ) hτC
  have hvD := Finset.add_sum_erase D (fun σ => w' σ • bary L σ) hτD
  have hC' : C = insert τ' (C.erase τ') := (Finset.insert_erase hτC).symm
  have hD' : D = insert τ' (D.erase τ') := (Finset.insert_erase hτD).symm
  have posC : (C.erase τ').Nonempty → 0 < ∑ σ ∈ C.erase τ', w σ := fun h =>
    Finset.sum_pos (fun σ hσ => hw σ (Finset.mem_of_mem_erase hσ)) h
  have posD : (D.erase τ').Nonempty → 0 < ∑ σ ∈ D.erase τ', w' σ := fun h =>
    Finset.sum_pos (fun σ hσ => hw' σ (Finset.mem_of_mem_erase hσ)) h
  have le1 := weight_le hneg hC hgC hgD hτC hτ hτD hτ' (fun σ hσ => (hw' σ hσ).le) hvec
  have le2 := weight_le hneg hD hgD hgC hτD hτ' hτC hτ (fun σ hσ => (hw σ hσ).le) hvec.symm
  rcases (C.erase τ').eq_empty_or_nonempty with heC | heC <;>
    rcases (D.erase τ').eq_empty_or_nonempty with heD | heD
  · rw [hC', hD', heC, heD]
  · rw [heC, Finset.sum_empty, add_zero] at hsC
    have := le2 heD; have := posD heD; linarith
  · rw [heD, Finset.sum_empty, add_zero] at hsD
    have := le1 heC; have := posC heC; linarith
  · have heq : w τ' = w' τ' := le_antisymm (le2 heD) (le1 heC)
    have := ih _ (hk ▸ Finset.card_erase_lt_of_mem hτC) (C.erase τ') (D.erase τ') rfl
      (hC.erase τ') (hD.erase τ') (fun σ hσ => hgC σ (Finset.mem_of_mem_erase hσ))
      (fun σ hσ => hgD σ (Finset.mem_of_mem_erase hσ)) heC heD
      (fun σ hσ => hw σ (Finset.mem_of_mem_erase hσ))
      (fun σ hσ => hw' σ (Finset.mem_of_mem_erase hσ)) (by linarith)
      (by
        have h := hvC.trans (hvec.trans hvD.symm)
        rw [heq] at h
        exact add_left_cancel h)
    rw [hC', hD', this]

end Cells

end CannonFloydParry.S7

/-!
# Common rational refinements, part 3: every point of `Δₙ` lies on a chain simplex
-/

namespace CannonFloydParry.S7

open Set

variable {n : ℕ} {L : Finset (Fin (n + 1) → ℤ)}

lemma exists_lt_of_ne {x b : Fin (n + 1) → ℝ} (hx : ∑ i, x i = 1) (hb : ∑ i, b i = 1)
    (hne : x ≠ b) : ∃ i, x i < b i := by
  by_contra h
  push Not at h
  apply hne
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 (by rw [hx, hb])
  exact (funext fun i => (this i (Finset.mem_univ i)).symm)

/-- Every point of `Δₙ` is in the convex hull of a chain whose top cell is its own cell. -/
lemma exists_chain_of_mem (hneg : ∀ a ∈ L, -a ∈ L) (hcoord : ∀ i, Pi.single i 1 ∈ L) :
    ∀ (k : ℕ) (x : Fin (n + 1) → ℝ), L.card - (cellOf L x).card = k → x ∈ Simplex n →
      ∃ C : Finset (Finset (Fin (n + 1) → ℤ)), IsCh C ∧ (∀ σ ∈ C, Good L σ) ∧
        cellOf L x ∈ C ∧ (∀ σ ∈ C, cellOf L x ⊆ σ) ∧
        x ∈ convexHull ℝ (↑(C.image (bary L)) : Set (Fin (n + 1) → ℝ)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hk hx
  set τ := cellOf L x with hτdef
  have hgτ : Good L τ := good_cellOf hcoord hx
  obtain ⟨hbq, hbτ⟩ := bary_spec hgτ
  set b := bary L τ with hbdef
  by_cases hxb : x = b
  · refine ⟨{τ}, ?_, by simpa using hgτ, Finset.mem_singleton_self _, by simp, ?_⟩
    · simp [IsCh]
    · rw [hxb]
      exact subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _
        (Finset.mem_singleton_self _)))
  -- the exit point of the ray from `b` through `x`
  set J := τ.filter (fun a => ell a x < ell a b) with hJdef
  have hJ : J.Nonempty := by
    obtain ⟨i, hi⟩ := exists_lt_of_ne hx.2 hbq.1.2 hxb
    refine ⟨Pi.single i 1, Finset.mem_filter.2 ⟨mem_cellOf.2 ⟨hcoord i, ?_⟩, ?_⟩⟩
    · rw [ell_single]; exact hx.1 i
    · rw [ell_single, ell_single]; exact hi
  have hJpos : ∀ a ∈ J, 0 < ell a x := by
    intro a ha
    obtain ⟨haτ, hlt⟩ := Finset.mem_filter.1 ha
    obtain ⟨haL, h0⟩ := mem_cellOf.1 haτ
    rcases h0.eq_or_lt with h0 | h0
    · exfalso
      have : -a ∈ τ := mem_cellOf.2 ⟨hneg a haL, by rw [ell_neg, ← h0]; simp⟩
      rw [← hbτ] at this
      have := (mem_cellOf.1 this).2
      rw [ell_neg] at this
      linarith
    · exact h0
  set r : (Fin (n + 1) → ℤ) → ℝ := fun a => ell a x / (ell a b - ell a x) with hr
  obtain ⟨a₀, ha₀J, hmin⟩ := J.exists_min_image r hJ
  have hd₀ : 0 < ell a₀ b - ell a₀ x := sub_pos.2 (Finset.mem_filter.1 ha₀J).2
  set t := r a₀ with htdef
  have ht : 0 < t := div_pos (hJpos a₀ ha₀J) hd₀
  set y := x + t • (x - b) with hydef
  have hell : ∀ a, ell a y = ell a x + t * (ell a x - ell a b) := by
    intro a; simp [hydef, map_add, map_smul, map_sub]
  have hsub : τ ⊆ cellOf L y := by
    intro a ha
    obtain ⟨haL, h0⟩ := mem_cellOf.1 ha
    refine mem_cellOf.2 ⟨haL, ?_⟩
    rw [hell]
    by_cases hlt : ell a x < ell a b
    · have haJ : a ∈ J := Finset.mem_filter.2 ⟨ha, hlt⟩
      have h1 : t ≤ ell a x / (ell a b - ell a x) := hmin a haJ
      rw [le_div_iff₀ (sub_pos.2 hlt)] at h1
      nlinarith
    · push Not at hlt
      nlinarith
  have hy0 : ell a₀ y = 0 := by
    rw [hell, htdef, hr]
    field_simp
    ring
  have hna₀ : -a₀ ∈ cellOf L y := by
    have ha₀L := (mem_cellOf.1 (Finset.mem_filter.1 ha₀J).1).1
    exact mem_cellOf.2 ⟨hneg a₀ ha₀L, by rw [ell_neg, hy0, neg_zero]⟩
  have hna₀' : -a₀ ∉ τ := by
    intro h
    have := (mem_cellOf.1 h).2
    rw [ell_neg] at this
    linarith [hJpos a₀ ha₀J]
  have hss : τ ⊂ cellOf L y := Finset.ssubset_iff_subset_ne.2
    ⟨hsub, fun h => hna₀' (h ▸ hna₀)⟩
  have hcard : L.card - (cellOf L y).card < k := by
    have h1 := Finset.card_lt_card hss
    have h2 : (cellOf L y).card ≤ L.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have hyS : y ∈ Simplex n := by
    refine ⟨fun i => ?_, ?_⟩
    · have : Pi.single i 1 ∈ τ := mem_cellOf.2 ⟨hcoord i, by rw [ell_single]; exact hx.1 i⟩
      have := (mem_cellOf.1 (hsub this)).2
      rwa [ell_single] at this
    · simp only [hydef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.2, hbq.1.2]
      ring
  obtain ⟨C', hC', hgC', hyC', hsubC', hconv⟩ := ih _ hcard y rfl hyS
  refine ⟨insert τ C', ?_, ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · rw [IsCh, Finset.coe_insert]
    exact hC'.insert fun σ hσ _ => Or.inl (hsub.trans (hsubC' σ hσ))
  · intro σ hσ
    rcases Finset.mem_insert.1 hσ with rfl | hσ
    · exact hgτ
    · exact hgC' σ hσ
  · intro σ hσ
    rcases Finset.mem_insert.1 hσ with rfl | hσ
    · exact subset_refl _
    · exact hsub.trans (hsubC' σ hσ)
  · have hy' : y ∈ convexHull ℝ (↑((insert τ C').image (bary L)) : Set (Fin (n + 1) → ℝ)) :=
      convexHull_mono (by
        rw [Finset.coe_subset]
        exact Finset.image_subset_image (Finset.subset_insert _ _)) hconv
    have hb' : b ∈ convexHull ℝ (↑((insert τ C').image (bary L)) : Set (Fin (n + 1) → ℝ)) :=
      subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _
        (Finset.mem_insert_self _ _)))
    have hx' : x = (1 + t)⁻¹ • y + (t * (1 + t)⁻¹) • b := by
      have h1 : (1 + t) ≠ 0 := by linarith
      ext i
      simp only [hydef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [hx']
    exact convex_convexHull ℝ _ hy' hb' (inv_nonneg.2 (by linarith))
      (mul_nonneg ht.le (inv_nonneg.2 (by linarith))) (by field_simp)

end CannonFloydParry.S7

/-!
# Common rational refinements, part 4: the chain complex of an arrangement

The simplices spanned by the representatives of chains of cells form a simplicial complex with
rational vertices whose underlying space is `Δₙ`, and each simplex lies in the closed cell of a
point of `Δₙ`.
-/

namespace CannonFloydParry.S7

open Set

variable {n : ℕ} {L : Finset (Fin (n + 1) → ℤ)}

/-- The simplices of the chain complex. -/
def arrFaces (L : Finset (Fin (n + 1) → ℤ)) : Set (Finset (Fin (n + 1) → ℝ)) :=
  {s | ∃ C : Finset (Finset (Fin (n + 1) → ℤ)), C.Nonempty ∧ IsCh C ∧ (∀ σ ∈ C, Good L σ) ∧
    s = C.image (bary L)}

lemma bary_injOn {C : Finset (Finset (Fin (n + 1) → ℤ))} (hg : ∀ σ ∈ C, Good L σ) :
    Set.InjOn (bary L) (C : Set (Finset (Fin (n + 1) → ℤ))) := by
  intro σ hσ σ' hσ' h
  rw [← (bary_spec (hg σ hσ)).2, ← (bary_spec (hg σ' hσ')).2, h]

lemma affineIndependent_chain (hneg : ∀ a ∈ L, -a ∈ L) {C : Finset (Finset (Fin (n + 1) → ℤ))}
    (hC : IsCh C) (hg : ∀ σ ∈ C, Good L σ) :
    AffineIndependent ℝ ((↑) : (C.image (bary L)) → (Fin (n + 1) → ℝ)) := by
  classical
  have h1 : AffineIndependent ℝ (fun σ : C => bary L σ) := by
    rw [affineIndependent_iff]
    intro t w hw0 hw1 e he
    set T := t.map (Function.Embedding.subtype (· ∈ C)) with hT
    set v : Finset (Fin (n + 1) → ℤ) → ℝ := fun σ => if h : σ ∈ C then w ⟨σ, h⟩ else 0 with hv
    have hve : ∀ e : C, v e = w e := fun e => by simp [hv, e.2]
    have e0 : ∑ σ ∈ T, v σ = ∑ e ∈ t, w e := by
      rw [hT, Finset.sum_map]
      exact Finset.sum_congr rfl fun e _ => hve e
    have e1 : ∑ σ ∈ T, v σ • bary L σ = ∑ e ∈ t, w e • bary L e := by
      rw [hT, Finset.sum_map]
      exact Finset.sum_congr rfl fun e _ => by rw [Function.Embedding.subtype_apply, hve e]
    have hTC : ∀ σ ∈ T, σ ∈ C := fun σ hσ => by
      obtain ⟨e, _, rfl⟩ := Finset.mem_map.1 hσ
      exact e.2
    have := eq_zero_of_chain hneg _ T rfl (hC.mono fun σ hσ => hTC σ hσ)
      (fun σ hσ => hg σ (hTC σ hσ)) v (e0.trans hw0) (e1.trans hw1) e.1
      (Finset.mem_map_of_mem _ he)
    rwa [hve e] at this
  have h2 := h1.range
  have hset : (↑(C.image (bary L)) : Set (Fin (n + 1) → ℝ)) ⊆
      Set.range (fun σ : C => bary L σ) := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    exact ⟨⟨σ, hσ⟩, rfl⟩
  exact h2.mono hset

lemma inter_subset_chain (hneg : ∀ a ∈ L, -a ∈ L) {C D : Finset (Finset (Fin (n + 1) → ℤ))}
    (hC : IsCh C) (hD : IsCh D) (hgC : ∀ σ ∈ C, Good L σ) (hgD : ∀ σ ∈ D, Good L σ) :
    convexHull ℝ (↑(C.image (bary L)) : Set (Fin (n + 1) → ℝ)) ∩
        convexHull ℝ (↑(D.image (bary L)) : Set (Fin (n + 1) → ℝ)) ⊆
      convexHull ℝ ((↑(C.image (bary L)) : Set (Fin (n + 1) → ℝ)) ∩ ↑(D.image (bary L))) := by
  classical
  rintro z ⟨hzC, hzD⟩
  rw [Finset.mem_convexHull'] at hzC hzD
  obtain ⟨w, hw0, hw1, hwz⟩ := hzC
  obtain ⟨w', hw0', hw1', hwz'⟩ := hzD
  rw [Finset.sum_image (bary_injOn hgC)] at hw1 hwz
  rw [Finset.sum_image (bary_injOn hgD)] at hw1' hwz'
  have hw0C : ∀ σ ∈ C, 0 ≤ w (bary L σ) := fun σ hσ => hw0 _ (Finset.mem_image_of_mem _ hσ)
  have hw0D : ∀ σ ∈ D, 0 ≤ w' (bary L σ) := fun σ hσ => hw0' _ (Finset.mem_image_of_mem _ hσ)
  set Cp := C.filter (fun σ => 0 < w (bary L σ)) with hCp
  set Dp := D.filter (fun σ => 0 < w' (bary L σ)) with hDp
  have s1 : ∑ σ ∈ Cp, w (bary L σ) = 1 := by
    rw [hCp, Finset.sum_filter_of_ne fun σ hσ h => lt_of_le_of_ne (hw0C σ hσ) (Ne.symm h), hw1]
  have s2 : ∑ σ ∈ Dp, w' (bary L σ) = 1 := by
    rw [hDp, Finset.sum_filter_of_ne fun σ hσ h => lt_of_le_of_ne (hw0D σ hσ) (Ne.symm h), hw1']
  have v1 : ∑ σ ∈ Cp, w (bary L σ) • bary L σ = z := by
    rw [hCp, Finset.sum_filter_of_ne fun σ hσ h =>
      lt_of_le_of_ne (hw0C σ hσ) (Ne.symm (left_ne_zero_of_smul h)), hwz]
  have v2 : ∑ σ ∈ Dp, w' (bary L σ) • bary L σ = z := by
    rw [hDp, Finset.sum_filter_of_ne fun σ hσ h =>
      lt_of_le_of_ne (hw0D σ hσ) (Ne.symm (left_ne_zero_of_smul h)), hwz']
  have hneC : Cp.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h, Finset.sum_empty] at s1; norm_num at s1
  have hneD : Dp.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h, Finset.sum_empty] at s2; norm_num at s2
  have hCpC : Cp ⊆ C := Finset.filter_subset _ _
  have hDpD : Dp ⊆ D := Finset.filter_subset _ _
  have heq : Cp = Dp := chain_unique hneg (fun σ => w (bary L σ)) (fun σ => w' (bary L σ)) _
    Cp Dp rfl (hC.mono (Finset.coe_subset.2 hCpC)) (hD.mono (Finset.coe_subset.2 hDpD))
    (fun σ hσ => hgC σ (hCpC hσ)) (fun σ hσ => hgD σ (hDpD hσ)) hneC hneD
    (fun σ hσ => (Finset.mem_filter.1 hσ).2) (fun σ hσ => (Finset.mem_filter.1 hσ).2)
    (s1.trans s2.symm) (v1.trans v2.symm)
  rw [← v1]
  refine (convex_convexHull ℝ _).sum_mem (fun σ hσ => (Finset.mem_filter.1 hσ).2.le) s1
    fun σ hσ => subset_convexHull ℝ _ ⟨?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hCpC hσ))
  · exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hDpD (heq ▸ hσ)))

/-- The chain complex of the arrangement. -/
noncomputable def arrComplex (L : Finset (Fin (n + 1) → ℤ)) (hneg : ∀ a ∈ L, -a ∈ L) :
    Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) where
  faces := arrFaces L
  isRelLowerSet_faces := by
    classical
    rintro s ⟨C, hne, hC, hg, rfl⟩
    refine ⟨hne.image _, fun t hts htne => ?_⟩
    refine ⟨C.filter (fun σ => bary L σ ∈ t), ?_, hC.mono (Finset.coe_subset.2
      (Finset.filter_subset _ _)), fun σ hσ => hg σ (Finset.mem_filter.1 hσ).1, ?_⟩
    · obtain ⟨p, hp⟩ := htne
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (hts hp)
      exact ⟨σ, Finset.mem_filter.2 ⟨hσ, hp⟩⟩
    · ext p
      constructor
      · intro hp
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (hts hp)
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hσ, hp⟩)
      · intro hp
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hp
        exact (Finset.mem_filter.1 hσ).2
  indep := by
    rintro s ⟨C, _, hC, hg, rfl⟩
    exact affineIndependent_chain hneg hC hg
  inter_subset_convexHull := by
    rintro s t ⟨C, _, hC, hgC, rfl⟩ ⟨D, _, hD, hgD, rfl⟩
    exact inter_subset_chain hneg hC hD hgC hgD

/-- For every finite set of integer forms there is a rational subdivision of `Δₙ` each of whose
simplices lies in the closed cell (for these forms) of a point of `Δₙ`. -/
theorem exists_rational_arrangement (L₀ : Finset (Fin (n + 1) → ℤ)) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ), IsSubdivision n K ∧
      (∀ s ∈ K.faces, ∀ v ∈ s, IsRationalPoint v) ∧
      ∀ s ∈ K.faces, ∃ y ∈ Simplex n, ∀ z ∈ convexHull ℝ (↑s : Set (Fin (n + 1) → ℝ)),
        ∀ a ∈ L₀, 0 ≤ ell a y → 0 ≤ ell a z := by
  classical
  set L₁ := L₀ ∪ Finset.univ.image (fun i : Fin (n + 1) => (Pi.single i 1 : Fin (n + 1) → ℤ))
  set L := L₁ ∪ L₁.image Neg.neg with hL
  have hneg : ∀ a ∈ L, -a ∈ L := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      rw [neg_neg]; exact Finset.mem_union_left _ hc
  have hcoord : ∀ i, Pi.single i 1 ∈ L := fun i =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hL₀ : L₀ ⊆ L := fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  have hgood : ∀ σ, Good L σ → σ ⊆ L := by
    rintro σ ⟨y, _, rfl⟩
    exact Finset.filter_subset _ _
  have hsimp : ∀ s ∈ arrFaces L, convexHull ℝ (↑s : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n := by
    rintro s ⟨C, _, _, hg, rfl⟩
    refine convexHull_min ?_ (convex_stdSimplex ℝ _)
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    exact (bary_spec (hg σ hσ)).1.1
  refine ⟨arrComplex L hneg, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- finiteness
    refine Set.Finite.subset (Finset.finite_toSet
      ((L.powerset.powerset).image (fun C => C.image (bary L)))) ?_
    rintro s ⟨C, _, _, hg, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨C, ?_, rfl⟩)
    rw [Finset.mem_powerset]
    intro σ hσ
    exact Finset.mem_powerset.2 (hgood σ (hg σ hσ))
  · ext x
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact hsimp s hs hx
    · intro hx
      obtain ⟨C, hC, hg, hxC, _, hconv⟩ := exists_chain_of_mem hneg hcoord _ x rfl hx
      exact ⟨_, ⟨C, ⟨_, hxC⟩, hC, hg, rfl⟩, hconv⟩
  · rintro s ⟨C, _, _, hg, rfl⟩ v hv
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hv
    exact (bary_spec (hg σ hσ)).1
  · rintro s ⟨C, hne, hC, hg, rfl⟩
    obtain ⟨τ, hτC, hτ⟩ := exists_top hC hne
    obtain ⟨hq, hcell⟩ := bary_spec (hg τ hτC)
    refine ⟨bary L τ, hq.1, fun z hz a ha hya => ?_⟩
    have haτ : a ∈ τ := by rw [← hcell]; exact mem_cellOf.2 ⟨hL₀ ha, hya⟩
    have hQ : convexHull ℝ (↑(C.image (bary L)) : Set (Fin (n + 1) → ℝ)) ⊆
        {z | ∀ c ∈ τ, 0 ≤ ell c z} := by
      refine convexHull_min ?_ ?_
      · intro p hp c hc
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
        exact ((mem_iff_of_good (hg σ hσ) c).1 (hτ σ hσ hc)).2
      · intro p hp q hq' α β hα hβ _ c hc
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact add_nonneg (mul_nonneg hα (hp c hc)) (mul_nonneg hβ (hq' c hc))
    exact hQ hz a haτ

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix

variable {n : ℕ}

/-- The real matrix of an integer matrix. -/
noncomputable abbrev rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

lemma rM_mul (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : rM (A * B) = rM A * rM B := by
  simp only [rM]
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

lemma rM_one : rM (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) = 1 := by
  simp only [rM]
  exact Matrix.map_one _ Int.cast_zero Int.cast_one

lemma glAct_eq (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A x = rM (A : Matrix _ _ ℤ) *ᵥ x := rfl

lemma glAct_inv_glAct (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A⁻¹ (glAct A x) = x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_mulVec, ← rM_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, rM_one, Matrix.one_mulVec]

lemma glAct_glAct_inv (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A (glAct A⁻¹ x) = x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_mulVec, ← rM_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, rM_one, Matrix.one_mulVec]

lemma glAct_smul (A : GL (Fin (n + 1)) ℤ) (c : ℝ) (x : Fin (n + 1) → ℝ) :
    glAct A (c • x) = c • glAct A x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_smul]

lemma glAct_ne_zero (A : GL (Fin (n + 1)) ℤ) {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    glAct A x ≠ 0 := by
  intro h
  apply hx
  rw [← glAct_inv_glAct A x, h, glAct_eq, Matrix.mulVec_zero]

lemma sum_abs_pos {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < ∑ i, |x i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))

lemma rho_smul {c : ℝ} (hc : 0 < c) (y : Fin (n + 1) → ℝ) : rho (c • y) = rho y := by
  unfold rho
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum, smul_smul]
  congr 1
  by_cases hs : ∑ i, |y i| = 0
  · simp [hs]
  · field_simp

lemma rho_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : rho x = x := by
  unfold rho
  have : ∑ i, |x i| = 1 := by
    rw [← hx.2]; exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx.1 i)
  simp [this]

lemma ne_zero_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : x ≠ 0 := by
  rintro rfl
  have := hx.2
  simp at this

lemma rho_mem {y : Fin (n + 1) → ℝ} (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) : rho y ∈ Simplex n := by
  have hs := sum_abs_pos hy0
  refine ⟨fun i => ?_, ?_⟩
  · unfold rho
    exact mul_nonneg (inv_nonneg.mpr hs.le) (hy i)
  · unfold rho
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => (abs_of_nonneg (hy i)).symm]
    exact inv_mul_cancel₀ hs.ne'

lemma rho_eq_smul (y : Fin (n + 1) → ℝ) : rho y = (∑ i, |y i|)⁻¹ • y := rfl


end CannonFloydParry.S7

/-!
# Common rational refinements, part 5: the theorem

Top simplices of a subdivision of `Δₙ` cover `Δₙ` (a measure-zero argument on cones), an integral
subsimplex is cut out of `Δₙ` by finitely many integer forms (the rows of `A⁻¹`), and the chain
complex of the arrangement of all these forms is a rational subdivision refining both.
-/

namespace CannonFloydParry.S7

open Set MeasureTheory

variable {n : ℕ}

/-- An integral subsimplex is cut out of `Δₙ` by finitely many integer forms. -/
lemma integral_polyhedron {S : Set (Fin (n + 1) → ℝ)} (h : IsIntegralSubsimplex n S) :
    ∃ R : Finset (Fin (n + 1) → ℤ), ∀ z, z ∈ S ↔ z ∈ Simplex n ∧ ∀ a ∈ R, 0 ≤ ell a z := by
  obtain ⟨f, ⟨A, hA⟩, rfl⟩ := h
  classical
  refine ⟨Finset.univ.image (fun j i => ((A⁻¹ : GL (Fin (n + 1)) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j i),
    fun z => ?_⟩
  have hrow : ∀ (j : Fin (n + 1)) (z : Fin (n + 1) → ℝ),
      ell (fun i => ((A⁻¹ : GL (Fin (n + 1)) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j i) z = glAct A⁻¹ z j := by
    intro j z; simp [ell_apply, glAct, Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨_, hfx⟩ := hA x (Set.mem_univ _)
    refine ⟨(f x).2, ?_⟩
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 ha
    rw [hrow]; show 0 ≤ glAct A⁻¹ (f x : Fin (n + 1) → ℝ) j
    rw [hfx, rho_eq_smul, glAct_smul, glAct_inv_glAct]
    exact mul_nonneg (inv_nonneg.2 (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (x.2.1 j)
  · rintro ⟨hz, hR⟩
    set w := glAct A⁻¹ z with hwdef
    have hw : ∀ j, 0 ≤ w j := fun j => by
      rw [hwdef, ← hrow]; exact hR _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hw0 : w ≠ 0 := glAct_ne_zero _ (ne_zero_of_mem hz)
    refine ⟨⟨rho w, rho_mem hw hw0⟩, ?_⟩
    obtain ⟨_, hfx⟩ := hA ⟨rho w, rho_mem hw hw0⟩ (Set.mem_univ _)
    show ((f _ : Simplex n) : Fin (n + 1) → ℝ) = z
    rw [hfx]
    show rho (glAct A (rho w)) = z
    rw [rho_eq_smul w, glAct_smul, hwdef, glAct_glAct_inv,
      rho_smul (inv_pos.2 (sum_abs_pos hw0)), rho_of_mem hz]

/-- Affinely independent points of `Δₙ` number at most `n + 1`. -/
lemma card_le_of_affineIndependent {s : Finset (Fin (n + 1) → ℝ)}
    (hs : (↑s : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n)
    (h : AffineIndependent ℝ ((↑) : s → (Fin (n + 1) → ℝ))) : s.card ≤ n + 1 := by
  have h1 : ∀ e : s, ∑ j, (e : Fin (n + 1) → ℝ) j = 1 := fun e => (hs (Finset.mem_coe.2 e.2)).2
  have hli : LinearIndependent ℝ ((↑) : s → (Fin (n + 1) → ℝ)) := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have hsum : ∑ i ∈ t, g i = 0 := by
      have := congrArg (fun v : Fin (n + 1) → ℝ => ∑ j, v j) hg
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Finset.sum_const_zero] at this
      rw [Finset.sum_comm] at this
      simpa [← Finset.mul_sum, h1] using this
    exact affineIndependent_iff.1 h t g hsum hg i hi
  have := hli.fintype_card_le_finrank
  simpa using this

/-- The top simplices of a subdivision of `Δₙ` cover `Δₙ`. -/
lemma exists_top_face {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (hK : IsSubdivision n K) {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) :
    ∃ T ∈ K.faces, T.card = n + 1 ∧ x ∈ convexHull ℝ (↑T : Set (Fin (n + 1) → ℝ)) := by
  classical
  obtain ⟨hfin, hspace⟩ := hK
  set S := ⋃ T ∈ {T | T ∈ K.faces ∧ T.card = n + 1},
    convexHull ℝ (↑T : Set (Fin (n + 1) → ℝ)) with hSdef
  have hS : IsClosed S :=
    (hfin.subset (fun T hT => hT.1)).isClosed_biUnion fun T _ =>
      (T.finite_toSet.isCompact_convexHull ℝ).isClosed
  suffices hxS : x ∈ closure S by
    rw [hS.closure_eq, hSdef, Set.mem_iUnion₂] at hxS
    obtain ⟨T, hT, hxT⟩ := hxS
    exact ⟨T, hT.1, hT.2, hxT⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  set P := {z : Fin (n + 1) → ℝ | ∀ i, 0 < z i} with hPdef
  set g : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun z => (∑ i, z i)⁻¹ • z with hgdef
  set O := P ∩ g ⁻¹' Metric.ball x ε with hOdef
  have hPo : IsOpen P := by
    have : P = ⋂ i, {z : Fin (n + 1) → ℝ | 0 < z i} := by ext; simp [P]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hgc : ContinuousOn g P := by
    refine ContinuousOn.smul (ContinuousOn.inv₀ (continuous_finsetSum _ fun i _ => continuous_apply i).continuousOn fun z hz => ?_) continuousOn_id
    exact (Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty).ne'
  have hOo : IsOpen O := hgc.isOpen_inter_preimage hPo Metric.isOpen_ball
  have hOne : O.Nonempty := by
    set δ := min (1 / 2 : ℝ) (ε / 2) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (half_pos hε)
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / 2 := min_le_right _ _
    set c : Fin (n + 1) → ℝ := fun _ => 1 / (n + 1) with hcdef
    have hc1 : ∑ i, c i = 1 := by simp [hcdef]; field_simp
    have hcpos : ∀ i, 0 < c i := fun i => by simp only [hcdef]; positivity
    have hcle : ∀ i, c i ≤ 1 := fun i => by
      simp only [hcdef]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hxle : ∀ i, x i ≤ 1 := fun i => by
      rw [← hx.2]
      exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
    set z := (1 - δ) • x + δ • c with hzdef
    have hz1 : ∑ i, z i = 1 := by
      simp only [hzdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.2, hc1]
      ring
    refine ⟨z, fun i => ?_, ?_⟩
    · simp only [hzdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx.1 i
      have := hcpos i
      nlinarith
    · show g z ∈ Metric.ball x ε
      have hgz : g z = z := by simp [hgdef, hz1]
      rw [hgz, Metric.mem_ball, dist_eq_norm]
      have hzx : z - x = δ • (c - x) := by
        simp only [hzdef]; ext i; simp; ring
      rw [hzx, norm_smul, Real.norm_of_nonneg hδ.le]
      have hn : ‖c - x‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hcpos i, hcle i, hx.1 i, hxle i]
      nlinarith [norm_nonneg (c - x)]
  -- the cones over low-dimensional faces are null
  set N := ⋃ t ∈ {t | t ∈ K.faces ∧ t.card ≤ n},
    ((Submodule.span ℝ (↑t : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ))) with hNdef
  have hN : volume N = 0 := by
    rw [hNdef, measure_biUnion_null_iff ((hfin.subset fun t ht => ht.1).countable)]
    intro t ht
    refine Measure.addHaar_submodule volume _ fun h => ?_
    have := finrank_span_finset_le_card (R := ℝ) t
    rw [Set.finrank, h, finrank_top, Module.finrank_fin_fun] at this
    have := ht.2
    omega
  have hnot : ¬ O ⊆ N := fun h => (hOo.measure_pos volume hOne).ne' (measure_mono_null h hN)
  obtain ⟨z, hzO, hzN⟩ := Set.not_subset.1 hnot
  have hzpos : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hzO.1 i) Finset.univ_nonempty
  have hyS : g z ∈ Simplex n := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [hgdef, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hzpos.le) (hzO.1 i).le
    · simp only [hgdef, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hzpos.ne'
  rw [← hspace, Geometry.SimplicialComplex.mem_space_iff] at hyS
  obtain ⟨t, ht, hyt⟩ := hyS
  have hcard : ¬ t.card ≤ n := by
    intro hc
    apply hzN
    rw [hNdef, Set.mem_iUnion₂]
    refine ⟨t, ⟨ht, hc⟩, ?_⟩
    have h1 : g z ∈ Submodule.span ℝ (↑t : Set (Fin (n + 1) → ℝ)) :=
      convexHull_min Submodule.subset_span (Submodule.convex _) hyt
    have h2 : z = (∑ i, z i) • g z := by
      simp only [hgdef, smul_smul, mul_inv_cancel₀ hzpos.ne', one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hle := card_le_of_affineIndependent
    ((K.subset_space ht).trans hspace.subset) (K.indep ht)
  refine ⟨g z, ?_, ?_⟩
  · rw [hSdef, Set.mem_iUnion₂]
    exact ⟨t, ⟨ht, by omega⟩, hyt⟩
  · rw [dist_comm]; exact hzO.2

/-- Finitely many integer forms cutting out all top simplices of an integral subdivision. -/
lemma exists_forms {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (hK : IsIntegralSubdivision n K) :
    ∃ L₀ : Finset (Fin (n + 1) → ℤ), ∀ T ∈ K.faces, T.card = n + 1 → ∃ R ⊆ L₀,
      ∀ z, z ∈ convexHull ℝ (↑T : Set (Fin (n + 1) → ℝ)) ↔
        z ∈ Simplex n ∧ ∀ a ∈ R, 0 ≤ ell a z := by
  classical
  have h : ∀ T : Finset (Fin (n + 1) → ℝ), ∃ R : Finset (Fin (n + 1) → ℤ),
      T ∈ K.faces → T.card = n + 1 → ∀ z, z ∈ convexHull ℝ (↑T : Set (Fin (n + 1) → ℝ)) ↔
        z ∈ Simplex n ∧ ∀ a ∈ R, 0 ≤ ell a z := by
    intro T
    by_cases hT : T ∈ K.faces ∧ T.card = n + 1
    · obtain ⟨R, hR⟩ := integral_polyhedron (hK.2 T hT.1 hT.2)
      exact ⟨R, fun _ _ => hR⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hT⟩
  choose R hR using h
  exact ⟨hK.1.1.toFinset.biUnion R, fun T hT hc => ⟨R T, fun a ha =>
    Finset.mem_biUnion.2 ⟨T, hK.1.1.mem_toFinset.2 hT, ha⟩, hR T hT hc⟩⟩

theorem exists_isRationalSubdivision_refines_of_isIntegralSubdivision' {n : ℕ}
    {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (h₁ : IsIntegralSubdivision n K₁) (h₂ : IsIntegralSubdivision n K₂) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂ := by
  classical
  obtain ⟨L₁, hL₁⟩ := exists_forms h₁
  obtain ⟨L₂, hL₂⟩ := exists_forms h₂
  obtain ⟨K, hK, hrat, hcell⟩ := exists_rational_arrangement (L₁ ∪ L₂)
  have href : ∀ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      IsIntegralSubdivision n K' → ∀ L' : Finset (Fin (n + 1) → ℤ), L' ⊆ L₁ ∪ L₂ →
      (∀ T ∈ K'.faces, T.card = n + 1 → ∃ R ⊆ L',
        ∀ z, z ∈ convexHull ℝ (↑T : Set (Fin (n + 1) → ℝ)) ↔
          z ∈ Simplex n ∧ ∀ a ∈ R, 0 ≤ ell a z) → Refines K K' := by
    intro K' hK' L' hL' hR
    refine ⟨hK.2.trans hK'.1.2.symm, fun s hs => ?_⟩
    obtain ⟨y, hy, hyz⟩ := hcell s hs
    obtain ⟨T, hT, hTc, hyT⟩ := exists_top_face hK'.1 hy
    obtain ⟨R, hRL, hRT⟩ := hR T hT hTc
    refine ⟨T, hT, fun z hz => (hRT z).2 ⟨?_, fun a ha =>
      hyz z hz a (hL' (hRL ha)) (((hRT y).1 hyT).2 a ha)⟩⟩
    rw [← hK.2]
    exact K.convexHull_subset_space hs hz
  exact ⟨K, ⟨hK, fun s hs _ => ⟨hrat s hs, K.indep hs⟩⟩,
    href K₁ h₁ L₁ Finset.subset_union_left hL₁, href K₂ h₂ L₂ Finset.subset_union_right hL₂⟩

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {n : ℕ}
    {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (h₁ : IsIntegralSubdivision n K₁) (h₂ : IsIntegralSubdivision n K₂) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂ := by
  exact S7.exists_isRationalSubdivision_refines_of_isIntegralSubdivision' h₁ h₂
