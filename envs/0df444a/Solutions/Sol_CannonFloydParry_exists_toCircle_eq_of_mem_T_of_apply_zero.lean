-- Prove2me | solution 1 for CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T19:56:14.35446+00:00
-- url     : https://prove2.me/submissions/886138a2-b6cd-4fe4-9899-dbae1b2d8e02

import Definitions.Def_CannonFloydParry_T
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_mem_T_iff_isThompsonCircle

/-! Lifts of elements of `T` to the line, and the closure theorem (the first milestone): the
maps satisfying `IsThompsonCircle` form a group. -/

namespace CannonFloydParry.S5

/-! ### Dyadic arithmetic -/

lemma isDyadic_int (k : ℤ) : IsDyadic (k : ℝ) := ⟨k, 0, by simp⟩

lemma dy_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨n, l, rfl⟩ := hy
  refine ⟨m * 2 ^ l + n * 2 ^ k, k + l, ?_⟩
  push_cast
  field_simp
  ring

lemma dy_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma dy_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using dy_add hx (dy_neg hy)

lemma dy_zpow {x : ℝ} (hx : IsDyadic x) (n : ℤ) : IsDyadic ((2 : ℝ) ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  rcases n with n | n
  · refine ⟨m * 2 ^ n, k, ?_⟩
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    push_cast
    ring
  · refine ⟨m, k + (n + 1), ?_⟩
    rw [zpow_negSucc, pow_add]
    field_simp
    ring

lemma dy_fract {x : ℝ} (hx : IsDyadic x) : IsDyadic (Int.fract x) := by
  rw [Int.fract]; exact dy_sub hx (isDyadic_int _)

/-! ### Good lifts -/

/-- `L` is affine with slope a power of `2` on every closed interval whose interior avoids the
integer translates of `B`. -/
def IsPL (L : ℝ ≃o ℝ) (B : Finset ℝ) : Prop :=
  ∀ x y : ℝ, x < y → (∀ t ∈ Set.Ioo x y, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k) →
    ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c

structure GoodLift (L : ℝ ≃o ℝ) : Prop where
  per : ∀ x, L (x + 1) = L x + 1
  dy : ∀ x, IsDyadic x → IsDyadic (L x)
  pl : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ IsPL L B

lemma isThompsonCircle_iff {f : Equiv.Perm UnitAddCircle} :
    IsThompsonCircle f ↔ ∃ L : ℝ ≃o ℝ, GoodLift L ∧ ∀ x : ℝ, f (x : UnitAddCircle) = ((L x : ℝ) : UnitAddCircle) := by
  constructor
  · rintro ⟨L, hper, hcov, hdy, B, hB, hpl⟩
    exact ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
  · rintro ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
    exact ⟨L, hper, hcov, hdy, B, hB, hpl⟩

namespace GoodLift
variable {L : ℝ ≃o ℝ}

lemma per_nat (hL : GoodLift L) (x : ℝ) (n : ℕ) : L (x + n) = L x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hL.per, ih]; ring

lemma per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L (x + k) = L x + k := by
  rcases k with n | n
  · simpa using hL.per_nat x n
  · have hc : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by rw [Int.cast_negSucc]; push_cast; ring
    have := hL.per_nat (x + ((Int.negSucc n : ℤ) : ℝ)) (n + 1)
    rw [hc] at this ⊢
    push_cast at this
    rw [show x + -((n : ℝ) + 1) + ((n : ℝ) + 1) = x by ring] at this
    linarith

lemma symm_per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L.symm (x + k) = L.symm x + k := by
  apply L.injective
  rw [hL.per_int, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

/-- The key fact: the inverse of a good lift maps dyadic rationals to dyadic rationals. -/
lemma symm_dy (hL : GoodLift L) (w : ℝ) (hw : IsDyadic w) : IsDyadic (L.symm w) := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  set z := L.symm w
  let S : Finset ℝ := insert ((⌊z⌋ : ℤ) : ℝ) (B.image fun b => b + ⌊z - b⌋)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  set x := S.max' hS
  have hxS : x ∈ S := S.max'_mem hS
  have hle : ∀ s ∈ S, s ≤ z := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact Int.floor_le z
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hs
      linarith [Int.floor_le (z - b)]
  have hxz : x ≤ z := hle x hxS
  have hxdy : IsDyadic x := by
    rcases Finset.mem_insert.1 hxS with h | h
    · rw [h]; exact isDyadic_int _
    · obtain ⟨b, hb, h⟩ := Finset.mem_image.1 h
      rw [← h]; exact dy_add (hB b hb) (isDyadic_int _)
  rcases eq_or_lt_of_le hxz with h | h
  · rw [← h]; exact hxdy
  have havoid : ∀ t ∈ Set.Ioo x z, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    rintro t ⟨ht1, ht2⟩ b hb k rfl
    have hk : k ≤ ⌊z - b⌋ := Int.le_floor.2 (by linarith)
    have : b + ⌊z - b⌋ ≤ x := S.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb))
    have : (k : ℝ) ≤ ⌊z - b⌋ := by exact_mod_cast hk
    linarith
  obtain ⟨n, c, hc⟩ := hpl x z h havoid
  have hcx := hc x ⟨le_rfl, hxz⟩
  have hcz := hc z ⟨hxz, le_rfl⟩
  have hcdy : IsDyadic c := by
    have : c = L x - 2 ^ n * x := by linarith
    rw [this]; exact dy_sub (hL.dy x hxdy) (dy_zpow hxdy n)
  have hzw : L z = w := OrderIso.apply_symm_apply L w
  have : z = 2 ^ (-n) * (w - c) := by
    rw [← hzw, hcz, zpow_neg]
    field_simp
    ring
  rw [this]
  exact dy_zpow (dy_sub hw hcdy) _

lemma symm (hL : GoodLift L) : GoodLift L.symm := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  refine ⟨fun x => by simpa using hL.symm_per_int x 1, hL.symm_dy, B.image (fun b => Int.fract (L b)), ?_, ?_⟩
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact dy_fract (hL.dy b (hB b hb))
  · intro x y hxy havoid
    have hxy' : L.symm x < L.symm y := L.symm.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L.symm x) (L.symm y), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L (b + k)) ⟨?_, ?_⟩ (Int.fract (L b)) (Finset.mem_image_of_mem _ hb) (⌊L b⌋ + k) ?_
      · have := L.strictMono ht1; rwa [OrderIso.apply_symm_apply] at this
      · have := L.strictMono ht2; rwa [OrderIso.apply_symm_apply] at this
      · rw [hL.per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c, hc⟩ := hpl _ _ hxy' havoid'
    refine ⟨-n, -(2 ^ (-n) * c), fun z hz => ?_⟩
    have hs : L.symm z ∈ Set.Icc (L.symm x) (L.symm y) :=
      ⟨L.symm.monotone hz.1, L.symm.monotone hz.2⟩
    have := hc _ hs
    rw [OrderIso.apply_symm_apply] at this
    rw [zpow_neg]
    field_simp
    linarith

lemma trans {L₁ L₂ : ℝ ≃o ℝ} (h₁ : GoodLift L₁) (h₂ : GoodLift L₂) : GoodLift (L₁.trans L₂) := by
  obtain ⟨B₁, hB₁, hpl₁⟩ := h₁.pl
  obtain ⟨B₂, hB₂, hpl₂⟩ := h₂.pl
  refine ⟨fun x => by simp [h₁.per, h₂.per], fun x hx => h₂.dy _ (h₁.dy x hx),
    B₁ ∪ B₂.image (fun b => Int.fract (L₁.symm b)), ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact hB₁ b hb
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      exact dy_fract (h₁.symm_dy b' (hB₂ b' hb'))
  · intro x y hxy havoid
    obtain ⟨m, c₁, hc₁⟩ := hpl₁ x y hxy (fun t ht b hb k => havoid t ht b (Finset.mem_union_left _ hb) k)
    have hxy' : L₁ x < L₁ y := L₁.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L₁ x) (L₁ y), ∀ b ∈ B₂, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L₁.symm (b + k)) ⟨?_, ?_⟩ (Int.fract (L₁.symm b))
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)) (⌊L₁.symm b⌋ + k) ?_
      · have := L₁.symm.strictMono ht1; rwa [OrderIso.symm_apply_apply] at this
      · have := L₁.symm.strictMono ht2; rwa [OrderIso.symm_apply_apply] at this
      · rw [h₁.symm_per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c₂, hc₂⟩ := hpl₂ _ _ hxy' havoid'
    refine ⟨n + m, 2 ^ n * c₁ + c₂, fun z hz => ?_⟩
    have hz' : L₁ z ∈ Set.Icc (L₁ x) (L₁ y) := ⟨L₁.monotone hz.1, L₁.monotone hz.2⟩
    simp only [OrderIso.trans_apply]
    rw [hc₂ _ hz', hc₁ z hz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

end GoodLift

/-! ### The closure theorem -/

end CannonFloydParry.S5

/-! `toCircle` is an injective group homomorphism from the order isomorphisms of `[0,1]`. -/

namespace CannonFloydParry.S5

lemma icoPerm_mul (f g : UI ≃o UI) : icoPerm (f * g) = icoPerm f * icoPerm g := by
  ext x; rfl

lemma toCircle_mul (f g : UI ≃o UI) : toCircle (f * g) = toCircle f * toCircle g := by
  ext x
  simp only [toCircle, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, icoPerm_mul]

lemma toCircle_one : toCircle 1 = 1 := by
  ext x
  simp only [toCircle, Equiv.trans_apply, Equiv.Perm.coe_one, id]
  have : icoPerm (1 : UI ≃o UI) = 1 := by ext y; rfl
  rw [this, Equiv.Perm.coe_one, id, Equiv.symm_apply_apply]

/-- `toCircle` as a group homomorphism. -/
noncomputable def toCircleHom : (UI ≃o UI) →* Equiv.Perm UnitAddCircle where
  toFun := toCircle
  map_one' := toCircle_one
  map_mul' := toCircle_mul

@[simp] lemma toCircleHom_apply (f : UI ≃o UI) : toCircleHom f = toCircle f := rfl

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C` and their inverses on `[0,1)` representatives of the circle. -/

namespace CannonFloydParry.S5

/-- The representative in `[0,1)` of a point of the circle. -/
noncomputable def ico (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

lemma ico_nonneg (x : UnitAddCircle) : 0 ≤ ico x := (AddCircle.equivIco (1 : ℝ) 0 x).2.1
lemma ico_lt_one (x : UnitAddCircle) : ico x < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 x).2.2
  unfold ico
  linarith

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

/-! Piecewise formulas. -/

/-! The generators and their inverses on representatives. -/

end CannonFloydParry.S5

/-! Example 5.1 (the second milestone): elements of `F` induce elements of `T`, and `C ∈ T`.
Both lifts are periodic extensions `x ↦ ℓ(fract x) + ⌊x⌋`. -/

namespace CannonFloydParry.S5

lemma ico_coe (x : ℝ) : ico (x : UnitAddCircle) = Int.fract x := by
  simp [ico, AddCircle.coe_equivIco_mk_apply]

lemma circle_ext {u v : UnitAddCircle} (h : ico u = ico v) : u = v :=
  (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

/-! ### Periodic extensions -/

noncomputable def perExt (ℓ : ℝ → ℝ) (x : ℝ) : ℝ := ℓ (Int.fract x) + ⌊x⌋

structure PerData (ℓ : ℝ → ℝ) : Prop where
  mono : StrictMonoOn ℓ (Set.Icc 0 1)
  one : ℓ 1 = ℓ 0 + 1
  surj : ∀ v ∈ Set.Icc (ℓ 0) (ℓ 0 + 1), ∃ u ∈ Set.Icc (0 : ℝ) 1, ℓ u = v

namespace PerData
variable {ℓ : ℝ → ℝ} (h : PerData ℓ)
include h

lemma fract_mem (x : ℝ) : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma lt_top (x : ℝ) : ℓ (Int.fract x) < ℓ 0 + 1 := by
  rw [← h.one]; exact h.mono (h.fract_mem x) ⟨zero_le_one, le_rfl⟩ (Int.fract_lt_one x)

lemma bot_le (x : ℝ) : ℓ 0 ≤ ℓ (Int.fract x) :=
  h.mono.monotoneOn ⟨le_rfl, zero_le_one⟩ (h.fract_mem x) (Int.fract_nonneg x)

lemma strictMono : StrictMono (perExt ℓ) := by
  intro x y hxy
  unfold perExt
  rcases eq_or_lt_of_le (Int.floor_mono hxy.le) with he | hl
  · have : Int.fract x < Int.fract y := by
      unfold Int.fract; rw [he]; linarith
    rw [he]
    have := h.mono (h.fract_mem x) (h.fract_mem y) this
    linarith
  · have hk : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hl
    linarith [h.lt_top x, h.bot_le y]

lemma surjective : Function.Surjective (perExt ℓ) := by
  intro v
  set k := ⌊v - ℓ 0⌋
  have hk1 : (k : ℝ) ≤ v - ℓ 0 := Int.floor_le _
  have hk2 : v - ℓ 0 < k + 1 := Int.lt_floor_add_one _
  obtain ⟨u, hu, hlu⟩ := h.surj (v - k) ⟨by linarith, by linarith⟩
  have hu1 : u < 1 := by
    rcases eq_or_lt_of_le hu.2 with rfl | h1
    · rw [h.one] at hlu; linarith
    · exact h1
  refine ⟨u + k, ?_⟩
  unfold perExt
  rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hu.1, hu1⟩, Int.floor_add_intCast,
    Int.floor_eq_zero_iff.2 ⟨hu.1, hu1⟩]
  push_cast
  linarith

/-- The lift as an order isomorphism of the line. -/
noncomputable def lift : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective _ h.strictMono h.surjective

@[simp] lemma lift_apply (x : ℝ) : h.lift x = perExt ℓ x := rfl

lemma per (x : ℝ) : h.lift (x + 1) = h.lift x + 1 := by
  simp only [lift_apply, perExt]
  rw [Int.fract_add_one, Int.floor_add_one]; push_cast; ring

end PerData

/-! ### Elements of `F` -/

/-! ### The map `C` -/

end CannonFloydParry.S5

/-! The third milestone: an element of `T` fixing `[0]` comes from `F` (CFP p. 235). -/

namespace CannonFloydParry.S5

lemma coe_ico (p : UnitAddCircle) : ((ico p : ℝ) : UnitAddCircle) = p := by
  apply circle_ext
  rw [ico_coe, Int.fract_eq_self.2 ⟨ico_nonneg p, ico_lt_one p⟩]

lemma GoodLift.translate (k : ℤ) : GoodLift (OrderIso.addRight (k : ℝ)) := by
  refine ⟨fun x => by simp; ring, fun x hx => by simpa using dy_add hx (isDyadic_int k), ∅, by simp,
    fun x y _ _ => ⟨0, k, fun z _ => by simp⟩⟩

/-- An order isomorphism of the line fixing `0` and `1` restricts to one of `[0,1]`. -/
noncomputable def restrictUI (L : ℝ ≃o ℝ) (h0 : L 0 = 0) (h1 : L 1 = 1) : UI ≃o UI := by
  have hs0 : L.symm 0 = 0 := by rw [L.symm_apply_eq, h0]
  have hs1 : L.symm 1 = 1 := by rw [L.symm_apply_eq, h1]
  refine
    { toFun := fun z => ⟨L z, ?_, ?_⟩
      invFun := fun z => ⟨L.symm z, ?_, ?_⟩
      left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_ }
  · have := L.monotone z.2.1; rwa [h0] at this
  · have := L.monotone z.2.2; rwa [h1] at this
  · have := L.symm.monotone z.2.1; rwa [hs0] at this
  · have := L.symm.monotone z.2.2; rwa [hs1] at this
  · intro z; ext; simp
  · intro z; ext; simp
  · intro a b; exact L.le_iff_le

@[simp] lemma restrictUI_coe (L : ℝ ≃o ℝ) (h0 : L 0 = 0) (h1 : L 1 = 1) (z : UI) :
    ((restrictUI L h0 h1 z : UI) : ℝ) = L z := rfl

theorem exists_toCircle_eq_of_mem_T_of_apply_zero' {f : Equiv.Perm UnitAddCircle} (hf : f ∈ T)
    (h0 : f 0 = 0) : ∃ g ∈ F, toCircle g = f := by
  obtain ⟨L, hL, hcov⟩ := isThompsonCircle_iff.1 (mem_T_iff_isThompsonCircle.1 hf)
  -- `L 0` is an integer `k`
  set k := ⌊L 0⌋
  have hfr : Int.fract (L 0) = 0 := by
    have := congrArg ico (hcov 0)
    rw [show ((0 : ℝ) : UnitAddCircle) = 0 from rfl, h0, ico_coe] at this
    rw [← this, show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) from rfl, ico_coe, Int.fract_zero]
  have hk : L 0 = k := by have := Int.fract_add_floor (L 0); rw [hfr, zero_add] at this; exact this.symm
  set L' := L.trans (OrderIso.addRight (-k : ℝ))
  have hL' : GoodLift L' := hL.trans (by simpa using GoodLift.translate (-k))
  have hL'0 : L' 0 = 0 := by simp [L', hk]
  have hL'1 : L' 1 = 1 := by
    have := hL'.per 0; rw [zero_add, hL'0, zero_add] at this; exact this
  have hcov' : ∀ x : ℝ, f (x : UnitAddCircle) = ((L' x : ℝ) : UnitAddCircle) := by
    intro x
    apply circle_ext
    rw [hcov, ico_coe, ico_coe]
    simp only [L', OrderIso.trans_apply, OrderIso.addRight_apply]
    rw [show L x + -(k : ℝ) = L x + ((-k : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
  set g := restrictUI L' hL'0 hL'1
  obtain ⟨B, hB, hpl⟩ := hL'.pl
  have hg : IsThompson g := by
    refine ⟨B.image Int.fract, fun b hb => ?_, fun x y hxy havoid => ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb; exact dy_fract (hB b' hb')
    · have havoid' : ∀ t ∈ Set.Ioo (x : ℝ) y, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
        rintro t ⟨ht1, ht2⟩ b hb k' rfl
        have ht0 : 0 ≤ b + k' := le_trans x.2.1 ht1.le
        have ht1' : b + k' < 1 := lt_of_lt_of_le ht2 y.2.2
        have : b + k' = Int.fract b := by
          rw [← Int.fract_add_intCast b k', Int.fract_eq_self.2 ⟨ht0, ht1'⟩]
        have hmem : b + k' ∈ Set.Ioo (x : ℝ) y ∩ ((B.image Int.fract : Finset ℝ) : Set ℝ) :=
          ⟨⟨ht1, ht2⟩, by rw [this]; exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb)⟩
        rw [havoid] at hmem; exact hmem
      obtain ⟨n, c, hc⟩ := hpl x y hxy havoid'
      exact ⟨n, c, fun z hz => by rw [restrictUI_coe]; exact hc z hz⟩
  refine ⟨g, mem_F_iff_isThompson.2 hg, ?_⟩
  ext p
  apply circle_ext
  have hp := coe_ico p
  have hmem : ico p ∈ Set.Icc (0 : ℝ) 1 := ⟨ico_nonneg p, (ico_lt_one p).le⟩
  rw [ico_toCircle]
  conv_rhs => rw [← hp, hcov', ico_coe]
  rw [restrictUI_coe]
  have hlt : L' (ico p) < 1 := by
    rw [← hL'1]; exact L'.strictMono (ico_lt_one p)
  have hge : 0 ≤ L' (ico p) := by
    rw [← hL'0]; exact L'.monotone (ico_nonneg p)
  rw [Int.fract_eq_self.2 ⟨hge, hlt⟩]

end CannonFloydParry.S5

open CannonFloydParry

theorem solution {f : Equiv.Perm UnitAddCircle} (hf : f ∈ T)
    (h0 : f 0 = 0) : ∃ g ∈ F, toCircle g = f :=
  CannonFloydParry.S5.exists_toCircle_eq_of_mem_T_of_apply_zero' hf h0
