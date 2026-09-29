-- Prove2me | solution 1 for CannonFloydParry.toCircle_mem_T_and_mapC_mem_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T19:54:06.971677+00:00
-- url     : https://prove2.me/submissions/fb42ff8c-4a3b-4254-9a34-ab853c3421fe

import Definitions.Def_CannonFloydParry_T
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_bijOn_dyadic

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
lemma cFun_of_mem1 {x : ℝ} (h1 : x < 1/2) : cFun x = x / 2 + 3/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem2 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x < 3/4) : cFun x = 2 * x - 1 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem3 {x : ℝ} (h0 : 3/4 ≤ x) : cFun x = x - 1/4 := by
  unfold cFun; split_ifs <;> linarith

/-! The generators and their inverses on representatives. -/

lemma ico_C (x : UnitAddCircle) : ico (symT FormalABC.C x) = cFun (ico x) := by
  simp only [symT, mapC, Equiv.trans_apply, ico_symm]
  rfl

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

lemma eq_on {k : ℤ} {z : ℝ} (hz : z ∈ Set.Icc (k : ℝ) (k + 1)) : h.lift z = ℓ (z - k) + k := by
  simp only [lift_apply, perExt]
  rcases eq_or_lt_of_le hz.2 with he | hlt
  · rw [he, show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, Int.fract_intCast,
      Int.floor_intCast]
    push_cast
    rw [show (k : ℝ) + 1 - k = 1 by ring, h.one]; ring
  · have hfl : ⌊z⌋ = k := Int.floor_eq_iff.2 ⟨hz.1, hlt⟩
    rw [Int.fract, hfl]

end PerData

/-! ### Elements of `F` -/

lemma orderIso_zero (f : UI ≃o UI) : f ⟨0, zero_mem_UI⟩ = ⟨0, zero_mem_UI⟩ := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := f.surjective ⟨0, zero_mem_UI⟩
    have := f.monotone (show (⟨0, zero_mem_UI⟩ : UI) ≤ z from Subtype.coe_le_coe.mp z.2.1)
    rwa [hz] at this
  · exact Subtype.coe_le_coe.mp (f ⟨0, zero_mem_UI⟩).2.1

lemma perData_extendFun (f : UI ≃o UI) : PerData (extendFun f) := by
  have h0 : extendFun f 0 = 0 := by
    rw [extendFun_of_mem f zero_mem_UI, orderIso_zero]
  have h1 : extendFun f 1 = 1 := by
    rw [extendFun_of_mem f one_mem_UI, orderIso_one]
  refine ⟨fun a _ b _ hab => (extend f).strictMono hab, by rw [h0, h1]; ring, ?_⟩
  intro v hv
  rw [h0] at hv
  have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by simpa using hv
  refine ⟨f.symm ⟨v, hv'⟩, (f.symm ⟨v, hv'⟩).2, ?_⟩
  rw [extendFun_of_mem f (f.symm ⟨v, hv'⟩).2]
  simp

lemma extendFun_lt_one (f : UI ≃o UI) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hu1 : u < 1) :
    extendFun f u < 1 := by
  rw [extendFun_of_mem f hu]
  exact (orderIso_lt_one_iff f ⟨u, hu⟩).2 hu1

lemma extendFun_nonneg (f : UI ≃o UI) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ extendFun f u := by
  rw [extendFun_of_mem f hu]; exact (f ⟨u, hu⟩).2.1

lemma toCircle_mem_T_of_mem_F {f : UI ≃o UI} (hf : f ∈ F) : toCircle f ∈ T := by
  apply Subgroup.subset_closure
  have hd := perData_extendFun f
  obtain ⟨B, hB, hpl⟩ := mem_F_iff_isThompson.1 hf
  refine isThompsonCircle_iff.2 ⟨hd.lift, ⟨hd.per, ?_, insert 0 B, ?_, ?_⟩, ?_⟩
  · -- dyadics to dyadics
    intro x hx
    simp only [PerData.lift_apply, perExt]
    have hfx := dy_fract hx
    have hm := (bijOn_dyadic hf).mapsTo (show (⟨Int.fract x, hd.fract_mem x⟩ : UI) ∈
      {z : UI | IsDyadic (z : ℝ)} from hfx)
    rw [extendFun_of_mem f (hd.fract_mem x)]
    exact dy_add hm (isDyadic_int _)
  · intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    · exact hB b hb
  · intro x y hxy havoid
    set k := ⌊x⌋
    have hkx : (k : ℝ) ≤ x := Int.floor_le x
    have hxk : x < k + 1 := Int.lt_floor_add_one x
    have hyk : y ≤ k + 1 := by
      by_contra hy; push Not at hy
      exact havoid (k + 1) ⟨hxk, hy⟩ 0 (Finset.mem_insert_self _ _) (k + 1) (by push_cast; ring)
    have hx' : x - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hy' : y - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨n, c, hc⟩ := hpl ⟨x - k, hx'⟩ ⟨y - k, hy'⟩ (by simp; linarith) (by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro ht hbt
      exact havoid (t + k) ⟨by linarith [ht.1], by linarith [ht.2]⟩ t
        (Finset.mem_insert_of_mem hbt) k rfl)
    refine ⟨n, c + k - 2 ^ n * k, fun z hz => ?_⟩
    have hzk : z ∈ Set.Icc (k : ℝ) (k + 1) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hz' : z - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hzk.1], by linarith [hzk.2]⟩
    rw [hd.eq_on hzk, extendFun_of_mem f hz']
    have := hc ⟨z - k, hz'⟩ ⟨by simp; linarith [hz.1], by simp; linarith [hz.2]⟩
    simp only at this
    rw [this]; ring
  · -- covering
    intro x
    apply circle_ext
    have e : (⟨ico (x : UnitAddCircle), ico_nonneg _, (ico_lt_one _).le⟩ : UI) =
        ⟨Int.fract x, hd.fract_mem x⟩ := Subtype.ext (ico_coe x)
    rw [ico_toCircle, e, ico_coe]
    simp only [PerData.lift_apply, perExt]
    rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨extendFun_nonneg f (hd.fract_mem x),
      extendFun_lt_one f (hd.fract_mem x) (Int.fract_lt_one x)⟩, extendFun_of_mem f (hd.fract_mem x)]

/-! ### The map `C` -/

/-- The lift of `C` on `[0,1]`: values in `[3/4, 7/4]`. -/
noncomputable def ellC (u : ℝ) : ℝ := if u ≤ 1/2 then u / 2 + 3/4 else if u ≤ 3/4 then 2 * u else u + 3/4

lemma ellC_1 {u : ℝ} (h1 : u ≤ 1/2) : ellC u = u / 2 + 3/4 := by unfold ellC; split_ifs <;> linarith
lemma ellC_2 {u : ℝ} (h0 : 1/2 ≤ u) (h1 : u ≤ 3/4) : ellC u = 2 * u := by
  unfold ellC; split_ifs <;> linarith
lemma ellC_3 {u : ℝ} (h0 : 3/4 ≤ u) : ellC u = u + 3/4 := by unfold ellC; split_ifs <;> linarith

lemma perData_ellC : PerData ellC := by
  refine ⟨?_, by rw [ellC_3 (by norm_num), ellC_1 (by norm_num)]; norm_num, ?_⟩
  · intro a ha b hb hab
    unfold ellC; split_ifs <;> linarith
  · intro v hv
    rw [ellC_1 (by norm_num)] at hv
    obtain ⟨hv0, hv1⟩ := hv
    rcases le_or_gt v 1 with h1 | h1
    · refine ⟨2 * (v - 3/4), ⟨by linarith, by linarith⟩, ?_⟩
      rw [ellC_1 (by linarith)]; ring
    rcases le_or_gt v (3/2) with h2 | h2
    · exact ⟨v / 2, ⟨by linarith, by linarith⟩, by rw [ellC_2 (by linarith) (by linarith)]; ring⟩
    · exact ⟨v - 3/4, ⟨by linarith, by linarith⟩, by rw [ellC_3 (by linarith)]; ring⟩

lemma fract_ellC {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : Int.fract (ellC u) = cFun u := by
  rcases le_or_gt u (1/2) with ha | ha
  · rw [ellC_1 ha]
    rcases lt_or_eq_of_le ha with ha' | rfl
    · rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩, cFun_of_mem1 ha']
    · rw [cFun_of_mem2 (by norm_num) (by norm_num)]; norm_num
  rcases lt_or_ge u (3/4) with hb | hb
  · rw [ellC_2 ha.le hb.le, cFun_of_mem2 ha.le hb, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨1, by push_cast; ring⟩⟩
  · rw [ellC_3 hb, cFun_of_mem3 hb, Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨1, by push_cast; ring⟩⟩

lemma mapC_mem_T : mapC ∈ T := by
  apply Subgroup.subset_closure
  have hd := perData_ellC
  have d34 : IsDyadic (3/4 : ℝ) := ⟨3, 2, by norm_num⟩
  refine isThompsonCircle_iff.2 ⟨hd.lift, ⟨hd.per, ?_, {0, 1/2, 3/4}, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [PerData.lift_apply, perExt]
    have hfx := dy_fract hx
    refine dy_add ?_ (isDyadic_int _)
    set u := Int.fract x
    unfold ellC
    split_ifs
    · have := dy_add (dy_zpow hfx (-1)) d34
      convert this using 1; rw [zpow_neg_one]; ring
    · have := dy_zpow hfx 1
      convert this using 1; rw [zpow_one]
    · exact dy_add hfx d34
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact d34
  · intro x y hxy havoid
    set k := ⌊x⌋
    have hkx : (k : ℝ) ≤ x := Int.floor_le x
    have hxk : x < k + 1 := Int.lt_floor_add_one x
    have hB : ∀ b ∈ ({0, 1/2, 3/4} : Finset ℝ), ¬ (x < b + k ∧ b + k < y) := by
      intro b hb h; exact havoid (b + k) h b hb k rfl
    have hyk : y ≤ k + 1 := by
      by_contra hy; push Not at hy
      exact havoid (k + 1) ⟨hxk, hy⟩ 0 (by simp) (k + 1) (by push_cast; ring)
    have h12 := hB (1/2) (by simp)
    have h34 := hB (3/4) (by simp)
    have hon : ∀ z ∈ Set.Icc x y, hd.lift z = ellC (z - k) + k := fun z hz =>
      hd.eq_on ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rcases le_or_gt y (1/2 + k) with hy1 | hy1
    · refine ⟨-1, 3/4 + k - k / 2, fun z hz => ?_⟩
      rw [hon z hz, ellC_1 (by linarith [hz.2]), zpow_neg_one]; ring
    have hx1 : 1/2 + k ≤ x := by
      by_contra hx; push Not at hx; exact h12 ⟨hx, hy1⟩
    rcases le_or_gt y (3/4 + k) with hy2 | hy2
    · refine ⟨1, -k, fun z hz => ?_⟩
      rw [hon z hz, ellC_2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]; ring
    have hx2 : 3/4 + k ≤ x := by
      by_contra hx; push Not at hx; exact h34 ⟨hx, hy2⟩
    refine ⟨0, 3/4, fun z hz => ?_⟩
    rw [hon z hz, ellC_3 (by linarith [hz.1]), zpow_zero]; ring
  · intro x
    apply circle_ext
    have hC : mapC = symT FormalABC.C := rfl
    rw [hC, ico_C, ico_coe, ico_coe]
    simp only [PerData.lift_apply, perExt]
    rw [Int.fract_add_intCast, fract_ellC (Int.fract_nonneg x) (Int.fract_lt_one x)]

theorem toCircle_mem_T_and_mapC_mem_T' : (∀ f ∈ F, toCircle f ∈ T) ∧ mapC ∈ T :=
  ⟨fun _ hf => toCircle_mem_T_of_mem_F hf, mapC_mem_T⟩

end CannonFloydParry.S5

open CannonFloydParry

theorem solution :
    (∀ f ∈ F, toCircle f ∈ T) ∧ mapC ∈ T :=
  CannonFloydParry.S5.toCircle_mem_T_and_mapC_mem_T'
