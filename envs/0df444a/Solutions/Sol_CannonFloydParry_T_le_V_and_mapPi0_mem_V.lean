-- Prove2me | solution 1 for CannonFloydParry.T_le_V_and_mapPi0_mem_V
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T10:29:04.649989+00:00
-- url     : https://prove2.me/submissions/5daa1e4d-a1a3-4329-bc64-9984272ed61d

import Definitions.Def_CannonFloydParry_T
import Mathlib
import Definitions.Def_CannonFloydParry_V

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

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

/-! Piecewise formulas. -/

/-! The generators and their inverses on representatives. -/

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C`, `π₀` and their inverses on `[0,1)` representatives. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma piFun_of_mem1 {y : ℝ} (h1 : y < 1 / 2) : piFun y = y / 2 + 1 / 2 := by
  unfold piFun; rw [if_pos h1]

lemma piFun_of_mem2 {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y < 3 / 4) : piFun y = 2 * y - 1 := by
  unfold piFun; rw [if_neg (by linarith), if_pos h1]

lemma piFun_of_mem3 {y : ℝ} (h0 : 3 / 4 ≤ y) : piFun y = y := by
  unfold piFun; rw [if_neg (by linarith), if_neg (by linarith)]

lemma ico_P (x : UnitAddCircle) : ico (symV FormalV.P x) = piFun (ico x) := by
  simp only [symV, mapPi0, Equiv.trans_apply, ico_symm]
  rfl

end CannonFloydParry.S6

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

/-! `T ≤ V` and `π₀ ∈ V` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma circ_ext {p q : UnitAddCircle} (h : ico p = ico q) : p = q :=
  (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

lemma coe_fract (x : ℝ) : ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [Int.fract, sub_eq_add_neg, AddCircle.coe_add]
  have : (((-⌊x⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨-⌊x⌋, by simp⟩
  push_cast at this
  rw [this, add_zero]

lemma ico_coe (x : ℝ) : ico (x : UnitAddCircle) = Int.fract x := by
  rw [← coe_fract, ico, AddCircle.equivIco_coe_eq ⟨Int.fract_nonneg x, by
    simpa using Int.fract_lt_one x⟩]

lemma mapPi0_coe (z : ℝ) : mapPi0 (z : UnitAddCircle) = ((piFun (Int.fract z) : ℝ) : UnitAddCircle) := by
  apply circ_ext
  have h := ico_P (z : UnitAddCircle)
  simp only [symV] at h
  obtain ⟨m0, m1⟩ := piFun_mem (x := Int.fract z) ⟨Int.fract_nonneg z, by
    simpa using Int.fract_lt_one z⟩
  rw [h, ico_coe, ico_coe, Int.fract_eq_self.2 ⟨m0, by simpa using m1⟩]

lemma fract_of {z : ℝ} {k : ℤ} (h1 : (k : ℝ) ≤ z) (h2 : z < k + 1) : Int.fract z = z - k := by
  rw [Int.fract, Int.floor_eq_iff.2 ⟨h1, h2⟩]

lemma dy_half : IsDyadic (1 / 2 : ℝ) := ⟨1, 1, by norm_num⟩
lemma dy_three_quarters : IsDyadic (3 / 4 : ℝ) := ⟨3, 2, by norm_num⟩
lemma dy_zero : IsDyadic (0 : ℝ) := ⟨0, 0, by norm_num⟩
lemma dy_one : IsDyadic (1 : ℝ) := ⟨1, 0, by norm_num⟩

lemma dy_piFun {x : ℝ} (hx : IsDyadic x) : IsDyadic (piFun x) := by
  unfold piFun
  split_ifs
  · have := dy_add (dy_zpow hx (-1)) dy_half
    rwa [zpow_neg_one, show (2 : ℝ)⁻¹ * x = x / 2 by ring] at this
  · have := dy_sub (dy_zpow hx 1) dy_one
    rwa [zpow_one] at this
  · exact hx

theorem T_le_V_and_mapPi0_mem_V' : T ≤ V ∧ mapPi0 ∈ V := by
  constructor
  · rw [T, Subgroup.closure_le]
    intro f hf
    apply Subgroup.subset_closure
    obtain ⟨L, -, hcov, hdy, B, hB, hpl⟩ := hf
    refine ⟨fun x hx => ⟨L x, hdy x hx, hcov x⟩, B, hB, fun x y hxy hav => ?_⟩
    obtain ⟨n, c, h⟩ := hpl x y hxy hav
    exact ⟨n, c, fun z hz => by rw [hcov, h z (Set.Ico_subset_Icc_self hz)]⟩
  · apply Subgroup.subset_closure
    refine ⟨fun x hx => ⟨piFun (Int.fract x), dy_piFun (dy_fract hx), mapPi0_coe x⟩,
      {0, 1 / 2, 3 / 4}, ?_, fun x y hxy hav => ?_⟩
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact dy_zero
      · exact dy_half
      · exact dy_three_quarters
    set k := ⌊x⌋
    have hk1 : (k : ℝ) ≤ x := Int.floor_le x
    have hk2 : x < k + 1 := Int.lt_floor_add_one x
    -- `y` stays below the next breakpoint after `x`
    have bound : ∀ b ∈ ({0, 1 / 2, 3 / 4} : Finset ℝ), ∀ j : ℤ, x < b + j → y ≤ b + j := by
      intro b hb j hxb
      by_contra hy
      exact hav (b + j) ⟨hxb, lt_of_not_ge hy⟩ b hb j rfl
    have fz : ∀ z ∈ Set.Ico x y, y ≤ k + 1 → Int.fract z = z - k := fun z hz hy =>
      fract_of (le_trans hk1 hz.1) (lt_of_lt_of_le hz.2 hy)
    rcases lt_or_ge x (k + 1 / 2) with h1 | h1
    · have hy : y ≤ k + 1 / 2 := by
        have := bound (1 / 2) (by simp) k (by linarith); linarith
      refine ⟨-1, 1 / 2 - k / 2, fun z hz => ?_⟩
      rw [mapPi0_coe, fz z hz (by linarith), piFun_of_mem1 (by linarith [hz.2]), zpow_neg_one]
      congr 1; ring
    rcases lt_or_ge x (k + 3 / 4) with h2 | h2
    · have hy : y ≤ k + 3 / 4 := by
        have := bound (3 / 4) (by simp) k (by linarith); linarith
      refine ⟨1, -1 - 2 * k, fun z hz => ?_⟩
      rw [mapPi0_coe, fz z hz (by linarith), piFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]),
        zpow_one]
      congr 1; ring
    · have hy : y ≤ k + 1 := by
        have := bound 0 (by simp) (k + 1) (by push_cast; linarith); push_cast at this; linarith
      refine ⟨0, -k, fun z hz => ?_⟩
      rw [mapPi0_coe, fz z hz hy, piFun_of_mem3 (by linarith [hz.1]), zpow_zero]
      congr 1; ring

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution : T ≤ V ∧ mapPi0 ∈ V := by
  exact S6.T_le_V_and_mapPi0_mem_V'
