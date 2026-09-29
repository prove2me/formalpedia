-- Prove2me | solution 1 for CannonFloydParry.mem_T_iff_isThompsonCircle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T19:52:17.007513+00:00
-- url     : https://prove2.me/submissions/4ae11528-7fe2-4e46-9363-412444857232

import Definitions.Def_CannonFloydParry_T
import Mathlib

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

lemma refl : GoodLift (OrderIso.refl ℝ) :=
  ⟨fun _ => rfl, fun _ h => h, ∅, by simp, fun x y _ _ => ⟨0, 0, fun z _ => by simp⟩⟩

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

/-- The maps satisfying `IsThompsonCircle`, as a subgroup. -/
def TC : Subgroup (Equiv.Perm UnitAddCircle) where
  carrier := {f | IsThompsonCircle f}
  one_mem' := isThompsonCircle_iff.2 ⟨OrderIso.refl ℝ, GoodLift.refl, fun x => rfl⟩
  mul_mem' := by
    intro f g hf hg
    obtain ⟨Lf, hLf, hf⟩ := isThompsonCircle_iff.1 hf
    obtain ⟨Lg, hLg, hg⟩ := isThompsonCircle_iff.1 hg
    exact isThompsonCircle_iff.2 ⟨Lg.trans Lf, hLg.trans hLf, fun x => by
      simp [Equiv.Perm.coe_mul, hg, hf]⟩
  inv_mem' := by
    intro f hf
    obtain ⟨L, hL, hf⟩ := isThompsonCircle_iff.1 hf
    refine isThompsonCircle_iff.2 ⟨L.symm, hL.symm, fun x => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hf, OrderIso.apply_symm_apply]

theorem mem_T_iff_isThompsonCircle' {f : Equiv.Perm UnitAddCircle} :
    f ∈ T ↔ IsThompsonCircle f := by
  constructor
  · intro hf
    have : T ≤ TC := (Subgroup.closure_le TC).2 (fun g hg => hg)
    exact this hf
  · intro hf
    exact Subgroup.subset_closure hf

end CannonFloydParry.S5

open CannonFloydParry

theorem solution {f : Equiv.Perm UnitAddCircle} :
    f ∈ T ↔ IsThompsonCircle f :=
  CannonFloydParry.S5.mem_T_iff_isThompsonCircle'
