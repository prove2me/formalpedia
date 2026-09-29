-- Prove2me | solution 1 for CannonFloydParry.exists_standardDyadicPartitions_of_mem_V
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T10:30:42.944998+00:00
-- url     : https://prove2.me/submissions/c8520335-26e2-405f-bc7c-99b202f7e2bf

import Theorems.Thm_CannonFloydParry_mem_V_iff_isThompsonV
import Definitions.Def_CannonFloydParry_T
import Mathlib
import Definitions.Def_CannonFloydParry_V
import Definitions.Def_CannonFloydParry_TreeDiagrams

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

/-! Piecewise formulas. -/

/-! The generators and their inverses on representatives. -/

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C`, `π₀` and their inverses on `[0,1)` representatives. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

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


end CannonFloydParry.S6

/-! For `f` satisfying `IsThompsonV`: a uniform dyadic partition on whose pieces `f` is affine and
carries each piece onto a standard dyadic interval. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- `x · 2ᵈ` is an integer. -/
def IntAt (x : ℝ) (d : ℕ) : Prop := ∃ z : ℤ, x * 2 ^ d = z

lemma IntAt.mono {x : ℝ} {d d' : ℕ} (h : IntAt x d) (hd : d ≤ d') : IntAt x d' := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨e, rfl⟩ : ∃ e, d' = d + e := ⟨d' - d, by omega⟩
  exact ⟨z * 2 ^ e, by rw [pow_add, ← mul_assoc, hz]; push_cast; ring⟩

lemma dy_intAt {x : ℝ} (hx : IsDyadic x) : ∃ d, IntAt x d := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨k, m, by field_simp⟩

lemma coe_eq_coe {a b : ℝ} (h : (a : UnitAddCircle) = b) : ∃ m : ℤ, b = a + m := by
  have := QuotientAddGroup.eq.1 h
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 this
  exact ⟨m, by simp at hm; linarith⟩

lemma coe_add_int (a : ℝ) (m : ℤ) : ((a + m : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
  rw [AddCircle.coe_add]
  have : ((m : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨m, by simp⟩
  rw [this, add_zero]

lemma dy_div_two_pow (j M : ℕ) : IsDyadic ((j : ℝ) / 2 ^ M) := ⟨j, M, by push_cast; ring⟩

/-- Level `M₀`: `f` is `z ↦ 2ᵏ z + c`, with `c` dyadic, on each `[j/2^M₀, (j+1)/2^M₀)`. -/
lemma uniform_affine {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M0 : ℕ, ∀ j : ℕ, j < 2 ^ M0 → ∃ (k : ℤ) (c : ℝ), IsDyadic c ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0),
        f (z : UnitAddCircle) = ((2 ^ k * z + c : ℝ) : UnitAddCircle) := by
  obtain ⟨hdy, B, hB, hpl⟩ := hf
  have hd : ∀ b ∈ B, ∃ d, IntAt b d := fun b hb => dy_intAt (hB b hb)
  choose! db hdb using hd
  refine ⟨B.sup db, fun j _ => ?_⟩
  set M0 := B.sup db
  have hpos : (0 : ℝ) < 2 ^ M0 := by positivity
  have hav : ∀ t ∈ Set.Ioo ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    intro t ht b hb k htb
    obtain ⟨z, hz⟩ := (hdb b hb).mono (Finset.le_sup hb)
    have h1 : (j : ℝ) < t * 2 ^ M0 := by rw [← div_lt_iff₀ hpos]; exact ht.1
    have h2 : t * 2 ^ M0 < j + 1 := by rw [← lt_div_iff₀ hpos]; exact ht.2
    have e : t * 2 ^ M0 = ((z + k * 2 ^ M0 : ℤ) : ℝ) := by rw [htb, add_mul, hz]; push_cast; ring
    rw [e] at h1 h2
    have h1' : (j : ℤ) < z + k * 2 ^ M0 := by exact_mod_cast h1
    have h2' : z + k * 2 ^ M0 < (j : ℤ) + 1 := by exact_mod_cast h2
    omega
  have hlt : (j : ℝ) / 2 ^ M0 < (j + 1) / 2 ^ M0 := by
    rw [div_lt_div_iff_of_pos_right hpos]; linarith
  obtain ⟨n, c, hc⟩ := hpl _ _ hlt hav
  refine ⟨n, c, ?_, hc⟩
  obtain ⟨d, hd, hfx⟩ := hdy _ (dy_div_two_pow j M0)
  rw [hc _ ⟨le_rfl, hlt⟩] at hfx
  obtain ⟨m, hm⟩ := coe_eq_coe hfx
  have : c = d - m - 2 ^ n * ((j : ℝ) / 2 ^ M0) := by linarith
  rw [this]
  exact dy_sub (dy_sub hd (isDyadic_int m)) (dy_zpow (dy_div_two_pow j M0) n)

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- A finer uniform level at which every piece is carried onto a standard dyadic interval:
on `[j/2^M, (j+1)/2^M)`, `f` is `z ↦ A/2^m + 2ᵏ (z - j/2^M)` with `2ᵏ·2^m = 2^M`, `A < 2^m`. -/
lemma uniform_std {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ j : ℕ, j < 2 ^ M → ∃ (k : ℤ) (m A : ℕ), A + 1 ≤ 2 ^ m ∧
      (2 : ℝ) ^ k * 2 ^ m = 2 ^ M ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M),
        f (z : UnitAddCircle) = (((A : ℝ) / 2 ^ m + 2 ^ k * (z - j / 2 ^ M) : ℝ) : UnitAddCircle) := by
  obtain ⟨M0, h0⟩ := uniform_affine hf
  have h1 : ∀ j : Fin (2 ^ M0), ∃ (k : ℤ) (c : ℝ), IsDyadic c ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0),
        f (z : UnitAddCircle) = ((2 ^ k * z + c : ℝ) : UnitAddCircle) := fun j => h0 j j.2
  choose K C hC hK using h1
  have h2 : ∀ j : Fin (2 ^ M0), ∃ d, IntAt (C j) d := fun j => dy_intAt (hC j)
  choose D hD using h2
  obtain ⟨E, hE2, hkE_all⟩ : ∃ E : ℕ, 2 ≤ E ∧ ∀ j : Fin (2 ^ M0), (K j).toNat + D j ≤ E :=
    ⟨Finset.univ.sup (fun j : Fin (2 ^ M0) => (K j).toNat + D j) + 2, Nat.le_add_left _ _,
      fun j => le_trans (Finset.le_sup (f := fun j : Fin (2 ^ M0) => (K j).toNat + D j)
        (Finset.mem_univ j)) (Nat.le_add_right _ _)⟩
  refine ⟨M0 + E, by omega, fun j' hj' => ?_⟩
  have hE : (0 : ℕ) < 2 ^ E := by positivity
  set q := j' / 2 ^ E
  have hq : q < 2 ^ M0 := by
    rw [Nat.div_lt_iff_lt_mul hE, ← pow_add]; exact hj'
  set jq : Fin (2 ^ M0) := ⟨q, hq⟩
  set k := K jq
  set c := C jq
  have hkE : k.toNat + D jq ≤ E := hkE_all jq
  have hk_le : k ≤ k.toNat := Int.self_le_toNat k
  set m := ((M0 + E : ℕ) - k).toNat
  have hm : (m : ℤ) = (M0 + E : ℕ) - k := Int.toNat_of_nonneg (by push_cast; omega)
  have hDm : D jq ≤ m := by omega
  have hpow : (2 : ℝ) ^ k * 2 ^ m = 2 ^ (M0 + E) := by
    rw [← zpow_natCast (2 : ℝ) m, ← zpow_natCast (2 : ℝ) (M0 + E), ← zpow_add₀ two_ne_zero, hm]
    congr 1; ring
  -- the level-`M0` piece containing the level-`M0+E` piece `j'`
  have hdm : 2 ^ E * q + j' % 2 ^ E = j' := Nat.div_add_mod j' (2 ^ E)
  have hmod : j' % 2 ^ E < 2 ^ E := Nat.mod_lt j' hE
  have hsub : Set.Ico ((j' : ℝ) / 2 ^ (M0 + E)) ((j' + 1) / 2 ^ (M0 + E)) ⊆
      Set.Ico ((q : ℝ) / 2 ^ M0) ((q + 1) / 2 ^ M0) := by
    intro z ⟨hz1, hz2⟩
    have e1 : (q : ℝ) / 2 ^ M0 = (q * 2 ^ E : ℕ) / 2 ^ (M0 + E) := by
      push_cast; rw [pow_add]; field_simp
    have e2 : ((q : ℝ) + 1) / 2 ^ M0 = ((q + 1) * 2 ^ E : ℕ) / 2 ^ (M0 + E) := by
      push_cast; rw [pow_add]; field_simp
    have hpos : (0 : ℝ) < 2 ^ (M0 + E) := by positivity
    constructor
    · rw [e1]; refine le_trans ?_ hz1
      apply div_le_div_of_nonneg_right _ hpos.le
      have : q * 2 ^ E ≤ j' := Nat.div_mul_le_self j' (2 ^ E)
      exact_mod_cast this
    · rw [e2]; refine lt_of_lt_of_le hz2 ?_
      apply div_le_div_of_nonneg_right _ hpos.le
      have : j' + 1 ≤ (q + 1) * 2 ^ E := by nlinarith
      exact_mod_cast this
  -- the left endpoint of the image
  set x' : ℝ := (j' : ℝ) / 2 ^ (M0 + E)
  set u : ℝ := 2 ^ k * x' + c
  have hu : IntAt u m := by
    obtain ⟨z, hz⟩ := (hD jq).mono hDm
    refine ⟨j' + z, ?_⟩
    have : (2 : ℝ) ^ k * x' * 2 ^ m = j' := by
      calc (2 : ℝ) ^ k * x' * 2 ^ m = ((2 : ℝ) ^ k * 2 ^ m) * x' := by ring
        _ = j' := by rw [hpow]; simp only [x']; field_simp
    simp only [u]; rw [add_mul, this, hz]; push_cast; ring
  obtain ⟨zu, hzu⟩ := hu
  have hfr : ∃ A : ℕ, Int.fract u * 2 ^ m = A ∧ A + 1 ≤ 2 ^ m := by
    have e : Int.fract u * 2 ^ m = ((zu - ⌊u⌋ * 2 ^ m : ℤ) : ℝ) := by
      rw [Int.fract, sub_mul, hzu]; push_cast; ring
    have h0 : (0 : ℝ) ≤ Int.fract u * 2 ^ m := by positivity
    have h1 : Int.fract u * 2 ^ m < 2 ^ m := by
      have := Int.fract_lt_one u; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
    rw [e] at h0 h1
    have h0' : (0 : ℤ) ≤ zu - ⌊u⌋ * 2 ^ m := by exact_mod_cast h0
    have h1' : zu - ⌊u⌋ * 2 ^ m < 2 ^ m := by exact_mod_cast h1
    refine ⟨(zu - ⌊u⌋ * 2 ^ m).toNat, ?_, ?_⟩
    · rw [e, show (((zu - ⌊u⌋ * 2 ^ m).toNat : ℕ) : ℝ) = (((zu - ⌊u⌋ * 2 ^ m).toNat : ℤ) : ℝ) by
        norm_cast, Int.toNat_of_nonneg h0']
    · have : ((zu - ⌊u⌋ * 2 ^ m).toNat : ℤ) + 1 ≤ 2 ^ m := by rw [Int.toNat_of_nonneg h0']; omega
      exact_mod_cast this
  obtain ⟨A, hA, hA1⟩ := hfr
  refine ⟨k, m, A, hA1, hpow, fun z hz => ?_⟩
  rw [hK jq z (hsub hz)]
  have e : (2 : ℝ) ^ k * z + c = ((A : ℝ) / 2 ^ m + 2 ^ k * (z - x')) + ⌊u⌋ := by
    have : (A : ℝ) / 2 ^ m = Int.fract u := by rw [← hA]; field_simp
    rw [this, Int.fract]; simp only [u]; ring
  rw [e, coe_add_int]

end CannonFloydParry.S6

/-! Disjoint standard dyadic intervals covering `[0,1)`, sorted, form a standard dyadic partition. -/

namespace CannonFloydParry.S6

lemma sdi_bounds {x y : ℝ} (h : IsStandardDyadicInterval x y) : 0 ≤ x ∧ x < y ∧ y ≤ 1 := by
  obtain ⟨a, n, ha, rfl, rfl⟩ := h
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨by positivity, by rw [div_lt_div_iff_of_pos_right hp]; linarith, ?_⟩
  rw [div_le_one hp]; exact_mod_cast ha

theorem sort_partition {N : ℕ} (a ℓ : Fin N → ℝ)
    (hstd : ∀ j, IsStandardDyadicInterval (a j) (a j + ℓ j))
    (hdisj : ∀ j j' w, w ∈ Set.Ico (a j) (a j + ℓ j) → w ∈ Set.Ico (a j') (a j' + ℓ j') → j = j')
    (hcov : ∀ w ∈ Set.Ico (0 : ℝ) 1, ∃ j, w ∈ Set.Ico (a j) (a j + ℓ j)) :
    ∃ (y : Fin (N + 1) → ℝ) (σ : Equiv.Perm (Fin N)), IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ j, y (σ j).castSucc = a j ∧ y (σ j).succ = a j + ℓ j := by
  have hb := fun j => sdi_bounds (hstd j)
  have hmem : ∀ j, a j ∈ Set.Ico (a j) (a j + ℓ j) := fun j => ⟨le_rfl, (hb j).2.1⟩
  have hinj : Function.Injective a := fun j j' h => hdisj j j' (a j) (hmem j) (h ▸ hmem j')
  set s := Finset.univ.image a
  have hcard : s.card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set e := s.orderIsoOfFin hcard
  have he_mem : ∀ j, a j ∈ s := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have he_surj : ∀ w ∈ s, ∃ r, (e r : ℝ) = w := fun w hw => ⟨e.symm ⟨w, hw⟩, by simp⟩
  have he_in : ∀ r, ∃ j, (e r : ℝ) = a j := fun r => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (e r).2; exact ⟨j, hj.symm⟩
  let σf : Fin N → Fin N := fun j => e.symm ⟨a j, he_mem j⟩
  have hσf : ∀ j, (e (σf j) : ℝ) = a j := fun j => by simp [σf]
  have σinj : Function.Injective σf := fun j j' h => hinj (by rw [← hσf, h, hσf])
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 σinj)
  let y : Fin (N + 1) → ℝ := fun r => if h : (r : ℕ) < N then (e ⟨r, h⟩ : ℝ) else 1
  have hy_lt : ∀ r : Fin N, y r.castSucc = e r := fun r => by simp [y]
  have hy_last : y (Fin.last N) = 1 := by simp [y]
  have emono : StrictMono (fun r => (e r : ℝ)) := fun r r' h => by
    simpa using e.strictMono h
  -- the successor of `a j` among the left endpoints is `a j + ℓ j`
  have succ : ∀ j, y (σ j).succ = a j + ℓ j := by
    intro j
    set r := σ j
    have hr : (e r : ℝ) = a j := hσf j
    by_cases hb1 : a j + ℓ j = 1
    · -- `r` is the last index
      have hlast : (r : ℕ) + 1 = N := by
        by_contra hne
        have hlt : (r : ℕ) + 1 < N := by omega
        obtain ⟨j'', hj''⟩ := he_in ⟨r + 1, hlt⟩
        have hgt : a j < a j'' := by
          rw [← hr, ← hj'']; exact emono (show r < ⟨r + 1, hlt⟩ from Fin.lt_def.2 (Nat.lt_succ_self _))
        have : j'' = j := hdisj j'' j (a j'') (hmem j'') ⟨hgt.le, by
          have := hb j''; linarith [(hb j'').2.1]⟩
        rw [this] at hgt; exact lt_irrefl _ hgt
      have : y r.succ = 1 := by
        rw [show r.succ = Fin.last N from Fin.ext (by rw [Fin.val_succ, Fin.val_last]; omega)]
        exact hy_last
      rw [this, hb1]
    · have hb1' : a j + ℓ j < 1 := lt_of_le_of_ne (hb j).2.2 hb1
      obtain ⟨j', hj'⟩ := hcov (a j + ℓ j) ⟨by linarith [(hb j).1, (hb j).2.1], hb1'⟩
      have hj'ne : j' ≠ j := fun h => by rw [h] at hj'; exact lt_irrefl _ hj'.2
      -- `a j' = a j + ℓ j`
      have haj' : a j' = a j + ℓ j := by
        rcases lt_trichotomy (a j') (a j + ℓ j) with h | h | h
        · exfalso
          rcases le_or_gt (a j) (a j') with h2 | h2
          · exact hj'ne (hdisj j' j (a j') (hmem j') ⟨h2, h⟩)
          · exact hj'ne (hdisj j' j (a j) ⟨h2.le, by linarith [hj'.2, (hb j).2.1]⟩ (hmem j))
        · exact h
        · exact absurd hj'.1 (not_le.2 h)
      obtain ⟨t, ht⟩ := he_surj (a j + ℓ j) (haj' ▸ he_mem j')
      have hrt : r < t := by
        by_contra h
        have h' : (e t : ℝ) ≤ e r := emono.monotone (not_lt.1 h)
        rw [ht, hr] at h'; linarith [(hb j).2.1]
      have hnext : (t : ℕ) = r + 1 := by
        by_contra hne
        have hlt : (r : ℕ) + 1 < t := by omega
        have hlt' : (r : ℕ) + 1 < N := lt_trans hlt t.2
        obtain ⟨j'', hj''⟩ := he_in ⟨r + 1, hlt'⟩
        have h1 : a j < a j'' := by
          rw [← hr, ← hj'']; exact emono (show r < ⟨r + 1, hlt'⟩ from Fin.lt_def.2 (Nat.lt_succ_self _))
        have h2 : a j'' < a j + ℓ j := by
          rw [← ht, ← hj'']; exact emono (show (⟨r + 1, hlt'⟩ : Fin N) < t from Fin.lt_def.2 hlt)
        have := hdisj j'' j (a j'') (hmem j'') ⟨h1.le, h2⟩
        rw [this] at h1; exact lt_irrefl _ h1
      have : r.succ = t.castSucc := Fin.ext (by rw [Fin.val_succ, Fin.coe_castSucc, hnext])
      rw [this, hy_lt, ht]
  refine ⟨y, σ, ⟨?_, ?_, ?_⟩, fun j => ⟨by rw [hy_lt]; exact hσf j, succ j⟩⟩
  · -- the first breakpoint is `0`
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exfalso; obtain ⟨j, -⟩ := hcov 0 ⟨le_rfl, one_pos⟩; exact j.elim0
    obtain ⟨j0, hj0⟩ := hcov 0 ⟨le_rfl, one_pos⟩
    have ha0 : a j0 = 0 := le_antisymm hj0.1 (hb j0).1
    have hy0 : y 0 = e ⟨0, hN⟩ := by simp [y, hN]
    rw [List.ofFn_succ, List.head?_cons, hy0]
    congr 1
    apply le_antisymm
    · rw [← ha0, ← hσf j0]; exact emono.monotone (Fin.le_def.2 (Nat.zero_le _))
    · obtain ⟨j1, hj1⟩ := he_in ⟨0, hN⟩; rw [hj1]; exact (hb j1).1
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]; simp [hy_last]
  · rw [List.isChain_ofFn]
    intro i hi
    have hiN : i < N := by omega
    obtain ⟨j, hj⟩ : ∃ j, σ j = ⟨i, hiN⟩ := σ.surjective _
    have h1 := hy_lt (σ j)
    have h2 := succ j
    rw [hj] at h1 h2
    have ea : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (N + 1)) = (⟨i, hiN⟩ : Fin N).castSucc := rfl
    have eb : (⟨i + 1, hi⟩ : Fin (N + 1)) = (⟨i, hiN⟩ : Fin N).succ := rfl
    have h3 : (e ⟨i, hiN⟩ : ℝ) = a j := by rw [← hj]; exact hσf j
    rw [ea, eb, h1, h2, h3]
    exact hstd j

end CannonFloydParry.S6

/-! Tree diagrams for maps satisfying `IsThompsonV` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma coe_inj_Ico {z z' : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) (hz' : z' ∈ Set.Ico (0 : ℝ) 1)
    (h : (z : UnitAddCircle) = z') : z = z' := by
  have := congrArg ico h
  rw [ico_coe, ico_coe, Int.fract_eq_self.2 hz, Int.fract_eq_self.2 hz'] at this
  exact this

lemma uniform_partition (M : ℕ) :
    IsStandardDyadicPartition (List.ofFn (fun i : Fin (2 ^ M + 1) => ((i : ℕ) : ℝ) / 2 ^ M)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.ofFn_succ, List.head?_cons]; simp
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]; simp
  · rw [List.isChain_ofFn]
    intro i hi
    exact ⟨i, M, by omega, rfl, by push_cast; ring⟩

lemma floor_piece {M : ℕ} {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ∃ j : ℕ, j < 2 ^ M ∧ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M) := by
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  set j := ⌊z * 2 ^ M⌋.toNat
  have h0 : (0 : ℤ) ≤ ⌊z * 2 ^ M⌋ := Int.floor_nonneg.2 (by nlinarith [hz.1])
  have hjz : (j : ℤ) = ⌊z * 2 ^ M⌋ := Int.toNat_of_nonneg h0
  have hj : (j : ℝ) = ⌊z * 2 ^ M⌋ := by exact_mod_cast hjz
  refine ⟨j, ?_, ?_, ?_⟩
  · have : z * 2 ^ M < 2 ^ M := by nlinarith [hz.2]
    have h1 : ⌊z * 2 ^ M⌋ < (2 : ℤ) ^ M := by
      rw [Int.floor_lt]; push_cast; exact this
    have : (j : ℤ) < 2 ^ M := by rw [Int.toNat_of_nonneg h0]; exact h1
    exact_mod_cast this
  · rw [div_le_iff₀ hp, hj]; exact Int.floor_le _
  · rw [lt_div_iff₀ hp, hj]; exact Int.lt_floor_add_one _

/-- Tree diagram with the uniform domain partition of level `M ≥ 2`. -/
theorem treeV_unif {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M : ℕ, 2 ≤ M ∧ ∃ (y : Fin (2 ^ M + 1) → ℝ) (σ : Equiv.Perm (Fin (2 ^ M))),
      IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin (2 ^ M), ∃ k : ℤ,
        y (σ i).succ - y (σ i).castSucc = 2 ^ k * (((i.succ : ℕ) : ℝ) / 2 ^ M - ((i.castSucc : ℕ) : ℝ) / 2 ^ M) ∧
        ∀ z ∈ Set.Ico (((i.castSucc : ℕ) : ℝ) / 2 ^ M) (((i.succ : ℕ) : ℝ) / 2 ^ M),
          f (z : UnitAddCircle) =
            ((y (σ i).castSucc + 2 ^ k * (z - ((i.castSucc : ℕ) : ℝ) / 2 ^ M) : ℝ) : UnitAddCircle) := by
  obtain ⟨M, hM2, hM⟩ := uniform_std hf
  have h1 : ∀ j : Fin (2 ^ M), ∃ (k : ℤ) (m A : ℕ), A + 1 ≤ 2 ^ m ∧ (2 : ℝ) ^ k * 2 ^ m = 2 ^ M ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M),
        f (z : UnitAddCircle) = (((A : ℝ) / 2 ^ m + 2 ^ k * (z - j / 2 ^ M) : ℝ) : UnitAddCircle) :=
    fun j => hM j j.2
  choose K m A hA hpow hK using h1
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  set a : Fin (2 ^ M) → ℝ := fun j => (A j : ℝ) / 2 ^ m j
  set ℓ : Fin (2 ^ M) → ℝ := fun j => 1 / 2 ^ m j
  have hℓ : ∀ j, ℓ j = 2 ^ K j * (1 / 2 ^ M) := by
    intro j
    have := hpow j
    have hm : (0 : ℝ) < 2 ^ m j := by positivity
    simp only [ℓ]; field_simp; linarith
  have hkpos : ∀ j, (0 : ℝ) < 2 ^ K j := fun j => zpow_pos two_pos _
  have hstd : ∀ j, IsStandardDyadicInterval (a j) (a j + ℓ j) := fun j =>
    ⟨A j, m j, hA j, rfl, by simp only [a, ℓ]; ring⟩
  have hbd := fun j => sdi_bounds (hstd j)
  -- preimage of a point of `J_j` in `I_j`
  have pre : ∀ j w, w ∈ Set.Ico (a j) (a j + ℓ j) →
      ∃ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M), f (z : UnitAddCircle) = (w : UnitAddCircle) := by
    intro j w hw
    refine ⟨(j : ℝ) / 2 ^ M + (w - a j) / 2 ^ K j, ⟨?_, ?_⟩, ?_⟩
    · have : 0 ≤ (w - a j) / 2 ^ K j := div_nonneg (by linarith [hw.1]) (hkpos j).le
      linarith
    · have h2 : (w - a j) / 2 ^ K j < 1 / 2 ^ M := by
        rw [div_lt_iff₀ (hkpos j)]; have := hw.2; rw [hℓ j] at this; linarith
      have : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
      linarith
    · rw [hK j _ ⟨by
          have : 0 ≤ (w - a j) / 2 ^ K j := div_nonneg (by linarith [hw.1]) (hkpos j).le
          linarith, by
          have h2 : (w - a j) / 2 ^ K j < 1 / 2 ^ M := by
            rw [div_lt_iff₀ (hkpos j)]; have := hw.2; rw [hℓ j] at this; linarith
          have : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
          linarith⟩]
      congr 1
      have := (hkpos j).ne'
      simp only [a]
      field_simp
      ring
  have hI : ∀ (j : Fin (2 ^ M)) z, z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M) →
      z ∈ Set.Ico (0 : ℝ) 1 := by
    intro j z hz
    constructor
    · exact le_trans (by positivity) hz.1
    · refine lt_of_lt_of_le hz.2 ?_
      rw [div_le_one hp]
      have : (j : ℕ) + 1 ≤ 2 ^ M := j.2
      exact_mod_cast this
  have hdisj : ∀ j j' w, w ∈ Set.Ico (a j) (a j + ℓ j) → w ∈ Set.Ico (a j') (a j' + ℓ j') → j = j' := by
    intro j j' w hw hw'
    obtain ⟨z, hz, hfz⟩ := pre j w hw
    obtain ⟨z', hz', hfz'⟩ := pre j' w hw'
    have hzz : z = z' := coe_inj_Ico (hI j z hz) (hI j' z' hz') (f.injective (hfz.trans hfz'.symm))
    subst hzz
    have e1 : ⌊z * 2 ^ M⌋ = (j : ℤ) := by
      rw [Int.floor_eq_iff]; constructor
      · have := hz.1; rw [div_le_iff₀ hp] at this; exact_mod_cast this
      · have := hz.2; rw [lt_div_iff₀ hp] at this; push_cast; linarith
    have e2 : ⌊z * 2 ^ M⌋ = (j' : ℤ) := by
      rw [Int.floor_eq_iff]; constructor
      · have := hz'.1; rw [div_le_iff₀ hp] at this; exact_mod_cast this
      · have := hz'.2; rw [lt_div_iff₀ hp] at this; push_cast; linarith
    exact Fin.ext (by exact_mod_cast e1.symm.trans e2)
  have hcov : ∀ w ∈ Set.Ico (0 : ℝ) 1, ∃ j, w ∈ Set.Ico (a j) (a j + ℓ j) := by
    intro w hw
    set z0 := ico (f⁻¹ (w : UnitAddCircle))
    have hz0 : z0 ∈ Set.Ico (0 : ℝ) 1 := ⟨ico_nonneg _, ico_lt_one _⟩
    have hz0c : ((z0 : ℝ) : UnitAddCircle) = f⁻¹ (w : UnitAddCircle) := by
      apply circ_ext; rw [ico_coe, Int.fract_eq_self.2 hz0]
    obtain ⟨j, hj, hzj⟩ := floor_piece (M := M) hz0
    set jf : Fin (2 ^ M) := ⟨j, hj⟩
    have hf0 := hK jf z0 hzj
    rw [hz0c, show f (f⁻¹ (w : UnitAddCircle)) = (w : UnitAddCircle) by simp] at hf0
    set v := a jf + 2 ^ K jf * (z0 - j / 2 ^ M)
    have hv : v ∈ Set.Ico (a jf) (a jf + ℓ jf) := by
      constructor
      · have : 0 ≤ 2 ^ K jf * (z0 - j / 2 ^ M) := mul_nonneg (hkpos jf).le (by linarith [hzj.1])
        simp only [v]; linarith
      · rw [hℓ jf]; simp only [v]
        have : z0 - j / 2 ^ M < 1 / 2 ^ M := by
          have := hzj.2; have e : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
          linarith
        have := mul_lt_mul_of_pos_left this (hkpos jf)
        linarith
    have hv01 : v ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans (hbd jf).1 hv.1, lt_of_lt_of_le hv.2 (hbd jf).2.2⟩
    have : w = v := coe_inj_Ico hw hv01 hf0
    exact ⟨jf, this ▸ hv⟩
  obtain ⟨y, σ, hy, hyσ⟩ := sort_partition a ℓ hstd hdisj hcov
  refine ⟨M, hM2, y, σ, hy, fun i => ⟨K i, ?_, ?_⟩⟩
  · rw [(hyσ i).1, (hyσ i).2, add_sub_cancel_left, hℓ i]
    simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  · intro z hz
    rw [(hyσ i).1]
    simp only [Fin.val_succ, Fin.val_castSucc] at hz ⊢
    push_cast at hz
    exact hK i z hz

theorem treeV {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ (n : ℕ) (x y : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)),
      IsStandardDyadicPartition (List.ofFn x) ∧ IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin n, ∃ k : ℤ, y (σ i).succ - y (σ i).castSucc = 2 ^ k * (x i.succ - x i.castSucc) ∧
        ∀ z ∈ Set.Ico (x i.castSucc) (x i.succ),
          f (z : UnitAddCircle) = ((y (σ i).castSucc + 2 ^ k * (z - x i.castSucc) : ℝ) : UnitAddCircle) := by
  obtain ⟨M, -, y, σ, hy, h⟩ := treeV_unif hf
  exact ⟨2 ^ M, fun i => ((i : ℕ) : ℝ) / 2 ^ M, y, σ, uniform_partition M, hy, h⟩

end CannonFloydParry.S6

/-! Closure of `IsThompsonV`, part 1: locating intervals in a partition; inverses. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Closure of `IsThompsonV`, part 2: products; `f ∈ V ↔ IsThompsonV f`; tree diagrams for `V`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

theorem mem_V_iff_isThompsonV' {f : Equiv.Perm UnitAddCircle} : f ∈ V ↔ IsThompsonV f :=
  by
  first
    | exact CannonFloydParry.mem_V_iff_isThompsonV
    | exact CannonFloydParry.mem_V_iff_isThompsonV ..
    | (apply CannonFloydParry.mem_V_iff_isThompsonV <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.mem_V_iff_isThompsonV


theorem exists_standardDyadicPartitions_of_mem_V' {f : Equiv.Perm UnitAddCircle} (hf : f ∈ V) :
    ∃ (n : ℕ) (x y : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)),
      IsStandardDyadicPartition (List.ofFn x) ∧ IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin n, ∃ k : ℤ, y (σ i).succ - y (σ i).castSucc = 2 ^ k * (x i.succ - x i.castSucc) ∧
        ∀ z ∈ Set.Ico (x i.castSucc) (x i.succ),
          f (z : UnitAddCircle) = ((y (σ i).castSucc + 2 ^ k * (z - x i.castSucc) : ℝ) : UnitAddCircle) :=
  treeV (mem_V_iff_isThompsonV'.1 hf)

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution {f : Equiv.Perm UnitAddCircle} (hf : f ∈ V) :
    ∃ (n : ℕ) (x y : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)),
      IsStandardDyadicPartition (List.ofFn x) ∧ IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin n, ∃ k : ℤ, y (σ i).succ - y (σ i).castSucc = 2 ^ k * (x i.succ - x i.castSucc) ∧
        ∀ z ∈ Set.Ico (x i.castSucc) (x i.succ),
          f (z : UnitAddCircle) = ((y (σ i).castSucc + 2 ^ k * (z - x i.castSucc) : ℝ) : UnitAddCircle) := by
  exact S6.exists_standardDyadicPartitions_of_mem_V' hf
