-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_perm_combInt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T10:32:45.649229+00:00
-- url     : https://prove2.me/submissions/0325a883-6e11-43d0-bd65-da00b17cfac0

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V

/-! Tree-diagram infrastructure for F, reused unchanged from the CFP §2/§4 solutions. -/


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

lemma perm_ext {σ τ : Equiv.Perm UnitAddCircle} (h : ∀ x, ico (σ x) = ico (τ x)) : σ = τ := by
  ext x
  exact (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext (h x))

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

/-! Piecewise formulas. -/

lemma aInv_of_mem1 {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1/4) : aInv y = 2 * y := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem2 {y : ℝ} (h0 : 1/4 ≤ y) (h1 : y ≤ 1/2) : aInv y = y + 1/4 := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem3 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 1) : aInv y = (y + 1) / 2 := by
  unfold aInv; split_ifs <;> linarith
lemma bInv_of_mem0 {y : ℝ} (h1 : y ≤ 1/2) : bInv y = y := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem1 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 5/8) : bInv y = 2 * y - 1/2 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem2 {y : ℝ} (h0 : 5/8 ≤ y) (h1 : y ≤ 3/4) : bInv y = y + 1/8 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) (h1 : y ≤ 1) : bInv y = (y + 1) / 2 := by
  unfold bInv; split_ifs <;> linarith
lemma cFun_of_mem1 {x : ℝ} (h1 : x < 1/2) : cFun x = x / 2 + 3/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem2 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x < 3/4) : cFun x = 2 * x - 1 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem3 {x : ℝ} (h0 : 3/4 ≤ x) : cFun x = x - 1/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cInv_of_mem1 {y : ℝ} (h1 : y < 1/2) : cInv y = (y + 1) / 2 := by
  unfold cInv; split_ifs <;> linarith
lemma cInv_of_mem2 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y < 3/4) : cInv y = y + 1/4 := by
  unfold cInv; split_ifs <;> linarith
lemma cInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) : cInv y = 2 * y - 3/2 := by
  unfold cInv; split_ifs <;> linarith

lemma aInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ aInv y ∧ aInv y ≤ 1 := by
  unfold aInv; split_ifs <;> constructor <;> linarith
lemma bInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ bInv y ∧ bInv y ≤ 1 := by
  unfold bInv; split_ifs <;> constructor <;> linarith

/-! The generators and their inverses on representatives. -/

lemma ico_A (x : UnitAddCircle) : ico (symT FormalABC.A x) = aFun (ico x) := by
  simp only [symT, ico_toCircle, mapA, restrict_coe, lineA_apply]

lemma ico_B (x : UnitAddCircle) : ico (symT FormalABC.B x) = bFun (ico x) := by
  simp only [symT, ico_toCircle, mapB, restrict_coe, lineB_apply]

lemma ico_C (x : UnitAddCircle) : ico (symT FormalABC.C x) = cFun (ico x) := by
  simp only [symT, mapC, Equiv.trans_apply, ico_symm]
  rfl

lemma inv_apply_eq_of {σ : Equiv.Perm UnitAddCircle} {x z : UnitAddCircle} (h : σ z = x) :
    σ⁻¹ x = z := by
  rw [Equiv.Perm.inv_eq_iff_eq]; exact h.symm

lemma ico_Ainv (x : UnitAddCircle) : ico ((symT FormalABC.A)⁻¹ x) = aInv (ico x) := by
  obtain ⟨h0, h1⟩ := aInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : aInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := aFun_aInv (ico x); rw [h] at this
      rw [aFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨aInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.A z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.A z) = ico x
    rw [ico_A, ico_symm]
    exact aFun_aInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Binv (x : UnitAddCircle) : ico ((symT FormalABC.B)⁻¹ x) = bInv (ico x) := by
  obtain ⟨h0, h1⟩ := bInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : bInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := bFun_bInv (ico x); rw [h] at this
      rw [bFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨bInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.B z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.B z) = ico x
    rw [ico_B, ico_symm]
    exact bFun_bInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Cinv (x : UnitAddCircle) : ico ((symT FormalABC.C)⁻¹ x) = cInv (ico x) := by
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨cInv (ico x), cInv_mem ⟨ico_nonneg x, by simpa using ico_lt_one x⟩⟩
  have hz : symT FormalABC.C z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.C z) = ico x
    rw [ico_C, ico_symm]
    exact cFun_cInv ⟨ico_nonneg x, by simpa using ico_lt_one x⟩
  rw [inv_apply_eq_of hz, ico_symm]

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

lemma ico_Av (x : UnitAddCircle) : ico (symV FormalV.A x) = aFun (ico x) := ico_A x
lemma ico_Bv (x : UnitAddCircle) : ico (symV FormalV.B x) = bFun (ico x) := ico_B x
lemma ico_Cv (x : UnitAddCircle) : ico (symV FormalV.C x) = cFun (ico x) := ico_C x
lemma ico_Avinv (x : UnitAddCircle) : ico ((symV FormalV.A)⁻¹ x) = aInv (ico x) := ico_Ainv x
lemma ico_Bvinv (x : UnitAddCircle) : ico ((symV FormalV.B)⁻¹ x) = bInv (ico x) := ico_Binv x
lemma ico_Cvinv (x : UnitAddCircle) : ico ((symV FormalV.C)⁻¹ x) = cInv (ico x) := ico_Cinv x

lemma ico_P (x : UnitAddCircle) : ico (symV FormalV.P x) = piFun (ico x) := by
  simp only [symV, mapPi0, Equiv.trans_apply, ico_symm]
  rfl

lemma mapPi0_mul_self : mapPi0 * mapPi0 = 1 := by
  apply perm_ext
  intro x
  have h := ico_P x
  simp only [symV] at h
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id]
  have h2 := ico_P (mapPi0 x)
  simp only [symV] at h2
  rw [h2, h, piFun_piFun ⟨ico_nonneg x, by simpa using ico_lt_one x⟩]

lemma mapPi0_inv : mapPi0⁻¹ = mapPi0 := inv_eq_of_mul_eq_one_right mapPi0_mul_self

lemma ico_Pinv (x : UnitAddCircle) : ico ((symV FormalV.P)⁻¹ x) = piFun (ico x) := by
  simp only [symV, mapPi0_inv]; exact ico_P x

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

lemma mapPi0_coe (z : ℝ) : mapPi0 (z : UnitAddCircle) = ((piFun (Int.fract z) : ℝ) : UnitAddCircle) := by
  apply circ_ext
  have h := ico_P (z : UnitAddCircle)
  simp only [symV] at h
  obtain ⟨m0, m1⟩ := piFun_mem (x := Int.fract z) ⟨Int.fract_nonneg z, by
    simpa using Int.fract_lt_one z⟩
  rw [h, ico_coe, ico_coe, Int.fract_eq_self.2 ⟨m0, by simpa using m1⟩]


end CannonFloydParry.S6

/-! Generation, part 1: the subgroup `G = ⟨A, B, C, π₀⟩` contains `F` and `T`; any two standard
dyadic partitions with the same number of pieces are matched, affinely on pieces, by an
element of `F`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! For `f` satisfying `IsThompsonV`: a uniform dyadic partition on whose pieces `f` is affine and
carries each piece onto a standard dyadic interval. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Generation, part 2: permutations of the pieces of the uniform partition `[j/2^L, (j+1)/2^L)`
realised by translations inside `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Generation, part 3: the swap of the first two uniform pieces lies in `G`, so every
permutation of the pieces is realised in `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Powers of `A` and `B` on representatives in `[0,1)`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B

lemma aFun_mem01 {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 ≤ aFun u ∧ aFun u < 1 := by
  rcases le_or_gt u (1 / 2) with h | h
  · rw [aFun_of_mem1 h0 h]; constructor <;> linarith
  rcases le_or_gt u (3 / 4) with h' | h'
  · rw [aFun_of_mem2 h.le h']; constructor <;> linarith
  · rw [aFun_of_mem3 h'.le h1.le]; constructor <;> linarith

/-- `Aᵏ` carries `[0, 1 - 2^{-(k+1)})` into `[0, 1/2)`. -/
lemma aIter_lo : ∀ (k : ℕ) (u : ℝ), 0 ≤ u → u < 1 - 1 / 2 ^ (k + 1) →
    0 ≤ aFun^[k] u ∧ aFun^[k] u < 1 / 2 := by
  intro k
  induction k with
  | zero => intro u h0 h1; norm_num at h1 ⊢; exact ⟨h0, h1⟩
  | succ k ih =>
    intro u h0 h1
    rw [Function.iterate_succ_apply]
    have ht : (1 : ℝ) / 2 ^ (k + 1 + 1) = 1 / 2 ^ (k + 1) / 2 := by rw [pow_succ]; field_simp
    have ht1 : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by norm_num)]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have htp : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
    rw [ht] at h1
    apply ih
    · rcases le_or_gt u (1 / 2) with h | h
      · rw [aFun_of_mem1 h0 h]; linarith
      rcases le_or_gt u (3 / 4) with h' | h'
      · rw [aFun_of_mem2 h.le h']; linarith
      · rw [aFun_of_mem3 h'.le (by linarith)]; linarith
    · rcases le_or_gt u (1 / 2) with h | h
      · rw [aFun_of_mem1 h0 h]; linarith
      rcases le_or_gt u (3 / 4) with h' | h'
      · rw [aFun_of_mem2 h.le h']; linarith
      · rw [aFun_of_mem3 h'.le (by linarith)]; linarith

/-- `Aᵏ z = 1 - 2ᵏ (1 - z)` on `[1 - 2^{-(k+1)}, 1)`. -/
lemma aIter_hi : ∀ (k : ℕ) (u : ℝ), 1 - 1 / 2 ^ (k + 1) ≤ u → u < 1 →
    aFun^[k] u = 1 - 2 ^ k * (1 - u) := by
  intro k
  induction k with
  | zero => intro u _ _; simp
  | succ k ih =>
    intro u h0 h1
    rw [Function.iterate_succ_apply]
    have ht : (1 : ℝ) / 2 ^ (k + 1 + 1) = 1 / 2 ^ (k + 1) / 2 := by rw [pow_succ]; field_simp
    have ht1 : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by norm_num)]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [ht] at h0
    have h34 : 3 / 4 ≤ u := by linarith
    rw [aFun_of_mem3 h34 h1.le, ih (2 * u - 1) (by linarith) (by linarith), pow_succ]
    ring

lemma bFun_half {z : ℝ} (h0 : 1 / 2 ≤ z) (h1 : z ≤ 1) : bFun z = (aFun (2 * z - 1) + 1) / 2 := by
  rcases le_or_gt z (3 / 4) with h | h
  · rw [bFun_of_mem1 h0 h, aFun_of_mem1 (by linarith) (by linarith)]; ring
  rcases le_or_gt z (7 / 8) with h' | h'
  · rw [bFun_of_mem2 h.le h', aFun_of_mem2 (by linarith) (by linarith)]; ring
  · rw [bFun_of_mem3 h'.le h1, aFun_of_mem3 (by linarith) (by linarith)]; ring

/-- On `[1/2, 1)`, `B` is a half-scale copy of `A`. -/
lemma bIter_half : ∀ (k : ℕ) (z : ℝ), 1 / 2 ≤ z → z < 1 →
    bFun^[k] z = (aFun^[k] (2 * z - 1) + 1) / 2 := by
  intro k
  induction k with
  | zero => intro z _ _; simp
  | succ k ih =>
    intro z h0 h1
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    obtain ⟨m0, m1⟩ := aFun_mem01 (u := 2 * z - 1) (by linarith) (by linarith)
    rw [bFun_half h0 h1.le, ih _ (by linarith) (by linarith)]
    congr 2; ring_nf

lemma bIter_lo : ∀ (k : ℕ) (z : ℝ), z ≤ 1 / 2 → bFun^[k] z = z := by
  intro k
  induction k with
  | zero => intro z _; rfl
  | succ k ih => intro z h; rw [Function.iterate_succ_apply, bFun_of_le_half h, ih z h]

lemma ico_Apow (k : ℕ) (x : UnitAddCircle) : ico ((a ^ k) x) = aFun^[k] (ico x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, ih, ico_Av, Function.iterate_succ_apply]

lemma ico_Bpow (k : ℕ) (x : UnitAddCircle) : ico ((b ^ k) x) = bFun^[k] (ico x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, ih, ico_Bv, Function.iterate_succ_apply]

lemma coe_of_ico {x : UnitAddCircle} {v : ℝ} (hv : v ∈ Set.Ico (0 : ℝ) 1) (h : ico x = v) :
    x = (v : UnitAddCircle) := circ_ext (by rw [h, ico_coe, Int.fract_eq_self.2 hv])

lemma Apow_inv_hi (k : ℕ) {w : ℝ} (hw : 1 / 2 ≤ w) (hw1 : w < 1) :
    (a ^ k)⁻¹ (w : UnitAddCircle) = ((1 - (1 - w) / 2 ^ k : ℝ) : UnitAddCircle) := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  set u := 1 - (1 - w) / 2 ^ k
  have hu0 : 1 - 1 / 2 ^ (k + 1) ≤ u := by
    have : (1 - w) / 2 ^ k ≤ 1 / 2 ^ (k + 1) := by
      rw [pow_succ, div_le_div_iff₀ hp (by positivity)]; nlinarith
    simp only [u]; linarith
  have hu1 : u < 1 := by
    have : 0 < (1 - w) / 2 ^ k := div_pos (by linarith) hp
    simp only [u]; linarith
  have hu00 : 0 ≤ u := by
    have : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  apply inv_apply_eq_of
  apply coe_of_ico ⟨by linarith, hw1⟩
  rw [ico_Apow, ico_coe, Int.fract_eq_self.2 ⟨hu00, hu1⟩, aIter_hi k u hu0 hu1]
  simp only [u]; field_simp; ring

end CannonFloydParry.S6

/-! `π₁` on representatives (generated by scripts/gen_pi1.py). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

/-- `π₁` on `[0,1)`. -/
noncomputable def p1Fun (y : ℝ) : ℝ :=
  if y < 1 / 2 then y else if y < 3 / 4 then y / 2 + 1 / 2 else if y < 7 / 8 then 2 * y - 1 else y

lemma p1Fun_of_mem1 {y : ℝ} (h1 : y < 1 / 2) : p1Fun y = y := by
  unfold p1Fun; rw [if_pos h1]
lemma p1Fun_of_mem2 {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y < 3 / 4) : p1Fun y = y / 2 + 1 / 2 := by
  unfold p1Fun; rw [if_neg (by linarith), if_pos h1]
lemma p1Fun_of_mem3 {y : ℝ} (h0 : 3 / 4 ≤ y) (h1 : y < 7 / 8) : p1Fun y = 2 * y - 1 := by
  unfold p1Fun; rw [if_neg (by linarith), if_neg (by linarith), if_pos h1]
lemma p1Fun_of_mem4 {y : ℝ} (h0 : 7 / 8 ≤ y) : p1Fun y = y := by
  unfold p1Fun; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

set_option maxHeartbeats 4000000 in
lemma ico_piV1_word (x : UnitAddCircle) :
    ico ((b⁻¹ * c⁻¹ * a * p * a⁻¹ * c * b) x) = p1Fun (ico x) := by
  simp only [mul_inv_rev, inv_inv, Equiv.Perm.coe_mul, Function.comp_apply, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL1 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL3 : piFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [piFun_of_mem3] <;> first | ring1 | linarith
    have eL4 : aFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL5 : cInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cInv_of_mem3] <;> first | ring1 | linarith
    have eL6 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL3 : piFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [piFun_of_mem1] <;> first | ring1 | linarith
    have eL4 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL5 : cInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [cInv_of_mem1] <;> first | ring1 | linarith
    have eL6 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith
    have eR0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL3 : piFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [piFun_of_mem2] <;> first | ring1 | linarith
    have eL4 : aFun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-3 / 2 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL5 : cInv ((2 : ℝ) * y + (-3 / 2 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cInv_of_mem1] <;> first | ring1 | linarith
    have eL6 : bInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith
    have eR0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL3 : piFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [piFun_of_mem3] <;> first | ring1 | linarith
  have eL4 : aFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL5 : cInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [cInv_of_mem2] <;> first | ring1 | linarith
  have eL6 : bInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
  have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1

end CannonFloydParry.S6

/-! Generation, part 4: every permutation of the uniform pieces is realised in `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma mapPi0_coe_of_mem {v : ℝ} (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    mapPi0 (v : UnitAddCircle) = ((piFun v : ℝ) : UnitAddCircle) := by
  rw [mapPi0_coe, Int.fract_eq_self.2 hv]

end CannonFloydParry.S6

/-! Lemma 6.1, relations 7)–14), for the circle maps (generated by scripts/gen_relations_v.py). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

end CannonFloydParry.S6

/-! Lemma 5.2, relations 1)–6), for the circle maps (generated by scripts/gen_relations.py). -/

namespace CannonFloydParry.S5

local notation "a" => symT FormalABC.A
local notation "b" => symT FormalABC.B
local notation "c" => symT FormalABC.C

end CannonFloydParry.S5

/-! The fourteen relations of Lemma 6.1 for the circle maps, and the homomorphism
`V₁ → Perm S¹` they give. -/

namespace CannonFloydParry.S6

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

lemma lift_of (s : FormalV) : FreeGroup.lift symV (FreeGroup.of s) = symV s :=
  FreeGroup.lift_apply_of

end CannonFloydParry.S6

/-! The action of `πᵢ` on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

lemma combPt_eq (j : ℕ) : combPt j = 1 - 1 / 2 ^ j := by simp [combPt, inv_pow]

lemma combPt_succ (j : ℕ) : combPt (j + 1) = combPt j + 1 / 2 ^ (j + 1) := by
  rw [combPt_eq, combPt_eq, pow_succ]; field_simp; try ring

lemma combPt_nonneg (j : ℕ) : 0 ≤ combPt j := by
  rw [combPt_eq]; have : (1 : ℝ) / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  linarith

lemma combPt_lt_one (j : ℕ) : combPt j < 1 := by
  rw [combPt_eq]; have : (0 : ℝ) < 1 / 2 ^ j := by positivity
  linarith

lemma combPt_mono {i j : ℕ} (h : i ≤ j) : combPt i ≤ combPt j := by
  rw [combPt_eq, combPt_eq]
  have : (1 : ℝ) / 2 ^ j ≤ 1 / 2 ^ i := by
    rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) h
  linarith

lemma piV_succ_eq (k : ℕ) : piV (k + 1) = (a ^ k)⁻¹ * (b⁻¹ * c⁻¹ * a * p * a⁻¹ * c * b) * a ^ k := by
  simp only [piV, wordPi, wordC, map_mul, map_inv, map_pow, lift_of, pow_one]
  group

lemma piV_zero_eq : piV 0 = mapPi0 := by simp [piV, wordPi, lift_of, symV]

lemma coe_mem_ico {v : ℝ} (hv : v ∈ Set.Ico (0 : ℝ) 1) : ico (v : UnitAddCircle) = v := by
  rw [ico_coe, Int.fract_eq_self.2 hv]

lemma piV_succ_lo (k : ℕ) {z : ℝ} (h0 : 0 ≤ z) (h : z < combPt (k + 1)) :
    piV (k + 1) (z : UnitAddCircle) = (z : UnitAddCircle) := by
  rw [combPt_eq] at h
  have hz1 : z < 1 := by have : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
                         linarith
  obtain ⟨v0, v1⟩ := aIter_lo k z h0 h
  have hA : (a ^ k) (z : UnitAddCircle) = ((aFun^[k] z : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨v0, by linarith⟩ (by rw [ico_Apow, coe_mem_ico ⟨h0, hz1⟩])
  have hW : (b⁻¹ * c⁻¹ * a * p * a⁻¹ * c * b) ((aFun^[k] z : ℝ) : UnitAddCircle) =
      ((aFun^[k] z : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨v0, by linarith⟩ (by rw [ico_piV1_word, coe_mem_ico ⟨v0, by linarith⟩,
      p1Fun_of_mem1 v1])
  rw [piV_succ_eq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hA, hW, ← hA]
  simp

lemma piV_succ_hi (k : ℕ) {z : ℝ} (h : combPt (k + 1) ≤ z) (h1 : z < 1) :
    piV (k + 1) (z : UnitAddCircle) =
      ((1 - (1 - p1Fun (1 - 2 ^ k * (1 - z))) / 2 ^ k : ℝ) : UnitAddCircle) := by
  rw [combPt_eq] at h
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hv := aIter_hi k z h h1
  set v := 1 - 2 ^ k * (1 - z)
  have hv0 : 1 / 2 ≤ v := by
    have : 2 ^ k * (1 - z) ≤ 1 / 2 := by
      have e : (1 : ℝ) / 2 ^ (k + 1) = 1 / 2 ^ k / 2 := by rw [pow_succ]; field_simp
      rw [e] at h
      have : 1 - z ≤ 1 / 2 ^ k / 2 := by linarith
      calc 2 ^ k * (1 - z) ≤ 2 ^ k * (1 / 2 ^ k / 2) := by
            exact mul_le_mul_of_nonneg_left this hp.le
        _ = 1 / 2 := by field_simp
    simp only [v]; linarith
  have hv1 : v < 1 := by
    have : 0 < 2 ^ k * (1 - z) := mul_pos hp (by linarith)
    simp only [v]; linarith
  have hz0 : 0 ≤ z := by
    have : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have hA : (a ^ k) (z : UnitAddCircle) = (v : UnitAddCircle) :=
    coe_of_ico ⟨by linarith, hv1⟩ (by rw [ico_Apow, coe_mem_ico ⟨hz0, h1⟩, hv])
  have hpv : 1 / 2 ≤ p1Fun v ∧ p1Fun v < 1 := by
    rcases lt_or_ge v (3 / 4) with h3 | h3
    · rw [p1Fun_of_mem2 hv0 h3]; constructor <;> linarith
    rcases lt_or_ge v (7 / 8) with h7 | h7
    · rw [p1Fun_of_mem3 h3 h7]; constructor <;> linarith
    · rw [p1Fun_of_mem4 h7]; exact ⟨hv0, hv1⟩
  have hW : (b⁻¹ * c⁻¹ * a * p * a⁻¹ * c * b) (v : UnitAddCircle) = ((p1Fun v : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨by linarith [hpv.1], hpv.2⟩ (by rw [ico_piV1_word, coe_mem_ico ⟨by linarith, hv1⟩])
  rw [piV_succ_eq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hA, hW,
    Apow_inv_hi k hpv.1 hpv.2]

/-- `πᵢ` is the identity below the `i`th comb interval. -/
lemma piV_below (i : ℕ) {z : ℝ} (h0 : 0 ≤ z) (h : z < combPt i) :
    piV i (z : UnitAddCircle) = (z : UnitAddCircle) := by
  rcases i with _ | k
  · rw [combPt_eq] at h; norm_num at h; linarith
  · exact piV_succ_lo k h0 (lt_of_lt_of_le h (combPt_mono (by omega)))

/-- `πᵢ` carries the `i`th comb interval onto the `(i+1)`st. -/
lemma piV_piece0 (i : ℕ) {z : ℝ} (h0 : combPt i ≤ z) (h1 : z < combPt (i + 1)) :
    piV i (z : UnitAddCircle) = ((combPt (i + 1) + (z - combPt i) / 2 : ℝ) : UnitAddCircle) := by
  rcases i with _ | k
  · rw [piV_zero_eq, mapPi0_coe_of_mem ⟨by simpa [combPt_eq] using h0, by
      have := combPt_lt_one 1; linarith⟩]
    rw [combPt_eq] at h1; norm_num at h1
    rw [piFun_of_mem1 h1]; congr 1; simp [combPt_eq]; ring
  · have hk := piV_succ_lo k (combPt_nonneg _ |>.trans h0)
    rw [piV_succ_hi k h0 (lt_of_lt_of_le h1 (combPt_lt_one _).le)]
    simp only [combPt_eq] at h1 h0 ⊢
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hv0 : 1 / 2 ≤ 1 - 2 ^ k * (1 - z) := by
      have e : (1 : ℝ) / 2 ^ (k + 1) = 1 / 2 ^ k / 2 := by rw [pow_succ]; field_simp
      rw [e] at h0
      have : 2 ^ k * (1 - z) ≤ 2 ^ k * (1 / 2 ^ k / 2) := mul_le_mul_of_nonneg_left (by linarith) hp.le
      have e2 : (2 : ℝ) ^ k * (1 / 2 ^ k / 2) = 1 / 2 := by field_simp
      linarith
    have hv3 : 1 - 2 ^ k * (1 - z) < 3 / 4 := by
      have e : (1 : ℝ) / 2 ^ (k + 1 + 1) = 1 / 2 ^ k / 4 := by rw [pow_succ, pow_succ]; field_simp; try ring
      rw [e] at h1
      have : 2 ^ k * (1 / 2 ^ k / 4) < 2 ^ k * (1 - z) := mul_lt_mul_of_pos_left (by linarith) hp
      have e2 : (2 : ℝ) ^ k * (1 / 2 ^ k / 4) = 1 / 4 := by field_simp; try ring
      linarith
    rw [p1Fun_of_mem2 hv0 hv3]
    congr 1
    rw [pow_succ, pow_succ]
    field_simp
    ring

/-- `πᵢ` carries the `(i+1)`st comb interval onto the `i`th. -/
lemma piV_piece1 (i : ℕ) {z : ℝ} (h0 : combPt (i + 1) ≤ z) (h1 : z < combPt (i + 2)) :
    piV i (z : UnitAddCircle) = ((combPt i + 2 * (z - combPt (i + 1)) : ℝ) : UnitAddCircle) := by
  rcases i with _ | k
  · rw [piV_zero_eq, mapPi0_coe_of_mem ⟨le_trans (combPt_nonneg _) h0, by
      have := combPt_lt_one 2; linarith⟩]
    rw [combPt_eq] at h0 h1; norm_num at h0 h1
    rw [piFun_of_mem2 h0 h1]; congr 1; simp [combPt_eq]; ring
  · rw [piV_succ_hi k (le_trans (combPt_mono (by omega)) h0) (lt_of_lt_of_le h1 (combPt_lt_one _).le)]
    simp only [combPt_eq] at h1 h0 ⊢
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hv3 : 3 / 4 ≤ 1 - 2 ^ k * (1 - z) := by
      have e : (1 : ℝ) / 2 ^ (k + 1 + 1) = 1 / 2 ^ k / 4 := by rw [pow_succ, pow_succ]; field_simp; try ring
      rw [e] at h0
      have : 2 ^ k * (1 - z) ≤ 2 ^ k * (1 / 2 ^ k / 4) := mul_le_mul_of_nonneg_left (by linarith) hp.le
      have e2 : (2 : ℝ) ^ k * (1 / 2 ^ k / 4) = 1 / 4 := by field_simp; try ring
      linarith
    have hv7 : 1 - 2 ^ k * (1 - z) < 7 / 8 := by
      have e : (1 : ℝ) / 2 ^ (k + 1 + 2) = 1 / 2 ^ k / 8 := by
        rw [show k + 1 + 2 = k + 3 by omega, pow_add]; field_simp; try ring
      rw [e] at h1
      have : 2 ^ k * (1 / 2 ^ k / 8) < 2 ^ k * (1 - z) := mul_lt_mul_of_pos_left (by linarith) hp
      have e2 : (2 : ℝ) ^ k * (1 / 2 ^ k / 8) = 1 / 8 := by field_simp; try ring
      linarith
    rw [p1Fun_of_mem3 hv3 hv7]
    congr 1
    rw [pow_succ]
    field_simp
    ring

/-- `πᵢ` is the identity above the `(i+1)`st comb interval. -/
lemma piV_above (i : ℕ) {z : ℝ} (h0 : combPt (i + 2) ≤ z) (h1 : z < 1) :
    piV i (z : UnitAddCircle) = (z : UnitAddCircle) := by
  rcases i with _ | k
  · rw [piV_zero_eq, mapPi0_coe_of_mem ⟨le_trans (combPt_nonneg _) h0, h1⟩]
    rw [combPt_eq] at h0; norm_num at h0
    rw [piFun_of_mem3 h0]
  · rw [piV_succ_hi k (le_trans (combPt_mono (by omega)) h0) h1]
    rw [combPt_eq] at h0
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hv7 : 7 / 8 ≤ 1 - 2 ^ k * (1 - z) := by
      have e : (1 : ℝ) / 2 ^ (k + 1 + 2) = 1 / 2 ^ k / 8 := by
        rw [show k + 1 + 2 = k + 3 by omega, pow_add]; field_simp; try ring
      rw [e] at h0
      have : 2 ^ k * (1 - z) ≤ 2 ^ k * (1 / 2 ^ k / 8) := mul_le_mul_of_nonneg_left (by linarith) hp.le
      have e2 : (2 : ℝ) ^ k * (1 / 2 ^ k / 8) = 1 / 8 := by field_simp; try ring
      linarith
    rw [p1Fun_of_mem4 hv7]
    congr 1
    field_simp
    ring

end CannonFloydParry.S6

/-! The action of `Cₙ` on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C

lemma CV_succ_eq (m : ℕ) : CV (m + 1) = (a ^ m)⁻¹ * c * b ^ m := by
  simp only [CV, wordC, map_mul, map_inv, map_pow, lift_of]

lemma Apow_inv_of {m : ℕ} {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (hv : aFun^[m] u ∈ Set.Ico (0 : ℝ) 1) :
    (a ^ m)⁻¹ ((aFun^[m] u : ℝ) : UnitAddCircle) = (u : UnitAddCircle) := by
  apply inv_apply_eq_of
  exact coe_of_ico hv (by rw [ico_Apow, coe_mem_ico hu])

/-- `Cₙ` (`n = m + 1`) carries `[0, 1/2)` onto the last comb interval. -/
lemma CV_piece0 (m : ℕ) {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1 / 2) :
    CV (m + 1) (z : UnitAddCircle) = ((combPt (m + 2) + z / 2 ^ (m + 1) : ℝ) : UnitAddCircle) := by
  have hB : (b ^ m) (z : UnitAddCircle) = (z : UnitAddCircle) :=
    coe_of_ico ⟨h0, by linarith⟩ (by rw [ico_Bpow, coe_mem_ico ⟨h0, by linarith⟩, bIter_lo m z h1.le])
  have hC : c (z : UnitAddCircle) = ((z / 2 + 3 / 4 : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨by linarith, by linarith⟩ (by rw [ico_Cv, coe_mem_ico ⟨h0, by linarith⟩,
      cFun_of_mem1 h1])
  rw [CV_succ_eq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hB, hC,
    Apow_inv_hi m (by linarith) (by linarith), combPt_eq]
  congr 1
  rw [pow_succ, pow_succ]
  field_simp
  ring

/-- `Cₙ` carries `[1/2, 1 - 2^{-(n+1)})` by `z ↦ 2z - 1`. -/
lemma CV_mid (m : ℕ) {z : ℝ} (h0 : 1 / 2 ≤ z) (h1 : z < combPt (m + 2)) :
    CV (m + 1) (z : UnitAddCircle) = ((2 * z - 1 : ℝ) : UnitAddCircle) := by
  have hz1 : z < 1 := lt_trans h1 (combPt_lt_one _)
  rw [combPt_eq] at h1
  set u := 2 * z - 1
  have hu : u < 1 - 1 / 2 ^ (m + 1) := by
    have e : (1 : ℝ) / 2 ^ (m + 2) = 1 / 2 ^ (m + 1) / 2 := by rw [pow_succ]; field_simp
    rw [e] at h1; simp only [u]; linarith
  obtain ⟨v0, v1⟩ := aIter_lo m u (by simp only [u]; linarith) hu
  have hB : (b ^ m) (z : UnitAddCircle) = (((aFun^[m] u + 1) / 2 : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨by linarith, by linarith⟩ (by rw [ico_Bpow, coe_mem_ico ⟨by linarith, hz1⟩,
      bIter_half m z h0 hz1])
  have hCi : ico (c ((((aFun^[m] u + 1) / 2 : ℝ)) : UnitAddCircle)) = aFun^[m] u := by
    rw [ico_Cv, coe_mem_ico ⟨by linarith, by linarith⟩, cFun_of_mem2 (by linarith) (by linarith)]
    ring
  have hC : c ((((aFun^[m] u + 1) / 2 : ℝ)) : UnitAddCircle) = ((aFun^[m] u : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨v0, by linarith⟩ hCi
  rw [CV_succ_eq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hB, hC,
    Apow_inv_of ⟨by simp only [u]; linarith, by linarith⟩ ⟨v0, by linarith⟩]

/-- `Cₙ` carries the last comb interval onto the one before it. -/
lemma CV_last (m : ℕ) {z : ℝ} (h0 : combPt (m + 2) ≤ z) (h1 : z < 1) :
    CV (m + 1) (z : UnitAddCircle) = ((z - 1 / 2 ^ (m + 2) : ℝ) : UnitAddCircle) := by
  rw [combPt_eq] at h0
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have e2 : (1 : ℝ) / 2 ^ (m + 2) = 1 / 2 ^ (m + 1) / 2 := by rw [pow_succ]; field_simp
  have hz0 : 1 / 2 ≤ z := by
    have : (1 : ℝ) / 2 ^ (m + 2) ≤ 1 / 4 := by
      rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by norm_num)]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  set u := 2 * z - 1
  have hu0 : 1 - 1 / 2 ^ (m + 1) ≤ u := by rw [e2] at h0; simp only [u]; linarith
  have hu1 : u < 1 := by simp only [u]; linarith
  have hA := aIter_hi m u hu0 hu1
  have hBz : bFun^[m] z = 1 - 2 ^ m * (1 - z) := by
    rw [bIter_half m z hz0 h1, hA]; simp only [u]; ring
  have hw3 : 3 / 4 ≤ 1 - 2 ^ m * (1 - z) := by
    have e : (1 : ℝ) / 2 ^ (m + 2) = 1 / 2 ^ m / 4 := by rw [pow_succ, pow_succ]; field_simp; ring
    rw [e] at h0
    have : 2 ^ m * (1 - z) ≤ 2 ^ m * (1 / 2 ^ m / 4) := mul_le_mul_of_nonneg_left (by linarith) hp.le
    have e' : (2 : ℝ) ^ m * (1 / 2 ^ m / 4) = 1 / 4 := by field_simp; try ring
    linarith
  have hw1 : 1 - 2 ^ m * (1 - z) < 1 := by
    have : 0 < 2 ^ m * (1 - z) := mul_pos hp (by linarith)
    linarith
  have hB : (b ^ m) (z : UnitAddCircle) = ((1 - 2 ^ m * (1 - z) : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨by linarith, hw1⟩ (by rw [ico_Bpow, coe_mem_ico ⟨by linarith, h1⟩, hBz])
  have hCi : ico (c ((1 - 2 ^ m * (1 - z) : ℝ) : UnitAddCircle)) = 3 / 4 - 2 ^ m * (1 - z) := by
    rw [ico_Cv, coe_mem_ico ⟨by linarith, hw1⟩, cFun_of_mem3 hw3]
    ring
  have hC : c ((1 - 2 ^ m * (1 - z) : ℝ) : UnitAddCircle) =
      ((3 / 4 - 2 ^ m * (1 - z) : ℝ) : UnitAddCircle) :=
    coe_of_ico ⟨by linarith, by linarith⟩ hCi
  rw [CV_succ_eq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hB, hC,
    Apow_inv_hi m (by linarith) (by linarith)]
  congr 1
  rw [pow_succ, pow_succ]
  field_simp
  ring

end CannonFloydParry.S6

/-! Disjoint standard dyadic intervals covering `[0,1)`, sorted, form a standard dyadic partition. -/

namespace CannonFloydParry.S6

end CannonFloydParry.S6

/-! Tree diagrams for maps satisfying `IsThompsonV` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma coe_inj_Ico {z z' : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) (hz' : z' ∈ Set.Ico (0 : ℝ) 1)
    (h : (z : UnitAddCircle) = z') : z = z' := by
  have := congrArg ico h
  rw [ico_coe, ico_coe, Int.fract_eq_self.2 hz, Int.fract_eq_self.2 hz'] at this
  exact this

end CannonFloydParry.S6

/-! Permutations of the pieces `[q j, q (j+1))` of a partition of `[0, q K)` realised by affine
maps, the tail `[q K, 1)` fixed. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

variable {K : ℕ} (q : Fin (K + 1) → ℝ)

/-- `g` carries the `j`th piece affinely onto the `σ j`th, and fixes the tail. -/
def CR (g : Equiv.Perm UnitAddCircle) (σ : Equiv.Perm (Fin K)) : Prop :=
  (∀ j : Fin K, ∀ z ∈ Set.Ico (q j.castSucc) (q j.succ),
    g (z : UnitAddCircle) = ((q (σ j).castSucc + (q (σ j).succ - q (σ j).castSucc) /
      (q j.succ - q j.castSucc) * (z - q j.castSucc) : ℝ) : UnitAddCircle)) ∧
  ∀ z ∈ Set.Ico (q (Fin.last K)) 1, g (z : UnitAddCircle) = (z : UnitAddCircle)

variable {q}

lemma cr_piece_mem (hq : StrictMono q) {j i : Fin K} {z : ℝ} (hz : z ∈ Set.Ico (q j.castSucc) (q j.succ)) :
    q i.castSucc + (q i.succ - q i.castSucc) / (q j.succ - q j.castSucc) * (z - q j.castSucc) ∈
      Set.Ico (q i.castSucc) (q i.succ) := by
  have hj : 0 < q j.succ - q j.castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
  have hi : 0 < q i.succ - q i.castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
  have h0 : 0 ≤ z - q j.castSucc := by linarith [hz.1]
  have h1 : z - q j.castSucc < q j.succ - q j.castSucc := by linarith [hz.2]
  constructor
  · have := mul_nonneg (div_pos hi hj).le h0; linarith
  · have : (q i.succ - q i.castSucc) / (q j.succ - q j.castSucc) * (z - q j.castSucc) <
        q i.succ - q i.castSucc := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hj]; nlinarith
    linarith

lemma cr_one : CR q 1 1 := by
  refine ⟨fun j z hz => ?_, fun z _ => rfl⟩
  have hj : q j.succ - q j.castSucc ≠ 0 := by
    intro h; have := hz.1; have := hz.2; linarith
  simp only [Equiv.Perm.coe_one, id]
  congr 1; field_simp; ring

lemma cr_mul (hq : StrictMono q) {g g' : Equiv.Perm UnitAddCircle} {σ σ' : Equiv.Perm (Fin K)}
    (h : CR q g σ) (h' : CR q g' σ') : CR q (g * g') (σ * σ') := by
  refine ⟨fun j z hz => ?_, fun z hz => by rw [Equiv.Perm.mul_apply, h'.2 z hz, h.2 z hz]⟩
  rw [Equiv.Perm.mul_apply, h'.1 j z hz, h.1 (σ' j) _ (cr_piece_mem hq hz)]
  have hj : 0 < q j.succ - q j.castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
  have hi : 0 < q (σ' j).succ - q (σ' j).castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
  simp only [Equiv.Perm.mul_apply]
  congr 1
  field_simp
  ring

lemma cr_inv (hq : StrictMono q) {g : Equiv.Perm UnitAddCircle} {σ : Equiv.Perm (Fin K)}
    (h : CR q g σ) : CR q g⁻¹ σ⁻¹ := by
  refine ⟨fun j z hz => ?_, fun z hz => ?_⟩
  · set i := σ⁻¹ j
    have hij : σ i = j := by simp [i]
    have hz' := cr_piece_mem hq (i := i) hz
    have := h.1 i _ hz'
    rw [hij] at this
    rw [Equiv.Perm.inv_eq_iff_eq, this]
    have hj : 0 < q j.succ - q j.castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
    have hi : 0 < q i.succ - q i.castSucc := sub_pos.2 (hq (Fin.castSucc_lt_succ))
    congr 1
    field_simp
    ring
  · rw [Equiv.Perm.inv_eq_iff_eq, h.2 z hz]

/-- Every point of `[0, q K)` lies in a piece. -/
lemma cr_locate (hq : StrictMono q) (hq0 : q 0 = 0) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < q (Fin.last K)) :
    ∃ j : Fin K, x ∈ Set.Ico (q j.castSucc) (q j.succ) := by
  classical
  have hex : ∃ (r : ℕ) (h : r < K), x < q ⟨r + 1, Nat.succ_lt_succ h⟩ := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; exfalso
      have : q (Fin.last 0) = 0 := hq0
      linarith
    · exact ⟨K - 1, by omega, by
        rw [show (⟨K - 1 + 1, by omega⟩ : Fin (K + 1)) = Fin.last K from Fin.ext (by simp; omega)]
        exact h1⟩
  obtain ⟨hrK, hr⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hrK⟩, ?_, hr⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · have : (⟨Nat.find hex, hrK⟩ : Fin K).castSucc = 0 := Fin.ext (by simp [h])
    rw [this, hq0]; exact h0
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    simp only [not_exists, not_lt] at hmin
    have := hmin (by omega)
    have e : (⟨Nat.find hex - 1 + 1, by omega⟩ : Fin (K + 1)) = (⟨Nat.find hex, hrK⟩ : Fin K).castSucc :=
      Fin.ext (by simp; omega)
    rwa [e] at this

lemma cr_unique (hq : StrictMono q) (hq0 : q 0 = 0) {g g' : Equiv.Perm UnitAddCircle}
    {σ : Equiv.Perm (Fin K)} (h : CR q g σ) (h' : CR q g' σ) : g = g' := by
  ext p
  have hp : p = ((ico p : ℝ) : UnitAddCircle) :=
    circ_ext (by rw [ico_coe, Int.fract_eq_self.2 ⟨ico_nonneg p, ico_lt_one p⟩])
  rw [hp]
  rcases lt_or_ge (ico p) (q (Fin.last K)) with hlt | hge
  · obtain ⟨j, hj⟩ := cr_locate hq hq0 (ico_nonneg p) hlt
    rw [h.1 j _ hj, h'.1 j _ hj]
  · rw [h.2 _ ⟨hge, ico_lt_one p⟩, h'.2 _ ⟨hge, ico_lt_one p⟩]

lemma cr_unique_perm (hq : StrictMono q) (hq0 : q 0 = 0) (hqK : q (Fin.last K) ≤ 1)
    {g : Equiv.Perm UnitAddCircle} {σ τ : Equiv.Perm (Fin K)}
    (h : CR q g σ) (h' : CR q g τ) : σ = τ := by
  ext j
  have hmem : q j.castSucc ∈ Set.Ico (q j.castSucc) (q j.succ) :=
    ⟨le_rfl, hq (Fin.castSucc_lt_succ)⟩
  have e := (h.1 j _ hmem).symm.trans (h'.1 j _ hmem)
  simp only [sub_self, mul_zero, add_zero] at e
  have hlt : ∀ i : Fin K, q i.castSucc ∈ Set.Ico (0 : ℝ) 1 := fun i =>
    ⟨by rw [← hq0]; exact hq.monotone (Fin.zero_le _),
     lt_of_lt_of_le (hq (Fin.castSucc_lt_last i)) hqK⟩
  have := coe_inj_Ico (hlt _) (hlt _) e
  have := hq.injective this
  exact congrArg Fin.val (Fin.castSucc_injective _ this)

/-- If every element of `H` realises a permutation and every permutation is realised in `H`,
then `H ≅ Perm (Fin K)` through the realised permutation. -/
theorem exists_mulEquiv_of_cr (hq : StrictMono q) (hq0 : q 0 = 0) (hqK : q (Fin.last K) ≤ 1)
    (H : Subgroup (Equiv.Perm UnitAddCircle)) (hH : ∀ g ∈ H, ∃ σ, CR q g σ)
    (hsurj : ∀ σ, ∃ g ∈ H, CR q g σ) :
    ∃ e : H ≃* Equiv.Perm (Fin K), ∀ g : H, CR q g (e g) := by
  choose φ hφ using fun g : H => hH g g.2
  let φh : H →* Equiv.Perm (Fin K) :=
    { toFun := φ
      map_one' := cr_unique_perm hq hq0 hqK (hφ 1) cr_one
      map_mul' := fun g g' => cr_unique_perm hq hq0 hqK (hφ (g * g')) (cr_mul hq (hφ g) (hφ g')) }
  have hinj : Function.Injective φh := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : CR q (g : Equiv.Perm UnitAddCircle) 1 := by
      have := hφ g; change φ g = 1 at hg; rwa [hg] at this
    exact Subtype.ext (cr_unique hq hq0 h1 cr_one)
  have hsurj' : Function.Surjective φh := by
    intro σ
    obtain ⟨g, hg, hgσ⟩ := hsurj σ
    exact ⟨⟨g, hg⟩, cr_unique_perm hq hq0 hqK (hφ ⟨g, hg⟩) hgσ⟩
  exact ⟨MulEquiv.ofBijective φh ⟨hinj, hsurj'⟩, fun g => hφ g⟩

/-- The permutations realised in `H` form a subgroup; if it contains a generating set, every
permutation is realised. -/
lemma cr_all (hq : StrictMono q) (H : Subgroup (Equiv.Perm UnitAddCircle)) (S : Set (Equiv.Perm (Fin K)))
    (hS : Subgroup.closure S = ⊤) (hSH : ∀ σ ∈ S, ∃ g ∈ H, CR q g σ) :
    ∀ σ, ∃ g ∈ H, CR q g σ := by
  let R : Subgroup (Equiv.Perm (Fin K)) :=
    { carrier := {σ | ∃ g ∈ H, CR q g σ}
      one_mem' := ⟨1, one_mem _, cr_one⟩
      mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', cr_mul hq h h'⟩
      inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, cr_inv hq h⟩ }
  have : R = ⊤ := by
    rw [eq_top_iff, ← hS, Subgroup.closure_le]; exact hSH
  intro σ
  have hσ : σ ∈ R := this ▸ Subgroup.mem_top σ
  exact hσ

end CannonFloydParry.S6

/-! The symmetric groups acting on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma combPt_strictMono : StrictMono combPt := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [combPt_succ]
  have : (0 : ℝ) < 1 / 2 ^ (j + 1) := by positivity
  linarith

lemma combPt_len (j : ℕ) : combPt (j + 1) - combPt j = 1 / 2 ^ (j + 1) := by
  rw [combPt_succ]; ring

lemma cr_id_formula {x y z : ℝ} (h : x < y) : x + (y - x) / (y - x) * (z - x) = z := by
  rw [div_self (by linarith)]; ring

/-- `πᵢ` swaps pieces `i` and `i+1` of any partition agreeing with the comb up to index `i+2`. -/
lemma piV_cr {K : ℕ} {q : Fin (K + 1) → ℝ} (hq : StrictMono q) {i : ℕ} (hi : i + 2 ≤ K)
    (hqc : ∀ (k : ℕ) (hk : k < K + 1), k ≤ i + 2 → q ⟨k, hk⟩ = combPt k)
    (hqge : ∀ j : Fin (K + 1), i + 2 ≤ (j : ℕ) → combPt (i + 2) ≤ q j)
    (hq1 : q (Fin.last K) ≤ 1) :
    CR q (piV i) (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) := by
  have hle1 : ∀ j : Fin (K + 1), q j ≤ 1 := fun j => le_trans (hq.monotone (Fin.le_last j)) hq1
  have hq0 : q 0 = 0 := by rw [show (0 : Fin (K + 1)) = ⟨0, by omega⟩ from rfl, hqc 0 _ (by omega)]
                           simp [combPt]
  refine ⟨fun j z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨jv, hjv⟩ := j
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hz ⊢
    have hlt : q ⟨jv, by omega⟩ < q ⟨jv + 1, by omega⟩ := hq (Fin.mk_lt_mk.2 (by omega))
    rcases (show jv < i ∨ jv = i ∨ jv = i + 1 ∨ i + 2 ≤ jv by omega) with h | rfl | rfl | h
    · -- below: fixed
      have hne1 : (⟨jv, hjv⟩ : Fin K) ≠ ⟨i, by omega⟩ := fun e => by simp at e; omega
      have hne2 : (⟨jv, hjv⟩ : Fin K) ≠ ⟨i + 1, by omega⟩ := fun e => by simp at e; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [cr_id_formula hlt]
      have hz0 : 0 ≤ z := le_trans (by rw [← hq0]; exact hq.monotone (Fin.zero_le _)) hz.1
      apply piV_below i hz0
      calc z < q ⟨jv + 1, by omega⟩ := hz.2
        _ = combPt (jv + 1) := hqc _ _ (by omega)
        _ ≤ combPt i := combPt_mono (by omega)
    · -- piece `i` goes to piece `i+1`
      rw [Equiv.swap_apply_left]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [hqc jv _ (by omega), hqc (jv + 1) _ (by omega)] at hz
      rw [hqc jv _ (by omega), hqc (jv + 1) _ (by omega), hqc (jv + 1 + 1) _ (by omega),
        piV_piece0 jv hz.1 hz.2, combPt_len, combPt_len]
      congr 1
      rw [pow_succ (2 : ℝ) (jv + 1)]
      field_simp
      try ring
    · -- piece `i+1` goes to piece `i`
      rw [Equiv.swap_apply_right]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [hqc (i + 1) _ (by omega), hqc (i + 1 + 1) _ (by omega)] at hz
      rw [hqc i _ (by omega), hqc (i + 1) _ (by omega), hqc (i + 1 + 1) _ (by omega),
        piV_piece1 i hz.1 hz.2, combPt_len, combPt_len]
      congr 1
      rw [pow_succ (2 : ℝ) (i + 1)]
      field_simp
      try ring
    · -- above: fixed
      have hne1 : (⟨jv, hjv⟩ : Fin K) ≠ ⟨i, by omega⟩ := fun e => by simp at e; omega
      have hne2 : (⟨jv, hjv⟩ : Fin K) ≠ ⟨i + 1, by omega⟩ := fun e => by simp at e; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [cr_id_formula hlt]
      have hz2 : combPt (i + 2) ≤ z := le_trans (hqge ⟨jv, by omega⟩ h) hz.1
      exact piV_above i hz2 (lt_of_lt_of_le hz.2 (hle1 _))
  · have hz2 : combPt (i + 2) ≤ z := le_trans (hqge _ (by simp; omega)) hz.1
    exact piV_above i hz2 hz.2

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- The comb partition with `n + 2` pieces, the last `[1 - 2^{-(n+1)}, 1)`. -/
noncomputable def q2 (n : ℕ) (j : Fin (n + 3)) : ℝ := if (j : ℕ) = n + 2 then 1 else combPt j

lemma one_sub_combPt (j : ℕ) : 1 - combPt j = 1 / 2 ^ j := by rw [combPt_eq]; ring

lemma combPt_zero' : combPt 0 = 0 := by rw [combPt_eq]; norm_num

lemma combPt_one : combPt 1 = 1 / 2 := by rw [combPt_eq]; norm_num

lemma q2_comb {n k : ℕ} (hk : k < n + 3) (h : k ≤ n + 1) : q2 n ⟨k, hk⟩ = combPt k := by
  show (if k = n + 2 then (1 : ℝ) else combPt k) = combPt k
  rw [if_neg (by omega)]

lemma q2_last (n : ℕ) : q2 n (Fin.last (n + 2)) = 1 := by simp [q2]

lemma q2_mono (n : ℕ) : StrictMono (q2 n) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain ⟨iv, hiv⟩ := i
  change q2 n ⟨iv, by omega⟩ < q2 n ⟨iv + 1, by omega⟩
  rw [q2_comb _ (by omega)]
  rcases (show iv + 1 ≤ n + 1 ∨ iv + 1 = n + 2 by omega) with h | h
  · rw [q2_comb _ h]; exact combPt_strictMono (by omega)
  · rw [show (⟨iv + 1, by omega⟩ : Fin (n + 3)) = Fin.last (n + 2) from Fin.ext (by simp; omega),
      q2_last]
    exact combPt_lt_one _

/-- `Cₙ` (`n = m+1`) cycles the `n + 2` comb pieces: `j ↦ j - 1`, `0 ↦ n + 1`. -/
lemma CV_cr (m : ℕ) : CR (q2 (m + 1)) (CV (m + 1)) (finRotate (m + 3)).symm := by
  have hρ : ∀ (j k : Fin (m + 3)), finRotate (m + 3) k = j → (finRotate (m + 3)).symm j = k :=
    fun j k h => by rw [← h]; simp
  refine ⟨fun j z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨jv, hjv⟩ := j
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hz ⊢
    rcases (show jv = 0 ∨ (1 ≤ jv ∧ jv ≤ m + 1) ∨ jv = m + 2 by omega) with rfl | ⟨h1, h2⟩ | rfl
    · -- piece 0 to the last piece
      have e : (finRotate (m + 3)).symm ⟨0, hjv⟩ = ⟨m + 2, by omega⟩ :=
        hρ _ _ (by rw [finRotate_last'])
      rw [e]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [q2_comb _ (by omega), q2_comb _ (by omega)] at hz
      rw [q2_comb (k := 0) _ (by omega), q2_comb (k := 0 + 1) _ (by omega), q2_comb (k := m + 2) _ le_rfl,
        show (⟨m + 2 + 1, by omega⟩ : Fin (m + 1 + 3)) = Fin.last (m + 1 + 2) from Fin.ext (by simp),
        q2_last]
      have hz0 : 0 ≤ z := by have := hz.1; rwa [combPt_zero'] at this
      have hz1 : z < 1 / 2 := by have := hz.2; rwa [zero_add, combPt_one] at this
      rw [CV_piece0 m hz0 hz1, one_sub_combPt, zero_add, combPt_one, combPt_zero']
      congr 1
      rw [pow_succ (2 : ℝ) (m + 1)]
      field_simp
      ring
    · -- piece `jv` to piece `jv - 1`
      obtain ⟨k, rfl⟩ : ∃ k, jv = k + 1 := ⟨jv - 1, by omega⟩
      have e : (finRotate (m + 3)).symm ⟨k + 1, hjv⟩ = ⟨k, by omega⟩ :=
        hρ _ _ (Fin.ext (by
          have := coe_finRotate_of_ne_last (n := m + 2) (i := ⟨k, by omega⟩) (by simp [Fin.ext_iff]; omega)
          simpa using this))
      rw [e]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [q2_comb _ (by omega), q2_comb _ (by omega)] at hz
      rw [q2_comb (k := k) _ (by omega), q2_comb (k := k + 1) _ (by omega),
        q2_comb (k := k + 1 + 1) _ (by omega)]
      have hz0 : 1 / 2 ≤ z := by
        have := combPt_mono (show 1 ≤ k + 1 by omega); rw [combPt_one] at this
        linarith [hz.1]
      have hz1 : z < combPt (m + 2) := lt_of_lt_of_le hz.2 (combPt_mono (by omega))
      rw [CV_mid m hz0 hz1, combPt_len, combPt_len]
      congr 1
      rw [combPt_eq, combPt_eq, pow_succ (2 : ℝ) (k + 1)]
      field_simp
      ring
    · -- the last piece to the one before
      have e : (finRotate (m + 3)).symm ⟨m + 2, hjv⟩ = ⟨m + 1, by omega⟩ :=
        hρ _ _ (Fin.ext (by
          have := coe_finRotate_of_ne_last (n := m + 2) (i := ⟨m + 1, by omega⟩) (by simp [Fin.ext_iff])
          simpa using this))
      rw [e]
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [q2_comb _ (by omega),
        show (⟨m + 2 + 1, by omega⟩ : Fin (m + 1 + 3)) = Fin.last (m + 1 + 2) from Fin.ext (by simp),
        q2_last] at hz
      rw [q2_comb (k := m + 1) _ (by omega), q2_comb (k := m + 1 + 1) _ (by omega),
        show (⟨m + 2 + 1, by omega⟩ : Fin (m + 1 + 3)) = Fin.last (m + 1 + 2) from Fin.ext (by simp),
        q2_last]
      rw [CV_last m hz.1 hz.2, combPt_len, one_sub_combPt]
      congr 1
      rw [combPt_eq, combPt_eq]
      field_simp
      ring
  · exfalso
    rw [q2_last] at hz
    exact absurd hz.2 (not_lt.2 hz.1)

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma cr_mem {K : ℕ} {q : Fin (K + 1) → ℝ} (hq : StrictMono q) {g : Equiv.Perm UnitAddCircle}
    {σ : Equiv.Perm (Fin K)} (h : CR q g σ) (j : Fin K) {z : ℝ}
    (hz : z ∈ Set.Ico (q j.castSucc) (q j.succ)) :
    ∃ w ∈ Set.Ico (q (σ j).castSucc) (q (σ j).succ), g (z : UnitAddCircle) = (w : UnitAddCircle) :=
  ⟨_, cr_piece_mem hq hz, h.1 j z hz⟩

lemma combInt_lt {m j : ℕ} (h : j < m) : combInt m j = Set.Ico (combPt j) (combPt (j + 1)) := by
  unfold combInt; rw [if_neg (by omega)]

theorem exists_mulEquiv_perm_combInt' (n : ℕ) (hn : 0 < n) :
    (∃ e : Subgroup.closure (piV '' Set.Iio n) ≃* Equiv.Perm (Fin (n + 1)),
      ∀ g (j : Fin (n + 1)), ∀ z ∈ combInt (n + 1) j,
        ∃ w ∈ combInt (n + 1) (e g j), (g : Equiv.Perm UnitAddCircle) (z : UnitAddCircle) = (w : UnitAddCircle)) ∧
    (∃ e : Subgroup.closure (insert (CV n) (piV '' Set.Iio n)) ≃* Equiv.Perm (Fin (n + 2)),
      ∀ g (j : Fin (n + 2)), ∀ z ∈ combInt (n + 1) j,
        ∃ w ∈ combInt (n + 1) (e g j), (g : Equiv.Perm UnitAddCircle) (z : UnitAddCircle) = (w : UnitAddCircle)) := by
  constructor
  · -- `n + 1` comb pieces, the tail fixed
    set q : Fin (n + 2) → ℝ := fun j => combPt j
    have hq : StrictMono q := fun a b h => combPt_strictMono h
    have hgen : ∀ (i : ℕ) (hi : i < n), CR q (piV i) (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) :=
      fun i hi => piV_cr hq (by omega) (fun k hk _ => rfl) (fun j h => combPt_mono h)
        (combPt_lt_one _).le
    set H := Subgroup.closure (piV '' Set.Iio n)
    have hH : ∀ g ∈ H, ∃ σ, CR q g σ := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact ⟨_, hgen i hi⟩
      | one => exact ⟨1, cr_one⟩
      | mul x y _ _ hx hy =>
        obtain ⟨σ, h⟩ := hx; obtain ⟨τ, h'⟩ := hy; exact ⟨σ * τ, cr_mul hq h h'⟩
      | inv x _ hx => obtain ⟨σ, h⟩ := hx; exact ⟨σ⁻¹, cr_inv hq h⟩
    have hsurj := cr_all hq H (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ)
      (Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n))
      (by rintro _ ⟨i, rfl⟩; exact ⟨piV i, Subgroup.subset_closure ⟨i, i.2, rfl⟩, hgen i i.2⟩)
    obtain ⟨e, he⟩ := exists_mulEquiv_of_cr hq (by simp [q, combPt]) (combPt_lt_one _).le H hH hsurj
    refine ⟨e, fun g j z hz => ?_⟩
    rw [combInt_lt (by omega)] at hz
    obtain ⟨w, hw, hgw⟩ := cr_mem hq (he g) j (z := z) (by simpa [q] using hz)
    exact ⟨w, by rw [combInt_lt (by omega)]; simpa [q] using hw, hgw⟩
  · -- `n + 2` comb pieces
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hq : StrictMono (q2 (m + 1)) := q2_mono _
    have hge : ∀ (i : ℕ) (j : Fin (m + 1 + 3)), i + 2 ≤ (j : ℕ) → i + 2 ≤ m + 2 →
        combPt (i + 2) ≤ q2 (m + 1) j := by
      intro i j h hi
      obtain ⟨jv, hjv⟩ := j
      rcases (show jv ≤ m + 2 ∨ jv = m + 3 by omega) with h' | h'
      · rw [q2_comb _ h']; exact combPt_mono h
      · rw [show (⟨jv, hjv⟩ : Fin (m + 1 + 3)) = Fin.last (m + 1 + 2) from Fin.ext (by simp; omega),
          q2_last]
        exact (combPt_lt_one _).le
    have hgen : ∀ (i : ℕ) (hi : i < m + 1),
        CR (q2 (m + 1)) (piV i) (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩) := fun i hi =>
      piV_cr hq (by omega) (fun k hk h => q2_comb hk (by omega)) (fun j h => hge i j h (by omega))
        (le_of_eq (q2_last _))
    set ρ : Equiv.Perm (Fin (m + 1 + 2)) := (finRotate (m + 1 + 2))⁻¹
    have hC : CR (q2 (m + 1)) (CV (m + 1)) ρ := CV_cr m
    set H := Subgroup.closure (insert (CV (m + 1)) (piV '' Set.Iio (m + 1)))
    have hH : ∀ g ∈ H, ∃ σ, CR (q2 (m + 1)) g σ := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | ⟨i, hi, rfl⟩
        · exact ⟨_, hC⟩
        · exact ⟨_, hgen i hi⟩
      | one => exact ⟨1, cr_one⟩
      | mul x y _ _ hx hy =>
        obtain ⟨σ, h⟩ := hx; obtain ⟨τ, h'⟩ := hy; exact ⟨σ * τ, cr_mul hq h h'⟩
      | inv x _ hx => obtain ⟨σ, h⟩ := hx; exact ⟨σ⁻¹, cr_inv hq h⟩
    have hcyc : ρ.IsCycle := (isCycle_finRotate (n := m + 1)).inv
    have hsupp : ρ.support = Finset.univ := by
      rw [Equiv.Perm.support_inv, support_finRotate]
    have hρ1 : ρ 1 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact (finRotate_apply_zero (n := m + 2)).symm
    have htop := Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp 1
    rw [hρ1] at htop
    have hsw : ∃ g ∈ H, CR (q2 (m + 1)) g (Equiv.swap 1 0) := by
      refine ⟨piV 0, Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨0, by simp, rfl⟩), ?_⟩
      rw [Equiv.swap_comm]
      exact hgen 0 (by omega)
    have hsurj := cr_all hq H _ htop (by
      rintro σ (rfl | rfl)
      · exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), hC⟩
      · exact hsw)
    have hq0 : q2 (m + 1) 0 = 0 := by
      have := q2_comb (n := m + 1) (k := 0) (by omega) (by omega)
      rw [show (0 : Fin (m + 1 + 3)) = ⟨0, by omega⟩ from rfl, this, combPt_zero']
    obtain ⟨e, he⟩ := exists_mulEquiv_of_cr hq hq0 (le_of_eq (q2_last _)) H hH hsurj
    have hint : ∀ j : Fin (m + 1 + 2),
        combInt (m + 1 + 1) j = Set.Ico (q2 (m + 1) j.castSucc) (q2 (m + 1) j.succ) := by
      intro j
      obtain ⟨jv, hjv⟩ := j
      simp only [Fin.castSucc_mk, Fin.succ_mk]
      rw [q2_comb _ (by omega)]
      rcases (show jv < m + 2 ∨ jv = m + 2 by omega) with h | rfl
      · rw [combInt_lt h, q2_comb _ (by omega)]
      · unfold combInt
        rw [if_pos rfl, show (⟨m + 2 + 1, by omega⟩ : Fin (m + 1 + 3)) = Fin.last (m + 1 + 2) from
          Fin.ext (by simp), q2_last]
    refine ⟨e, fun g j z hz => ?_⟩
    rw [hint] at hz
    obtain ⟨w, hw, hgw⟩ := cr_mem hq (he g) j hz
    exact ⟨w, by rw [hint]; exact hw, hgw⟩

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∃ e : Subgroup.closure (piV '' Set.Iio n) ≃* Equiv.Perm (Fin (n + 1)),
      ∀ g (j : Fin (n + 1)), ∀ z ∈ combInt (n + 1) j,
        ∃ w ∈ combInt (n + 1) (e g j), (g : Equiv.Perm UnitAddCircle) (z : UnitAddCircle) = (w : UnitAddCircle)) ∧
    (∃ e : Subgroup.closure (insert (CV n) (piV '' Set.Iio n)) ≃* Equiv.Perm (Fin (n + 2)),
      ∀ g (j : Fin (n + 2)), ∀ z ∈ combInt (n + 1) j,
        ∃ w ∈ combInt (n + 1) (e g j), (g : Equiv.Perm UnitAddCircle) (z : UnitAddCircle) = (w : UnitAddCircle)) := by
  exact S6.exists_mulEquiv_perm_combInt' n hn
