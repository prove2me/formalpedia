-- Prove2me | solution 1 for CannonFloydParry.exists_hom_T1_V1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:35:51.952981+00:00
-- url     : https://prove2.me/submissions/b2d20205-94f5-45f4-98bd-094fba7cdc64

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

end GoodLift

/-! ### The closure theorem -/


end CannonFloydParry.S5

/-! `T ≤ V` and `π₀ ∈ V` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5


end CannonFloydParry.S6

/-! Generation, part 1: the subgroup `G = ⟨A, B, C, π₀⟩` contains `F` and `T`; any two standard
dyadic partitions with the same number of pieces are matched, affinely on pieces, by an
element of `F`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- `G = ⟨A, B, C, π₀⟩`. -/
abbrev G : Subgroup (Equiv.Perm UnitAddCircle) := Subgroup.closure (Set.range symV)

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

/-! Generation, part 4: every permutation of the uniform pieces is realised in `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Disjoint standard dyadic intervals covering `[0,1)`, sorted, form a standard dyadic partition. -/

namespace CannonFloydParry.S6

end CannonFloydParry.S6

/-! Tree diagrams for maps satisfying `IsThompsonV` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Generation, part 5: every map satisfying `IsThompsonV` lies in `⟨A, B, C, π₀⟩`, so
`A`, `B`, `C`, `π₀` generate `V` (Lemma 6.1). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! The algebra of `V₁` (CFP p. 242): its relators, the map `T₁ → V₁`, and Lemmas 5.5, 5.6
carried into `V₁`. -/

namespace CannonFloydParry.S6

open PresentedGroup

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)
local notation "cV" => (PresentedGroup.of FormalV.C : V1)
local notation "pV" => (PresentedGroup.of FormalV.P : V1)

lemma mk_of (s : FormalV) : PresentedGroup.mk relsV1 (FreeGroup.of s) = PresentedGroup.of s := rfl
lemma XV1_succ (n : ℕ) : XV1 (n + 1) = (aV ^ n)⁻¹ * bV * aV ^ n := by
  simp [XV1, wordX, map_mul, map_inv, map_pow, mk_of]
lemma CV1_succ (n : ℕ) : CV1 (n + 1) = (aV ^ n)⁻¹ * cV * bV ^ n := by
  simp [CV1, wordC, map_mul, map_inv, map_pow, mk_of]

lemma rel (r : FreeGroup FormalV) (h : r ∈ relsV1) : PresentedGroup.mk relsV1 r = 1 :=
  PresentedGroup.one_of_mem h

/-- The fourteen relations of `V₁`, as equations. -/
lemma relV1 :
    (aV * bV⁻¹) * XV1 2 * (aV * bV⁻¹)⁻¹ * (XV1 2)⁻¹ = 1 ∧
    (aV * bV⁻¹) * XV1 3 * (aV * bV⁻¹)⁻¹ * (XV1 3)⁻¹ = 1 ∧
    CV1 1 = bV * CV1 2 ∧
    CV1 2 * XV1 2 = bV * CV1 3 ∧
    CV1 1 * aV = CV1 2 ^ 2 ∧
    CV1 1 ^ 3 = 1 ∧
    piV1 1 ^ 2 = 1 ∧
    piV1 1 * piV1 3 = piV1 3 * piV1 1 ∧
    (piV1 2 * piV1 1) ^ 3 = 1 ∧
    XV1 3 * piV1 1 = piV1 1 * XV1 3 ∧
    piV1 1 * XV1 2 = bV * piV1 2 * piV1 1 ∧
    piV1 2 * bV = bV * piV1 3 ∧
    piV1 1 * CV1 3 = CV1 3 * piV1 2 ∧
    (piV1 1 * CV1 2) ^ 3 = 1 := by
  have R := fun r (h : r ∈ relsV1) => rel r h
  have h1 := R _ (Or.inl rfl)
  have h2 := R _ (Or.inr (Or.inl rfl))
  have h3 := R _ (Or.inr (Or.inr (Or.inl rfl)))
  have h4 := R _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h7 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h8 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h9 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h10 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl))))))))))
  have h11 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl)))))))))))
  have h12 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h13 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  have h14 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))))
  simp only [map_mul, map_inv, map_pow, mk_of] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  change (aV * bV⁻¹) * XV1 2 * (aV * bV⁻¹)⁻¹ * (XV1 2)⁻¹ = 1 at h1
  change (aV * bV⁻¹) * XV1 3 * (aV * bV⁻¹)⁻¹ * (XV1 3)⁻¹ = 1 at h2
  change bV * CV1 2 * (CV1 1)⁻¹ = 1 at h3
  change bV * CV1 3 * (CV1 2 * XV1 2)⁻¹ = 1 at h4
  change CV1 2 ^ 2 * (CV1 1 * aV)⁻¹ = 1 at h5
  change CV1 1 ^ 3 = 1 at h6
  change piV1 1 ^ 2 = 1 at h7
  change piV1 3 * piV1 1 * (piV1 1 * piV1 3)⁻¹ = 1 at h8
  change (piV1 2 * piV1 1) ^ 3 = 1 at h9
  change piV1 1 * XV1 3 * (XV1 3 * piV1 1)⁻¹ = 1 at h10
  change bV * piV1 2 * piV1 1 * (piV1 1 * XV1 2)⁻¹ = 1 at h11
  change bV * piV1 3 * (piV1 2 * bV)⁻¹ = 1 at h12
  change CV1 3 * piV1 2 * (piV1 1 * CV1 3)⁻¹ = 1 at h13
  change (piV1 1 * CV1 2) ^ 3 = 1 at h14
  refine ⟨h1, h2, (mul_inv_eq_one.1 h3).symm, (mul_inv_eq_one.1 h4).symm,
    (mul_inv_eq_one.1 h5).symm, h6, h7, (mul_inv_eq_one.1 h8).symm, h9, (mul_inv_eq_one.1 h10).symm,
    (mul_inv_eq_one.1 h11).symm, (mul_inv_eq_one.1 h12).symm, (mul_inv_eq_one.1 h13).symm, h14⟩

/-- The map `T₁ → V₁`, `A, B, C ↦ A, B, C`. -/
noncomputable def fromT1 : T1 →* V1 :=
  PresentedGroup.toGroup (f := fun s => match s with
    | FormalABC.A => aV | FormalABC.B => bV | FormalABC.C => cV) (by
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := relV1
    simp only [XV1_succ, CV1_succ, pow_one, pow_zero, inv_one, one_mul, mul_one] at h1 h2 h3 h4 h5 h6
    intro r hr
    simp only [relsT1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    · exact h1
    · rw [inv_pow]; exact h2
    · calc _ = cV⁻¹ * (bV * (aV⁻¹ * cV * bV)) := by group
        _ = 1 := by rw [← h3]; group
    · calc _ = ((aV⁻¹ * cV * bV) * (aV⁻¹ * bV * aV))⁻¹ * (bV * ((aV ^ 2)⁻¹ * cV * bV ^ 2)) := by
            rw [inv_pow]; group
        _ = 1 := by rw [← h4]; group
    · calc _ = (cV * aV)⁻¹ * (aV⁻¹ * cV * bV) ^ 2 := rfl
        _ = 1 := by rw [h5]; group
    · exact h6)

@[simp] lemma fromT1_A : fromT1 (PresentedGroup.of FormalABC.A) = aV := PresentedGroup.toGroup.of _
@[simp] lemma fromT1_B : fromT1 (PresentedGroup.of FormalABC.B) = bV := PresentedGroup.toGroup.of _
@[simp] lemma fromT1_C : fromT1 (PresentedGroup.of FormalABC.C) = cV := PresentedGroup.toGroup.of _

end CannonFloydParry.S6

/-! Lemma 6.2 (CFP pp. 243–244), with `Commute` doing the bookkeeping. -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

end CannonFloydParry.S6

/-! Lemma 6.2 iii) (CFP p. 244) and the assembled Lemma 6.2. -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)
local notation "cV" => (PresentedGroup.of FormalV.C : V1)


end CannonFloydParry.S6

/-! Lemma 6.3 (CFP pp. 244–245). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


end CannonFloydParry.S6

/-! Lemma 6.4 (CFP p. 245). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


end CannonFloydParry.S6

/-! Lemma 6.5 (CFP pp. 245–246). -/

namespace CannonFloydParry.S6


end CannonFloydParry.S6

/-! Lemma 6.6 (CFP pp. 246–247). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


end CannonFloydParry.S6

/-! `Π(n)` is finite: a coset count, `|Π(k+1) : Π(k)| ≤ k + 2`. -/

namespace CannonFloydParry.S6

end CannonFloydParry.S6

/-! Lemmas 6.7 and 6.8 (CFP p. 247). -/

namespace CannonFloydParry.S6


end CannonFloydParry.S6

/-! The normal form `g = p π Cₙ^m q⁻¹` in `V₁` (CFP p. 248, proof of Theorem 6.9). -/

namespace CannonFloydParry.S6


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

end CannonFloydParry.S6

/-! The subgroup of `V₁` generated by `A` and `B` is torsion-free (CFP p. 248): it maps
injectively to `F ⊆ V` by Theorem 3.4, and `F` is totally ordered (Theorem 4.11). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5


end CannonFloydParry.S6

/-! A coset count for elements satisfying the relations of Σ's presentation (CFP p. 247):
if `t₀, t₁, …` are involutions with `(tᵢtᵢ₊₁)³ = 1` and `tᵢtⱼ = tⱼtᵢ` for `j ≥ i + 2`, then
`⟨t₀, …, t_{n-1}⟩` has at most `(n + 1)!` elements. -/

namespace CannonFloydParry.S6.CoxA

variable {G : Type*} [Group G]

/-- The relations of the presentation of `Σ` on p. 247, for a sequence `t` in `G`. -/
structure IsCoxA (t : ℕ → G) : Prop where
  sq : ∀ i, t i * t i = 1
  cube : ∀ i, (t i * t (i + 1)) ^ 3 = 1
  comm : ∀ i j, i + 2 ≤ j → t i * t j = t j * t i

variable {t : ℕ → G}

namespace IsCoxA

variable (h : IsCoxA t)
include h

end IsCoxA

end CannonFloydParry.S6.CoxA

/-! In every proper quotient of `Σ`, `s₀` and `s₁` have the same image (CFP p. 247). -/

namespace CannonFloydParry.S6

open Equiv Equiv.Perm

instance (K : ℕ) : Fintype {x : ℕ // x < K} := Fintype.ofEquiv _ Fin.equivSubtype


end CannonFloydParry.S6

/-! The presentation of `Σ` (CFP p. 247). -/

namespace CannonFloydParry.S6

open Equiv Equiv.Perm CoxA

instance (K : ℕ) : Finite {x : ℕ // x < K} := Finite.of_equiv _ Fin.equivSubtype


end CannonFloydParry.S6

/-! `Π ≅ Σ` (CFP p. 247). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5 Equiv


end CannonFloydParry.S6

/-! Theorem 6.9: `V₁` is simple (CFP p. 248). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5 Equiv

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


end CannonFloydParry.S6

/-! `V₁ ≅ V` and `V` is simple (CFP p. 243), from the surjection of Lemma 6.1 and Theorem 6.9. -/

namespace CannonFloydParry.S6

open Equiv

end CannonFloydParry.S6

namespace CannonFloydParry.S6

end CannonFloydParry.S6


/-! Closure of `IsThompsonV`, part 1: locating intervals in a partition; inverses. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

/-! Closure of `IsThompsonV`, part 2: products; `f ∈ V ↔ IsThompsonV f`; tree diagrams for `V`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5


end CannonFloydParry.S6

/-! Powers of `A` and `B` on representatives in `[0,1)`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B

end CannonFloydParry.S6

/-! `π₁` on representatives (generated by scripts/gen_pi1.py). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

end CannonFloydParry.S6

/-! The action of `πᵢ` on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

end CannonFloydParry.S6

/-! The action of `Cₙ` on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C

end CannonFloydParry.S6

/-! Permutations of the pieces `[q j, q (j+1))` of a partition of `[0, q K)` realised by affine
maps, the tail `[q K, 1)` fixed. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

variable {K : ℕ} (q : Fin (K + 1) → ℝ)

variable {q}

end CannonFloydParry.S6

/-! The symmetric groups acting on the comb intervals (CFP p. 241). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5


end CannonFloydParry.S6

open CannonFloydParry in
theorem solution :
    ∃ φ : T1 →* V1, φ (PresentedGroup.of FormalABC.A) = PresentedGroup.of FormalV.A ∧
      φ (PresentedGroup.of FormalABC.B) = PresentedGroup.of FormalV.B ∧
      φ (PresentedGroup.of FormalABC.C) = PresentedGroup.of FormalV.C := by
  exact ⟨S6.fromT1, S6.fromT1_A, S6.fromT1_B, S6.fromT1_C⟩
