-- Prove2me | solution 1 for Garrido.isParadoxical_closedBall_and_isParadoxical_univ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:53.954493+00:00
-- url     : https://prove2.me/submissions/d2b758c0-277e-4dc1-8eec-be0b94ff073b

import Mathlib
import Theorems.Thm_Garrido_isParadoxical_sphere_two_and_isParadoxical_sphere
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ
abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem eq_trans {G X : Type*} [Group G] [MulAction G X] {A B C : Set X}
    (h1 : Equidecomposable G A B) (h2 : Equidecomposable G B C) : Equidecomposable G A C := by
  obtain ⟨e, rfl, rfl⟩ := h1
  obtain ⟨f, hf, rfl⟩ := h2
  refine ⟨e.trans f, ?_, ?_⟩
  · change e.source ∩ e ⁻¹' f.source = e.source
    rw [hf]; exact inter_eq_self_of_subset_left fun x hx => e.map_source hx
  · change (e.toPartialEquiv.trans f.toPartialEquiv).target = f.target
    rw [PartialEquiv.trans_target, ← hf]
    exact inter_eq_self_of_subset_left fun x hx => f.map_target hx

/-- Pull-back of an equidecomposition along an equivariant map. -/
theorem pullback {G H X Y : Type*} [Group G] [Group H] [MulAction G Y] [MulAction H X]
    (φ : G →* H) (π : X → Y) (S : Set X) (hS : ∀ g : G, ∀ x ∈ S, φ g • x ∈ S)
    (hπ : ∀ g : G, ∀ x ∈ S, π (φ g • x) = g • π x) {A B : Set Y}
    (h : Equidecomposable G A B) : Equidecomposable H (S ∩ π ⁻¹' A) (S ∩ π ⁻¹' B) := by
  classical
  obtain ⟨e, rfl, rfl⟩ := h
  have hc : ∀ y, ∃ g : G, y ∈ e.source → (g ∈ e.witness ∧ e y = g • y) := by
    intro y
    by_cases hy : y ∈ e.source
    · obtain ⟨g, hg, hgy⟩ := e.isDecompOn y hy
      exact ⟨g, fun _ => ⟨hg, hgy⟩⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose γ hγ using hc
  let P : PartialEquiv X X :=
    { toFun := fun x => φ (γ (π x)) • x
      invFun := fun x => φ (γ (e.symm (π x)))⁻¹ • x
      source := S ∩ π ⁻¹' e.source
      target := S ∩ π ⁻¹' e.target
      map_source' := by
        rintro x ⟨hxS, hx⟩
        refine ⟨hS _ x hxS, ?_⟩
        change π (φ (γ (π x)) • x) ∈ e.target
        rw [hπ _ x hxS, ← (hγ _ hx).2]
        exact e.map_source hx
      map_target' := by
        rintro x ⟨hxS, hx⟩
        have hy := e.map_target hx
        refine ⟨hS _ x hxS, ?_⟩
        change π (φ (γ (e.symm (π x)))⁻¹ • x) ∈ e.source
        rw [hπ _ x hxS]
        have h' : (γ (e.symm (π x)))⁻¹ • π x = e.symm (π x) := by
          rw [inv_smul_eq_iff, ← (hγ _ hy).2]; exact (Equidecomp.right_inv hx).symm
        rw [h']
        exact hy
      left_inv' := by
        rintro x ⟨hxS, hx⟩
        rw [hπ _ x hxS, ← (hγ _ hx).2]
        change φ (γ (e.toPartialEquiv.symm (e (π x))))⁻¹ • φ (γ (π x)) • x = x
        rw [Equidecomp.left_inv hx, map_inv, inv_smul_smul]
      right_inv' := by
        rintro x ⟨hxS, hx⟩
        have hy := e.map_target hx
        have key : π (φ (γ (e.symm (π x)))⁻¹ • x) = e.symm (π x) := by
          rw [hπ _ x hxS, inv_smul_eq_iff, ← (hγ _ hy).2]
          exact (Equidecomp.right_inv hx).symm
        change φ (γ (π (φ (γ (e.symm (π x)))⁻¹ • x))) • φ (γ (e.symm (π x)))⁻¹ • x = x
        rw [key, map_inv, smul_inv_smul] }
  refine ⟨⟨P, e.witness.image φ, ?_⟩, rfl, rfl⟩
  rintro x ⟨-, hx⟩
  exact ⟨φ (γ (π x)), Finset.mem_image_of_mem _ (hγ _ hx).1, rfl⟩

/-- A single group element as an equidecomposition. -/
noncomputable def single {G X : Type*} [Group G] [MulAction G X] (g : G) : Equidecomp X G where
  toPartialEquiv := (MulAction.toPerm g : Equiv.Perm X).toPartialEquiv
  isDecompOn' := ⟨{g}, fun _ _ => ⟨g, Finset.mem_singleton_self _, rfl⟩⟩

theorem eq_union {G X : Type*} [Group G] [MulAction G X] {A B C D : Set X}
    (hAC : Disjoint A C) (hBD : Disjoint B D) (h1 : Equidecomposable G A B)
    (h2 : Equidecomposable G C D) : Equidecomposable G (A ∪ C) (B ∪ D) := by
  classical
  obtain ⟨e, rfl, rfl⟩ := h1
  obtain ⟨e', rfl, rfl⟩ := h2
  refine ⟨⟨e.toPartialEquiv.disjointUnion e'.toPartialEquiv hAC hBD,
    e.witness ∪ e'.witness, ?_⟩, rfl, rfl⟩
  intro a ha
  change a ∈ e.source ∪ e'.source at ha
  by_cases h : a ∈ e.source
  · obtain ⟨g, hg, hga⟩ := e.isDecompOn a h
    refine ⟨g, Finset.mem_union_left _ hg, ?_⟩
    change (e.source.piecewise e e') a = g • a
    rw [Set.piecewise_eq_of_mem _ _ _ h]; exact hga
  · obtain ⟨g, hg, hga⟩ := e'.isDecompOn a (ha.resolve_left h)
    refine ⟨g, Finset.mem_union_right _ hg, ?_⟩
    change (e.source.piecewise e e') a = g • a
    rw [Set.piecewise_eq_of_notMem _ _ _ h]; exact hga

theorem eq_refl {G X : Type*} [Group G] [MulAction G X] (A : Set X) :
    Equidecomposable G A A :=
  ⟨(Equidecomp.refl X G).restr A, by simp, by simp⟩

theorem eq_symm {G X : Type*} [Group G] [MulAction G X] {A B : Set X}
    (h : Equidecomposable G A B) : Equidecomposable G B A := by
  obtain ⟨e, rfl, rfl⟩ := h
  exact ⟨e.symm, rfl, rfl⟩

/-- Absorbing a point along an orbit that does not return. -/
theorem absorb {G X : Type*} [Group G] [MulAction G X] (E : Set X) (p : X) (ρ : G)
    (hE : ∀ n : ℕ, ρ ^ n • p ∈ E) (hne : ∀ n : ℕ, 0 < n → ρ ^ n • p ≠ p) :
    Equidecomposable G E (E \ {p}) := by
  set D : Set X := range fun n : ℕ => ρ ^ n • p
  have hDE : D ⊆ E := by rintro _ ⟨n, rfl⟩; exact hE n
  have himg : (single ρ : Equidecomp X G).toPartialEquiv '' D = range fun n : ℕ => ρ ^ (n + 1) • p := by
    ext y; constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by simp [single, pow_succ', mul_smul]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, by simp [single, pow_succ', mul_smul]⟩
  have h1 : Equidecomposable G D (range fun n : ℕ => ρ ^ (n + 1) • p) := by
    refine ⟨(single ρ).restr D, by simp [single], ?_⟩
    rw [← himg]
    change (single ρ).toPartialEquiv.target ∩ _ = _
    ext y; simp only [single, Equiv.toPartialEquiv_target, univ_inter, mem_preimage,
      mem_image]
    constructor
    · intro hy; exact ⟨_, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩; simpa using hx
  have hsplit : E = D ∪ (E \ D) := (union_sdiff_cancel hDE).symm
  have hsplit2 : E \ {p} = (range fun n : ℕ => ρ ^ (n + 1) • p) ∪ (E \ D) := by
    ext y; constructor
    · rintro ⟨hyE, hyp⟩
      by_cases hyD : y ∈ D
      · obtain ⟨n, rfl⟩ := hyD
        rcases n with _ | n
        · exact absurd (by simp) hyp
        · exact Or.inl ⟨n, rfl⟩
      · exact Or.inr ⟨hyE, hyD⟩
    · rintro (⟨n, rfl⟩ | ⟨hyE, hyD⟩)
      · exact ⟨hE _, hne _ n.succ_pos⟩
      · refine ⟨hyE, fun h => hyD ⟨0, by simpa using h.symm⟩⟩
  rw [hsplit2]
  conv_lhs => rw [hsplit]
  refine eq_union disjoint_sdiff_right ?_ h1 (eq_refl _)
  rw [Set.disjoint_left]
  rintro _ ⟨n, rfl⟩ ⟨-, h⟩
  exact h ⟨n + 1, rfl⟩

theorem isParadoxical_of_subset {G X : Type*} [Group G] [MulAction G X] {S T : Set X}
    (hS : IsParadoxical G S) (hST : S ⊆ T) (h : Equidecomposable G S T) : IsParadoxical G T := by
  obtain ⟨A, B, hA, hB, hAS, hBS, hAB, hAe, hBe⟩ := hS
  refine ⟨A, B, hA.trans hST, hB.trans hST, ?_, ?_, hAB, eq_trans hAe h, eq_trans hBe h⟩
  · rintro rfl; exact hAS (subset_antisymm hA hST)
  · rintro rfl; exact hBS (subset_antisymm hB hST)

theorem isParadoxical_pullback {G H X Y : Type*} [Group G] [Group H] [MulAction G Y]
    [MulAction H X] (φ : G →* H) (π : X → Y) (S : Set X) (hS : ∀ g : G, ∀ x ∈ S, φ g • x ∈ S)
    (hπ : ∀ g : G, ∀ x ∈ S, π (φ g • x) = g • π x) (hsurj : ∀ y, ∃ x ∈ S, π x = y)
    (h : IsParadoxical G (univ : Set Y)) : IsParadoxical H S := by
  obtain ⟨A, B, -, -, hA, hB, hAB, hAe, hBe⟩ := h
  have hne : ∀ C : Set Y, C ≠ univ → S ∩ π ⁻¹' C ≠ S := by
    intro C hC heq
    obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem C).1 hC
    obtain ⟨x, hxS, rfl⟩ := hsurj y
    have : x ∈ S ∩ π ⁻¹' C := by rw [heq]; exact hxS
    exact hy this.2
  have e1 := pullback φ π S hS hπ hAe
  have e2 := pullback φ π S hS hπ hBe
  simp only [preimage_univ, inter_univ] at e1 e2
  refine ⟨_, _, inter_subset_left, inter_subset_left, hne A hA, hne B hB, ?_, e1, e2⟩
  exact (hAB.preimage π).inter_left' S |>.inter_right' S


theorem orth (A : SO3) : (A : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1

/-- the linear action of a matrix -/
noncomputable def lin (A : SO3) (x : E3) : E3 :=
  WithLp.toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.ofLp)

theorem lin_sub (A : SO3) (x y : E3) : lin A (x - y) = lin A x - lin A y := by
  simp [lin, Matrix.mulVec_sub]

theorem lin_smul (A : SO3) (t : ℝ) (x : E3) : lin A (t • x) = t • lin A x := by
  simp [lin, Matrix.mulVec_smul]

theorem norm_lin (A : SO3) (x : E3) : ‖lin A x‖ = ‖x‖ :=
  norm_toLp_mulVec_of_mem_orthogonalGroup (orth A) x

theorem lin_mul (A B : SO3) (x : E3) : lin (A * B) x = lin A (lin B x) := by
  simp [lin, Matrix.mulVec_mulVec]

theorem lin_one (x : E3) : lin 1 x = x := by
  simp [lin]

theorem lin_inv_lin (A : SO3) (x : E3) : lin A⁻¹ (lin A x) = x := by
  rw [← lin_mul, inv_mul_cancel, lin_one]

theorem lin_lin_inv (A : SO3) (x : E3) : lin A (lin A⁻¹ x) = x := by
  rw [← lin_mul, mul_inv_cancel, lin_one]

/-- rotation about the point `q` -/
noncomputable def rotAt (q : E3) (A : SO3) : EuclideanGroup 3 where
  toFun x := q + lin A (x - q)
  invFun x := q + lin A⁻¹ (x - q)
  left_inv x := by simp [lin_inv_lin]
  right_inv x := by simp [lin_lin_inv]
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← lin_sub, norm_lin]
    congr 1; abel

noncomputable def rotHom (q : E3) : SO3 →* EuclideanGroup 3 :=
  MonoidHom.mk' (rotAt q) fun A B => by
    ext1 x
    change q + lin (A * B) (x - q) = q + lin A ((q + lin B (x - q)) - q)
    rw [lin_mul, add_sub_cancel_left]

theorem rotHom_smul (q : E3) (A : SO3) (x : E3) : rotHom q A • x = q + lin A (x - q) := rfl



/-- rotation by `arccos (3/5)` about the first coordinate axis -/
noncomputable def R : SO3 :=
  ⟨!![1, 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
    · simp [Matrix.det_fin_three]; norm_num⟩

def ab : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => (3 * (ab n).1 - 4 * (ab n).2, 4 * (ab n).1 + 3 * (ab n).2)

theorem ab_mod (n : ℕ) (hn : 0 < n) : (ab n).1 % 5 = 1 ∧ (ab n).2 % 5 = 3 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [ab]
    · obtain ⟨h1, h2⟩ := ih hn'
      simp only [ab]
      omega

theorem R_pow_mulVec (n : ℕ) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) ^ n) *ᵥ ![0, 0, 1] =
      ![0, ((ab n).1 : ℝ) / 5 ^ n, ((ab n).2 : ℝ) / 5 ^ n] := by
  induction n with
  | zero => simp [ab]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    ext i
    fin_cases i <;> simp [R, ab, Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_succ] <;>
      field_simp <;> ring

theorem R_pow_ne (n : ℕ) (hn : 0 < n) :
    ((R : Matrix (Fin 3) (Fin 3) ℝ) ^ n) *ᵥ ![0, 0, 1] ≠ ![0, 0, 1] := by
  intro h
  rw [R_pow_mulVec] at h
  have h2 := congrFun h 2
  simp at h2
  rw [div_eq_one_iff_eq (by positivity)] at h2
  have : (ab n).2 = 5 ^ n := by exact_mod_cast h2
  have := (ab_mod n hn).2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [‹(ab _).2 = _›, pow_succ] at this
  omega

/-! ## The radial projection -/

noncomputable def proj (c x : E3) : Sphere 2 :=
  if h : x = c then ⟨EuclideanSpace.single 0 1, by simp⟩
  else ⟨‖x - c‖⁻¹ • (x - c), by
    have : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h)
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ this]⟩

theorem proj_val (c x : E3) (h : x ≠ c) : (proj c x).1 = ‖x - c‖⁻¹ • (x - c) := by
  simp [proj, h]

theorem rot_ne (c : E3) (A : SO3) (x : E3) (h : x ≠ c) : rotHom c A • x ≠ c := by
  rw [rotHom_smul]
  intro h'
  have : lin A (x - c) = 0 := by
    have := congrArg (· - c) h'; simpa using this
  have := norm_lin A (x - c)
  rw [‹lin A (x - c) = 0›, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at this
  exact h this

theorem proj_equivariant (c : E3) (A : SO3) (x : E3) (h : x ≠ c) :
    proj c (rotHom c A • x) = A • proj c x := by
  apply Subtype.ext
  rw [proj_val _ _ (rot_ne c A x h)]
  change _ = lin A (proj c x).1
  rw [proj_val _ _ h, lin_smul, rotHom_smul, add_sub_cancel_left, norm_lin]

theorem dist_rot (c : E3) (A : SO3) (x : E3) : ‖rotHom c A • x - c‖ = ‖x - c‖ := by
  rw [rotHom_smul, add_sub_cancel_left, norm_lin]

theorem isParadoxical_ball_punctured (h : IsParadoxical SO3 (univ : Set (Sphere 2)))
    (c : E3) (r : ℝ) (hr : 0 < r) :
    IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r \ {c}) := by
  refine isParadoxical_pullback (rotHom c) (proj c) _ ?_ ?_ ?_ h
  · rintro A x ⟨hx, hxc⟩
    refine ⟨?_, rot_ne c A x hxc⟩
    rw [Metric.mem_closedBall, dist_eq_norm, dist_rot]
    rwa [Metric.mem_closedBall, dist_eq_norm] at hx
  · rintro A x ⟨-, hxc⟩
    exact proj_equivariant c A x hxc
  · intro y
    have hy : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
    have hne : c + r • y.1 ≠ c := by
      intro h; have := congrArg (‖· - c‖) h
      simp [norm_smul, hy, abs_of_pos hr] at this; linarith
    refine ⟨c + r • y.1, ⟨?_, hne⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hy,
        Real.norm_eq_abs, abs_of_pos hr, mul_one]
    · apply Subtype.ext
      rw [proj_val _ _ hne, add_sub_cancel_left, norm_smul, hy, Real.norm_eq_abs, abs_of_pos hr,
        mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem isParadoxical_punctured_univ (h : IsParadoxical SO3 (univ : Set (Sphere 2))) :
    IsParadoxical (EuclideanGroup 3) (univ \ {(0 : E3)}) := by
  refine isParadoxical_pullback (rotHom 0) (proj 0) _ ?_ ?_ ?_ h
  · rintro A x ⟨-, hxc⟩
    exact ⟨trivial, rot_ne 0 A x hxc⟩
  · rintro A x ⟨-, hxc⟩
    exact proj_equivariant 0 A x hxc
  · intro y
    have hy : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
    have hne : y.1 ≠ 0 := by intro h; rw [h, norm_zero] at hy; exact zero_ne_one hy
    refine ⟨y.1, ⟨trivial, hne⟩, ?_⟩
    apply Subtype.ext
    rw [proj_val _ _ hne, sub_zero, hy, inv_one, one_smul]

/-! ## Absorbing the centre -/

/-- The unit vector along the third axis. -/
noncomputable def e3 : E3 := WithLp.toLp 2 ![0, 0, 1]

theorem norm_e3 : ‖e3‖ = 1 := by
  simp [e3, EuclideanSpace.norm_eq, Fin.sum_univ_three]

theorem rot_pow_ne (c : E3) (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) :
    rotHom (c + (r / 2) • e3) R ^ n • c ≠ c := by
  rw [← map_pow, rotHom_smul]
  intro h
  have h1 : lin (R ^ n) (c - (c + (r / 2) • e3)) = c - (c + (r / 2) • e3) := by
    have := congrArg (· - (c + (r / 2) • e3)) h
    simpa using this
  rw [sub_add_cancel_left, show -((r / 2) • e3) = (-(r / 2)) • e3 by rw [neg_smul], lin_smul] at h1
  have h2 : lin (R ^ n) e3 = e3 := smul_right_injective _ (by linarith : -(r / 2) ≠ 0) h1
  apply R_pow_ne n hn
  have := congrArg WithLp.ofLp h2
  simpa [lin, e3] using this

theorem rot_pow_mem (c : E3) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    rotHom (c + (r / 2) • e3) R ^ n • c ∈ Metric.closedBall c r := by
  rw [← map_pow, rotHom_smul, Metric.mem_closedBall, dist_eq_norm]
  calc ‖c + (r / 2) • e3 + lin (R ^ n) (c - (c + (r / 2) • e3)) - c‖
      ≤ ‖(r / 2) • e3‖ + ‖lin (R ^ n) (c - (c + (r / 2) • e3))‖ := by
        rw [add_sub_right_comm, add_sub_cancel_left]; exact norm_add_le _ _
    _ = r := by
        rw [norm_lin, sub_add_cancel_left, norm_neg, norm_smul, norm_e3, Real.norm_eq_abs,
          abs_of_pos (by linarith)]; ring

/-! ## The targets -/

theorem isParadoxical_closedBall_and_isParadoxical_univ'
    (h_19 : IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n))) :
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
        IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r)) ∧
      IsParadoxical (EuclideanGroup 3) (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := by
  refine ⟨fun c r hr => ?_, ?_⟩
  · refine isParadoxical_of_subset (isParadoxical_ball_punctured h_19.1 c r hr) sdiff_subset
      (eq_symm (absorb _ c (rotHom (c + (r / 2) • e3) R) (rot_pow_mem c r hr)
        (rot_pow_ne c r hr)))
  · refine isParadoxical_of_subset (isParadoxical_punctured_univ h_19.1) sdiff_subset
      (eq_symm (absorb _ 0 (rotHom ((0 : E3) + (1 / 2 : ℝ) • e3) R) (fun _ => trivial)
        (rot_pow_ne 0 1 one_pos)))

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem isParadoxical_sphere_two_and_isParadoxical_sphere :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) :=
  Garrido.isParadoxical_sphere_two_and_isParadoxical_sphere

theorem isParadoxical_closedBall_and_isParadoxical_univ :
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
        IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r)) ∧
      IsParadoxical (EuclideanGroup 3) (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
  Garrido.BT.isParadoxical_closedBall_and_isParadoxical_univ'
    isParadoxical_sphere_two_and_isParadoxical_sphere

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
        IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r)) ∧
      IsParadoxical (EuclideanGroup 3) (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
  Garrido.BT.Final.isParadoxical_closedBall_and_isParadoxical_univ
