-- Prove2me | solution 1 for Garrido.isParadoxical_sphere_two_and_isParadoxical_sphere
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:52.894466+00:00
-- url     : https://prove2.me/submissions/e2f2e624-57ae-4019-8a9c-8e9835692ccc

import Mathlib
import Theorems.Thm_Garrido_exists_countable_isParadoxical_compl
import Theorems.Thm_Garrido_equidecomposable_univ_compl_of_countable
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

/-- `W c`: the elements whose reduced word starts with the letter `c`. -/
def W (c : α × Bool) : Set (FreeGroup α) := {w | (FreeGroup.toWord w).head? = some c}

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix

noncomputable def vec (a b c : ℤ) (k : ℕ) : Fin 3 → ℝ :=
  ![a / 3 ^ k, b * √2 / 3 ^ k, c / 3 ^ k]

noncomputable def act (g : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v

theorem sq2 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

theorem act_mul (g h : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    act (g * h) v = act g (act h v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 3 → ℝ) : act 1 v = v := by simp [act]

theorem act_inv_act (g : specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem vec_nine (a b c : ℤ) (k : ℕ) :
    vec (9 * a) (9 * b) (9 * c) (k + 2) = vec a b c k := by
  funext i
  fin_cases i <;> simp [vec, pow_add] <;> field_simp <;> ring

theorem act_rho (a b c : ℤ) (k : ℕ) :
    act rho (vec a b c k) = vec (a - 4 * b) (2 * a + b) (3 * c) (k + 1) := by
  funext i
  fin_cases i <;>
    simp [act, vec, rho, mulVec, dotProduct, Fin.sum_univ_three, pow_succ] <;>
    field_simp <;> (try simp only [sq2]) <;> ring

theorem act_sigma (a b c : ℤ) (k : ℕ) :
    act sigma (vec a b c k) = vec (3 * a) (b - 2 * c) (c + 4 * b) (k + 1) := by
  funext i
  fin_cases i <;>
    simp [act, vec, sigma, mulVec, dotProduct, Fin.sum_univ_three, pow_succ] <;>
    field_simp <;> (try simp only [sq2]) <;> ring

theorem act_rho_inv (a b c : ℤ) (k : ℕ) :
    act rho⁻¹ (vec a b c k) = vec (a + 4 * b) (b - 2 * a) (3 * c) (k + 1) := by
  conv_lhs => rw [← vec_nine a b c k, show 9 * a = (a + 4 * b) - 4 * (b - 2 * a) by ring,
    show 9 * b = 2 * (a + 4 * b) + (b - 2 * a) by ring, show 9 * c = 3 * (3 * c) by ring,
    ← act_rho]
  exact act_inv_act _ _

theorem act_sigma_inv (a b c : ℤ) (k : ℕ) :
    act sigma⁻¹ (vec a b c k) = vec (3 * a) (b + 2 * c) (c - 4 * b) (k + 1) := by
  conv_lhs => rw [← vec_nine a b c k, show 9 * a = 3 * (3 * a) by ring,
    show 9 * b = (b + 2 * c) - 2 * (c - 4 * b) by ring,
    show 9 * c = (c - 4 * b) + 4 * (b + 2 * c) by ring, ← act_sigma]
  exact act_inv_act _ _


/-- The four residue patterns mod 3 (reduced words ending/starting with `ρ, ρ⁻¹, σ, σ⁻¹`). -/
def patB : Fin 2 × Bool → ZMod 3 → ZMod 3 → ZMod 3 → Bool
  | (0, true), x, y, z => decide (x ≠ 0 ∧ y = -x ∧ z = 0)
  | (0, false), x, y, z => decide (x ≠ 0 ∧ y = x ∧ z = 0)
  | (1, true), x, y, z => decide (x = 0 ∧ y ≠ 0 ∧ z = y)
  | (1, false), x, y, z => decide (x = 0 ∧ y ≠ 0 ∧ z = -y)

def InP (l : Fin 2 × Bool) (v : Fin 3 → ℝ) : Prop :=
  ∃ a b c : ℤ, ∃ k : ℕ, v = vec a b c k ∧ patB l a b c = true

noncomputable def gen (x : Fin 2 × Bool) : specialOrthogonalGroup (Fin 3) ℝ :=
  cond x.2 (![rho, sigma] x.1) (![rho, sigma] x.1)⁻¹


/-- The base point `(1, 0, 1)`, whose residue pattern is in none of the four classes. -/
noncomputable def v0 : Fin 3 → ℝ := vec 1 0 1 0

theorem base (l : Fin 2 × Bool) : InP l (act (gen l) v0) := by
  rcases l with ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp only [v0, gen, cond, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, act_rho, act_rho_inv, act_sigma, act_sigma_inv] <;>
    refine ⟨_, _, _, _, rfl, ?_⟩ <;> decide

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

theorem c5_equidecomposable_symm {G X : Type*} [Group G] [MulAction G X] {A B : Set X}
    (h : Equidecomposable G A B) : Equidecomposable G B A := by
  obtain ⟨e, rfl, rfl⟩ := h
  exact ⟨e.symm, rfl, rfl⟩

theorem c5_equidecomposable_refl {G X : Type*} [Group G] [MulAction G X] (A : Set X) :
    Equidecomposable G A A :=
  ⟨(Equidecomp.refl X G).restr A, by simp, by simp⟩

theorem c5_equidecomposable_trans {G X : Type*} [Group G] [MulAction G X] {A B C : Set X}
    (h1 : Equidecomposable G A B) (h2 : Equidecomposable G B C) : Equidecomposable G A C := by
  obtain ⟨e, rfl, he⟩ := h1
  obtain ⟨f, hf, rfl⟩ := h2
  refine ⟨e.trans f, ?_, ?_⟩
  · change (e.toPartialEquiv.trans f.toPartialEquiv).source = _
    rw [PartialEquiv.trans_source]
    rw [hf, ← he]
    exact inter_eq_left.2 fun x hx => e.toPartialEquiv.map_source hx
  · change (e.toPartialEquiv.trans f.toPartialEquiv).target = _
    rw [PartialEquiv.trans_target]
    rw [he, ← hf]
    exact inter_eq_left.2 fun x hx => f.toPartialEquiv.map_target hx

theorem c5_equidecomposable_union {G X : Type*} [Group G] [MulAction G X] {A B C D : Set X}
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

theorem c5_equidecomposable_image {G X : Type*} [Group G] [MulAction G X] (e : Equidecomp X G)
    {S : Set X} (hS : S ⊆ e.source) : Equidecomposable G S (e.toPartialEquiv '' S) := by
  refine ⟨e.restr S, Equidecomp.source_restr e hS, ?_⟩
  rw [PartialEquiv.image_eq_target_inter_inv_preimage _ hS]
  rfl

/-- An injective piecewise-`G` map gives an equidecomposition onto its image. -/
theorem c5_equidecomposable_of_injOn {G X : Type*} [Group G] [MulAction G X] (f : X → X)
    (s : Set X) (hf : InjOn f s) (W : Finset G) (hW : Equidecomp.IsDecompOn f s W) :
    Equidecomposable G s (f '' s) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Set.eq_empty_of_isEmpty s, image_empty]
    exact c5_equidecomposable_refl _
  · exact ⟨⟨hf.toPartialEquiv f s, ⟨W, hW⟩⟩, rfl, rfl⟩

theorem c5_equidecomposable_smul {G X : Type*} [Group G] [MulAction G X] (g : G) (T : Set X) :
    Equidecomposable G T (g • T) := by
  rw [← Set.image_smul]
  exact c5_equidecomposable_of_injOn _ T (MulAction.injective g).injOn {g}
    (fun a _ => ⟨g, Finset.mem_singleton_self g, rfl⟩)

/-- Paradoxicality transfers backwards along equidecomposability. -/
theorem c5_isParadoxical_of_equidecomposable {G X : Type*} [Group G] [MulAction G X]
    {E E' : Set X} (h : Equidecomposable G E E') (hp : IsParadoxical G E') :
    IsParadoxical G E := by
  obtain ⟨e, rfl, rfl⟩ := h
  obtain ⟨A, B, hA, hB, hAE, hBE, hAB, hAe, hBe⟩ := hp
  have key : ∀ C : Set X, C ⊆ e.target → C ≠ e.target → Equidecomposable G C e.target →
      e.toPartialEquiv.symm '' C ⊆ e.source ∧ e.toPartialEquiv.symm '' C ≠ e.source ∧
      Equidecomposable G (e.toPartialEquiv.symm '' C) e.source := by
    intro C hC hCE hCe
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact e.toPartialEquiv.map_target (hC hx)
    · intro heq
      apply hCE
      rw [← e.toPartialEquiv.image_symm_image_of_subset_target hC, heq]
      exact e.toPartialEquiv.image_source_eq_target
    · have h1 : Equidecomposable G C (e.symm.toPartialEquiv '' C) :=
        c5_equidecomposable_image e.symm hC
      exact c5_equidecomposable_trans (c5_equidecomposable_symm h1)
        (c5_equidecomposable_trans hCe ⟨e.symm, rfl, rfl⟩)
  obtain ⟨hA1, hA2, hA3⟩ := key A hA hAE hAe
  obtain ⟨hB1, hB2, hB3⟩ := key B hB hBE hBe
  refine ⟨_, _, hA1, hB1, hA2, hB2, ?_, hA3, hB3⟩
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have : b = a := e.toPartialEquiv.symm.injOn (hB hb) (hA ha) hab
  exact Set.disjoint_left.1 hAB ha (this ▸ hb)


/-- Pulling back an equidecomposition along an equivariant map. -/
theorem c5_equidecomposable_pullback {G H X Y : Type*} [Group G] [Group H] [MulAction G X]
    [MulAction H Y] (φ : G →* H) (π : Y → X) (S : Set Y)
    (hS : ∀ g : G, ∀ y ∈ S, φ g • y ∈ S) (hπ : ∀ g : G, ∀ y ∈ S, π (φ g • y) = g • π y)
    {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable H (S ∩ π ⁻¹' A) (S ∩ π ⁻¹' B) := by
  classical
  obtain ⟨e, rfl, rfl⟩ := h
  have hd := e.isDecompOn
  choose c hcW hc using hd
  let γ : X → G := fun x => if hx : x ∈ e.source then c x hx else 1
  have hγ : ∀ x ∈ e.source, e x = γ x • x ∧ γ x ∈ e.witness := by
    intro x hx
    simp only [γ, dif_pos hx]
    exact ⟨hc x hx, hcW x hx⟩
  let f : Y → Y := fun y => φ (γ (π y)) • y
  have hπf : ∀ y ∈ S ∩ π ⁻¹' e.source, π (f y) = e (π y) := by
    intro y hy
    rw [hπ _ _ hy.1, (hγ _ hy.2).1]
  have hinj : InjOn f (S ∩ π ⁻¹' e.source) := by
    intro y1 hy1 y2 hy2 h12
    have h1 : e (π y1) = e (π y2) := by rw [← hπf _ hy1, ← hπf _ hy2, h12]
    have h2 : π y1 = π y2 := e.toPartialEquiv.injOn hy1.2 hy2.2 h1
    have h3 : φ (γ (π y1)) • y1 = φ (γ (π y1)) • y2 := by
      have : f y1 = f y2 := h12
      simp only [f] at this
      rw [this, h2]
    exact smul_left_cancel _ h3
  have himg : f '' (S ∩ π ⁻¹' e.source) = S ∩ π ⁻¹' e.target := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨hS _ _ hy.1, ?_⟩
      change π (f y) ∈ e.target
      rw [hπf _ hy]
      exact e.toPartialEquiv.map_source hy.2
    · rintro z ⟨hzS, hz⟩
      have hz' : π z ∈ e.target := hz
      set x := e.toPartialEquiv.symm (π z) with hx
      have hxs : x ∈ e.source := e.toPartialEquiv.map_target hz'
      have hex : e x = π z := e.toPartialEquiv.right_inv hz'
      have hyS : φ (γ x)⁻¹ • z ∈ S := hS _ _ hzS
      have hπy : π (φ (γ x)⁻¹ • z) = x := by
        have := hπ (γ x)⁻¹ z hzS
        rw [this, ← hex, (hγ x hxs).1, inv_smul_smul]
      refine ⟨φ (γ x)⁻¹ • z, ⟨hyS, ?_⟩, ?_⟩
      · change π _ ∈ e.source; rw [hπy]; exact hxs
      · simp only [f]
        rw [hπy, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have := c5_equidecomposable_of_injOn f _ hinj (e.witness.image φ) (by
    intro y hy
    exact ⟨φ (γ (π y)), Finset.mem_image_of_mem _ (hγ _ hy.2).2, rfl⟩)
  rwa [himg] at this

/-- A paradoxical decomposition pulls back along an equivariant map onto the whole space. -/
theorem c5_isParadoxical_pullback {G H X Y : Type*} [Group G] [Group H] [MulAction G X]
    [MulAction H Y] (φ : G →* H) (π : Y → X) (S : Set Y)
    (hS : ∀ g : G, ∀ y ∈ S, φ g • y ∈ S) (hπ : ∀ g : G, ∀ y ∈ S, π (φ g • y) = g • π y)
    (hsurj : ∀ x : X, ∃ y ∈ S, π y = x)
    (hp : IsParadoxical G (Set.univ : Set X)) : IsParadoxical H S := by
  obtain ⟨A, B, -, -, hA, hB, hAB, hAe, hBe⟩ := hp
  have hS' : S ∩ π ⁻¹' (Set.univ : Set X) = S := by simp
  have ne : ∀ C : Set X, C ≠ Set.univ → S ∩ π ⁻¹' C ≠ S := by
    intro C hC heq
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem C).1 hC
    obtain ⟨y, hy, rfl⟩ := hsurj x
    exact hx (heq.symm ▸ hy : y ∈ S ∩ π ⁻¹' C).2
  refine ⟨S ∩ π ⁻¹' A, S ∩ π ⁻¹' B, inter_subset_left, inter_subset_left, ne A hA, ne B hB,
    ?_, ?_, ?_⟩
  · exact (hAB.preimage π).mono inter_subset_right inter_subset_right
  · have := c5_equidecomposable_pullback φ π S hS hπ hAe
    rwa [hS'] at this
  · have := c5_equidecomposable_pullback φ π S hS hπ hBe
    rwa [hS'] at this

/-- Absorbing a set that a single element moves off itself in all positive powers. -/
theorem c5_equidecomposable_univ_compl {G X : Type*} [Group G] [MulAction G X] (ρ : G)
    (D : Set X) (h : ∀ k : ℕ, 0 < k → Disjoint ((ρ ^ k) • D) D) :
    Equidecomposable G (Set.univ : Set X) Dᶜ := by
  let Dbar : Set X := ⋃ k : ℕ, (ρ ^ k) • D
  have hshift : ρ • Dbar = ⋃ k : ℕ, (ρ ^ (k + 1)) • D := by
    simp only [Dbar, Set.smul_set_iUnion, smul_smul, pow_succ']
  have hDD : Dbar \ D = ρ • Dbar := by
    rw [hshift]
    apply Subset.antisymm
    · rintro x ⟨hx, hxD⟩
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      cases k with
      | zero => simp at hk; exact absurd hk hxD
      | succ k => exact mem_iUnion.2 ⟨k, hk⟩
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      exact ⟨mem_iUnion.2 ⟨k + 1, hk⟩, fun hxD =>
        Set.disjoint_left.1 (h (k + 1) (Nat.succ_pos k)) hk hxD⟩
  have hDsub : D ⊆ Dbar := fun x hx => mem_iUnion.2 ⟨0, by simpa using hx⟩
  have h1 : (Set.univ : Set X) = Dbar ∪ Dbarᶜ := (union_compl_self _).symm
  have h2 : Dᶜ = ρ • Dbar ∪ Dbarᶜ := by
    rw [← hDD]
    ext x
    by_cases hx : x ∈ Dbar
    · simp [hx]
    · simp only [mem_compl_iff, mem_union, mem_sdiff, hx, false_and, not_false_eq_true,
        or_true, iff_true]
      exact fun hxD => hx (hDsub hxD)
  rw [h1, h2]
  refine c5_equidecomposable_union disjoint_compl_right ?_ (c5_equidecomposable_smul ρ Dbar)
    (c5_equidecomposable_refl _)
  rw [← hDD]
  exact Set.disjoint_left.2 fun x hx hx' => hx' hx.1

end Garrido.BT

namespace Garrido.BT

open Matrix

/-- Block-diagonal matrix `diag(A, B)` indexed by `Fin (k + l)`. -/
noncomputable def c5_blk {k l : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin l) (Fin l) ℝ) :
    Matrix (Fin (k + l)) (Fin (k + l)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem c5_blk_mul {k l : ℕ} (A A' : Matrix (Fin k) (Fin k) ℝ) (B B' : Matrix (Fin l) (Fin l) ℝ) :
    c5_blk A B * c5_blk A' B' = c5_blk (A * A') (B * B') := by
  simp only [c5_blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem c5_blk_one {k l : ℕ} : c5_blk (1 : Matrix (Fin k) (Fin k) ℝ) (1 : Matrix (Fin l) (Fin l) ℝ) = 1 := by
  simp only [c5_blk, Matrix.reindex_apply, fromBlocks_one, submatrix_one_equiv]

theorem c5_blk_transpose {k l : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin l) (Fin l) ℝ) :
    (c5_blk A B)ᵀ = c5_blk Aᵀ Bᵀ := by
  simp only [c5_blk, Matrix.reindex_apply, transpose_submatrix, fromBlocks_transpose]
  simp

theorem c5_blk_det {k l : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin l) (Fin l) ℝ) :
    (c5_blk A B).det = A.det * B.det := by
  rw [c5_blk, det_reindex_self, det_fromBlocks_zero₂₁]

theorem c5_mem_SO_iff {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    M ∈ specialOrthogonalGroup (Fin m) ℝ ↔ M * Mᵀ = 1 ∧ M.det = 1 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]

theorem c5_blk_mem {k l : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} {B : Matrix (Fin l) (Fin l) ℝ}
    (hA : A ∈ specialOrthogonalGroup (Fin k) ℝ) (hB : B ∈ specialOrthogonalGroup (Fin l) ℝ) :
    c5_blk A B ∈ specialOrthogonalGroup (Fin (k + l)) ℝ := by
  rw [c5_mem_SO_iff] at *
  rw [c5_blk_transpose, c5_blk_mul, hA.1, hB.1, c5_blk_one, c5_blk_det, hA.2, hB.2, mul_one]
  exact ⟨rfl, rfl⟩

theorem c5_blk_mulVec {k l : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin l) (Fin l) ℝ)
    (v : Fin (k + l) → ℝ) :
    (∀ a : Fin k, (c5_blk A B *ᵥ v) (Fin.castAdd l a) = (A *ᵥ fun a => v (Fin.castAdd l a)) a) ∧
    (∀ b : Fin l, (c5_blk A B *ᵥ v) (Fin.natAdd k b) = (B *ᵥ fun b => v (Fin.natAdd k b)) b) := by
  simp only [c5_blk, Matrix.reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_mulVec]
  constructor <;> intro _ <;> simp [Function.comp_def]

/-- The planar rotation by angle `t`. -/
noncomputable def c5_R (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem c5_R_mul (s t : ℝ) : c5_R s * c5_R t = c5_R (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c5_R, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem c5_R_mem (t : ℝ) : c5_R t ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  rw [c5_mem_SO_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [c5_R, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq t]
  · simp [c5_R, Matrix.det_fin_two]; nlinarith [Real.sin_sq_add_cos_sq t]

theorem c5_sin_natCast_ne_zero {k : ℕ} (hk : 0 < k) : Real.sin k ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 h
  have hm0 : (m : ℝ) ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hm; exact (Nat.cast_pos.2 hk).ne' hm.symm
  apply irrational_pi
  refine ⟨(k : ℚ) / m, ?_⟩
  push_cast
  field_simp
  linarith

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

/-- The block embedding `SO(n+1) → SO(n+2)`, `A ↦ diag(A, 1)`. -/
noncomputable def c5_phi (n : ℕ) :
    specialOrthogonalGroup (Fin (n + 1)) ℝ →* specialOrthogonalGroup (Fin (n + 1 + 1)) ℝ where
  toFun A := ⟨c5_blk (A : Matrix _ _ ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ),
    c5_blk_mem A.2 (one_mem _)⟩
  map_one' := by
    apply Subtype.ext
    exact c5_blk_one
  map_mul' A B := by
    apply Subtype.ext
    change c5_blk ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) * (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) = c5_blk (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 1 *
      c5_blk (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 1
    rw [c5_blk_mul, mul_one]

/-- The rotation of `Sⁿ⁺¹` by angle `1` in the plane of the last two coordinates. -/
noncomputable def c5_rho (n : ℕ) : specialOrthogonalGroup (Fin (n + 1 + 1)) ℝ :=
  ⟨c5_blk (k := n) (l := 2) 1 (c5_R 1), c5_blk_mem (one_mem _) (c5_R_mem 1)⟩

theorem c5_rho_pow (n k : ℕ) :
    ((c5_rho n ^ k : specialOrthogonalGroup (Fin (n + 1 + 1)) ℝ) : Matrix _ _ ℝ) =
      c5_blk (k := n) (l := 2) 1 (c5_R k) := by
  induction k with
  | zero =>
    simp only [pow_zero, OneMemClass.coe_one, Nat.cast_zero]
    rw [show c5_R 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [c5_R]]
    exact (c5_blk_one (k := n) (l := 2)).symm
  | succ k ih =>
    rw [pow_succ, MulMemClass.coe_mul, ih]
    change c5_blk 1 (c5_R k) * c5_blk 1 (c5_R 1) = _
    rw [c5_blk_mul, c5_R_mul, mul_one]
    push_cast; rfl

/-- The first `n + 1` coordinates of a point of `Sⁿ⁺¹`. -/
noncomputable def c5_p {n : ℕ} (y : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => y.1.ofLp (Fin.castSucc i))

theorem c5_default_mem (n : ℕ) :
    (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) ∈ Sphere n := by
  simp [Sphere]

/-- The radial projection `Sⁿ⁺¹ ∖ {poles} → Sⁿ`. -/
noncomputable def c5_pi {n : ℕ} (y : Sphere (n + 1)) : Sphere n := by
  classical
  exact if h : c5_p y ≠ 0 then ⟨‖c5_p y‖⁻¹ • c5_p y, by
      simp only [Sphere, mem_sphere_zero_iff_norm]; exact norm_smul_inv_norm h⟩
    else ⟨_, c5_default_mem n⟩

theorem c5_pi_of_ne {n : ℕ} (y : Sphere (n + 1)) (h : c5_p y ≠ 0) :
    (c5_pi y : EuclideanSpace ℝ (Fin (n + 1))) = ‖c5_p y‖⁻¹ • c5_p y := by
  simp [c5_pi, h]

theorem c5_p_phi {n : ℕ} (A : specialOrthogonalGroup (Fin (n + 1)) ℝ) (y : Sphere (n + 1)) :
    c5_p (c5_phi n A • y) = WithLp.toLp 2 ((A : Matrix _ _ ℝ) *ᵥ (c5_p y).ofLp) := by
  ext i
  change ((c5_blk (A : Matrix _ _ ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ y.1.ofLp)
    (Fin.castAdd 1 i) = _
  rw [(c5_blk_mulVec _ _ _).1]
  rfl

theorem c5_norm_p_phi {n : ℕ} (A : specialOrthogonalGroup (Fin (n + 1)) ℝ) (y : Sphere (n + 1)) :
    ‖c5_p (c5_phi n A • y)‖ = ‖c5_p y‖ := by
  rw [c5_p_phi]
  exact norm_toLp_mulVec_of_mem_orthogonalGroup
    (mem_specialOrthogonalGroup_iff.mp A.2).1 _

theorem c5_pi_phi {n : ℕ} (A : specialOrthogonalGroup (Fin (n + 1)) ℝ) (y : Sphere (n + 1))
    (h : c5_p y ≠ 0) : c5_pi (c5_phi n A • y) = A • c5_pi y := by
  have h' : c5_p (c5_phi n A • y) ≠ 0 := by
    rw [← norm_ne_zero_iff, c5_norm_p_phi, norm_ne_zero_iff]; exact h
  apply Subtype.ext
  rw [c5_pi_of_ne _ h', c5_norm_p_phi]
  change _ = WithLp.toLp 2 ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ (c5_pi y).1.ofLp)
  rw [c5_pi_of_ne _ h, c5_p_phi]
  ext i
  simp [Matrix.mulVec_smul]

theorem c5_last_ne_zero {n : ℕ} (y : Sphere (n + 1)) (h : c5_p y = 0) :
    y.1.ofLp (Fin.last (n + 1)) ≠ 0 := by
  intro hl
  have hy := y.2
  simp only [Sphere, mem_sphere_zero_iff_norm] at hy
  have hc : ∀ i : Fin (n + 1), y.1.ofLp (Fin.castSucc i) = 0 := fun i => by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v.ofLp i) h
    simpa [c5_p] using this
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc] at hy
  simp [hc, hl] at hy

theorem c5_disjoint_rho (n k : ℕ) (hk : 0 < k) :
    Disjoint ((c5_rho n ^ k) • {y : Sphere (n + 1) | c5_p y = 0}) {y | c5_p y = 0} := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ hz
  have hy' : c5_p y = 0 := hy
  have hz' : c5_p ((c5_rho n ^ k) • y) = 0 := hz
  have hcoord : ∀ w : Sphere (n + 1), c5_p w = 0 → w.1.ofLp (Fin.natAdd n (0 : Fin 2)) = 0 := by
    intro w hw
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v.ofLp (Fin.last n)) hw
    have e : (Fin.natAdd n (0 : Fin 2) : Fin (n + 1 + 1)) = Fin.castSucc (Fin.last n) :=
      Fin.ext (by simp)
    rw [e]
    simpa [c5_p] using this
  have h1 := hcoord _ hz'
  change ((((c5_rho n ^ k : specialOrthogonalGroup (Fin (n + 1 + 1)) ℝ)) : Matrix _ _ ℝ) *ᵥ
    y.1.ofLp) (Fin.natAdd n (0 : Fin 2)) = 0 at h1
  rw [c5_rho_pow, (c5_blk_mulVec _ _ _).2] at h1
  have h0 := hcoord _ hy'
  have hl := c5_last_ne_zero y hy'
  have e1 : (Fin.natAdd n (1 : Fin 2) : Fin (n + 1 + 1)) = Fin.last (n + 1) := Fin.ext (by simp)
  simp only [c5_R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
  simp [h0, e1] at h1
  rcases h1 with h1 | h1
  · exact c5_sin_natCast_ne_zero hk h1
  · exact hl h1

theorem c5_isParadoxical_succ (n : ℕ)
    (hp : IsParadoxical (specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n))) :
    IsParadoxical (specialOrthogonalGroup (Fin (n + 1 + 1)) ℝ)
      (Set.univ : Set (Sphere (n + 1))) := by
  let S : Set (Sphere (n + 1)) := {y | c5_p y ≠ 0}
  have hS : ∀ A : specialOrthogonalGroup (Fin (n + 1)) ℝ, ∀ y ∈ S, c5_phi n A • y ∈ S := by
    intro A y hy
    change c5_p _ ≠ 0
    rw [← norm_ne_zero_iff, c5_norm_p_phi, norm_ne_zero_iff]; exact hy
  have hsurj : ∀ x : Sphere n, ∃ y ∈ S, c5_pi y = x := by
    intro x
    have hx := x.2
    simp only [Sphere, mem_sphere_zero_iff_norm] at hx
    let v : EuclideanSpace ℝ (Fin (n + 1 + 1)) := WithLp.toLp 2 (Fin.snoc x.1.ofLp 0)
    have hv : v ∈ Sphere (n + 1) := by
      simp only [Sphere, mem_sphere_zero_iff_norm]
      rw [EuclideanSpace.norm_eq] at hx ⊢
      simpa [v, Fin.sum_univ_castSucc] using hx
    have hp : c5_p ⟨v, hv⟩ = x.1 := by
      ext i; simp [c5_p, v]
    have hne : c5_p ⟨v, hv⟩ ≠ 0 := by
      rw [hp]; intro h0; rw [h0, norm_zero] at hx; exact zero_ne_one hx
    refine ⟨⟨v, hv⟩, hne, ?_⟩
    apply Subtype.ext
    rw [c5_pi_of_ne _ hne, hp, hx, inv_one, one_smul]
  have hpS := c5_isParadoxical_pullback (c5_phi n) c5_pi S hS
    (fun A y hy => c5_pi_phi A y hy) hsurj hp
  have hSD : S = {y : Sphere (n + 1) | c5_p y = 0}ᶜ := by ext; simp [S]
  have habs := c5_equidecomposable_univ_compl (c5_rho n) _ (c5_disjoint_rho n)
  rw [← hSD] at habs
  exact c5_isParadoxical_of_equidecomposable habs hpS
theorem isParadoxical_sphere_two_and_isParadoxical_sphere'
    (h_17 : ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ)
    (h_18 : ∀ (D : Set (Sphere 2)) (hD : D.Countable),
      Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ) :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) := by
  have h2 : IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) := by
    obtain ⟨D, hD, hp⟩ := h_17
    exact c5_isParadoxical_of_equidecomposable (h_18 D hD) hp
  refine ⟨h2, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact h2
  | succ n _ ih => exact c5_isParadoxical_succ n ih

-- p. 3, after Corollary 1.9

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-- A single group element as an equidecomposition. -/
noncomputable def single {G X : Type*} [Group G] [MulAction G X] (g : G) : Equidecomp X G where
  toPartialEquiv := (MulAction.toPerm g : Equiv.Perm X).toPartialEquiv
  isDecompOn' := ⟨{g}, fun _ _ => ⟨g, Finset.mem_singleton_self _, rfl⟩⟩

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem exists_countable_isParadoxical_compl :
    ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ :=
  Garrido.exists_countable_isParadoxical_compl

theorem equidecomposable_univ_compl_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ :=
  Garrido.equidecomposable_univ_compl_of_countable D hD

theorem isParadoxical_sphere_two_and_isParadoxical_sphere :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) :=
  Garrido.BT.isParadoxical_sphere_two_and_isParadoxical_sphere'
    exists_countable_isParadoxical_compl equidecomposable_univ_compl_of_countable

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) :=
  Garrido.BT.Final.isParadoxical_sphere_two_and_isParadoxical_sphere
