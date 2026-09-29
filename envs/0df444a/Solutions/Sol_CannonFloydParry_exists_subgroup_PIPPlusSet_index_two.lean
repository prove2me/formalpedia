-- Prove2me | solution 1 for CannonFloydParry.exists_subgroup_PIPPlusSet_index_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:55:15.431338+00:00
-- url     : https://prove2.me/submissions/098c2ff1-f15e-47c7-ace3-2cf4d0ea0b07

import Theorems.Thm_CannonFloydParry_exists_isRationalSubdivision_refines_of_isIntegralSubdivision
import Theorems.Thm_CannonFloydParry_exists_refines_isIntegralSubdivision
import Theorems.Thm_CannonFloydParry_exists_subgroup_coe_eq_PIPSet
import Definitions.Def_CannonFloydParry_PIP
import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_T

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

lemma glAct_smul (A : GL (Fin (n + 1)) ℤ) (c : ℝ) (x : Fin (n + 1) → ℝ) :
    glAct A (c • x) = c • glAct A x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_smul]

lemma glAct_injective (A : GL (Fin (n + 1)) ℤ) : Function.Injective (glAct A) := fun x y h => by
  rw [← glAct_inv_glAct A x, h, glAct_inv_glAct]

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

/-- Key identity: `ρ (A⁻¹ ρ (A x)) = x` for `x ∈ Δₙ`. -/
lemma rho_glAct_inv_rho_glAct (A : GL (Fin (n + 1)) ℤ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ Simplex n) : rho (glAct A⁻¹ (rho (glAct A x))) = x := by
  have hs := sum_abs_pos (glAct_ne_zero A (ne_zero_of_mem hx))
  rw [rho_eq_smul (glAct A x), glAct_smul, glAct_inv_glAct, rho_smul (inv_pos.mpr hs),
    rho_of_mem hx]


end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

/-! ### Convex hulls of finite families -/

/-! ### Columns -/

/-! ### Primitive lifts -/

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

/-! ### Images of convex hulls of finite families under `ρ ∘ A` -/

lemma mem_convexHull_range_iff_fintype {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (u : ι → E) (y : E) :
    y ∈ convexHull ℝ (range u) ↔ ∃ t ∈ stdSimplex ℝ ι, ∑ j, t j • u j = y := by
  classical
  constructor
  · intro hy
    refine convexHull_min (t := {y | ∃ t ∈ stdSimplex ℝ ι, ∑ j, t j • u j = y}) ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, ?_⟩
      simp [Pi.single_apply]
    · rintro y₁ ⟨t₁, ht₁, rfl⟩ y₂ ⟨t₂, ht₂, rfl⟩ a b ha hb hab
      refine ⟨a • t₁ + b • t₂, convex_stdSimplex ℝ _ ht₁ ht₂ ha hb hab, ?_⟩
      simp [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  · rintro ⟨t, ht, rfl⟩
    exact mem_convexHull_of_exists_fintype t u ht.1 ht.2 (fun j => mem_range_self j) rfl

lemma exists_pos_of_mem_stdSimplex {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ stdSimplex ℝ ι) : ∃ j, 0 < t j := by
  by_contra h
  push Not at h
  have : ∑ j, t j ≤ 0 := Finset.sum_nonpos fun j _ => h j
  rw [ht.2] at this
  norm_num at this

lemma glAct_sum {ι : Type*} (A : GL (Fin (n + 1)) ℤ) (s : Finset ι) (t : ι → ℝ)
    (p : ι → Fin (n + 1) → ℝ) :
    glAct A (∑ j ∈ s, t j • p j) = ∑ j ∈ s, t j • glAct A (p j) := by
  simp only [glAct_eq, Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma glAct_mul (A B : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct (A * B) x = glAct A (glAct B x) := by
  rw [glAct_eq, glAct_eq, glAct_eq, Units.val_mul, rM_mul, Matrix.mulVec_mulVec]

lemma image_convexHull_rho_glAct {ι : Type*} [Fintype ι] (A : GL (Fin (n + 1)) ℤ)
    (p : ι → Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Simplex n)
    (hA : ∀ x ∈ convexHull ℝ (range p), ∀ i, 0 ≤ glAct A x i) :
    (fun x => rho (glAct A x)) '' convexHull ℝ (range p) =
      convexHull ℝ (range fun j => rho (glAct A (p j))) := by
  set c := fun j => glAct A (p j) with hc
  set u := fun j => rho (c j) with hu
  have hcne : ∀ j, c j ≠ 0 := fun j => glAct_ne_zero A (ne_zero_of_mem (hp j))
  have hcnn : ∀ j i, 0 ≤ c j i := fun j i =>
    hA (p j) (subset_convexHull ℝ _ (mem_range_self j)) i
  have hs : ∀ j, 0 < ∑ i, |c j i| := fun j => sum_abs_pos (hcne j)
  have hcu : ∀ j, c j = (∑ i, |c j i|) • u j := fun j => by
    simp only [hu, rho_eq_smul, smul_smul, mul_inv_cancel₀ (hs j).ne', one_smul]
  have humem : ∀ j, u j ∈ Simplex n := fun j => rho_mem (hcnn j) (hcne j)
  have hsub : convexHull ℝ (range u) ⊆ Simplex n :=
    convexHull_min (by rintro _ ⟨j, rfl⟩; exact humem j) (convex_stdSimplex ℝ _)
  have hsubp : convexHull ℝ (range p) ⊆ Simplex n :=
    convexHull_min (by rintro _ ⟨j, rfl⟩; exact hp j) (convex_stdSimplex ℝ _)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_convexHull_range_iff_fintype p x).1 hx
    set T := ∑ j, t j * ∑ i, |c j i| with hT
    have hTpos : 0 < T := by
      obtain ⟨j, hj⟩ := exists_pos_of_mem_stdSimplex ht
      exact Finset.sum_pos' (fun k _ => mul_nonneg (ht.1 k) (hs k).le)
        ⟨j, Finset.mem_univ _, mul_pos hj (hs j)⟩
    have hAx : glAct A (∑ j, t j • p j) = T • ∑ j, (T⁻¹ * (t j * ∑ i, |c j i|)) • u j := by
      rw [glAct_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hTpos.ne', one_mul, ← smul_smul]
      show t j • c j = _
      rw [← hcu]
    have hmem : ∑ j, (T⁻¹ * (t j * ∑ i, |c j i|)) • u j ∈ convexHull ℝ (range u) := by
      refine mem_convexHull_of_exists_fintype _ u (fun j => ?_) ?_ (fun j => mem_range_self j) rfl
      · exact mul_nonneg (inv_nonneg.mpr hTpos.le) (mul_nonneg (ht.1 j) (hs j).le)
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hTpos.ne']
    show rho (glAct A _) ∈ _
    rw [hAx, rho_smul hTpos, rho_of_mem (hsub hmem)]
    exact hmem
  · intro hy
    obtain ⟨t, ht, rfl⟩ := (mem_convexHull_range_iff_fintype u y).1 hy
    set x' : _ → ℝ := fun j => t j / ∑ i, |c j i| with hx'
    set N := ∑ j, x' j with hN
    have hNpos : 0 < N := by
      obtain ⟨j, hj⟩ := exists_pos_of_mem_stdSimplex ht
      exact Finset.sum_pos' (fun k _ => div_nonneg (ht.1 k) (hs k).le)
        ⟨j, Finset.mem_univ _, div_pos hj (hs j)⟩
    have hxmem : ∑ j, (N⁻¹ * x' j) • p j ∈ convexHull ℝ (range p) := by
      refine mem_convexHull_of_exists_fintype _ p (fun j => ?_) ?_ (fun j => mem_range_self j) rfl
      · exact mul_nonneg (inv_nonneg.mpr hNpos.le) (div_nonneg (ht.1 j) (hs j).le)
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hNpos.ne']
    refine ⟨_, hxmem, ?_⟩
    have hmem := (mem_convexHull_range_iff_fintype u _).2 ⟨t, ht, rfl⟩
    have : ∑ j, (N⁻¹ * x' j) • p j = N⁻¹ • ∑ j, x' j • p j := by
      rw [Finset.smul_sum]; simp only [smul_smul]
    show rho (glAct A _) = _
    rw [this, glAct_smul, rho_smul (inv_pos.mpr hNpos), glAct_sum]
    have : ∑ j, x' j • glAct A (p j) = ∑ j, t j • u j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      show x' j • c j = _
      rw [hcu j, smul_smul, hx', div_mul_cancel₀ _ (hs j).ne']
    rw [this, rho_of_mem (hsub hmem)]

lemma affineIndependent_rho_glAct {ι : Type*} (A : GL (Fin (n + 1)) ℤ)
    (p : ι → Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Simplex n) (hind : AffineIndependent ℝ p) :
    AffineIndependent ℝ (fun j => rho (glAct A (p j))) := by
  rw [affineIndependent_iff] at hind ⊢
  intro s w hw0 hw1
  set c := fun j => glAct A (p j)
  have hs : ∀ j, 0 < ∑ i, |c j i| := fun j => sum_abs_pos (glAct_ne_zero A (ne_zero_of_mem (hp j)))
  have h1 : glAct A (∑ e ∈ s, (w e * (∑ i, |c e i|)⁻¹) • p e) = 0 := by
    rw [glAct_sum, ← hw1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rho_eq_smul, smul_smul]
  have h2 : ∑ e ∈ s, (w e * (∑ i, |c e i|)⁻¹) • p e = 0 := by
    apply glAct_injective A
    rw [h1, glAct_eq, Matrix.mulVec_zero]
  have h3 : ∑ e ∈ s, w e * (∑ i, |c e i|)⁻¹ = 0 := by
    have := congrArg (fun z : Fin (n + 1) → ℝ => ∑ i, z i) h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Finset.sum_const_zero] at this
    rw [Finset.sum_comm] at this
    simpa [← Finset.mul_sum, (hp _).2] using this
  intro e he
  have := hind s _ h3 h2 e he
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (inv_ne_zero (hs e).ne')

/-! ### The inverse of a PIP homeomorphism is PIP -/


end CannonFloydParry.S7

/-!
# PIP(Δₙ) is closed under composition and inverses (reduction to the two refinement results)
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

open Classical in
/-- The extension of a homeomorphism of `Δₙ` to the ambient space (the identity off `Δₙ`). -/
noncomputable def extF (f : Simplex n ≃ₜ Simplex n) (y : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  if h : y ∈ Simplex n then (f ⟨y, h⟩ : Fin (n + 1) → ℝ) else y

lemma extF_apply (f : Simplex n ≃ₜ Simplex n) (x : Simplex n) :
    extF f (x : Fin (n + 1) → ℝ) = f x := dif_pos x.2

lemma extF_injOn (f : Simplex n ≃ₜ Simplex n) : InjOn (extF f) (Simplex n) := by
  intro x hx y hy h
  have h' : (f ⟨x, hx⟩ : Fin (n + 1) → ℝ) = f ⟨y, hy⟩ := by
    rw [← extF_apply f ⟨x, hx⟩, ← extF_apply f ⟨y, hy⟩]; exact h
  have := f.injective (Subtype.ext h')
  exact congrArg Subtype.val this

lemma IsIntegralProjectiveVia.mono' {A : GL (Fin (n + 1)) ℤ} {U U' : Set (Simplex n)}
    {f : Simplex n → Simplex n} (h : IsIntegralProjectiveVia A U f) (hU : U' ⊆ U) :
    IsIntegralProjectiveVia A U' f := fun x hx => h x (hU hx)

/-- Composition of integral projective maps. -/
lemma IsIntegralProjectiveVia.comp' {A B : GL (Fin (n + 1)) ℤ} {U V : Set (Simplex n)}
    {f g h : Simplex n → Simplex n}
    (hg : IsIntegralProjectiveVia B U g) (hUV : ∀ x ∈ U, g x ∈ V)
    (hf : IsIntegralProjectiveVia A V f) (hh : ∀ x, h x = f (g x)) :
    IsIntegralProjectiveVia (A * B) U h := by
  intro x hx
  have hBx := hg x hx
  have hne := glAct_ne_zero B (ne_zero_of_mem x.2)
  have hsB := sum_abs_pos hne
  have hdecomp : glAct B x = (∑ i, |glAct B x i|) • (g x : Fin (n + 1) → ℝ) := by
    rw [hBx.2, rho_eq_smul, smul_smul, mul_inv_cancel₀, one_smul]
    exact hsB.ne'
  have hAg := hf (g x) (hUV x hx)
  rw [glAct_mul, hdecomp, glAct_smul, hh]
  refine ⟨fun i => mul_nonneg hsB.le (hAg.1 i), ?_⟩
  exact hAg.2.trans (rho_smul hsB _).symm

/-- The image complex of a subdivision under a homeomorphism that is integral projective on each
face. -/
theorem exists_imageComplex (f : Simplex n ≃ₜ Simplex n)
    (S : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hS : IsSubdivision n S)
    (hproj : ∀ σ ∈ S.faces,
      IsIntegralProjective {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f) :
    ∃ S' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      S'.faces = (fun σ => σ.image (extF f)) '' S.faces ∧ IsSubdivision n S' ∧
      (∀ σ ∈ S.faces, extF f '' convexHull ℝ ↑σ = convexHull ℝ ↑(σ.image (extF f))) ∧
      ((∀ σ ∈ S.faces, σ.card = n + 1 → IsIntegralSubsimplex n (convexHull ℝ ↑σ)) →
        IsIntegralSubdivision n S') := by
  classical
  obtain ⟨hfin, hspace⟩ := hS
  choose A hA using hproj
  set F := extF f with hFdef
  have hF : ∀ x : Simplex n, F x = f x := fun x => extF_apply f x
  have hFinj : InjOn F (Simplex n) := extF_injOn f
  have hhull : ∀ σ ∈ S.faces, convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    fun σ hσ => hspace ▸ S.convexHull_subset_space hσ
  have hpts : ∀ σ ∈ S.faces, (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    fun σ hσ => (subset_convexHull ℝ _).trans (hhull σ hσ)
  have hFA : ∀ σ (hσ : σ ∈ S.faces), ∀ x ∈ convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)),
      (∀ i, 0 ≤ glAct (A σ hσ) x i) ∧ F x = rho (glAct (A σ hσ) x) := by
    intro σ hσ x hx
    have := hA σ hσ ⟨x, hhull σ hσ hx⟩ hx
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [← hF] at h2
    exact h2
  have hrange : ∀ τ : Finset (Fin (n + 1) → ℝ),
      range (fun p : τ => (p : Fin (n + 1) → ℝ)) = (τ : Set (Fin (n + 1) → ℝ)) :=
    fun τ => Subtype.range_coe
  have himg : ∀ σ (hσ : σ ∈ S.faces), ∀ τ ⊆ σ,
      F '' convexHull ℝ (τ : Set (Fin (n + 1) → ℝ)) =
        convexHull ℝ ((τ.image F : Finset _) : Set (Fin (n + 1) → ℝ)) := by
    intro σ hσ τ hτ
    have hτσ : convexHull ℝ (τ : Set (Fin (n + 1) → ℝ)) ⊆ convexHull ℝ σ :=
      convexHull_mono (by exact_mod_cast hτ)
    have heq : EqOn F (fun x => rho (glAct (A σ hσ) x)) (convexHull ℝ (τ : Set _)) :=
      fun x hx => (hFA σ hσ x (hτσ hx)).2
    rw [heq.image_eq, ← hrange τ, image_convexHull_rho_glAct]
    · congr 1
      rw [Finset.coe_image, ← hrange τ, ← range_comp]
      apply congrArg
      funext p
      exact ((hFA σ hσ p (hτσ (subset_convexHull ℝ _ p.2))).2).symm
    · exact fun p => hpts σ hσ (hτ p.2)
    · intro x hx
      rw [hrange τ] at hx
      exact (hFA σ hσ x (hτσ hx)).1
  let faces' : Set (Finset (Fin (n + 1) → ℝ)) := (fun σ => σ.image F) '' S.faces
  let S' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) :=
    { faces := faces'
      isRelLowerSet_faces := by
        rintro _ ⟨σ, hσ, rfl⟩
        refine ⟨(S.nonempty_of_mem_faces hσ).image F, ?_⟩
        intro b hb hbne
        refine ⟨σ.filter (fun p => F p ∈ b), S.down_closed hσ (Finset.filter_subset _ _) ?_, ?_⟩
        · obtain ⟨y, hy⟩ := hbne
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hb hy)
          exact ⟨p, Finset.mem_filter.2 ⟨hp, hy⟩⟩
        · ext y
          simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨p, ⟨_, hp⟩, rfl⟩; exact hp
          · intro hy
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hb hy)
            exact ⟨p, ⟨hp, hy⟩, rfl⟩
      indep := by
        rintro _ ⟨σ, hσ, rfl⟩
        let e : σ ≃ (σ.image F : Finset _) := Equiv.ofBijective
          (fun p => ⟨F p, Finset.mem_image_of_mem F p.2⟩)
          ⟨fun p q h => Subtype.ext (hFinj (hpts σ hσ p.2) (hpts σ hσ q.2)
              (congrArg Subtype.val h)),
            fun y => by
              obtain ⟨p, hp, hpy⟩ := Finset.mem_image.1 y.2
              exact ⟨⟨p, hp⟩, Subtype.ext hpy⟩⟩
        rw [← affineIndependent_equiv e]
        have : (((↑) : {y // y ∈ Finset.image F σ} → Fin (n + 1) → ℝ) ∘ e) =
            fun p : σ => rho (glAct (A σ hσ) (p : Fin (n + 1) → ℝ)) := by
          funext p
          exact (hFA σ hσ p (subset_convexHull ℝ _ p.2)).2
        rw [this]
        exact affineIndependent_rho_glAct _ _ (fun p => hpts σ hσ p.2) (S.indep hσ)
      inter_subset_convexHull := by
        rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
        rw [← himg σ hσ σ le_rfl, ← himg τ hτ τ le_rfl,
          ← hFinj.image_inter (hhull σ hσ) (hhull τ hτ)]
        have hsub : convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ∩ convexHull ℝ τ ⊆
            convexHull ℝ ((σ ∩ τ : Finset _) : Set (Fin (n + 1) → ℝ)) := by
          rw [Finset.coe_inter]; exact S.inter_subset_convexHull hσ hτ
        refine (image_mono hsub).trans ?_
        rw [himg σ hσ (σ ∩ τ) Finset.inter_subset_left,
          Finset.image_inter_of_injOn σ τ (hFinj.mono (by
            exact union_subset (hpts σ hσ) (hpts τ hτ))), Finset.coe_inter] }
  have hspace' : S'.space = Simplex n := by
    ext y
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨_, ⟨σ, hσ, rfl⟩, hy⟩
      rw [← himg σ hσ σ le_rfl] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [show x = ((⟨x, hhull σ hσ hx⟩ : Simplex n) : Fin (n + 1) → ℝ) from rfl, hF]
      exact (f _).2
    · intro hy
      set x := f.symm ⟨y, hy⟩
      have hx : (x : Fin (n + 1) → ℝ) ∈ S.space := by rw [hspace]; exact x.2
      obtain ⟨σ, hσ, hxσ⟩ := (Geometry.SimplicialComplex.mem_space_iff).1 hx
      refine ⟨σ.image F, ⟨σ, hσ, rfl⟩, ?_⟩
      rw [← himg σ hσ σ le_rfl]
      refine ⟨x, hxσ, ?_⟩
      rw [hF]
      show ((f (f.symm ⟨y, hy⟩) : Simplex n) : Fin (n + 1) → ℝ) = y
      rw [Homeomorph.apply_symm_apply]
      rfl
  refine ⟨S', rfl, ⟨hfin.image _, hspace'⟩, fun σ hσ => himg σ hσ σ le_rfl, fun hint => ?_⟩
  refine ⟨⟨hfin.image _, hspace'⟩, ?_⟩
  rintro _ ⟨σ, hσ, rfl⟩ hcard
  have hcσ : σ.card = n + 1 := by
    have := Finset.card_image_of_injOn (s := σ) (hFinj.mono (hpts σ hσ))
    rw [this] at hcard
    exact hcard
  obtain ⟨g, ⟨B, hB⟩, hg⟩ := hint σ hσ hcσ
  have hgmem : ∀ x, (g x : Fin (n + 1) → ℝ) ∈ convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) :=
    fun x => hg ▸ mem_range_self x
  refine ⟨fun x => f (g x), ⟨A σ hσ * B, fun x _ => ?_⟩, ?_⟩
  · have hBx := hB x (mem_univ _)
    have hne := glAct_ne_zero B (ne_zero_of_mem x.2)
    have hsB := sum_abs_pos hne
    have hdecomp : glAct B x = (∑ i, |glAct B x i|) • (g x : Fin (n + 1) → ℝ) := by
      rw [hBx.2, rho_eq_smul, smul_smul, mul_inv_cancel₀, one_smul]
      exact hsB.ne'
    have hAg := hFA σ hσ _ (hgmem x)
    rw [glAct_mul, hdecomp, glAct_smul]
    refine ⟨fun i => mul_nonneg hsB.le (hAg.1 i), ?_⟩
    rw [rho_smul, ← hAg.2, hF]
    exact hsB
  · rw [← himg σ hσ σ le_rfl, ← hg, ← range_comp]
    ext y
    simp only [mem_range, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, hF (g x)⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, (hF (g x)).symm⟩

/-- On the image of a face, the inverse is integral projective via the inverse matrix, and maps
back into the face. -/
lemma symm_via_image (f : Simplex n ≃ₜ Simplex n) {σ : Finset (Fin (n + 1) → ℝ)}
    (hσ : convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n) {A : GL (Fin (n + 1)) ℤ}
    (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f)
    (himg : extF f '' convexHull ℝ ↑σ = convexHull ℝ ↑(σ.image (extF f))) :
    IsIntegralProjectiveVia A⁻¹
        {y : Simplex n | (y : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑(σ.image (extF f))} f.symm ∧
      ∀ y : Simplex n, (y : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑(σ.image (extF f)) →
        (f.symm y : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ := by
  have key : ∀ y : Simplex n, (y : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑(σ.image (extF f)) →
      ∃ x ∈ convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)), ∃ hxs : x ∈ Simplex n,
        f.symm y = ⟨x, hxs⟩ ∧ (y : Fin (n + 1) → ℝ) = rho (glAct A x) ∧
          ∀ i, 0 ≤ glAct A x i := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxs := hσ hx
    have hfx : f ⟨x, hxs⟩ = y := by
      apply Subtype.ext
      exact (extF_apply f ⟨x, hxs⟩).symm.trans hxy
    have hsymm : f.symm y = ⟨x, hxs⟩ := by rw [← hfx, Homeomorph.symm_apply_apply]
    have hAx := hA ⟨x, hxs⟩ hx
    refine ⟨x, hx, hxs, hsymm, ?_, hAx.1⟩
    rw [← hfx]
    exact hAx.2
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxs, hsymm, hyx, hnn⟩ := key y hy
    have hne := glAct_ne_zero A (ne_zero_of_mem hxs)
    have hsA := sum_abs_pos hne
    rw [hsymm]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hyx, rho_eq_smul, glAct_smul, glAct_inv_glAct]
      exact mul_nonneg (inv_nonneg.mpr hsA.le) (hxs.1 i)
    · show x = _
      rw [hyx, rho_glAct_inv_rho_glAct _ hxs]
  · obtain ⟨x, hx, hxs, hsymm, -, -⟩ := key y hy
    rw [hsymm]
    exact hx

/-! ### PIP with a constraint on the matrices -/

/-- `f` is PIP with all matrices satisfying `P`. -/
def IsPIPW (P : GL (Fin (n + 1)) ℤ → Prop) (f : Simplex n ≃ₜ Simplex n) : Prop :=
  ∃ S, IsIntegralSubdivision n S ∧ ∀ σ ∈ S.faces, ∃ A, P A ∧
    IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f

lemma isPIP_iff_isPIPW (f : Simplex n ≃ₜ Simplex n) : IsPIP f ↔ IsPIPW (fun _ => True) f := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact ⟨S, hS, fun σ hσ => by obtain ⟨A, hA⟩ := h σ hσ; exact ⟨A, trivial, hA⟩⟩
  · rintro ⟨S, hS, h⟩
    exact ⟨S, hS, fun σ hσ => by obtain ⟨A, -, hA⟩ := h σ hσ; exact ⟨A, hA⟩⟩

lemma isPIPPlus_iff_isPIPW (f : Simplex n ≃ₜ Simplex n) :
    IsPIPPlus f ↔ IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1) f :=
  Iff.rfl

lemma IsPIPW.mono {P Q : GL (Fin (n + 1)) ℤ → Prop} {f : Simplex n ≃ₜ Simplex n}
    (h : IsPIPW P f) (hPQ : ∀ A, P A → Q A) : IsPIPW Q f := by
  obtain ⟨S, hS, h⟩ := h
  exact ⟨S, hS, fun σ hσ => by obtain ⟨A, hP, hA⟩ := h σ hσ; exact ⟨A, hPQ A hP, hA⟩⟩

lemma IsPIPW.symm {P : GL (Fin (n + 1)) ℤ → Prop} {f : Simplex n ≃ₜ Simplex n}
    (h : IsPIPW P f) : IsPIPW (fun B => P B⁻¹) f.symm := by
  obtain ⟨S, hS, hA⟩ := h
  choose A hPA hA using hA
  obtain ⟨S', hfaces, -, himg, hint⟩ :=
    exists_imageComplex f S hS.1 fun σ hσ => ⟨A σ hσ, hA σ hσ⟩
  refine ⟨S', hint hS.2, ?_⟩
  rw [hfaces]
  rintro _ ⟨σ, hσ, rfl⟩
  have hhull : convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hS.1.2 ▸ S.convexHull_subset_space hσ
  refine ⟨(A σ hσ)⁻¹, by show P (A σ hσ)⁻¹⁻¹; rw [inv_inv]; exact hPA σ hσ, ?_⟩
  exact (symm_via_image f hhull (hA σ hσ) (himg σ hσ)).1

/-- Composition, assuming the two refinement results. -/
lemma IsPIPW.mul
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    {P Q : GL (Fin (n + 1)) ℤ → Prop} {f g : Simplex n ≃ₜ Simplex n}
    (hf : IsPIPW P f) (hg : IsPIPW Q g) :
    IsPIPW (fun C => ∃ A B, P A ∧ Q B ∧ C = A * B) (f * g) := by
  obtain ⟨T, hT, hTm⟩ := hg.symm
  obtain ⟨S, hS, hSm⟩ := hf
  obtain ⟨K, hKrat, hKT, hKS⟩ := hRS hT hS
  obtain ⟨K', hK'K, hK'⟩ := h71 hKrat
  have hsub : ∀ κ ∈ K'.faces, (∃ t ∈ T.faces, convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) ⊆
      convexHull ℝ ↑t) ∧ ∃ σ ∈ S.faces, convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) ⊆
      convexHull ℝ ↑σ := by
    intro κ hκ
    obtain ⟨k, hk, hκk⟩ := hK'K.2 κ hκ
    obtain ⟨t, ht, hkt⟩ := hKT.2 k hk
    obtain ⟨σ, hσ, hkσ⟩ := hKS.2 k hk
    exact ⟨⟨t, ht, hκk.trans hkt⟩, ⟨σ, hσ, hκk.trans hkσ⟩⟩
  have hC : ∀ κ ∈ K'.faces, ∃ C : GL (Fin (n + 1)) ℤ, Q C⁻¹ ∧
      IsIntegralProjectiveVia C {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑κ}
        g.symm := by
    intro κ hκ
    obtain ⟨⟨t, ht, hκt⟩, -⟩ := hsub κ hκ
    obtain ⟨C, hQ, hCv⟩ := hTm t ht
    exact ⟨C, hQ, IsIntegralProjectiveVia.mono' hCv fun x hx => hκt hx⟩
  choose C hQC hCv using hC
  obtain ⟨S', hfaces, -, himg, hint⟩ :=
    exists_imageComplex g.symm K' hK'.1 fun κ hκ => ⟨C κ hκ, hCv κ hκ⟩
  refine ⟨S', hint hK'.2, ?_⟩
  rw [hfaces]
  rintro _ ⟨κ, hκ, rfl⟩
  have hhull : convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hK'.1.2 ▸ K'.convexHull_subset_space hκ
  obtain ⟨hv, hmaps⟩ := symm_via_image g.symm hhull (hCv κ hκ) (himg κ hκ)
  rw [Homeomorph.symm_symm] at hv hmaps
  obtain ⟨-, σ, hσ, hκσ⟩ := hsub κ hκ
  obtain ⟨A, hPA, hAv⟩ := hSm σ hσ
  refine ⟨A * (C κ hκ)⁻¹, ⟨A, (C κ hκ)⁻¹, hPA, hQC κ hκ, rfl⟩, ?_⟩
  exact IsIntegralProjectiveVia.comp' hv (fun y hy => hκσ (hmaps y hy)) hAv fun x => rfl

end CannonFloydParry.S7

/-!
# The trivial subdivision, coordinate permutations, and genericity
-/

namespace CannonFloydParry.S7

open Matrix Set MeasureTheory

variable {n : ℕ}

/-! ### The trivial subdivision -/

/-- The standard vertices of `Δₙ`. -/
def stdV (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℝ := fun j => if i = j then 1 else 0

lemma stdV_eq (n : ℕ) : stdV n = fun i => Pi.single i (1 : ℝ) := by
  funext i j
  simp [stdV, Pi.single_apply, eq_comm]

lemma stdV_linearIndependent (n : ℕ) : LinearIndependent ℝ (stdV n) := by
  rw [stdV_eq]; exact Pi.linearIndependent_single_one _ _

lemma stdV_injective (n : ℕ) : Function.Injective (stdV n) :=
  (stdV_linearIndependent n).injective

/-- The vertex set of `Δₙ`. -/
noncomputable def E0 (n : ℕ) : Finset (Fin (n + 1) → ℝ) := Finset.univ.image (stdV n)

lemma coe_E0 (n : ℕ) : ((E0 n : Finset _) : Set (Fin (n + 1) → ℝ)) = range (stdV n) := by
  simp [E0]

lemma card_E0 (n : ℕ) : (E0 n).card = n + 1 := by
  rw [E0, Finset.card_image_of_injective _ (stdV_injective n)]; simp

lemma E0_indep (n : ℕ) :
    AffineIndependent ℝ ((↑) : ((E0 n : Finset _) : Set (Fin (n + 1) → ℝ)) → Fin (n + 1) → ℝ) := by
  have h := ((stdV_linearIndependent n).affineIndependent ℝ).range
  rw [coe_E0]
  exact h

lemma convexHull_E0 (n : ℕ) :
    convexHull ℝ ((E0 n : Finset _) : Set (Fin (n + 1) → ℝ)) = Simplex n := by
  rw [coe_E0]
  exact convexHull_basis_eq_stdSimplex ℝ _

/-- The trivial subdivision of `Δₙ`: all faces of `Δₙ` itself. -/
noncomputable def trivCx (n : ℕ) : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) where
  faces := {s | s.Nonempty ∧ s ⊆ E0 n}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun b hb hbne => ⟨hbne, hb.trans hs.2⟩⟩
  indep := fun {s} hs => (E0_indep n).mono (Finset.coe_subset.2 hs.2)
  inter_subset_convexHull := fun {s t} hs ht => by
    rw [← AffineIndependent.convexHull_inter (s := E0 n) (E0_indep n) hs.2 ht.2]

lemma via_one (U : Set (Simplex n)) :
    IsIntegralProjectiveVia (1 : GL (Fin (n + 1)) ℤ) U id := by
  intro x _
  have h1 : glAct (1 : GL (Fin (n + 1)) ℤ) x = x := by
    rw [glAct_eq, Units.val_one, rM_one, Matrix.one_mulVec]
  rw [h1]
  exact ⟨fun i => x.2.1 i, (rho_of_mem x.2).symm⟩

lemma isIntegralSubsimplex_simplex (n : ℕ) : IsIntegralSubsimplex n (Simplex n) :=
  ⟨id, ⟨1, via_one _⟩, Subtype.range_coe⟩

lemma trivCx_isIntegral (n : ℕ) : IsIntegralSubdivision n (trivCx n) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (E0 n).powerset.finite_toSet.subset ?_
    intro s hs
    exact Finset.mem_coe.2 (Finset.mem_powerset.2 hs.2)
  · ext x
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [← convexHull_E0]
      exact convexHull_mono (Finset.coe_subset.2 hs.2) hx
    · intro hx
      refine ⟨E0 n, ⟨Finset.univ_nonempty.image _, subset_rfl⟩, ?_⟩
      rw [convexHull_E0]; exact hx
  · intro s hs hcard
    have : s = E0 n := Finset.eq_of_subset_of_card_le hs.2 (by rw [card_E0, hcard])
    rw [this, convexHull_E0]
    exact isIntegralSubsimplex_simplex n

lemma isPIPW_one {P : GL (Fin (n + 1)) ℤ → Prop} (hP : P 1) :
    IsPIPW P (1 : Simplex n ≃ₜ Simplex n) :=
  ⟨trivCx n, trivCx_isIntegral n, fun _ _ => ⟨1, hP, via_one _⟩⟩

/-! ### Coordinate permutations -/

lemma perm_mem (π : Equiv.Perm (Fin (n + 1))) {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) :
    x ∘ π ∈ Simplex n :=
  ⟨fun i => hx.1 (π i), by rw [← hx.2]; exact Equiv.sum_comp π x⟩

/-- The homeomorphism of `Δₙ` permuting coordinates. -/
def permH (π : Equiv.Perm (Fin (n + 1))) : Simplex n ≃ₜ Simplex n where
  toFun x := ⟨x.1 ∘ π, perm_mem π x.2⟩
  invFun x := ⟨x.1 ∘ π.symm, perm_mem π.symm x.2⟩
  left_inv x := Subtype.ext (funext fun i => by
    show x.1 (π (π.symm i)) = x.1 i
    rw [Equiv.apply_symm_apply])
  right_inv x := Subtype.ext (funext fun i => by
    show x.1 (π.symm (π i)) = x.1 i
    rw [Equiv.symm_apply_apply])
  continuous_toFun := (show Continuous fun x : Simplex n => x.1 ∘ π from
    continuous_pi fun i => (continuous_apply (π i)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (show Continuous fun x : Simplex n => x.1 ∘ π.symm from
    continuous_pi fun i => (continuous_apply (π.symm i)).comp continuous_subtype_val).subtype_mk _

lemma permH_apply (π : Equiv.Perm (Fin (n + 1))) (x : Simplex n) :
    ((permH π x : Simplex n) : Fin (n + 1) → ℝ) = (x : Fin (n + 1) → ℝ) ∘ π := rfl

lemma permMatrix_mul_inv (π : Equiv.Perm (Fin (n + 1))) :
    π.permMatrix ℤ * π⁻¹.permMatrix ℤ = 1 := by
  rw [← Matrix.permMatrix_mul, inv_mul_cancel]
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]

lemma permMatrix_inv_mul (π : Equiv.Perm (Fin (n + 1))) :
    π⁻¹.permMatrix ℤ * π.permMatrix ℤ = 1 := by
  rw [← Matrix.permMatrix_mul, mul_inv_cancel]
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]

/-- The permutation matrix, as an element of `GL(n+1, ℤ)`. -/
def permGL (π : Equiv.Perm (Fin (n + 1))) : GL (Fin (n + 1)) ℤ :=
  ⟨π.permMatrix ℤ, π⁻¹.permMatrix ℤ, permMatrix_mul_inv π, permMatrix_inv_mul π⟩

lemma glAct_permGL (π : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℝ) :
    glAct (permGL π) x = x ∘ π := by
  rw [glAct_eq]
  have : rM ((permGL π : GL (Fin (n + 1)) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) =
      π.permMatrix ℝ := by
    ext i j
    simp [permGL, rM, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [this, Matrix.permMatrix_mulVec]

lemma det_permGL (π : Equiv.Perm (Fin (n + 1))) :
    ((permGL π : GL (Fin (n + 1)) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det =
      (Equiv.Perm.sign π : ℤ) := by
  show (π.permMatrix ℤ).det = _
  simp [Matrix.det_permutation]

lemma via_permGL (π : Equiv.Perm (Fin (n + 1))) (U : Set (Simplex n)) :
    IsIntegralProjectiveVia (permGL π) U (permH π) := by
  intro x _
  rw [glAct_permGL, permH_apply]
  exact ⟨fun i => x.2.1 (π i), (rho_of_mem (perm_mem π x.2)).symm⟩

lemma isPIPW_permH {P : GL (Fin (n + 1)) ℤ → Prop} (π : Equiv.Perm (Fin (n + 1)))
    (hP : P (permGL π)) : IsPIPW P (permH π) :=
  ⟨trivCx n, trivCx_isIntegral n, fun _ _ => ⟨permGL π, hP, via_permGL π _⟩⟩

/-! ### Linear independence of faces -/

lemma sum_coord_sum {ι : Type*} (t : Finset ι) (g : ι → ℝ) (p : ι → Fin (n + 1) → ℝ)
    (hp : ∀ i ∈ t, p i ∈ Simplex n) : ∑ j, (∑ i ∈ t, g i • p i) j = ∑ i ∈ t, g i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_sum, (hp i hi).2, mul_one]

lemma linearIndependent_of_affineIndependent {ι : Type*} {p : ι → Fin (n + 1) → ℝ}
    (hp : ∀ i, p i ∈ Simplex n) (h : AffineIndependent ℝ p) : LinearIndependent ℝ p := by
  rw [linearIndependent_iff']
  intro t g hg
  rw [affineIndependent_iff] at h
  refine h t g ?_ hg
  rw [← sum_coord_sum t g p fun i _ => hp i, hg]
  simp

lemma face_linearIndependent (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ))
    (hK : K.space ⊆ Simplex n) {s : Finset (Fin (n + 1) → ℝ)} (hs : s ∈ K.faces) :
    LinearIndependent ℝ ((↑) : s → Fin (n + 1) → ℝ) :=
  linearIndependent_of_affineIndependent (fun p => hK (K.subset_space hs p.2)) (K.indep hs)

lemma face_card_le (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ))
    (hK : K.space ⊆ Simplex n) {s : Finset (Fin (n + 1) → ℝ)} (hs : s ∈ K.faces) :
    s.card ≤ n + 1 := by
  have := (face_linearIndependent K hK hs).fintype_card_le_finrank
  simpa using this

lemma span_ne_top_of_card_le {s : Finset (Fin (n + 1) → ℝ)} (hs : s.card ≤ n) :
    Submodule.span ℝ (s : Set (Fin (n + 1) → ℝ)) ≠ ⊤ := by
  intro h
  have h1 := finrank_span_finset_le_card (R := ℝ) s
  have h2 : Set.finrank ℝ (s : Set (Fin (n + 1) → ℝ)) = n + 1 := by
    rw [Set.finrank, h, finrank_top, Module.finrank_fin_fun]
  omega

lemma convexHull_subset_span' (s : Set (Fin (n + 1) → ℝ)) :
    convexHull ℝ s ⊆ Submodule.span ℝ s :=
  convexHull_min Submodule.subset_span (Submodule.convex _)

/-! ### Generic points -/

lemma exists_generic (s : Finset (Fin (n + 1) → ℝ))
    (hs : LinearIndependent ℝ ((↑) : s → Fin (n + 1) → ℝ)) (hcard : s.card = n + 1)
    (W : Set (Submodule ℝ (Fin (n + 1) → ℝ))) (hW : W.Countable) (hWt : ∀ w ∈ W, w ≠ ⊤) :
    ∃ p ∈ convexHull ℝ (s : Set (Fin (n + 1) → ℝ)), ∀ w ∈ W, p ∉ w := by
  have hne : s.Nonempty := Finset.card_pos.1 (by omega)
  have : Nonempty s := ⟨⟨_, hne.choose_spec⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [hcard])
  have hb : ∀ v : s, b v = v := fun v => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  let U : Set (Fin (n + 1) → ℝ) := ⋂ v : s, {y | 0 < b.coord v y}
  have hU : IsOpen U := isOpen_iInter_of_finite fun v =>
    isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional (b.coord v))
  have hy₀ : (∑ v : s, (1 : ℝ) • b v) ∈ U := by
    simp only [U, mem_iInter, Set.mem_ofPred_eq, Module.Basis.coord_apply, Module.Basis.repr_sum_self]
    intro v; norm_num
  have hpos : 0 < volume U := hU.measure_pos volume ⟨_, hy₀⟩
  have hnull : volume (⋃ w ∈ W, (w : Set (Fin (n + 1) → ℝ))) = 0 :=
    (measure_biUnion_null_iff hW).2 fun w hw => Measure.addHaar_submodule volume w (hWt w hw)
  obtain ⟨y, hyU, hyW⟩ : ∃ y ∈ U, y ∉ ⋃ w ∈ W, (w : Set (Fin (n + 1) → ℝ)) := by
    by_contra h
    push Not at h
    have := measure_mono (μ := volume) h
    rw [hnull] at this
    exact hpos.ne' (nonpos_iff_eq_zero.1 this)
  have hc : ∀ v : s, 0 < b.repr y v := fun v => by
    have := mem_iInter.1 hyU v
    simpa using this
  set T := ∑ v : s, b.repr y v with hT
  have hTpos : 0 < T := Finset.sum_pos (fun v _ => hc v) Finset.univ_nonempty
  have hy : ∑ v : s, b.repr y v • (v : Fin (n + 1) → ℝ) = y := by
    conv_rhs => rw [← b.sum_repr y]
    simp only [hb]
  refine ⟨T⁻¹ • y, ?_, ?_⟩
  · refine mem_convexHull_of_exists_fintype (fun v : s => T⁻¹ * b.repr y v) (fun v : s => (v : _))
      (fun v => mul_nonneg (inv_nonneg.2 hTpos.le) (hc v).le) ?_ (fun v => v.2) ?_
    · rw [← Finset.mul_sum, ← hT, inv_mul_cancel₀ hTpos.ne']
    · have := congrArg (T⁻¹ • ·) hy
      simp only [Finset.smul_sum, smul_smul] at this
      exact this
  · intro w hw hmem
    apply hyW
    rw [mem_iUnion₂]
    refine ⟨w, hw, ?_⟩
    have := w.smul_mem T hmem
    rwa [smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul] at this

/-! ### Every point lies in a top-dimensional simplex -/

lemma top_cover (S : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hS : IsSubdivision n S)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) :
    ∃ κ ∈ S.faces, κ.card = n + 1 ∧ x ∈ convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) := by
  classical
  have hK : S.space ⊆ Simplex n := hS.2.le
  set L := {G ∈ S.faces | G.card ≤ n} with hL
  have hLfin : L.Finite := hS.1.subset fun G hG => hG.1
  set W := (fun G : Finset (Fin (n + 1) → ℝ) => Submodule.span ℝ (G : Set (Fin (n + 1) → ℝ))) '' L
  have hW : W.Countable := (hLfin.image _).countable
  have hWt : ∀ w ∈ W, w ≠ ⊤ := by
    rintro _ ⟨G, hG, rfl⟩
    exact span_ne_top_of_card_le hG.2
  have hE0 : LinearIndependent ℝ ((↑) : E0 n → Fin (n + 1) → ℝ) :=
    face_linearIndependent (trivCx n) (trivCx_isIntegral n).1.2.le
      (s := E0 n) ⟨Finset.univ_nonempty.image _, subset_rfl⟩
  obtain ⟨c, hc, hcW⟩ := exists_generic (E0 n) hE0 (card_E0 n) W hW hWt
  rw [convexHull_E0] at hc
  set γ : ℝ → Fin (n + 1) → ℝ := fun t => c + t • (x - c) with hγ
  have hγcont : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Simplex n := fun t ht =>
    (convex_stdSimplex ℝ _).add_smul_sub_mem hc hx ht
  set B := ⋃ G ∈ L, {t : ℝ | γ t ∈ Submodule.span ℝ (G : Set (Fin (n + 1) → ℝ))} with hB
  have hBc : B.Countable := by
    refine hLfin.countable.biUnion fun G hG => ?_
    refine Set.Subsingleton.countable ?_
    intro t₁ h₁ t₂ h₂
    by_contra hne
    set V := Submodule.span ℝ (G : Set (Fin (n + 1) → ℝ))
    have hdiff : (t₁ - t₂) • (x - c) ∈ V := by
      have := V.sub_mem h₁ h₂
      simp only [hγ] at this
      convert this using 1
      rw [sub_smul]; abel
    have hxc : x - c ∈ V := by
      have := V.smul_mem (t₁ - t₂)⁻¹ hdiff
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at this
    have hcV : c ∈ V := by
      have := V.sub_mem h₁ (V.smul_mem t₁ hxc)
      simpa [hγ] using this
    exact hcW V ⟨G, hG, rfl⟩ hcV
  set T := {κ ∈ S.faces | κ.card = n + 1} with hT
  have hTfin : T.Finite := hS.1.subset fun G hG => hG.1
  set C := ⋃ κ ∈ T, γ ⁻¹' convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) with hC
  have hCclosed : IsClosed C := hTfin.isClosed_biUnion fun κ _ =>
    ((κ.finite_toSet.isCompact_convexHull ℝ).isClosed).preimage hγcont
  have hsub : Ioo (0 : ℝ) 1 ∩ Bᶜ ⊆ C := by
    rintro t ⟨ht, htB⟩
    have hmem := hγmem t (Ioo_subset_Icc_self ht)
    rw [← hS.2] at hmem
    obtain ⟨κ, hκ, hκt⟩ := (Geometry.SimplicialComplex.mem_space_iff).1 hmem
    have hcard : κ.card = n + 1 := by
      have hle := face_card_le S hK hκ
      by_contra hne
      apply htB
      rw [hB, mem_iUnion₂]
      exact ⟨κ, ⟨hκ, by omega⟩, convexHull_subset_span' _ hκt⟩
    rw [hC, mem_iUnion₂]
    exact ⟨κ, ⟨hκ, hcard⟩, hκt⟩
  have h1 : (1 : ℝ) ∈ C := by
    have hd : Dense Bᶜ := hBc.dense_compl ℝ
    have h2 : Ioo (0 : ℝ) 1 ⊆ closure (Ioo 0 1 ∩ Bᶜ) := hd.open_subset_closure_inter isOpen_Ioo
    have h3 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one, le_rfl⟩
    have h4 : closure (Ioo (0 : ℝ) 1) ⊆ C := by
      refine closure_minimal (h2.trans ?_) hCclosed
      exact closure_minimal hsub hCclosed
    exact h4 h3
  rw [hC, mem_iUnion₂] at h1
  obtain ⟨κ, hκ, h⟩ := h1
  refine ⟨κ, hκ.1, hκ.2, ?_⟩
  have : γ 1 = x := by simp [hγ]
  rw [← this]
  exact h

end CannonFloydParry.S7

/-!
# Determinants of vertex matrices; adjacent top simplices lie on opposite sides
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

lemma det_rM (A : GL (Fin (n + 1)) ℤ) :
    (rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).det =
      (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) := by
  rw [show rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) =
      (Int.castRingHom ℝ).mapMatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) from rfl,
    ← RingHom.map_det]
  rfl

lemma det_GL_eq (A : GL (Fin (n + 1)) ℤ) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1 ∨
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = -1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact Int.isUnit_iff.1 (Units.isUnit _)

/-- The key determinant identity: if `A wᵢ = sᵢ uᵢ` then `det A · det w = (∏ sᵢ) · det u`. -/
lemma det_formula (A : GL (Fin (n + 1)) ℤ) (w u : Fin (n + 1) → Fin (n + 1) → ℝ)
    (s : Fin (n + 1) → ℝ) (h : ∀ i, glAct A (w i) = s i • u i) :
    (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) * (Matrix.of w).det =
      (∏ i, s i) * (Matrix.of u).det := by
  have hM : Matrix.of w * (rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ))ᵀ =
      Matrix.diagonal s * Matrix.of u := by
    ext i j
    rw [Matrix.diagonal_mul]
    have := congrFun (h i) j
    rw [glAct_eq] at this
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rM, Matrix.det_diagonal] at this
  rw [mul_comm]; exact this

lemma det_of_ne_zero {w : Fin (n + 1) → Fin (n + 1) → ℝ} (hw : LinearIndependent ℝ w) :
    (Matrix.of w).det ≠ 0 := by
  have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

/-- The linear functional `y ↦ det (y, v₁, …, vₙ)`. -/
noncomputable def detL (v : Fin n → Fin (n + 1) → ℝ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
  (Matrix.detRowAlternating : (Fin (n + 1) → ℝ) [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap
    (Fin.cons 0 v) 0

lemma detL_apply (v : Fin n → Fin (n + 1) → ℝ) (y : Fin (n + 1) → ℝ) :
    detL v y = (Matrix.of (Fin.cons y v : Fin (n + 1) → Fin (n + 1) → ℝ)).det := by
  rw [detL, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
  rfl

lemma detL_v (v : Fin n → Fin (n + 1) → ℝ) (i : Fin n) : detL v (v i) = 0 := by
  rw [detL_apply]
  exact Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm (by
    show (Fin.cons (v i) v : Fin (n + 1) → Fin (n + 1) → ℝ) 0 =
      (Fin.cons (v i) v : Fin (n + 1) → Fin (n + 1) → ℝ) i.succ
    rw [Fin.cons_zero, Fin.cons_succ])

lemma detL_hull (v : Fin n → Fin (n + 1) → ℝ) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ convexHull ℝ (range v)) : detL v y = 0 := by
  have : convexHull ℝ (range v) ⊆ (LinearMap.ker (detL v) : Set (Fin (n + 1) → ℝ)) :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact detL_v v i) (Submodule.convex _)
  exact this hy

lemma coe_insert_image (a : Fin (n + 1) → ℝ) (v : Fin n → Fin (n + 1) → ℝ) :
    ((insert a (Finset.univ.image v) : Finset _) : Set (Fin (n + 1) → ℝ)) =
      range (Fin.cons a v : Fin (n + 1) → Fin (n + 1) → ℝ) := by
  rw [Fin.range_cons]; simp

/-- Facts about a top face written as `insert a (image v)`. -/
lemma top_face_facts (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ))
    (hK : K.space ⊆ Simplex n) (v : Fin n → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ)
    (ha : insert a (Finset.univ.image v) ∈ K.faces)
    (hca : (insert a (Finset.univ.image v)).card = n + 1) :
    a ∉ Finset.univ.image v ∧ Function.Injective v ∧
      LinearIndependent ℝ (Fin.cons a v : Fin (n + 1) → Fin (n + 1) → ℝ) ∧
      ∀ i, (Fin.cons a v : Fin (n + 1) → Fin (n + 1) → ℝ) i ∈ Simplex n := by
  classical
  have hle : (Finset.univ.image v).card ≤ n := by
    have := Finset.card_image_le (s := Finset.univ) (f := v); simpa using this
  have hins := Finset.card_insert_le a (Finset.univ.image v)
  have hanot : a ∉ Finset.univ.image v := by
    intro h
    rw [Finset.insert_eq_of_mem h] at hca
    omega
  have hcardF : (Finset.univ.image v).card = n := by
    rw [Finset.card_insert_of_notMem hanot] at hca; omega
  have hinj : Function.Injective v := by
    have := Finset.card_image_iff.1 (hcardF.trans (by simp))
    intro i j hij
    exact this (by simp) (by simp) hij
  have hcinj : Function.Injective (Fin.cons a v : Fin (n + 1) → Fin (n + 1) → ℝ) := by
    rw [Fin.cons_injective_iff]
    refine ⟨fun ⟨i, hi⟩ => hanot (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩), hinj⟩
  have hmem : ∀ i, (Fin.cons a v : Fin (n + 1) → Fin (n + 1) → ℝ) i ∈
      insert a (Finset.univ.image v) := by
    intro i
    rw [← Finset.mem_coe, coe_insert_image]
    exact mem_range_self i
  have hli := face_linearIndependent K hK ha
  refine ⟨hanot, hinj, ?_, fun i => hK (K.subset_space ha (hmem i))⟩
  have := hli.comp (fun i => (⟨_, hmem i⟩ : (insert a (Finset.univ.image v) : Finset _)))
    (fun i j h => hcinj (congrArg Subtype.val h))
  exact this

/-- Two distinct top simplices sharing a facet lie on opposite sides of it. -/
lemma opp_sides (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ))
    (hK : K.space ⊆ Simplex n) (hn : 1 ≤ n) (v : Fin n → Fin (n + 1) → ℝ)
    (a b : Fin (n + 1) → ℝ)
    (ha : insert a (Finset.univ.image v) ∈ K.faces) (hb : insert b (Finset.univ.image v) ∈ K.faces)
    (hca : (insert a (Finset.univ.image v)).card = n + 1)
    (hcb : (insert b (Finset.univ.image v)).card = n + 1) (hab : a ≠ b) :
    detL v a * detL v b < 0 := by
  classical
  obtain ⟨hanot, -, hlia, hma⟩ := top_face_facts K hK v a ha hca
  obtain ⟨hbnot, -, hlib, hmb⟩ := top_face_facts K hK v b hb hcb
  have hDa : detL v a ≠ 0 := by rw [detL_apply]; exact det_of_ne_zero hlia
  have hDb : detL v b ≠ 0 := by rw [detL_apply]; exact det_of_ne_zero hlib
  by_contra hcon
  have hprod : 0 < detL v a * detL v b := by
    rcases lt_or_gt_of_ne (mul_ne_zero hDa hDb) with h | h
    · exact absurd h hcon
    · exact h
  set wb : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons b v with hwb
  set wa : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons a v with hwa
  let bb := basisOfLinearIndependentOfCardEqFinrank hlib (by simp)
  have hbb : ∀ j, bb j = wb j := fun j => by
    simp [bb, coe_basisOfLinearIndependentOfCardEqFinrank]
  set γ := bb.repr a with hγ
  have ha_eq : ∑ j, γ j • wb j = a := by
    conv_rhs => rw [← bb.sum_repr a]
    simp only [hbb, hγ]
  have hsumγ : ∑ j, γ j = 1 := by
    have h1 := sum_coord_sum Finset.univ γ wb (fun j _ => hmb j)
    rw [ha_eq] at h1
    have h2 := (hK (K.subset_space ha (Finset.mem_insert_self _ _))).2
    rw [← h1, h2]
  have hDaγ : detL v a = γ 0 * detL v b := by
    rw [← ha_eq, map_sum, Fin.sum_univ_succ]
    simp only [map_smul, smul_eq_mul, hwb, Fin.cons_zero, Fin.cons_succ, detL_v, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hγ0 : 0 < γ 0 := by
    rw [hDaγ, mul_assoc] at hprod
    exact pos_of_mul_pos_left hprod (mul_self_nonneg _)
  set M := ∑ j, |γ j| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hγle : ∀ j, |γ j| ≤ M := fun j =>
    Finset.single_le_sum (f := fun j => |γ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set ε := 1 / (1 + n * M) with hε
  have hden : 0 < 1 + n * M := by positivity
  have hεpos : 0 < ε := by positivity
  have hεn : ε + n * (ε * M) = 1 := by
    rw [hε]; field_simp
  set z := ε • a + (ε * M) • ∑ i, v i with hz
  -- `z` in the first simplex
  have hza : z ∈ convexHull ℝ ((insert a (Finset.univ.image v) : Finset _) : Set _) := by
    rw [coe_insert_image]
    refine mem_convexHull_of_exists_fintype (Fin.cons ε (fun _ => ε * M) : Fin (n + 1) → ℝ) wa
      ?_ ?_ (fun j => mem_range_self j) ?_
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; exact hεpos.le
      · simp only [Fin.cons_succ]; exact mul_nonneg hεpos.le hM0
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      exact hεn
    · rw [Fin.sum_univ_succ]
      simp only [hwa, Fin.cons_zero, Fin.cons_succ, hz, Finset.smul_sum]
  -- `z` in the second simplex
  have hzb : z ∈ convexHull ℝ ((insert b (Finset.univ.image v) : Finset _) : Set _) := by
    rw [coe_insert_image]
    refine mem_convexHull_of_exists_fintype
      (fun j => ε * γ j + (Fin.cons 0 (fun _ => ε * M) : Fin (n + 1) → ℝ) j) wb
      ?_ ?_ (fun j => mem_range_self j) ?_
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero, add_zero]; exact (mul_pos hεpos hγ0).le
      · simp only [Fin.cons_succ]
        have := neg_abs_le (γ i.succ)
        have h2 := hγle i.succ
        nlinarith
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumγ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, zero_add, mul_one]
      exact hεn
    · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, ha_eq]
      rw [Fin.sum_univ_succ]
      simp only [hwb, Fin.cons_zero, Fin.cons_succ, zero_smul, zero_add, hz, Finset.smul_sum]
  have hzF : z ∈ convexHull ℝ (range v) := by
    have h := K.inter_subset_convexHull ha hb ⟨hza, hzb⟩
    refine convexHull_mono ?_ h
    rintro y ⟨hy1, hy2⟩
    rw [Finset.mem_coe, Finset.mem_insert] at hy1 hy2
    have : y ∈ Finset.univ.image v := by
      rcases hy1 with rfl | hy1
      · rcases hy2 with rfl | hy2
        · exact absurd rfl hab
        · exact hy2
      · exact hy1
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 this
    exact mem_range_self i
  have h0 := detL_hull v hzF
  rw [hz, map_add, map_smul, map_smul, map_sum] at h0
  simp only [detL_v, Finset.sum_const_zero, smul_eq_mul, mul_zero, add_zero] at h0
  exact hDa ((mul_eq_zero.1 h0).resolve_left hεpos.ne')

end CannonFloydParry.S7

/-!
# The sign of the determinant is the same on all top simplices
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

lemma via_scale (f : Simplex n ≃ₜ Simplex n) {U : Set (Fin (n + 1) → ℝ)} (hU : U ⊆ Simplex n)
    {A : GL (Fin (n + 1)) ℤ} (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ U} f)
    {y : Fin (n + 1) → ℝ} (hy : y ∈ U) :
    glAct A y = (∑ i, |glAct A y i|) • extF f y ∧ 0 < ∑ i, |glAct A y i| := by
  have hys := hU hy
  have h := hA ⟨y, hys⟩ hy
  have hne := glAct_ne_zero A (ne_zero_of_mem hys)
  have hs := sum_abs_pos hne
  refine ⟨?_, hs⟩
  have e : extF f y = rho (glAct A y) := (extF_apply f ⟨y, hys⟩).trans h.2
  rw [e, rho_eq_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- The determinant identity on a face, with a positive factor. -/
lemma det_identity (f : Simplex n ≃ₜ Simplex n) {U : Set (Fin (n + 1) → ℝ)}
    (hU : U ⊆ Simplex n) {A : GL (Fin (n + 1)) ℤ}
    (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ U} f)
    (w : Fin (n + 1) → Fin (n + 1) → ℝ) (hw : ∀ i, w i ∈ U) :
    ∃ P : ℝ, 0 < P ∧ (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) *
      (Matrix.of w).det = P * (Matrix.of (extF f ∘ w)).det := by
  refine ⟨∏ i, ∑ k, |glAct A (w i) k|, Finset.prod_pos fun i _ => (via_scale f hU hA (hw i)).2,
    det_formula A w (extF f ∘ w) _ fun i => (via_scale f hU hA (hw i)).1⟩

lemma int_eq_of_mul_pos {A B : GL (Fin (n + 1)) ℤ}
    (h : 0 < (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) *
      (((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ)) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det := by
  rcases det_GL_eq A with hA | hA <;> rcases det_GL_eq B with hB | hB <;>
    rw [hA, hB] at h ⊢ <;> (try norm_num at h)

/-- Adjacent top simplices carry matrices with the same determinant. -/
lemma det_eq_of_adjacent (f : Simplex n ≃ₜ Simplex n)
    (S : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hS : IsSubdivision n S)
    (hproj : ∀ σ ∈ S.faces,
      IsIntegralProjective {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f)
    (hn : 1 ≤ n) (v : Fin n → Fin (n + 1) → ℝ) (a b : Fin (n + 1) → ℝ)
    (ha : insert a (Finset.univ.image v) ∈ S.faces) (hb : insert b (Finset.univ.image v) ∈ S.faces)
    (hca : (insert a (Finset.univ.image v)).card = n + 1)
    (hcb : (insert b (Finset.univ.image v)).card = n + 1) (hab : a ≠ b)
    {A B : GL (Fin (n + 1)) ℤ}
    (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈
      convexHull ℝ ↑(insert a (Finset.univ.image v))} f)
    (hB : IsIntegralProjectiveVia B {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈
      convexHull ℝ ↑(insert b (Finset.univ.image v))} f) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det := by
  classical
  obtain ⟨S', hfaces, hS', -, -⟩ := exists_imageComplex f S hS hproj
  have hK : S.space ⊆ Simplex n := hS.2.le
  have hK' : S'.space ⊆ Simplex n := hS'.2.le
  have h1 := opp_sides S hK hn v a b ha hb hca hcb hab
  set F := extF f with hF
  have hpts : ∀ c, insert c (Finset.univ.image v) ∈ S.faces →
      ((insert c (Finset.univ.image v) : Finset _) : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    fun c hc => fun y hy => hK (S.subset_space hc hy)
  have himage : ∀ c, (insert c (Finset.univ.image v)).image F =
      insert (F c) (Finset.univ.image (F ∘ v)) := by
    intro c
    rw [Finset.image_insert, Finset.image_image]
  have hface' : ∀ c, insert c (Finset.univ.image v) ∈ S.faces →
      insert (F c) (Finset.univ.image (F ∘ v)) ∈ S'.faces := by
    intro c hc
    rw [hfaces, ← himage]
    exact ⟨_, hc, rfl⟩
  have hcard' : ∀ c, insert c (Finset.univ.image v) ∈ S.faces →
      (insert c (Finset.univ.image v)).card = n + 1 →
      (insert (F c) (Finset.univ.image (F ∘ v))).card = n + 1 := by
    intro c hc hcc
    rw [← himage, Finset.card_image_of_injOn ((extF_injOn f).mono (hpts c hc)), hcc]
  have hFab : F a ≠ F b := by
    intro h
    exact hab (extF_injOn f (hpts a ha (Finset.mem_insert_self _ _))
      (hpts b hb (Finset.mem_insert_self _ _)) h)
  have h2 := opp_sides S' hK' hn (F ∘ v) (F a) (F b) (hface' a ha) (hface' b hb)
    (hcard' a ha hca) (hcard' b hb hcb) hFab
  have hhull : ∀ c, insert c (Finset.univ.image v) ∈ S.faces →
      convexHull ℝ ((insert c (Finset.univ.image v) : Finset _) : Set (Fin (n + 1) → ℝ)) ⊆
        Simplex n := fun c hc => hS.2 ▸ S.convexHull_subset_space hc
  have hmemw : ∀ c i, (Fin.cons c v : Fin (n + 1) → Fin (n + 1) → ℝ) i ∈
      convexHull ℝ ((insert c (Finset.univ.image v) : Finset _) : Set (Fin (n + 1) → ℝ)) := by
    intro c i
    apply subset_convexHull
    rw [coe_insert_image]
    exact mem_range_self i
  obtain ⟨P₁, hP₁, hA'⟩ := det_identity f (hhull a ha) hA _ (hmemw a)
  obtain ⟨P₂, hP₂, hB'⟩ := det_identity f (hhull b hb) hB _ (hmemw b)
  rw [Fin.comp_cons, ← detL_apply, ← detL_apply] at hA' hB'
  apply int_eq_of_mul_pos
  have key : ((((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) *
      (((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ)) * (detL v a * detL v b) =
      (P₁ * P₂) * (detL (F ∘ v) (F a) * detL (F ∘ v) (F b)) := by
    calc _ = ((((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) * detL v a) *
          ((((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) * detL v b) := by ring
      _ = _ := by rw [hA', hB']; ring
  have hrhs : (P₁ * P₂) * (detL (F ∘ v) (F a) * detL (F ∘ v) (F b)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hP₁ hP₂) h2
  rw [← key] at hrhs
  exact pos_of_mul_neg_left hrhs h1.le

/-- An enumeration of a top face. -/
lemma top_enum (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hK : K.space ⊆ Simplex n)
    {κ : Finset (Fin (n + 1) → ℝ)} (hκ : κ ∈ K.faces) (hc : κ.card = n + 1) :
    ∃ w : Fin (n + 1) → Fin (n + 1) → ℝ, LinearIndependent ℝ w ∧ ∀ i, w i ∈ κ := by
  let e := (κ.equivFinOfCardEq hc).symm
  refine ⟨fun i => (e i : Fin (n + 1) → ℝ), ?_, fun i => (e i).2⟩
  exact (face_linearIndependent K hK hκ).comp (fun i => e i) e.injective

/-- Two matrices valid on the same top simplex have the same determinant. -/
lemma det_eq_of_same (f : Simplex n ≃ₜ Simplex n)
    (K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hK : K.space = Simplex n)
    {κ : Finset (Fin (n + 1) → ℝ)} (hκ : κ ∈ K.faces) (hc : κ.card = n + 1)
    {A B : GL (Fin (n + 1)) ℤ}
    (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑κ} f)
    (hB : IsIntegralProjectiveVia B {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑κ} f) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det := by
  obtain ⟨w, hw, hwκ⟩ := top_enum K hK.le hκ hc
  have hhull : convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hK ▸ K.convexHull_subset_space hκ
  have hmem : ∀ i, w i ∈ convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) :=
    fun i => subset_convexHull ℝ _ (hwκ i)
  obtain ⟨P₁, hP₁, hA'⟩ := det_identity f hhull hA w hmem
  obtain ⟨P₂, hP₂, hB'⟩ := det_identity f hhull hB w hmem
  have hD := det_of_ne_zero hw
  by_contra hne
  have hprod : (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) *
      (((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) = -1 := by
    rcases det_GL_eq A with h1 | h1 <;> rcases det_GL_eq B with h2 | h2 <;>
      rw [h1, h2] at hne ⊢ <;> first | exact absurd rfl hne | norm_num
  have key : ((((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) *
      (((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ)) * ((Matrix.of w).det *
      (Matrix.of w).det) = (P₁ * P₂) * ((Matrix.of (extF f ∘ w)).det *
        (Matrix.of (extF f ∘ w)).det) := by
    calc _ = ((((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) * (Matrix.of w).det) *
          ((((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det : ℤ) : ℝ) * (Matrix.of w).det) := by
            ring
      _ = _ := by rw [hA', hB']; ring
  rw [hprod] at key
  have h1 : 0 < (Matrix.of w).det * (Matrix.of w).det := mul_self_pos.2 hD
  have h2 : 0 ≤ (P₁ * P₂) * ((Matrix.of (extF f ∘ w)).det * (Matrix.of (extF f ∘ w)).det) :=
    mul_nonneg (mul_pos hP₁ hP₂).le (mul_self_nonneg _)
  linarith

end CannonFloydParry.S7

/-!
# Consistency of the determinant sign over all top simplices, and its consequences
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

/-- All matrices on all top simplices of a PIP subdivision have the same determinant. -/
theorem det_eq_of_top (f : Simplex n ≃ₜ Simplex n)
    (S : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hS : IsSubdivision n S)
    (hproj : ∀ σ ∈ S.faces,
      IsIntegralProjective {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f)
    (hn : 1 ≤ n) {σ τ : Finset (Fin (n + 1) → ℝ)} (hσ : σ ∈ S.faces) (hτ : τ ∈ S.faces)
    (hcσ : σ.card = n + 1) (hcτ : τ.card = n + 1) {A B : GL (Fin (n + 1)) ℤ}
    (hA : IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑σ} f)
    (hB : IsIntegralProjectiveVia B {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑τ} f) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det := by
  classical
  by_contra hne
  have hK : S.space ⊆ Simplex n := hS.2.le
  set d₀ := (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det with hd₀
  set L := {G ∈ S.faces | G.card < n} with hL
  have hLfin : L.Finite := hS.1.subset fun G hG => hG.1
  -- a generic point `q` of `τ`
  obtain ⟨q, hq, hqW⟩ := exists_generic τ (face_linearIndependent S hK hτ) hcτ
    ((fun G : Finset (Fin (n + 1) → ℝ) => Submodule.span ℝ (G : Set (Fin (n + 1) → ℝ))) '' L)
    (hLfin.image _).countable (by
      rintro _ ⟨G, hG, rfl⟩
      exact span_ne_top_of_card_le (by have := hG.2; omega))
  -- a generic point `p` of `σ`
  obtain ⟨p, hp, hpW⟩ := exists_generic σ (face_linearIndependent S hK hσ) hcσ
    ((fun G : Finset (Fin (n + 1) → ℝ) =>
      Submodule.span ℝ ((insert q G : Finset _) : Set (Fin (n + 1) → ℝ))) '' L)
    (hLfin.image _).countable (by
      rintro _ ⟨G, hG, rfl⟩
      refine span_ne_top_of_card_le ?_
      have := Finset.card_insert_le q G
      have := hG.2
      omega)
  have hσΔ : convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hS.2 ▸ S.convexHull_subset_space hσ
  have hτΔ : convexHull ℝ (τ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hS.2 ▸ S.convexHull_subset_space hτ
  set γ : ℝ → Fin (n + 1) → ℝ := fun t => p + t • (q - p) with hγ
  have hγcont : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Simplex n := fun t ht =>
    (convex_stdSimplex ℝ _).add_smul_sub_mem (hσΔ hp) (hτΔ hq) ht
  set Tp := {κ ∈ S.faces | κ.card = n + 1 ∧ ∃ C : GL (Fin (n + 1)) ℤ,
    IsIntegralProjectiveVia C {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑κ} f ∧
      (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = d₀} with hTp
  set Tm := {κ ∈ S.faces | κ.card = n + 1 ∧ ∃ C : GL (Fin (n + 1)) ℤ,
    IsIntegralProjectiveVia C {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑κ} f ∧
      (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det ≠ d₀} with hTm
  set Cp := ⋃ κ ∈ Tp, γ ⁻¹' convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) with hCp
  set Cm := ⋃ κ ∈ Tm, γ ⁻¹' convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) with hCm
  have hclosed : ∀ T : Set (Finset (Fin (n + 1) → ℝ)), T ⊆ S.faces →
      IsClosed (⋃ κ ∈ T, γ ⁻¹' convexHull ℝ (κ : Set (Fin (n + 1) → ℝ))) := fun T hT =>
    (hS.1.subset hT).isClosed_biUnion fun κ _ =>
      ((κ.finite_toSet.isCompact_convexHull ℝ).isClosed).preimage hγcont
  have hCpc : IsClosed Cp := hclosed Tp fun κ hκ => hκ.1
  have hCmc : IsClosed Cm := hclosed Tm fun κ hκ => hκ.1
  have hcover : Icc (0 : ℝ) 1 ⊆ Cp ∪ Cm := by
    intro t ht
    obtain ⟨κ, hκ, hcκ, hκt⟩ := top_cover S hS (hγmem t ht)
    obtain ⟨C, hC⟩ := hproj κ hκ
    by_cases hd : (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = d₀
    · left; rw [hCp, mem_iUnion₂]; exact ⟨κ, ⟨hκ, hcκ, C, hC, hd⟩, hκt⟩
    · right; rw [hCm, mem_iUnion₂]; exact ⟨κ, ⟨hκ, hcκ, C, hC, hd⟩, hκt⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∩ Cp := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [hCp, mem_iUnion₂]
    refine ⟨σ, ⟨hσ, hcσ, A, hA, rfl⟩, ?_⟩
    simpa [hγ] using hp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 ∩ Cm := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    rw [hCm, mem_iUnion₂]
    refine ⟨τ, ⟨hτ, hcτ, B, hB, fun h => hne h.symm⟩, ?_⟩
    simpa [hγ] using hq
  obtain ⟨t, ht, htp, htm⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc Cp Cm hCpc hCmc
    hcover ⟨0, h0⟩ ⟨1, h1⟩
  rw [hCp, mem_iUnion₂] at htp
  rw [hCm, mem_iUnion₂] at htm
  obtain ⟨κ₁, ⟨hκ₁, hc₁, C₁, hC₁, hd₁⟩, ht₁⟩ := htp
  obtain ⟨κ₂, ⟨hκ₂, hc₂, C₂, hC₂, hd₂⟩, ht₂⟩ := htm
  by_cases h12 : κ₁ = κ₂
  · subst h12
    exact hd₂ (hd₁ ▸ (det_eq_of_same f S hS.2 hκ₁ hc₁ hC₂ hC₁))
  -- the common face
  set G := κ₁ ∩ κ₂ with hG
  have htG : γ t ∈ convexHull ℝ (G : Set (Fin (n + 1) → ℝ)) := by
    rw [hG, Finset.coe_inter]
    exact S.inter_subset_convexHull hκ₁ hκ₂ ⟨ht₁, ht₂⟩
  have hGne : G.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at htG
    exact htG
  have hGface : G ∈ S.faces := S.down_closed hκ₁ Finset.inter_subset_left hGne
  have hGge : n ≤ G.card := by
    by_contra hlt
    push Not at hlt
    have hGL : G ∈ L := ⟨hGface, hlt⟩
    have hspan := convexHull_subset_span' _ htG
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      apply hqW _ ⟨G, hGL, rfl⟩
      simpa [hγ] using hspan
    · apply hpW _ ⟨G, hGL, rfl⟩
      set V := Submodule.span ℝ ((insert q G : Finset _) : Set (Fin (n + 1) → ℝ))
      have hGV : Submodule.span ℝ (G : Set (Fin (n + 1) → ℝ)) ≤ V :=
        Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
      have hqV : q ∈ V := Submodule.subset_span (by simp)
      have h1t : (1 - t) • p ∈ V := by
        have := V.sub_mem (hGV hspan) (V.smul_mem t hqV)
        convert this using 1
        simp only [hγ, sub_smul, one_smul, smul_sub]
        abel
      have := V.smul_mem (1 - t)⁻¹ h1t
      rwa [smul_smul, inv_mul_cancel₀ (by linarith), one_smul] at this
  have hGsub : G ⊆ κ₁ := Finset.inter_subset_left
  have hGlt : G.card < n + 1 := by
    refine lt_of_lt_of_eq
      (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hGsub, fun h => h12 ?_⟩)) hc₁
    have h' : κ₁ ⊆ κ₂ := by rw [← h, hG]; exact Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le h' (by rw [hc₁, hc₂])
  have hGcard : G.card = n := by omega
  -- the extra vertices
  have hextra : ∀ κ ∈ ({κ₁, κ₂} : Set (Finset (Fin (n + 1) → ℝ))), κ.card = n + 1 → G ⊆ κ →
      ∃ a ∈ κ, a ∉ G ∧ κ = insert a G := by
    intro κ _ hc hGκ
    have : (κ \ G).card = 1 := by rw [Finset.card_sdiff_of_subset hGκ, hc, hGcard]; simp
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 this
    have haκ : a ∈ κ \ G := by rw [ha]; exact Finset.mem_singleton_self a
    rw [Finset.mem_sdiff] at haκ
    refine ⟨a, haκ.1, haκ.2, ?_⟩
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.insert_subset haκ.1 hGκ) ?_
    rw [Finset.card_insert_of_notMem haκ.2, hc, hGcard]
  obtain ⟨a, haκ, haG, hκa⟩ := hextra κ₁ (by simp) hc₁ hGsub
  obtain ⟨b, hbκ, hbG, hκb⟩ := hextra κ₂ (by simp) hc₂ Finset.inter_subset_right
  have hab : a ≠ b := by
    rintro rfl
    exact haG (Finset.mem_inter.2 ⟨haκ, hbκ⟩)
  -- enumerate the common facet
  let e := (G.equivFinOfCardEq hGcard).symm
  set v : Fin n → Fin (n + 1) → ℝ := fun i => (e i : Fin (n + 1) → ℝ) with hv
  have hvG : Finset.univ.image v = G := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hy; exact ⟨e.symm ⟨y, hy⟩, by simp [hv]⟩
  rw [← hvG] at hκa hκb
  rw [hκa] at hκ₁ hc₁ hC₁
  rw [hκb] at hκ₂ hc₂ hC₂
  exact hd₂ (hd₁ ▸ (det_eq_of_adjacent f S hS hproj hn v a b hκ₁ hκ₂ hc₁ hc₂ hab hC₁ hC₂).symm)

/-- Every PIP map is PIP with all determinants `1` or with all determinants `-1`. -/
theorem isPIPW_det_dichotomy (hn : 1 ≤ n) {f : Simplex n ≃ₜ Simplex n} (hf : IsPIP f) :
    IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1) f ∨
      IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = -1) f := by
  classical
  obtain ⟨S, hS, hproj⟩ := hf
  obtain ⟨κ₀, hκ₀, hc₀, -⟩ := top_cover S hS.1 (single_mem_stdSimplex ℝ (0 : Fin (n + 1)))
  obtain ⟨A₀, hA₀⟩ := hproj κ₀ hκ₀
  -- the pure part of `S`
  let Sp : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) :=
    { faces := {G ∈ S.faces | ∃ κ ∈ S.faces, κ.card = n + 1 ∧ G ⊆ κ}
      isRelLowerSet_faces := by
        rintro G ⟨hG, κ, hκ, hcκ, hGκ⟩
        refine ⟨S.nonempty_of_mem_faces hG, fun b hb hbne => ?_⟩
        exact ⟨S.down_closed hG hb hbne, κ, hκ, hcκ, hb.trans hGκ⟩
      indep := fun hs => S.indep hs.1
      inter_subset_convexHull := fun hs ht => S.inter_subset_convexHull hs.1 ht.1 }
  have hSp : IsIntegralSubdivision n Sp := by
    refine ⟨⟨hS.1.1.subset fun G hG => hG.1, ?_⟩, fun G hG hc => hS.2 G hG.1 hc⟩
    ext x
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨G, hG, hx⟩
      exact hS.1.2 ▸ S.convexHull_subset_space hG.1 hx
    · intro hx
      obtain ⟨κ, hκ, hcκ, hxκ⟩ := top_cover S hS.1 hx
      exact ⟨κ, ⟨hκ, κ, hκ, hcκ, subset_rfl⟩, hxκ⟩
  have hall : ∀ G ∈ Sp.faces, ∃ A : GL (Fin (n + 1)) ℤ,
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det =
        (A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det ∧
      IsIntegralProjectiveVia A {x : Simplex n | (x : Fin (n + 1) → ℝ) ∈ convexHull ℝ ↑G} f := by
    rintro G ⟨hG, κ, hκ, hcκ, hGκ⟩
    obtain ⟨A, hA⟩ := hproj κ hκ
    refine ⟨A, det_eq_of_top f S hS.1 hproj hn hκ hκ₀ hcκ hc₀ hA hA₀, ?_⟩
    exact IsIntegralProjectiveVia.mono' hA fun x hx =>
      convexHull_mono (Finset.coe_subset.2 hGκ) hx
  rcases det_GL_eq A₀ with h | h
  · left
    exact ⟨Sp, hSp, fun G hG => by obtain ⟨A, hA, hv⟩ := hall G hG; exact ⟨A, hA.trans h, hv⟩⟩
  · right
    exact ⟨Sp, hSp, fun G hG => by obtain ⟨A, hA, hv⟩ := hall G hG; exact ⟨A, hA.trans h, hv⟩⟩

/-- The identity is not PIP with all determinants `-1`. -/
theorem not_isPIPW_one_neg :
    ¬ IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = -1)
      (1 : Simplex n ≃ₜ Simplex n) := by
  rintro ⟨S, hS, hproj⟩
  obtain ⟨κ, hκ, hc, -⟩ := top_cover S hS.1 (single_mem_stdSimplex ℝ (0 : Fin (n + 1)))
  obtain ⟨A, hdet, hA⟩ := hproj κ hκ
  obtain ⟨w, hw, hwκ⟩ := top_enum S hS.1.2.le hκ hc
  have hhull : convexHull ℝ (κ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    hS.1.2 ▸ S.convexHull_subset_space hκ
  obtain ⟨P, hP, hid⟩ := det_identity 1 hhull hA w fun i => subset_convexHull ℝ _ (hwκ i)
  have hext : extF (1 : Simplex n ≃ₜ Simplex n) ∘ w = w := by
    funext i
    have hwi : w i ∈ Simplex n := hhull (subset_convexHull ℝ _ (hwκ i))
    exact extF_apply 1 ⟨w i, hwi⟩
  rw [hext, hdet] at hid
  have hD := det_of_ne_zero hw
  have : (P + 1) * (Matrix.of w).det = 0 := by push_cast at hid; linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact hD h

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix

lemma det_one_of_inv {n : ℕ} {u : ℤ} {B : GL (Fin (n + 1)) ℤ}
    (h : ((B⁻¹ : GL (Fin (n + 1)) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = u) :
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det * u = 1 := by
  rw [← h, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/-- PIP⁺(Δₙ) as a subgroup, assuming the two refinement results. -/
def pipPlusSubgroup
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    (n : ℕ) : Subgroup (Simplex n ≃ₜ Simplex n) where
  carrier := PIPPlusSet n
  one_mem' := (isPIPPlus_iff_isPIPW _).2
    (isPIPW_one (P := fun A : GL (Fin (n + 1)) ℤ =>
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1) (by simp))
  mul_mem' := fun {f g} hf hg => (IsPIPW.mul hRS h71 hf hg).mono fun C ⟨A, B, hA, hB, hC⟩ => by
    rw [hC, Units.val_mul, Matrix.det_mul, hA, hB, mul_one]
  inv_mem' := fun {f} hf => (IsPIPW.symm hf).mono fun B hB => by
    have := det_one_of_inv hB
    rwa [mul_one] at this

/-- Composition of PIP maps with prescribed determinant. -/
lemma IsPIPW.mul_det
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    {n : ℕ} {u v : ℤ} {f g : Simplex n ≃ₜ Simplex n}
    (hf : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = u) f)
    (hg : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = v) g) :
    IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = u * v) (f * g) :=
  (IsPIPW.mul hRS h71 hf hg).mono fun C ⟨A, B, hA, hB, hC⟩ => by
    rw [hC, Units.val_mul, Matrix.det_mul, hA, hB]

/-- A PIP map cannot have both determinant signs. -/
lemma not_both
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    {n : ℕ} {f : Simplex n ≃ₜ Simplex n}
    (h1 : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1) f)
    (h2 : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = -1) f) : False := by
  have hs : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = 1) f.symm :=
    (IsPIPW.symm h1).mono fun B hB => by
      have := det_one_of_inv hB
      rwa [mul_one] at this
  have h := IsPIPW.mul_det hRS h71 h2 hs
  rw [mul_one] at h
  have hid : f * f.symm = 1 := by
    ext x
    simp [Homeomorph.mul_apply]
  rw [hid] at h
  exact not_isPIPW_one_neg h

theorem exists_subgroup_PIPPlusSet_index_two_of
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ H K : Subgroup (Simplex n ≃ₜ Simplex n),
      (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n ∧
      (K : Set (Simplex n ≃ₜ Simplex n)) = PIPPlusSet n ∧ K ≤ H ∧ (K.subgroupOf H).index = 2 := by
  classical
  obtain ⟨H, hH⟩ := exists_subgroup_coe_eq_PIPSet n
  have hmem : ∀ f : Simplex n ≃ₜ Simplex n, f ∈ H ↔ IsPIP f := fun f => by
    rw [← SetLike.mem_coe, hH]; rfl
  have hKH : pipPlusSubgroup hRS h71 n ≤ H := fun f hf =>
    (hmem f).2 ((isPIP_iff_isPIPW f).2
      (IsPIPW.mono ((isPIPPlus_iff_isPIPW f).1 hf) fun _ _ => trivial))
  refine ⟨H, pipPlusSubgroup hRS h71 n, hH, rfl, hKH, ?_⟩
  -- the orientation-reversing element
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 (Fin.last n) with hπ
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hPneg : IsPIPW (fun A => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).det = -1)
      (permH π) := isPIPW_permH π (by rw [det_permGL, hπ, Equiv.Perm.sign_swap h0l]; rfl)
  have hPmem : permH π ∈ H :=
    (hmem _).2 ((isPIP_iff_isPIPW _).2 (hPneg.mono fun _ _ => trivial))
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨permH π, hPmem⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hb : IsPIP (b : Simplex n ≃ₜ Simplex n) := (hmem _).1 b.2
  rcases isPIPW_det_dichotomy hn hb with h | h
  · -- `b` preserves orientation
    have hbP := IsPIPW.mul_det hRS h71 h hPneg
    rw [one_mul] at hbP
    right
    exact ⟨h, fun h' => not_both hRS h71 h' hbP⟩
  · have hbP := IsPIPW.mul_det hRS h71 h hPneg
    norm_num at hbP
    left
    exact ⟨hbP, fun h' => not_both hRS h71 h' h⟩

end CannonFloydParry.S7


open CannonFloydParry in
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    ∃ H K : Subgroup (Simplex n ≃ₜ Simplex n),
      (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n ∧
      (K : Set (Simplex n ≃ₜ Simplex n)) = PIPPlusSet n ∧ K ≤ H ∧ (K.subgroupOf H).index = 2 := by
  exact S7.exists_subgroup_PIPPlusSet_index_two_of (fun h₁ h₂ => exists_isRationalSubdivision_refines_of_isIntegralSubdivision h₁ h₂) (fun hK => exists_refines_isIntegralSubdivision hK) hn
