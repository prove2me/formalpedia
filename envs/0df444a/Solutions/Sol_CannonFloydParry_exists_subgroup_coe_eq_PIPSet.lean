-- Prove2me | solution 1 for CannonFloydParry.exists_subgroup_coe_eq_PIPSet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:18:59.523965+00:00
-- url     : https://prove2.me/submissions/ea67bfd6-c5e5-445f-86ee-cffc821aacb5

import Theorems.Thm_CannonFloydParry_exists_isRationalSubdivision_refines_of_isIntegralSubdivision
import Theorems.Thm_CannonFloydParry_exists_refines_isIntegralSubdivision
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

/-! ### Linear independence of faces -/

/-! ### Generic points -/

/-! ### Every point lies in a top-dimensional simplex -/

end CannonFloydParry.S7

/-!
# Determinants of vertex matrices; adjacent top simplices lie on opposite sides
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

end CannonFloydParry.S7

/-!
# The sign of the determinant is the same on all top simplices
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

end CannonFloydParry.S7

/-!
# Consistency of the determinant sign over all top simplices, and its consequences
-/

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix

/-- PIP(Δₙ) as a subgroup, assuming the two refinement results. -/
def pipSubgroup
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    (n : ℕ) : Subgroup (Simplex n ≃ₜ Simplex n) where
  carrier := PIPSet n
  one_mem' := (isPIP_iff_isPIPW _).2 (isPIPW_one trivial)
  mul_mem' := fun {f g} hf hg => (isPIP_iff_isPIPW _).2
    ((IsPIPW.mul hRS h71 ((isPIP_iff_isPIPW f).1 hf) ((isPIP_iff_isPIPW g).1 hg)).mono
      fun _ _ => trivial)
  inv_mem' := fun {f} hf => (isPIP_iff_isPIPW _).2
    ((((isPIP_iff_isPIPW f).1 hf).symm).mono fun _ _ => trivial)

theorem exists_subgroup_coe_eq_PIPSet_of
    (hRS : ∀ {n : ℕ} {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsIntegralSubdivision n K₁ → IsIntegralSubdivision n K₂ →
      ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂)
    (h71 : ∀ {n : ℕ} {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)},
      IsRationalSubdivision n K →
      ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
        Refines K' K ∧ IsIntegralSubdivision n K')
    (n : ℕ) :
    ∃ H : Subgroup (Simplex n ≃ₜ Simplex n), (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n :=
  ⟨pipSubgroup hRS h71 n, rfl⟩

end CannonFloydParry.S7


open CannonFloydParry in
theorem solution (n : ℕ) :
    ∃ H : Subgroup (Simplex n ≃ₜ Simplex n), (H : Set (Simplex n ≃ₜ Simplex n)) = PIPSet n := by
  exact S7.exists_subgroup_coe_eq_PIPSet_of (fun h₁ h₂ => exists_isRationalSubdivision_refines_of_isIntegralSubdivision h₁ h₂) (fun hK => exists_refines_isIntegralSubdivision hK) n
