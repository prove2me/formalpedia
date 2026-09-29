-- Prove2me | solution 1 for CannonFloydParry.isPIP_symm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:07:20.460063+00:00
-- url     : https://prove2.me/submissions/6545ffe6-759e-4ca6-b2af-9488aa689a85

import Definitions.Def_CannonFloydParry_PIP
import Mathlib

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

theorem isPIP_symm' {n : ℕ} {f : Simplex n ≃ₜ Simplex n} (hf : IsPIP f) : IsPIP f.symm := by
  classical
  obtain ⟨S, ⟨⟨hfin, hspace⟩, hint⟩, hproj⟩ := hf
  choose A hA using hproj
  let F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun y =>
    if h : y ∈ Simplex n then (f ⟨y, h⟩ : Fin (n + 1) → ℝ) else y
  have hF : ∀ x : Simplex n, F x = f x := fun x => dif_pos x.2
  have hFinj : InjOn F (Simplex n) := by
    intro x hx y hy h
    have h' : (f ⟨x, hx⟩ : Fin (n + 1) → ℝ) = f ⟨y, hy⟩ := by
      rw [← hF ⟨x, hx⟩, ← hF ⟨y, hy⟩]; exact h
    have := f.injective (Subtype.ext h')
    exact congrArg Subtype.val this
  have hhull : ∀ σ ∈ S.faces, convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    fun σ hσ => hspace ▸ S.convexHull_subset_space hσ
  have hpts : ∀ σ ∈ S.faces, (σ : Set (Fin (n + 1) → ℝ)) ⊆ Simplex n :=
    fun σ hσ => (subset_convexHull ℝ _).trans (hhull σ hσ)
  -- on each face, `F = ρ ∘ A`
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
  -- the image complex
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
  refine ⟨S', ⟨⟨hfin.image _, hspace'⟩, ?_⟩, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩ hcard
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
  · rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨(A σ hσ)⁻¹, fun y hy => ?_⟩
    have hy' : (y : Fin (n + 1) → ℝ) ∈ F '' convexHull ℝ (σ : Set (Fin (n + 1) → ℝ)) := by
      rw [himg σ hσ σ le_rfl]; exact hy
    obtain ⟨x, hx, hxy⟩ := hy'
    have hxs := hhull σ hσ hx
    have hfx : f ⟨x, hxs⟩ = y := Subtype.ext ((hF ⟨x, hxs⟩).symm.trans hxy)
    have hsymm : f.symm y = ⟨x, hxs⟩ := by rw [← hfx, Homeomorph.symm_apply_apply]
    have hAx := hFA σ hσ x hx
    have hne := glAct_ne_zero (A σ hσ) (ne_zero_of_mem hxs)
    have hsA := sum_abs_pos hne
    rw [hsymm]
    refine ⟨fun i => ?_, ?_⟩
    · rw [← hxy, hAx.2, rho_eq_smul, glAct_smul, glAct_inv_glAct]
      exact mul_nonneg (inv_nonneg.mpr hsA.le) (hxs.1 i)
    · show x = _
      rw [← hxy, hAx.2, rho_glAct_inv_rho_glAct _ hxs]

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {n : ℕ} {f : Simplex n ≃ₜ Simplex n} (hf : IsPIP f) : IsPIP f.symm := by
  exact S7.isPIP_symm' hf
