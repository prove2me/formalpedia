-- Prove2me | solution 1 for Disjunctive.Polarity.projection_dimension_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:05:02.209998+00:00
-- url     : https://prove2.me/submissions/3e4281d4-5956-48c7-ba7c-04ea038fbcbb

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem



namespace Disjunctive.Polarity

section PDim

open Matrix Topology Filter

variable {m p q : ℕ}

/-- The row map `z ↦ A z.1 + B z.2`. -/
noncomputable def pdRow (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) :
    ((Fin p → ℝ) × (Fin q → ℝ)) →ₗ[ℝ] (Fin m → ℝ) :=
  A.mulVecLin ∘ₗ LinearMap.fst ℝ _ _ + B.mulVecLin ∘ₗ LinearMap.snd ℝ _ _

lemma pdRow_apply (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (z : (Fin p → ℝ) × (Fin q → ℝ)) (i : Fin m) :
    pdRow A B z i = A.mulVec z.1 i + B.mulVec z.2 i := by
  simp [pdRow]

lemma pd_mem_poly2 (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) (z : (Fin p → ℝ) × (Fin q → ℝ)) :
    z ∈ Poly2 A B b ↔ ∀ i, pdRow A B z i ≤ b i := by
  simp only [pdRow_apply]
  exact Iff.rfl

/-- The kernel of the tight rows. -/
def pdKT (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (T : Set (Fin m)) :
    Submodule ℝ ((Fin p → ℝ) × (Fin q → ℝ)) where
  carrier := {d | ∀ i ∈ T, pdRow A B d i = 0}
  add_mem' := by
    intro x y hx hy i hi
    rw [map_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  zero_mem' := by intro i _; simp
  smul_mem' := by
    intro c x hx i hi
    rw [map_smul, Pi.smul_apply, hx i hi, smul_zero]

lemma pd_vectorSpan (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) (hne : (Poly2 A B b).Nonempty) :
    vectorSpan ℝ (Poly2 A B b) = pdKT A B (TightRows A B b (Poly2 A B b)) := by
  classical
  set T := TightRows A B b (Poly2 A B b) with hT
  have hTi : ∀ i ∈ T, ∀ z ∈ Poly2 A B b, pdRow A B z i = b i := by
    intro i hi z hz; rw [pdRow_apply]; exact hi z hz
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨z1, hz1, z2, hz2, rfl⟩ i hi
    show pdRow A B (z1 -ᵥ z2) i = 0
    rw [vsub_eq_sub, map_sub, Pi.sub_apply, hTi i hi z1 hz1, hTi i hi z2 hz2, sub_self]
  · obtain ⟨zs, hzs⟩ := hne
    have hw : ∀ i : Fin m, ∃ w ∈ Poly2 A B b, (i ∉ T → pdRow A B w i < b i) := by
      intro i
      by_cases hi : i ∈ T
      · exact ⟨zs, hzs, fun h => absurd hi h⟩
      · have : ¬ ∀ ux ∈ Poly2 A B b, A.mulVec ux.1 i + B.mulVec ux.2 i = b i := hi
        push_neg at this
        obtain ⟨w, hw, hne⟩ := this
        refine ⟨w, hw, fun _ => ?_⟩
        rw [pdRow_apply]
        exact lt_of_le_of_ne (((pd_mem_poly2 A B b w).mp hw i).trans_eq' (pdRow_apply A B w i).symm) hne
    choose w hwQ hwlt using hw
    set z0 := ((m : ℝ)⁻¹) • ∑ i, w i with hz0
    have hrz0 : ∀ j, pdRow A B z0 j = (m : ℝ)⁻¹ * ∑ i, pdRow A B (w i) j := by
      intro j
      rw [hz0, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hmpos : ∀ j : Fin m, (0 : ℝ) < m := fun j => by
      have := j.pos; exact_mod_cast this
    have hz0Q : z0 ∈ Poly2 A B b := by
      rw [pd_mem_poly2]
      intro j
      rw [hrz0, inv_mul_le_iff₀ (hmpos j)]
      calc ∑ i, pdRow A B (w i) j ≤ ∑ _i : Fin m, b j :=
            Finset.sum_le_sum (fun i _ => (pd_mem_poly2 A B b _).mp (hwQ i) j)
        _ = m * b j := by simp
    have hz0lt : ∀ j, j ∉ T → pdRow A B z0 j < b j := by
      intro j hj
      rw [hrz0, inv_mul_lt_iff₀ (hmpos j)]
      calc ∑ i, pdRow A B (w i) j < ∑ _i : Fin m, b j :=
            Finset.sum_lt_sum (fun i _ => (pd_mem_poly2 A B b _).mp (hwQ i) j)
              ⟨j, Finset.mem_univ _, hwlt j hj⟩
        _ = m * b j := by simp
    clear_value z0
    intro d hd
    have hd' : ∀ i ∈ T, pdRow A B d i = 0 := hd
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ j, j ∉ T → ε * |pdRow A B d j| < b j - pdRow A B z0 j := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j ∈ T
      · exact Filter.Eventually.of_forall (fun _ h => absurd hj h)
      · have ht : Tendsto (fun ε : ℝ => ε * |pdRow A B d j|) (𝓝[>] 0) (𝓝 0) :=
          ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left
            nhdsWithin_le_nhds
        have hpos : 0 < b j - pdRow A B z0 j := by linarith [hz0lt j hj]
        exact (ht.eventually (gt_mem_nhds hpos)).mono (fun ε h _ => h)
    obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hεpos' : 0 < ε := hεpos
    have hz1 : z0 + ε • d ∈ Poly2 A B b := by
      rw [pd_mem_poly2]
      intro j
      rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : j ∈ T
      · rw [hd' j hj, mul_zero, add_zero]
        exact (pd_mem_poly2 A B b z0).mp hz0Q j
      · have h1 := hε j hj
        have h2 : ε * pdRow A B d j ≤ ε * |pdRow A B d j| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hεpos'.le
        linarith
    have : d = ε⁻¹ • ((z0 + ε • d) -ᵥ z0) := by
      rw [vsub_eq_sub, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hεpos'.ne', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hz1 hz0Q)

lemma pd_proj_eq (Q : Set ((Fin p → ℝ) × (Fin q → ℝ))) :
    ProjOntoX Q = (LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) '' Q := by
  ext x
  constructor
  · rintro ⟨u, hu⟩; exact ⟨(u, x), hu, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z.1, hz⟩

/-- Rank-nullity for the projection of a nonempty set. -/
lemma pd_B0 (Q : Set ((Fin p → ℝ) × (Fin q → ℝ))) (hne : Q.Nonempty) :
    PolyDim (ProjOntoX Q) +
      (Module.finrank ℝ (LinearMap.ker ((LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) ∘ₗ
        (vectorSpan ℝ Q).subtype)) : ℤ) = PolyDim Q := by
  classical
  have hne' : (ProjOntoX Q).Nonempty := by
    obtain ⟨z, hz⟩ := hne; exact ⟨z.2, z.1, hz⟩
  simp only [PolyDim, hne, hne', if_true]
  have hvs : vectorSpan ℝ (ProjOntoX Q) =
      Submodule.map (LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) (vectorSpan ℝ Q) := by
    rw [pd_proj_eq]
    exact (AffineMap.map_vectorSpan (LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)).toAffineMap).symm
  rw [hvs]
  have := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) ∘ₗ (vectorSpan ℝ Q).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at this
  exact_mod_cast this

/-- The `u`-kernel of the tight rows. -/
lemma pd_rank_add (A : Matrix (Fin m) (Fin p) ℝ) (T : Set (Fin m)) :
    Module.finrank ℝ (LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin)
      + SystemRankA A T = p := by
  have := LinearMap.finrank_range_add_finrank_ker
    (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin
  rw [Module.finrank_fin_fun] at this
  unfold SystemRankA Matrix.rank
  omega

lemma pd_mem_kerA (A : Matrix (Fin m) (Fin p) ℝ) (T : Set (Fin m)) (u : Fin p → ℝ) :
    u ∈ LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin ↔
      ∀ i ∈ T, A.mulVec u i = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    simpa [Matrix.mulVec, Matrix.submatrix, dotProduct] using this
  · intro h
    funext ⟨i, hi⟩
    have := h i hi
    simpa [Matrix.mulVec, Matrix.submatrix, dotProduct] using this

/-- The kernel of the projection restricted to a submodule inside `pdKT`. -/
lemma pd_B1 (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (T : Set (Fin m)) :
    Module.finrank ℝ (LinearMap.ker ((LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) ∘ₗ
        (pdKT A B T).subtype)) =
    Module.finrank ℝ (LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin) := by
  apply LinearEquiv.finrank_eq
  exact
  { toFun := fun v => ⟨v.1.1.1, by
      rw [pd_mem_kerA]
      intro i hi
      have h1 := v.1.2 i hi
      have h2 : v.1.1.2 = 0 := v.2
      rw [pdRow_apply, h2, Matrix.mulVec_zero, Pi.zero_apply, add_zero] at h1
      exact h1⟩
    invFun := fun u => ⟨⟨(u.1, 0), by
      intro i hi
      rw [pdRow_apply, Matrix.mulVec_zero, Pi.zero_apply, add_zero]
      exact (pd_mem_kerA A T u.1).mp u.2 i hi⟩, by
      simp⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl
    left_inv := by
      intro v
      apply Subtype.ext; apply Subtype.ext
      have h2 : v.1.1.2 = 0 := v.2
      ext <;> simp [h2]
    right_inv := by intro u; rfl }

theorem projection_dimension_formula_core (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hQ : (Poly2 A B b).Nonempty) :
    PolyDim (ProjOntoX (Poly2 A B b)) = PolyDim (Poly2 A B b) - (p : ℤ) + (EqRankA A B b : ℤ) := by
  have h0 := pd_B0 (Poly2 A B b) hQ
  rw [pd_vectorSpan A B b hQ, pd_B1] at h0
  have h1 := pd_rank_add A (TightRows A B b (Poly2 A B b))
  unfold EqRankA
  have h1' : (Module.finrank ℝ (LinearMap.ker (A.submatrix (Subtype.val :
      {i // i ∈ TightRows A B b (Poly2 A B b)} → Fin m) id).mulVecLin) : ℤ) +
      (SystemRankA A (TightRows A B b (Poly2 A B b)) : ℤ) = p := by exact_mod_cast h1
  linarith

end PDim

end Disjunctive.Polarity

open Disjunctive.Polarity


theorem solution {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hQ : (Poly2 A B b).Nonempty) :
    PolyDim (ProjOntoX (Poly2 A B b)) = PolyDim (Poly2 A B b) - (p : ℤ) + (EqRankA A B b : ℤ) := by
  exact projection_dimension_formula_core A B b hQ
