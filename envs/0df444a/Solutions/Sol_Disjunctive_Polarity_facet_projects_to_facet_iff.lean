-- Prove2me | solution 1 for Disjunctive.Polarity.facet_projects_to_facet_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:10:26.216502+00:00
-- url     : https://prove2.me/submissions/d4e9d200-a64d-4bad-9da4-160b9c1d0c86

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

section PFacet

open Matrix

variable {m p q : ℕ}

lemma pd_convex (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (Poly2 A B b) := by
  intro x hx y hy a c ha hc hac
  rw [pd_mem_poly2] at hx hy ⊢
  intro j
  rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hx j) ha
  have h2 := mul_le_mul_of_nonneg_left (hy j) hc
  have : a * b j + c * b j = b j := by rw [← add_mul, hac, one_mul]
  linarith

lemma pd_kerA_bot (A : Matrix (Fin m) (Fin p) ℝ) (T : Set (Fin m)) (h : SystemRankA A T = p)
    (u : Fin p → ℝ) (hu : ∀ i ∈ T, A.mulVec u i = 0) : u = 0 := by
  have h1 := pd_rank_add A T
  have h2 : Module.finrank ℝ (LinearMap.ker
      (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h2
  have : u ∈ LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin :=
    (pd_mem_kerA A T u).mpr hu
  rw [h2] at this
  exact (Submodule.mem_bot ℝ).mp this

theorem full_rank_core (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hFullRank : EqRankA A B b = p)
    (Fc : Set ((Fin p → ℝ) × (Fin q → ℝ))) (hFace : IsExtreme ℝ (Poly2 A B b) Fc)
    (d : ℕ) (hdimFc : PolyDim Fc = (d : ℤ)) :
    IsExtreme ℝ (ProjOntoX (Poly2 A B b)) (ProjOntoX Fc) ∧ PolyDim (ProjOntoX Fc) = (d : ℤ) := by
  classical
  set T := TightRows A B b (Poly2 A B b) with hT
  have hinj : ∀ u u' x, (u, x) ∈ Poly2 A B b → (u', x) ∈ Poly2 A B b → u = u' := by
    intro u u' x h1 h2
    have := pd_kerA_bot A T hFullRank (u - u') (fun i hi => by
      have e1 := hi _ h1
      have e2 := hi _ h2
      simp only at e1 e2
      rw [Matrix.mulVec_sub, Pi.sub_apply]
      linarith)
    exact sub_eq_zero.mp this
  have hFne : Fc.Nonempty := by
    by_contra h
    simp only [PolyDim, h, if_false] at hdimFc
    omega
  have hQne : (Poly2 A B b).Nonempty := hFne.mono hFace.subset
  refine ⟨⟨fun x ⟨u, hu⟩ => ⟨u, hFace.subset hu⟩, ?_⟩, ?_⟩
  · intro x1 hx1 x2 hx2 z hz hseg
    obtain ⟨u1, h1⟩ := hx1
    obtain ⟨u2, h2⟩ := hx2
    obtain ⟨uz, hzF⟩ := hz
    obtain ⟨a, c, ha, hc, hac, hz⟩ := hseg
    have hW : a • (u1, x1) + c • (u2, x2) ∈ Poly2 A B b :=
      pd_convex A B b h1 h2 ha.le hc.le hac
    have hW2 : (a • (u1, x1) + c • (u2, x2)).2 = z := by simp [hz]
    have heq : uz = (a • (u1, x1) + c • (u2, x2)).1 := by
      apply hinj uz _ z (hFace.subset hzF)
      rw [← hW2]; exact hW
    have hWF : a • (u1, x1) + c • (u2, x2) ∈ Fc := by
      have : a • (u1, x1) + c • (u2, x2) = (uz, z) := Prod.ext heq.symm hW2
      rw [this]; exact hzF
    exact ⟨u1, hFace.left_mem_of_mem_openSegment h1 h2 hWF ⟨a, c, ha, hc, hac, rfl⟩⟩
  · have h0 := pd_B0 Fc hFne
    have hker : LinearMap.ker ((LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) ∘ₗ
        (vectorSpan ℝ Fc).subtype) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv2 : v.1.2 = 0 := hv
      have hvQ : (v : (Fin p → ℝ) × (Fin q → ℝ)) ∈ pdKT A B T := by
        rw [← pd_vectorSpan A B b hQne]
        exact vectorSpan_mono ℝ hFace.subset v.2
      have hu : v.1.1 = 0 := pd_kerA_bot A T hFullRank _ (fun i hi => by
        have := hvQ i hi
        rw [pdRow_apply, hv2, Matrix.mulVec_zero, Pi.zero_apply, add_zero] at this
        exact this)
      apply Subtype.ext
      exact Prod.ext hu hv2
    rw [hker, finrank_bot] at h0
    simp only [Nat.cast_zero, add_zero] at h0
    rw [h0, hdimFc]

end PFacet

section PFacet2

open Matrix

variable {m p q : ℕ}

/-- The doubled system describing `FQ`. -/
def fA2 (A : Matrix (Fin m) (Fin p) ℝ) (α : Fin p → ℝ) : Matrix (Fin (m + 2)) (Fin p) ℝ :=
  Fin.cons α (Fin.cons (-α) A)

def fb2 (b : Fin m → ℝ) (β0 : ℝ) : Fin (m + 2) → ℝ := Fin.cons β0 (Fin.cons (-β0) b)

lemma f_cons_mulVec_zero {n : ℕ} (α : Fin p → ℝ) (A : Matrix (Fin n) (Fin p) ℝ) (u : Fin p → ℝ) :
    Matrix.mulVec (Fin.cons α A : Matrix (Fin (n + 1)) (Fin p) ℝ) u 0 = dotProduct α u := rfl

lemma f_cons_mulVec_succ {n : ℕ} (α : Fin p → ℝ) (A : Matrix (Fin n) (Fin p) ℝ) (u : Fin p → ℝ)
    (i : Fin n) :
    Matrix.mulVec (Fin.cons α A : Matrix (Fin (n + 1)) (Fin p) ℝ) u i.succ = A.mulVec u i := rfl

lemma f_mem2 (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ)
    (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ) (z : (Fin p → ℝ) × (Fin q → ℝ)) :
    z ∈ Poly2 (fA2 A α) (fA2 B β) (fb2 b β0) ↔
      (α ⬝ᵥ z.1 + β ⬝ᵥ z.2 ≤ β0 ∧ (-α) ⬝ᵥ z.1 + (-β) ⬝ᵥ z.2 ≤ -β0 ∧
        ∀ i, A.mulVec z.1 i + B.mulVec z.2 i ≤ b i) := by
  show (∀ i : Fin (m + 2), (fA2 A α).mulVec z.1 i + (fA2 B β).mulVec z.2 i ≤ fb2 b β0 i) ↔ _
  rw [Fin.forall_fin_succ, Fin.forall_fin_succ]
  exact Iff.rfl

lemma f_eq (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ)
    (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ) :
    FacetCandidate A B b α β β0 = Poly2 (fA2 A α) (fA2 B β) (fb2 b β0) := by
  ext z
  rw [f_mem2, neg_dotProduct, neg_dotProduct]
  constructor
  · rintro ⟨hQ, he⟩
    have he' : α ⬝ᵥ z.1 + β ⬝ᵥ z.2 = β0 := he
    exact ⟨he'.le, by linarith, fun i => hQ i⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i => h3 i, show α ⬝ᵥ z.1 + β ⬝ᵥ z.2 = β0 by linarith⟩

lemma pd_mem_kerA_cons {n : ℕ} (α : Fin p → ℝ) (A : Matrix (Fin n) (Fin p) ℝ)
    (T : Set (Fin (n + 1))) (u : Fin p → ℝ) :
    u ∈ LinearMap.ker (Matrix.submatrix (Fin.cons α A : Matrix (Fin (n + 1)) (Fin p) ℝ)
      (Subtype.val : {i // i ∈ T} → Fin (n + 1)) id).mulVecLin ↔
      ∀ i ∈ T, Matrix.mulVec (Fin.cons α A : Matrix (Fin (n + 1)) (Fin p) ℝ) u i = 0 :=
  pd_mem_kerA _ T u

lemma f_ker_eq (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ)
    (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ) :
    LinearMap.ker ((fA2 A α).submatrix (Subtype.val : {i // i ∈ TightRows (fA2 A α) (fA2 B β)
      (fb2 b β0) (Poly2 (fA2 A α) (fA2 B β) (fb2 b β0))} → Fin (m + 2)) id).mulVecLin =
    LinearMap.ker (Matrix.submatrix (Fin.cons α A : Matrix (Fin (m + 1)) (Fin p) ℝ)
      (Subtype.val : {i // i ∈ TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
        (FacetCandidate A B b α β β0)} → Fin (m + 1)) id).mulVecLin := by
  ext u
  rw [pd_mem_kerA, pd_mem_kerA_cons, ← f_eq]
  set FQ := FacetCandidate A B b α β β0 with hFQ
  have m0L : (0 : Fin (m + 2)) ∈ TightRows (fA2 A α) (fA2 B β) (fb2 b β0) FQ := by
    intro ux hux
    exact hux.2
  have m1L : (Fin.succ 0 : Fin (m + 2)) ∈ TightRows (fA2 A α) (fA2 B β) (fb2 b β0) FQ := by
    intro ux hux
    have h2 : α ⬝ᵥ ux.1 + β ⬝ᵥ ux.2 = β0 := hux.2
    show (-α) ⬝ᵥ ux.1 + (-β) ⬝ᵥ ux.2 = -β0
    rw [neg_dotProduct, neg_dotProduct]; linarith
  have m0R : (0 : Fin (m + 1)) ∈ TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b) FQ := by
    intro ux hux
    exact hux.2
  have mss : ∀ j : Fin m, (j.succ.succ ∈ TightRows (fA2 A α) (fA2 B β) (fb2 b β0) FQ ↔
      j.succ ∈ TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b) FQ) := fun j => Iff.rfl
  constructor
  · intro h i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h 0 m0L
    · exact h j.succ.succ ((mss j).mpr hi)
  · intro h i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact h 0 m0R
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · have h0 : α ⬝ᵥ u = 0 := h 0 m0R
        show (-α) ⬝ᵥ u = 0
        rw [neg_dotProduct, h0, neg_zero]
      · exact h j.succ ((mss j).mp hi)

theorem facet_projection_dimension_core (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    PolyDim (ProjOntoX (FacetCandidate A B b α β β0)) =
      PolyDim (ProjOntoX (Poly2 A B b)) - 1 +
        ((SystemRankA (Fin.cons α A)
            (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
              (FacetCandidate A B b α β β0)) : ℤ) -
          (EqRankA A B b : ℤ)) := by
  have hFne := hFacet.2.1
  have hQne : (Poly2 A B b).Nonempty := hFne.mono hFacet.1.subset
  have hQ := pd_B0 (Poly2 A B b) hQne
  rw [pd_vectorSpan A B b hQne, pd_B1] at hQ
  have hrQ := pd_rank_add A (TightRows A B b (Poly2 A B b))
  have hne2 : (Poly2 (fA2 A α) (fA2 B β) (fb2 b β0)).Nonempty := by rw [← f_eq]; exact hFne
  have hF := pd_B0 _ hne2
  rw [pd_vectorSpan _ _ _ hne2, pd_B1, f_ker_eq] at hF
  have hrF := pd_rank_add (Fin.cons α A : Matrix (Fin (m + 1)) (Fin p) ℝ)
    (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b) (FacetCandidate A B b α β β0))
  have hdim := hFacet.2.2
  have e1 : PolyDim (ProjOntoX (FacetCandidate A B b α β β0)) =
      PolyDim (ProjOntoX (Poly2 (fA2 A α) (fA2 B β) (fb2 b β0))) := by rw [f_eq]
  have e2 : PolyDim (FacetCandidate A B b α β β0) =
      PolyDim (Poly2 (fA2 A α) (fA2 B β) (fb2 b β0)) := by rw [f_eq]
  rw [e1]
  rw [e2] at hdim
  unfold EqRankA
  have hrQ' : (Module.finrank ℝ (LinearMap.ker (A.submatrix (Subtype.val :
      {i // i ∈ TightRows A B b (Poly2 A B b)} → Fin m) id).mulVecLin) : ℤ) +
      (SystemRankA A (TightRows A B b (Poly2 A B b)) : ℤ) = p := by exact_mod_cast hrQ
  have hrF' := congrArg (fun n : ℕ => (n : ℤ)) hrF
  push_cast at hrF'
  linarith

theorem facet_iff_core (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    IsFacet (ProjOntoX (Poly2 A B b)) (ProjOntoX (FacetCandidate A B b α β β0)) ↔
      SystemRankA (Fin.cons α A)
          (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
            (FacetCandidate A B b α β β0)) =
        EqRankA A B b := by
  have hcore := facet_projection_dimension_core A B b α β β0 hFacet
  constructor
  · intro h
    have h2 := h.2.2
    rw [hcore] at h2
    have : ((SystemRankA (Fin.cons α A)
          (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
            (FacetCandidate A B b α β β0)) : ℕ) : ℤ) = (EqRankA A B b : ℤ) := by linarith
    exact_mod_cast this
  · intro hr
    have hFne := hFacet.2.1
    set FQ := FacetCandidate A B b α β β0 with hFQ
    set T := TightRows A B b (Poly2 A B b) with hT
    set T' := TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b) FQ with hT'
    have hFQQ : FQ ⊆ Poly2 A B b := hFacet.1.subset
    have m0R : (0 : Fin (m + 1)) ∈ T' := by
      intro ux hux
      exact hux.2
    have hle : LinearMap.ker (Matrix.submatrix (Fin.cons α A : Matrix (Fin (m + 1)) (Fin p) ℝ)
        (Subtype.val : {i // i ∈ T'} → Fin (m + 1)) id).mulVecLin ≤
        LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin := by
      intro u hu
      rw [pd_mem_kerA_cons] at hu
      rw [pd_mem_kerA]
      intro i hi
      have hs : i.succ ∈ T' := by
        intro ux hux
        exact hi ux (hFQQ hux)
      exact hu i.succ hs
    have hrQ := pd_rank_add A T
    have hrF := pd_rank_add (Fin.cons α A : Matrix (Fin (m + 1)) (Fin p) ℝ) T'
    have hEq : EqRankA A B b = SystemRankA A T := rfl
    have hkeq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hα : ∀ u : Fin p → ℝ, (∀ i ∈ T, A.mulVec u i = 0) → α ⬝ᵥ u = 0 := by
      intro u hu
      have h1 : u ∈ LinearMap.ker (A.submatrix (Subtype.val : {i // i ∈ T} → Fin m) id).mulVecLin :=
        (pd_mem_kerA A T u).mpr hu
      rw [← hkeq, pd_mem_kerA_cons] at h1
      exact h1 0 m0R
    refine ⟨⟨fun x ⟨u, hu⟩ => ⟨u, hFQQ hu⟩, ?_⟩, ?_, ?_⟩
    · intro x1 hx1 x2 hx2 z hz hseg
      obtain ⟨u1, h1⟩ := hx1
      obtain ⟨u2, h2⟩ := hx2
      obtain ⟨uz, hzF⟩ := hz
      obtain ⟨a, c, ha, hc, hac, hz⟩ := hseg
      set W := a • (u1, x1) + c • (u2, x2) with hWdef
      have hW : W ∈ Poly2 A B b := pd_convex A B b h1 h2 ha.le hc.le hac
      have hW2 : W.2 = z := by simp [hWdef, hz]
      have hzQ : (uz, z) ∈ Poly2 A B b := hFQQ hzF
      have hdiff : α ⬝ᵥ (uz - W.1) = 0 := by
        apply hα
        intro i hi
        have e1 := hi _ hzQ
        have e2 := hi _ hW
        simp only at e1 e2
        rw [hW2] at e2
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        linarith
      have hzeq : α ⬝ᵥ uz + β ⬝ᵥ z = β0 := hzF.2
      have hWF : W ∈ FQ := by
        refine ⟨hW, ?_⟩
        show α ⬝ᵥ W.1 + β ⬝ᵥ W.2 = β0
        rw [dotProduct_sub] at hdiff
        rw [hW2]; linarith
      exact ⟨u1, hFacet.1.left_mem_of_mem_openSegment h1 h2 hWF ⟨a, c, ha, hc, hac, rfl⟩⟩
    · obtain ⟨z, hz⟩ := hFne
      exact ⟨z.2, z.1, hz⟩
    · rw [hcore, hr, sub_self, add_zero]

end PFacet2

end Disjunctive.Polarity

open Disjunctive.Polarity


theorem solution {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    IsFacet (ProjOntoX (Poly2 A B b)) (ProjOntoX (FacetCandidate A B b α β β0)) ↔
      SystemRankA (Fin.cons α A)
          (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
            (FacetCandidate A B b α β β0)) =
        EqRankA A B b := by
  exact facet_iff_core A B b α β β0 hFacet
