-- Prove2me | solution 1 for GaussianMatrix.gaussian_dist_colspace_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:56:01.781075+00:00
-- url     : https://prove2.me/submissions/f3c5f985-12d2-4d2f-909d-cf4d9c09eb63

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_chi_square_lower_tail

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open scoped RealInnerProductSpace in
/-- Rotation invariance in coordinates: for an orthonormal basis `b` of `ℝᴺ` indexed by `ι`,
the coordinates `(⟪b i, g⟫)ᵢ` of a standard Gaussian vector `g` are i.i.d. standard Gaussian. -/
theorem measurePreserving_orthonormalBasis_coords {N : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin N))) :
    MeasurePreserving (fun g : Fin N → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 g)))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hm1 : Measurable (fun g : Fin N → ℝ => WithLp.toLp 2 g) := by fun_prop
  have hm2 : Measurable (fun x : EuclideanSpace ℝ (Fin N) => b.repr x) :=
    b.repr.continuous.measurable
  have hm3 : Measurable (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) := by fun_prop
  refine ⟨hm3.comp (hm2.comp hm1), ?_⟩
  have h := map_pi_eq_stdGaussian (ι := Fin N)
  have h' := map_pi_eq_stdGaussian (ι := ι)
  have hfun : (fun g : Fin N → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 g)))
      = (fun y : EuclideanSpace ℝ ι => WithLp.ofLp y) ∘ ((fun x => b.repr x) ∘
          (fun g : Fin N → ℝ => WithLp.toLp 2 g)) := rfl
  rw [hfun, ← Measure.map_map hm3 (hm2.comp hm1), ← Measure.map_map hm2 hm1, h]
  rw [show (fun x : EuclideanSpace ℝ (Fin N) => b.repr x) = ⇑b.repr from rfl, stdGaussian_map,
    ← h', Measure.map_map hm3 (by fun_prop)]
  exact Measure.map_id

end GaussianMatrix

open GaussianMatrix
open scoped RealInnerProductSpace

theorem solution {N p d : ℕ} (B : Matrix (Fin N) (Fin p) ℝ)
    (hd : 1 ≤ d) (hrank : B.rank + d ≤ N) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ d) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
      {g | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by
  /- Geometry: the column space `V` of `B`, an orthonormal family `w` of `d` vectors in `Vᗮ`,
  and an orthonormal basis `b` of `ℝᴺ` (indexed by `Fin d ⊕ Fin (N - d)`) extending `w`. -/
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap
      (LinearMap.range B.mulVecLin)
  have hV : Module.finrank ℝ V = B.rank := by
    rw [Matrix.rank]; exact LinearEquiv.finrank_map_eq _ _
  have hmemV : ∀ c : Fin p → ℝ, WithLp.toLp 2 (B *ᵥ c) ∈ V := fun c =>
    Submodule.mem_map.2 ⟨B *ᵥ c, ⟨c, rfl⟩, rfl⟩
  have hW : d ≤ Module.finrank ℝ Vᗮ := by
    have := Submodule.finrank_add_finrank_orthogonal V
    rw [finrank_euclideanSpace_fin] at this; omega
  let bW := stdOrthonormalBasis ℝ Vᗮ
  let w : Fin d → EuclideanSpace ℝ (Fin N) := fun k => (bW (Fin.castLE hW k) : _)
  have hw : Orthonormal ℝ w :=
    (bW.orthonormal.comp _ (Fin.castLE_injective hW)).comp_linearIsometry Vᗮ.subtypeₗᵢ
  have hwV : ∀ k, w k ∈ Vᗮ := fun k => (bW (Fin.castLE hW k)).2
  let v : Fin d ⊕ Fin (N - d) → EuclideanSpace ℝ (Fin N) := Sum.elim w 0
  have hv : Orthonormal ℝ
      ((Set.range (Sum.inl : Fin d → Fin d ⊕ Fin (N - d))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, ⟨k, rfl⟩⟩ ⟨_, ⟨l, rfl⟩⟩
    have h1 := (orthonormal_iff_ite.1 hw) k l
    by_cases hkl : k = l
    · subst hkl; simpa [Set.domRestrict_apply, v] using h1
    · rw [if_neg (fun h => hkl (Sum.inl_injective (congrArg Subtype.val h)))]
      simpa [Set.domRestrict_apply, v, hkl] using h1
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        omega)
  have hbk : ∀ k, b (Sum.inl k) = w k := fun k => hb _ ⟨k, rfl⟩
  /- Bessel: the squared distance to `V` dominates `∑ₖ ⟪w k, g⟫²`. -/
  have hbessel : ∀ g : Fin N → ℝ,
      ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2
        ≤ (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 := by
    intro g
    have hS0 : 0 ≤ ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2 := by positivity
    have hc : ∀ c : Fin p → ℝ, Real.sqrt (∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2)
        ≤ Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c)) := by
      intro c
      refine Real.sqrt_le_sqrt ?_
      have h1 : ∀ k, ⟪w k, WithLp.toLp 2 g⟫ = ⟪w k, WithLp.toLp 2 (g - B *ᵥ c)⟫ := by
        intro k
        rw [WithLp.toLp_sub, inner_sub_right,
          Submodule.inner_left_of_mem_orthogonal (hmemV c) (hwV k), sub_zero]
      have h2 := hw.sum_inner_products_le (x := WithLp.toLp 2 (g - B *ᵥ c))
        (s := Finset.univ)
      rw [EuclideanSpace.real_norm_sq_eq] at h2
      simp only [Real.norm_eq_abs, sq_abs] at h2
      simp_rw [h1]
      refine h2.trans (le_of_eq ?_)
      simp [dotProduct, sq]
    have hle := le_ciInf hc
    calc ∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2
        = Real.sqrt (∑ k : Fin d, ⟪w k, WithLp.toLp 2 g⟫ ^ 2) ^ 2 := (Real.sq_sqrt hS0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  /- Probability: rotate and take the marginal on the first `d` coordinates. -/
  set T : (Fin N → ℝ) → (Fin d ⊕ Fin (N - d) → ℝ) :=
    fun g => WithLp.ofLp (b.repr (WithLp.toLp 2 g)) with hT_def
  have hT := measurePreserving_orthonormalBasis_coords b
  set C' : Set (Fin d ⊕ Fin (N - d) → ℝ) := {h | ∑ k : Fin d, h (Sum.inl k) ^ 2 ≤ u} with hC'
  have hC'm : MeasurableSet C' := by
    refine measurableSet_le ?_ measurable_const
    exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).pow_const 2
  have hsub : {g : Fin N → ℝ | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ⊆ T ⁻¹' C' := by
    intro g hg
    simp only [Set.mem_preimage, hC', Set.mem_ofPred_eq, hT_def] at hg ⊢
    refine le_trans (le_of_eq ?_) ((hbessel g).trans hg)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthonormalBasis.repr_apply_apply, hbk]
  have hmarg : (Measure.pi fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1) C'
      = (Measure.pi fun _ : Fin d => gaussianReal 0 1) {g | ∑ i, g i ^ 2 ≤ u} := by
    have he := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1)
    have hpre : C' = (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ Fin (N - d) => ℝ) ⁻¹'
        ({g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ u} ×ˢ Set.univ) := by
      ext h; simp [hC', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
    have hC0 : MeasurableSet {g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ u} := by
      refine measurableSet_le ?_ measurable_const
      exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).pow_const 2
    rw [hpre, he.measure_preimage (hC0.prod MeasurableSet.univ).nullMeasurableSet,
      Measure.prod_prod, measure_univ, mul_one]
  calc (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        {g | (⨅ c : Fin p → ℝ, Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) ^ 2 ≤ u}
      ≤ (Measure.pi fun _ : Fin N => gaussianReal 0 1) (T ⁻¹' C') := measure_mono hsub
    _ = (Measure.pi fun _ : Fin d ⊕ Fin (N - d) => gaussianReal 0 1) C' :=
        hT.measure_preimage hC'm.nullMeasurableSet
    _ = _ := hmarg
    _ ≤ _ := chi_square_lower_tail hd u hu hud
