-- Prove2me | solution 1 for BLTCounting.AccuracySpace.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:30.614419+00:00
-- url     : https://prove2.me/submissions/349842be-90f8-4d24-b155-f169c171c801

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

open Matrix BLTCounting.AccuracySpace

namespace AuxThm21

lemma eucl_inner_eq_dotProduct {K : ℕ} (x y : EuclideanSpace ℂ (Fin K)) :
    inner ℂ x y = star x.ofLp ⬝ᵥ y.ofLp := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, dotProduct, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma repr_symm_eq_sum {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) (w : EuclideanSpace ℂ ι) :
    b.repr.symm w = ∑ i : ι, w.ofLp i • b i := by
  have h := (b.sum_repr (b.repr.symm w)).symm
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

lemma euclSq_pos_of_ne_zero {K : ℕ} {u : Fin K → ℂ} (hu : u ≠ 0) :
    0 < euclSq u := by
  unfold euclSq
  by_contra hle
  have hsum0 : ∑ i : Fin K, ‖u i‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0
  apply hu
  ext i
  have hi := hall i (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

lemma rayleigh_smul {K : ℕ} (A : Matrix (Fin K) (Fin K) ℂ) {t : ℝ} (ht : t ≠ 0)
    (u : Fin K → ℂ) :
    rayleigh A ((t : ℂ) • u) = rayleigh A u := by
  unfold rayleigh euclSq
  have hnum : (star ((t : ℂ) • u) ⬝ᵥ (A *ᵥ ((t : ℂ) • u))).re =
      t ^ 2 * (star u ⬝ᵥ (A *ᵥ u)).re := by
    have h1 : star ((t : ℂ) • u) ⬝ᵥ (A *ᵥ ((t : ℂ) • u)) =
        (((t ^ 2 : ℝ) : ℂ)) * (star u ⬝ᵥ (A *ᵥ u)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
      simp [smul_eq_mul, sq, mul_assoc]
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hden : (∑ i : Fin K, ‖((t : ℂ) • u) i‖ ^ 2) = t ^ 2 * ∑ i : Fin K, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.smul_apply, mul_pow, sq_abs]
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

lemma exists_isLeast_rayleigh {K q : ℕ} (A : Matrix (Fin K) (Fin K) ℂ)
    (U : Submodule ℂ (Fin K → ℂ)) (hq1 : 1 ≤ q) (hU : Module.finrank ℂ U = q) :
    ∃ v : ℝ, IsLeast (rayleigh A '' {u | u ∈ U ∧ u ≠ 0}) v := by
  let L_eq : (Fin K → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin K) :=
    (WithLp.linearEquiv 2 ℂ (Fin K → ℂ)).symm
  let U_E : Submodule ℂ (EuclideanSpace ℂ (Fin K)) := U.map L_eq.toLinearMap
  have hfin_UE : Module.finrank ℂ U_E = q := by
    rw [LinearEquiv.finrank_map_eq L_eq U, hU]
  have hUE_ne_bot : U_E ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin_UE
    omega
  rcases U_E.exists_mem_ne_zero_of_ne_bot hUE_ne_bot with ⟨x₀, hx₀_mem, hx₀_ne⟩
  let S : Set (EuclideanSpace ℂ (Fin K)) := (U_E : Set _) ∩ Metric.sphere 0 1
  have hS_ne : S.Nonempty := by
    have hx₀_norm : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hx₀_ne
    refine ⟨(((‖x₀‖⁻¹ : ℝ) : ℂ)) • x₀, U_E.smul_mem _ hx₀_mem, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ hx₀_norm]
  have hS_comp : IsCompact S :=
    (isCompact_sphere (0 : EuclideanSpace ℂ (Fin K)) 1).inter_left
      (Submodule.closed_of_finiteDimensional U_E)
  let f : EuclideanSpace ℂ (Fin K) → ℝ := fun x => (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re
  have hf_cont : Continuous f := by
    have hf_eq : f = fun x => ∑ i : Fin K, ∑ j : Fin K,
        (star (x.ofLp i) * (A i j * x.ofLp j)).re := by
      ext x
      simp [f, dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
    rw [hf_eq]
    refine continuous_finsetSum Finset.univ fun i _ =>
      continuous_finsetSum Finset.univ fun j _ => ?_
    have hproj_i : Continuous (fun x : EuclideanSpace ℂ (Fin K) => x.ofLp i) :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    have hproj_j : Continuous (fun x : EuclideanSpace ℂ (Fin K) => x.ofLp j) :=
      (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)
    exact Complex.continuous_re.comp ((continuous_star.comp hproj_i).mul (continuous_const.mul hproj_j))
  rcases hS_comp.exists_isMinOn hS_ne hf_cont.continuousOn with ⟨x_min, ⟨hxmin_U, hxmin_sph⟩, hmin⟩
  rcases Submodule.mem_map.mp hxmin_U with ⟨u_min, hu_min_U, hLu⟩
  have hu_min_eq : u_min = x_min.ofLp := by
    change (WithLp.toLp 2 u_min) = x_min at hLu
    exact congrArg WithLp.ofLp hLu
  have hxmin_norm1 : euclSq u_min = 1 := by
    rw [hu_min_eq]
    have h1 : ‖x_min‖ = 1 := mem_sphere_zero_iff_norm.mp hxmin_sph
    have hsq : ‖x_min‖ ^ 2 = euclSq x_min.ofLp := by
      rw [PiLp.norm_sq_eq_of_L2]
      rfl
    rw [h1, one_pow] at hsq
    exact hsq.symm
  have hu_min_ne : u_min ≠ 0 := by
    intro h0
    rw [h0] at hxmin_norm1
    simp [euclSq] at hxmin_norm1
  refine ⟨rayleigh A u_min, ⟨u_min, ⟨hu_min_U, hu_min_ne⟩, rfl⟩, ?_⟩
  rintro _ ⟨u, ⟨hu_U, hu_ne⟩, rfl⟩
  have hpos_sq : 0 < euclSq u := euclSq_pos_of_ne_zero hu_ne
  let s : ℝ := (Real.sqrt (euclSq u))⁻¹
  have hs_pos : 0 < s := by positivity
  let u_unit : Fin K → ℂ := (s : ℂ) • u
  have hx_unit_mem : WithLp.toLp 2 u_unit ∈ S := by
    refine ⟨Submodule.mem_map.mpr ⟨u_unit, U.smul_mem (s : ℂ) hu_U, rfl⟩, ?_⟩
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖WithLp.toLp 2 u_unit‖ ^ 2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      have hsum_s : (∑ i : Fin K, ‖(WithLp.toLp 2 u_unit).ofLp i‖ ^ 2) = s ^ 2 * euclSq u := by
        unfold euclSq
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change ‖(s : ℂ) * u i‖ ^ 2 = s ^ 2 * ‖u i‖ ^ 2
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le, mul_pow]
      rw [hsum_s]
      dsimp [s]
      rw [inv_pow, Real.sq_sqrt hpos_sq.le, inv_mul_cancel₀ (ne_of_gt hpos_sq)]
    exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg (WithLp.toLp 2 u_unit)])
  have hle_f : f x_min ≤ f (WithLp.toLp 2 u_unit) := hmin hx_unit_mem
  have hray_min : rayleigh A u_min = f x_min := by
    unfold rayleigh
    rw [hxmin_norm1, div_one, hu_min_eq]
  have hray_unit : rayleigh A u_unit = f (WithLp.toLp 2 u_unit) := by
    unfold rayleigh
    have hnorm_u : euclSq u_unit = 1 := by
      have h1 : ‖WithLp.toLp 2 u_unit‖ = 1 := mem_sphere_zero_iff_norm.mp hx_unit_mem.2
      have hsq : ‖WithLp.toLp 2 u_unit‖ ^ 2 = euclSq u_unit := by
        rw [PiLp.norm_sq_eq_of_L2]
        rfl
      rw [h1, one_pow] at hsq
      exact hsq.symm
    rw [hnorm_u, div_one]
  rw [hray_min, ← rayleigh_smul A (ne_of_gt hs_pos) u, hray_unit]
  exact hle_f

lemma spectral_expansion_aux {K : ℕ} {A : Matrix (Fin K) (Fin K) ℂ} (hA : A.IsHermitian)
    (σ : Fin K ≃ Fin (Fintype.card (Fin K)))
    (hσ : ∀ i : Fin K, hA.eigenvalues i = hA.eigenvalues₀ (σ i)) :
    ∃ e : OrthonormalBasis (Fin (Fintype.card (Fin K))) ℂ (EuclideanSpace ℂ (Fin K)),
      ∀ u : Fin K → ℂ,
        euclSq u = ∑ m : Fin (Fintype.card (Fin K)), ‖(e.repr (WithLp.toLp 2 u)).ofLp m‖ ^ 2 ∧
        (star u ⬝ᵥ (A *ᵥ u)).re =
          ∑ m : Fin (Fintype.card (Fin K)),
            hA.eigenvalues₀ m * ‖(e.repr (WithLp.toLp 2 u)).ofLp m‖ ^ 2 := by
  let e := hA.eigenvectorBasis.reindex σ
  refine ⟨e, fun u => ?_⟩
  let x : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 u
  let c : Fin (Fintype.card (Fin K)) → ℂ := (e.repr x).ofLp
  have heucl : euclSq u = ∑ m : Fin (Fintype.card (Fin K)), ‖c m‖ ^ 2 := by
    unfold euclSq
    have h1 : ∑ i : Fin K, ‖u i‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    rw [h1, ← e.repr.norm_map x, PiLp.norm_sq_eq_of_L2]
  refine ⟨heucl, ?_⟩
  have hx_eq : x = e.repr.symm (WithLp.toLp 2 c) := by
    have h : WithLp.toLp 2 c = e.repr x := rfl
    rw [h, LinearIsometryEquiv.symm_apply_apply]
  let cA : Fin (Fintype.card (Fin K)) → ℂ := fun m => c m * ((hA.eigenvalues₀ m : ℝ) : ℂ)
  have hAmul : A *ᵥ u = (e.repr.symm (WithLp.toLp 2 cA)).ofLp := by
    have hu_eq : u = (e.repr.symm (WithLp.toLp 2 c)).ofLp := congrArg WithLp.ofLp hx_eq
    have hr1 : (e.repr.symm (WithLp.toLp 2 c)).ofLp =
        ∑ m : Fin (Fintype.card (Fin K)), c m • (e m).ofLp := by
      rw [repr_symm_eq_sum]
      ext k
      simp
    have hr2 : (e.repr.symm (WithLp.toLp 2 cA)).ofLp =
        ∑ m : Fin (Fintype.card (Fin K)), cA m • (e m).ofLp := by
      rw [repr_symm_eq_sum]
      ext k
      simp [cA]
    rw [hu_eq, hr1, hr2, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have he_m : e m = hA.eigenvectorBasis (σ.symm m) := by
      simp [e, OrthonormalBasis.reindex_apply]
    have heig_m : hA.eigenvalues (σ.symm m) = hA.eigenvalues₀ m := by
      rw [hσ (σ.symm m), σ.apply_symm_apply]
    rw [Matrix.mulVec_smul, he_m, hA.mulVec_eigenvectorBasis (σ.symm m), heig_m]
    ext k
    simp [cA, Complex.real_smul, mul_assoc, mul_comm ((hA.eigenvalues₀ m : ℝ) : ℂ)]
  rw [hAmul]
  have hu_of : u = (e.repr.symm (WithLp.toLp 2 c)).ofLp := congrArg WithLp.ofLp hx_eq
  conv_lhs => rw [hu_of]
  rw [← eucl_inner_eq_dotProduct, LinearIsometryEquiv.inner_map_map, eucl_inner_eq_dotProduct]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, cA]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc_sq : star (c m) * (c m * ((hA.eigenvalues₀ m : ℝ) : ℂ)) =
      ((hA.eigenvalues₀ m * ‖c m‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : star (c m) * (c m * ((hA.eigenvalues₀ m : ℝ) : ℂ)) =
        ((hA.eigenvalues₀ m : ℝ) : ℂ) * (star (c m) * c m) := by ring
    have h2 : star (c m) * c m = ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
      simpa using Complex.conj_mul' (c m)
    rw [h1, h2, ← Complex.ofReal_mul]
  rw [hc_sq, Complex.ofReal_re]

lemma spectral_expansion {K : ℕ} {A : Matrix (Fin K) (Fin K) ℂ} (hA : A.IsHermitian) :
    ∃ e : OrthonormalBasis (Fin (Fintype.card (Fin K))) ℂ (EuclideanSpace ℂ (Fin K)),
      ∀ u : Fin K → ℂ,
        euclSq u = ∑ m : Fin (Fintype.card (Fin K)), ‖(e.repr (WithLp.toLp 2 u)).ofLp m‖ ^ 2 ∧
        (star u ⬝ᵥ (A *ᵥ u)).re =
          ∑ m : Fin (Fintype.card (Fin K)),
            hA.eigenvalues₀ m * ‖(e.repr (WithLp.toLp 2 u)).ofLp m‖ ^ 2 := by
  refine spectral_expansion_aux hA
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin K)))).symm fun i => ?_
  unfold Matrix.IsHermitian.eigenvalues
  rfl

end AuxThm21

theorem solution (K : ℕ) (A : Matrix (Fin K) (Fin K) ℂ) (hA : A.IsHermitian) :
    (∀ q : ℕ, 1 ≤ q → q ≤ K →
      IsGreatest
        {v : ℝ | ∃ U : Submodule ℂ (Fin K → ℂ), Module.finrank ℂ U = q ∧
          IsLeast (rayleigh A '' {u | u ∈ U ∧ u ≠ 0}) v}
        (eigAt hA (q - 1))) ∧
      ∀ (q : ℕ) (α : ℝ) (U : Submodule ℂ (Fin K → ℂ)), Module.finrank ℂ U = q →
        (∀ u ∈ U, α * euclSq u ≤ (star u ⬝ᵥ (A *ᵥ u)).re) →
        ∀ j : ℕ, 1 ≤ j → j ≤ q → α ≤ eigAt hA (j - 1) := by
  rcases AuxThm21.spectral_expansion hA with ⟨e, hexp⟩
  have hcardK : Fintype.card (Fin K) = K := Fintype.card_fin K
  have hpart1 : ∀ q : ℕ, 1 ≤ q → q ≤ K →
      IsGreatest
        {v : ℝ | ∃ U : Submodule ℂ (Fin K → ℂ), Module.finrank ℂ U = q ∧
          IsLeast (rayleigh A '' {u | u ∈ U ∧ u ≠ 0}) v}
        (eigAt hA (q - 1)) := by
    intro q hq1 hqK
    have hqm1_lt : q - 1 < Fintype.card (Fin K) := by omega
    have heigAt_eq : eigAt hA (q - 1) = hA.eigenvalues₀ ⟨q - 1, hqm1_lt⟩ := by
      unfold eigAt
      rw [dif_pos hqm1_lt]
    refine ⟨?_, ?_⟩
    · -- Construct the optimal q-dimensional subspace U₀ spanned by the first q eigenvectors
      let extQ : (Fin q → ℂ) → (Fin (Fintype.card (Fin K)) → ℂ) :=
        fun d m => if hm : m.1 < q then d ⟨m.1, hm⟩ else 0
      let Φ₀ : (Fin q → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
        { toFun := fun d => (e.repr.symm (WithLp.toLp 2 (extQ d))).ofLp
          map_add' := fun d₁ d₂ => by
            have h : WithLp.toLp 2 (extQ (d₁ + d₂)) =
                WithLp.toLp 2 (extQ d₁) + WithLp.toLp 2 (extQ d₂) := by
              ext m; by_cases hm : m.1 < q <;> simp [extQ, hm]
            rw [h, map_add]; rfl
          map_smul' := fun r d => by
            have h : WithLp.toLp 2 (extQ (r • d)) = r • WithLp.toLp 2 (extQ d) := by
              ext m; by_cases hm : m.1 < q <;> simp [extQ, hm]
            rw [h, map_smul]; rfl }
      have hΦ₀_inj : Function.Injective Φ₀ := by
        intro d₁ d₂ heq
        have h1 : extQ d₁ = extQ d₂ :=
          WithLp.toLp_injective 2 (e.repr.symm.injective (WithLp.ofLp_injective 2 heq))
        ext r
        have h2 := congrFun h1 ⟨r.1, lt_of_lt_of_le r.2 (by omega)⟩
        simpa [extQ, r.2] using h2
      let U₀ := LinearMap.range Φ₀
      have hU₀_dim : Module.finrank ℂ U₀ = q := by
        rw [LinearMap.finrank_range_of_inj hΦ₀_inj, Module.finrank_fin_fun]
      refine ⟨U₀, hU₀_dim, ?_, ?_⟩
      · -- Attained at the (q-1)-th eigenvector
        let dStar : Fin q → ℂ := Pi.single ⟨q - 1, by omega⟩ 1
        let uStar : Fin K → ℂ := Φ₀ dStar
        have hcStar : (e.repr (WithLp.toLp 2 uStar)).ofLp = extQ dStar := by
          have h1 : WithLp.toLp 2 uStar = e.repr.symm (WithLp.toLp 2 (extQ dStar)) := rfl
          rw [h1, LinearIsometryEquiv.apply_symm_apply]
        have heuclStar : euclSq uStar = 1 := by
          rw [(hexp uStar).1, hcStar]
          have hsingle : ∀ m : Fin (Fintype.card (Fin K)),
              ‖extQ dStar m‖ ^ 2 = if m = ⟨q - 1, hqm1_lt⟩ then 1 else 0 := by
            intro m
            by_cases hm : m.1 < q
            · dsimp only [extQ, dStar]
              rw [dif_pos hm]
              by_cases hmeq : m.1 = q - 1
              · have hm_fin : (⟨m.1, hm⟩ : Fin q) = ⟨q - 1, by omega⟩ := Fin.ext hmeq
                have hm_N : m = ⟨q - 1, hqm1_lt⟩ := Fin.ext hmeq
                rw [if_pos hm_N, hm_fin]
                simp [hm_N]
              · have hm_fin : (⟨m.1, hm⟩ : Fin q) ≠ ⟨q - 1, by omega⟩ :=
                  fun h => hmeq (Fin.mk.inj h)
                have hm_N : m ≠ ⟨q - 1, hqm1_lt⟩ := fun h => hmeq (Fin.mk.inj h)
                simp [hm_fin, hm_N]
            · have hm_N : m ≠ ⟨q - 1, hqm1_lt⟩ := by
                intro h
                have := Fin.mk.inj h
                omega
              simp [extQ, hm, hm_N]
          simp_rw [hsingle]
          simp
        have huStar_ne : uStar ≠ 0 := by
          intro h0
          rw [h0] at heuclStar
          simp [euclSq] at heuclStar
        refine ⟨uStar, ⟨⟨dStar, rfl⟩, huStar_ne⟩, ?_⟩
        unfold rayleigh
        rw [heuclStar, div_one, (hexp uStar).2, hcStar]
        have hsum_val : (∑ m : Fin (Fintype.card (Fin K)),
            hA.eigenvalues₀ m * ‖extQ dStar m‖ ^ 2) = hA.eigenvalues₀ ⟨q - 1, hqm1_lt⟩ := by
          have hsingle : ∀ m : Fin (Fintype.card (Fin K)),
              hA.eigenvalues₀ m * ‖extQ dStar m‖ ^ 2 =
                if m = ⟨q - 1, hqm1_lt⟩ then hA.eigenvalues₀ ⟨q - 1, hqm1_lt⟩ else 0 := by
            intro m
            by_cases hm : m.1 < q
            · dsimp only [extQ, dStar]
              rw [dif_pos hm]
              by_cases hmeq : m.1 = q - 1
              · have hm_fin : (⟨m.1, hm⟩ : Fin q) = ⟨q - 1, by omega⟩ := Fin.ext hmeq
                have hm_N : m = ⟨q - 1, hqm1_lt⟩ := Fin.ext hmeq
                rw [if_pos hm_N, hm_fin]
                simp [hm_N]
              · have hm_fin : (⟨m.1, hm⟩ : Fin q) ≠ ⟨q - 1, by omega⟩ :=
                  fun h => hmeq (Fin.mk.inj h)
                have hm_N : m ≠ ⟨q - 1, hqm1_lt⟩ := fun h => hmeq (Fin.mk.inj h)
                simp [hm_fin, hm_N]
            · have hm_N : m ≠ ⟨q - 1, hqm1_lt⟩ := by
                intro h; have := Fin.mk.inj h; omega
              simp [extQ, hm, hm_N]
          simp_rw [hsingle]
          simp
        rw [hsum_val, heigAt_eq]
      · -- Lower bound on U₀ \ {0}
        rintro _ ⟨u, ⟨⟨d, rfl⟩, hu_ne⟩, rfl⟩
        have hc_d : (e.repr (WithLp.toLp 2 (Φ₀ d))).ofLp = extQ d := by
          have h1 : WithLp.toLp 2 (Φ₀ d) = e.repr.symm (WithLp.toLp 2 (extQ d)) := rfl
          rw [h1, LinearIsometryEquiv.apply_symm_apply]
        have hpos_sq : 0 < euclSq (Φ₀ d) := AuxThm21.euclSq_pos_of_ne_zero hu_ne
        unfold rayleigh
        rw [le_div_iff₀ hpos_sq, (hexp (Φ₀ d)).1, (hexp (Φ₀ d)).2, hc_d, Finset.mul_sum]
        refine Finset.sum_le_sum fun m _ => ?_
        by_cases hm : m.1 < q
        · have hm_le : m ≤ ⟨q - 1, hqm1_lt⟩ := Fin.mk_le_mk.mpr (by omega)
          have hanti := hA.eigenvalues₀_antitone hm_le
          rw [heigAt_eq]
          exact mul_le_mul_of_nonneg_right hanti (sq_nonneg _)
        · have hz : extQ d m = 0 := by simp [extQ, hm]
          simp [hz]
    · -- Upper bound v ≤ eigAt hA (q - 1) for every q-dimensional U
      rintro v ⟨U, hU_dim, hv_least⟩
      let π_top : U →ₗ[ℂ] (Fin (q - 1) → ℂ) :=
        { toFun := fun u r =>
            (e.repr (WithLp.toLp 2 u.1)).ofLp ⟨r.1, lt_of_lt_of_le r.2 (by omega)⟩
          map_add' := fun u₁ u₂ => by
            ext r
            change (e.repr (WithLp.toLp 2 u₁.1 + WithLp.toLp 2 u₂.1)).ofLp ⟨r.1, _⟩ = _
            rw [map_add]
            rfl
          map_smul' := fun c u => by
            ext r
            change (e.repr (c • WithLp.toLp 2 u.1)).ofLp ⟨r.1, _⟩ = _
            rw [map_smul]
            rfl }
      have hker_ne_bot : LinearMap.ker π_top ≠ ⊥ := by
        intro hker
        have hrn := LinearMap.finrank_range_add_finrank_ker π_top
        rw [hker, finrank_bot, add_zero, hU_dim] at hrn
        have hle := Submodule.finrank_le (LinearMap.range π_top)
        rw [Module.finrank_fin_fun] at hle
        omega
      rcases (LinearMap.ker π_top).exists_mem_ne_zero_of_ne_bot hker_ne_bot with
        ⟨⟨u₀, hu₀_U⟩, hu₀_ker, hu₀_ne_sub⟩
      have hu₀_ne : u₀ ≠ 0 := fun h0 => hu₀_ne_sub (Subtype.ext h0)
      have hv_le_u₀ : v ≤ rayleigh A u₀ := hv_least.2 ⟨u₀, ⟨hu₀_U, hu₀_ne⟩, rfl⟩
      refine le_trans hv_le_u₀ ?_
      have hpos_sq : 0 < euclSq u₀ := AuxThm21.euclSq_pos_of_ne_zero hu₀_ne
      unfold rayleigh
      rw [div_le_iff₀ hpos_sq, (hexp u₀).1, (hexp u₀).2, Finset.mul_sum]
      refine Finset.sum_le_sum fun m _ => ?_
      by_cases hm : m.1 < q - 1
      · have hzero : (e.repr (WithLp.toLp 2 u₀)).ofLp m = 0 := by
          have h1 := congrFun (LinearMap.mem_ker.mp hu₀_ker) ⟨m.1, hm⟩
          simpa [π_top] using h1
        simp [hzero]
      · have hm_ge : ⟨q - 1, hqm1_lt⟩ ≤ m := Fin.mk_le_mk.mpr (by omega)
        have hanti := hA.eigenvalues₀_antitone hm_ge
        rw [heigAt_eq]
        exact mul_le_mul_of_nonneg_right hanti (sq_nonneg _)
  refine ⟨hpart1, fun q α U hU_dim hquad j hj1 hjq => ?_⟩
  have hq1 : 1 ≤ q := le_trans hj1 hjq
  have hqK : q ≤ K := by
    calc
      q = Module.finrank ℂ U := hU_dim.symm
      _ ≤ Module.finrank ℂ (Fin K → ℂ) := Submodule.finrank_le U
      _ = K := Module.finrank_fin_fun ℂ
  rcases AuxThm21.exists_isLeast_rayleigh A U hq1 hU_dim with ⟨v, hv_least⟩
  rcases hv_least.1 with ⟨u_min, ⟨hu_U, hu_ne⟩, rfl⟩
  have hα_le_v : α ≤ rayleigh A u_min := by
    have hpos := AuxThm21.euclSq_pos_of_ne_zero hu_ne
    unfold rayleigh
    exact (le_div_iff₀ hpos).mpr (hquad u_min hu_U)
  have hv_le_eigq : rayleigh A u_min ≤ eigAt hA (q - 1) :=
    (hpart1 q hq1 hqK).2 ⟨U, hU_dim, hv_least⟩
  have heigq_le_eigj : eigAt hA (q - 1) ≤ eigAt hA (j - 1) := by
    have hjm1_lt : j - 1 < Fintype.card (Fin K) := by omega
    have hqm1_lt : q - 1 < Fintype.card (Fin K) := by omega
    unfold eigAt
    rw [dif_pos hjm1_lt, dif_pos hqm1_lt]
    exact hA.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (by omega))
  exact le_trans hα_le_v (le_trans hv_le_eigq heigq_le_eigj)
