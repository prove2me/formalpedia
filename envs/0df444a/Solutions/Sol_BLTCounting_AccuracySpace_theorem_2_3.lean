-- Prove2me | solution 1 for BLTCounting.AccuracySpace.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:51:05.065479+00:00
-- url     : https://prove2.me/submissions/5e3e491d-4e1c-41cf-a233-07664a7e41bc

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

open Matrix BLTCounting.AccuracySpace

namespace AuxThm23

lemma repr_symm_eq_sum {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) (w : EuclideanSpace ℂ ι) :
    b.repr.symm w = ∑ i : ι, w.ofLp i • b i := by
  have h := (b.sum_repr (b.repr.symm w)).symm
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

lemma norm_sq_eq_sum_sym_eigenvalues {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {m : Type*} [Fintype m]
    (T : E →ₗ[ℂ] EuclideanSpace ℂ m) {N : ℕ} (hN : Module.finrank ℂ E = N)
    (hSym : (T.adjoint ∘ₗ T).IsSymmetric) (x : E) :
    ‖T x‖ ^ 2 = ∑ i : Fin N,
      hSym.eigenvalues hN i * ‖((hSym.eigenvectorBasis hN).repr x).ofLp i‖ ^ 2 := by
  let b := hSym.eigenvectorBasis hN
  let c : Fin N → ℂ := (b.repr x).ofLp
  have hx_eq : x = b.repr.symm (WithLp.toLp 2 c) := by
    have h : WithLp.toLp 2 c = b.repr x := rfl
    rw [h, LinearIsometryEquiv.symm_apply_apply]
  let cS : Fin N → ℂ := fun i => c i * ((hSym.eigenvalues hN i : ℝ) : ℂ)
  have hSx : (T.adjoint ∘ₗ T) x = b.repr.symm (WithLp.toLp 2 cS) := by
    have hr1 : b.repr.symm (WithLp.toLp 2 c) = ∑ i : Fin N, c i • b i :=
      repr_symm_eq_sum b (WithLp.toLp 2 c)
    have hr2 : b.repr.symm (WithLp.toLp 2 cS) = ∑ i : Fin N, cS i • b i :=
      repr_symm_eq_sum b (WithLp.toLp 2 cS)
    rw [hx_eq, hr1, hr2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hSym.apply_eigenvectorBasis hN i]
    change c i • (hSym.eigenvalues hN i • b i) = (c i * ((hSym.eigenvalues hN i : ℝ) : ℂ)) • b i
    rw [← Complex.coe_smul, smul_smul]
  have hnorm_inner : ‖T x‖ ^ 2 = (inner ℂ x ((T.adjoint ∘ₗ T) x)).re := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
    simp only [RCLike.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (T x).ofLp j * (starRingEnd ℂ) ((T x).ofLp j) =
        ((‖(T x).ofLp j‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm]
      simpa [Complex.star_def] using Complex.conj_mul' ((T x).ofLp j)
    rw [hj, Complex.ofReal_re]
  have hinner_eq : inner ℂ x ((T.adjoint ∘ₗ T) x) =
      inner ℂ (b.repr.symm (WithLp.toLp 2 c)) (b.repr.symm (WithLp.toLp 2 cS)) := by
    rw [← hx_eq, ← hSx]
  rw [hnorm_inner, hinner_eq, LinearIsometryEquiv.inner_map_map, PiLp.inner_apply]
  simp only [RCLike.inner_apply, Complex.re_sum, cS]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc_sq : c i * ((hSym.eigenvalues hN i : ℝ) : ℂ) * (starRingEnd ℂ) (c i) =
      ((hSym.eigenvalues hN i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : c i * ((hSym.eigenvalues hN i : ℝ) : ℂ) * (starRingEnd ℂ) (c i) =
        ((hSym.eigenvalues hN i : ℝ) : ℂ) * (star (c i) * c i) := by
      simp [Complex.star_def]
      ring
    have h2 : star (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      simpa using Complex.conj_mul' (c i)
    rw [h1, h2, ← Complex.ofReal_mul]
  rw [hc_sq, Complex.ofReal_re]

lemma finrank_range_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
  let em : (m → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ m := (WithLp.linearEquiv 2 ℂ (m → ℂ)).symm
  let en : EuclideanSpace ℂ n ≃ₗ[ℂ] (n → ℂ) := WithLp.linearEquiv 2 ℂ (n → ℂ)
  have hcomp : Matrix.toEuclideanLin X =
      em.toLinearMap ∘ₗ X.mulVecLin ∘ₗ en.toLinearMap := by
    ext x i
    rfl
  have hrange : LinearMap.range (Matrix.toEuclideanLin X) =
      (LinearMap.range X.mulVecLin).map em.toLinearMap := by
    rw [hcomp, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hrange, LinearEquiv.finrank_map_eq]
  rfl

lemma eym_bound_aux {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A X : Matrix m n ℂ) (d : ℕ) (hX : X.rank ≤ d)
    {N : ℕ} (hN : Module.finrank ℂ (EuclideanSpace ℂ n) = N)
    (hSym : ((Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A).IsSymmetric)
    (hd : d < N) :
    Real.sqrt (hSym.eigenvalues hN ⟨d, hd⟩) ≤ specNorm (A - X) := by
  by_cases hneg : hSym.eigenvalues hN ⟨d, hd⟩ ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hneg]
    exact norm_nonneg _
  · have hpos_eig : 0 < hSym.eigenvalues hN ⟨d, hd⟩ := not_le.mp hneg
    let T := Matrix.toEuclideanLin A
    let TX := Matrix.toEuclideanLin X
    let b := hSym.eigenvectorBasis hN
    let extD : (Fin (d + 1) → ℂ) → (Fin N → ℂ) :=
      fun c i => if hi : i.1 < d + 1 then c ⟨i.1, hi⟩ else 0
    let Φ : (Fin (d + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ n :=
      { toFun := fun c => b.repr.symm (WithLp.toLp 2 (extD c))
        map_add' := fun c₁ c₂ => by
          have h : extD (c₁ + c₂) = extD c₁ + extD c₂ := by
            ext i
            dsimp only [extD, Pi.add_apply]
            by_cases hi : i.1 < d + 1
            · rw [dif_pos hi, dif_pos hi, dif_pos hi]
            · rw [dif_neg hi, dif_neg hi, dif_neg hi, add_zero]
          rw [h, WithLp.toLp_add, map_add]
        map_smul' := fun r c => by
          have h : extD (r • c) = r • extD c := by
            ext i
            dsimp only [extD, Pi.smul_apply]
            by_cases hi : i.1 < d + 1
            · rw [dif_pos hi, dif_pos hi]
            · rw [dif_neg hi, dif_neg hi, smul_zero]
          rw [h, WithLp.toLp_smul, map_smul, RingHom.id_apply] }
    have hΦ_inj : Function.Injective Φ := by
      intro c₁ c₂ heq
      have h1 : extD c₁ = extD c₂ :=
        WithLp.toLp_injective 2 (b.repr.symm.injective heq)
      ext r
      have h2 := congrFun h1 ⟨r.1, lt_of_lt_of_le r.2 (by omega)⟩
      dsimp only [extD] at h2
      rwa [dif_pos r.2, dif_pos r.2] at h2
    let E_top := LinearMap.range Φ
    have hE_dim : Module.finrank ℂ E_top = d + 1 := by
      rw [LinearMap.finrank_range_of_inj hΦ_inj, Module.finrank_fin_fun]
    let f_res : E_top →ₗ[ℂ] EuclideanSpace ℂ m := TX.domRestrict E_top
    have hker_ne_bot : LinearMap.ker f_res ≠ ⊥ := by
      intro hker
      have hrn := LinearMap.finrank_range_add_finrank_ker f_res
      rw [hker, finrank_bot, add_zero, hE_dim] at hrn
      have hsub : LinearMap.range f_res ≤ LinearMap.range TX := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u.1, rfl⟩
      have hle1 : Module.finrank ℂ (LinearMap.range f_res) ≤
          Module.finrank ℂ (LinearMap.range TX) := Submodule.finrank_mono hsub
      rw [finrank_range_toEuclideanLin X] at hle1
      omega
    rcases (LinearMap.ker f_res).exists_mem_ne_zero_of_ne_bot hker_ne_bot with
      ⟨⟨x₀, ⟨c₀, rfl⟩⟩, hx₀_ker, hx₀_ne_sub⟩
    have hx₀_ne : Φ c₀ ≠ 0 := fun h0 => hx₀_ne_sub (Subtype.ext h0)
    have hnorm_pos : 0 < ‖Φ c₀‖ := norm_pos_iff.mpr hx₀_ne
    have hTX0 : TX (Φ c₀) = 0 := LinearMap.mem_ker.mp hx₀_ker
    have hc_eq : ((hSym.eigenvectorBasis hN).repr (Φ c₀)).ofLp = extD c₀ := by
      have h1 : Φ c₀ = b.repr.symm (WithLp.toLp 2 (extD c₀)) := rfl
      change (b.repr (Φ c₀)).ofLp = extD c₀
      rw [h1, LinearIsometryEquiv.apply_symm_apply]
    have hTx₀_lb : hSym.eigenvalues hN ⟨d, hd⟩ * ‖Φ c₀‖ ^ 2 ≤ ‖T (Φ c₀)‖ ^ 2 := by
      have hnorm_sq : ‖Φ c₀‖ ^ 2 = ∑ i : Fin N, ‖extD c₀ i‖ ^ 2 := by
        rw [← b.repr.norm_map (Φ c₀), PiLp.norm_sq_eq_of_L2]
        dsimp only [b]
        simp_rw [hc_eq]
      rw [norm_sq_eq_sum_sym_eigenvalues T hN hSym (Φ c₀), hnorm_sq, Finset.mul_sum]
      simp_rw [hc_eq]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i.1 < d + 1
      · have hle_d : i ≤ ⟨d, hd⟩ := Fin.mk_le_mk.mpr (by omega)
        exact mul_le_mul_of_nonneg_right (hSym.eigenvalues_antitone hN hle_d) (sq_nonneg _)
      · have hz : extD c₀ i = 0 := dif_neg hi
        simp [hz]
    have hsqrt_lb : Real.sqrt (hSym.eigenvalues hN ⟨d, hd⟩) * ‖Φ c₀‖ ≤ ‖T (Φ c₀)‖ := by
      have hsq : (Real.sqrt (hSym.eigenvalues hN ⟨d, hd⟩) * ‖Φ c₀‖) ^ 2 ≤ ‖T (Φ c₀)‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hpos_eig.le]
        exact hTx₀_lb
      exact le_of_sq_le_sq hsq (norm_nonneg _)
    have hT_eq_diff : T (Φ c₀) = (Matrix.toEuclideanLin (A - X)).toContinuousLinearMap (Φ c₀) := by
      change T (Φ c₀) = Matrix.toEuclideanLin (A - X) (Φ c₀)
      rw [map_sub, LinearMap.sub_apply, hTX0, sub_zero]
    have hdiff_ub : ‖T (Φ c₀)‖ ≤ specNorm (A - X) * ‖Φ c₀‖ := by
      rw [hT_eq_diff]
      exact ContinuousLinearMap.le_opNorm _ (Φ c₀)
    exact le_of_mul_le_mul_right (le_trans hsqrt_lb hdiff_ub) hnorm_pos

end AuxThm23

theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A X : Matrix m n ℂ) (d : ℕ) (hX : X.rank ≤ d) :
    singularValue A d ≤ specNorm (A - X) ∧
      ∀ τ : ℝ, specNorm (A - X) ≤ τ → singularCountAbove A τ ≤ d := by
  have h1 : singularValue A d ≤ specNorm (A - X) := by
    unfold singularValue LinearMap.singularValues
    by_cases hd : d < Module.finrank ℂ (EuclideanSpace ℂ n)
    · have heq : d = Fin.valEmbedding (⟨d, hd⟩ : Fin (Module.finrank ℂ (EuclideanSpace ℂ n))) := rfl
      rw [heq, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe]
      have hex : ∃ a : Fin (Module.finrank ℂ (EuclideanSpace ℂ n)),
          Fin.valEmbedding a = Fin.valEmbedding ⟨d, hd⟩ := ⟨⟨d, hd⟩, rfl⟩
      rw [dif_pos hex]
      have hch : hex.choose = ⟨d, hd⟩ := Fin.valEmbedding.injective hex.choose_spec
      rw [hch]
      exact AuxThm23.eym_bound_aux A X d hX rfl _ hd
    · rw [Finsupp.embDomain_of_notMem_range]
      · exact norm_nonneg _
      · rintro ⟨i, rfl⟩
        exact hd i.2
  refine ⟨h1, fun τ hτ => ?_⟩
  have hsd_le : singularValue A d ≤ τ := le_trans h1 hτ
  unfold singularCountAbove
  have hsub : (Finset.range (min (Fintype.card m) (Fintype.card n))).filter
      (fun j => τ < singularValue A j) ⊆ Finset.range d := by
    intro j hj
    have hgt : τ < singularValue A j := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_range]
    by_contra hge
    have hd_le_j : d ≤ j := not_lt.mp hge
    have hanti : singularValue A j ≤ singularValue A d :=
      LinearMap.singularValues_antitone (Matrix.toEuclideanLin A) hd_le_j
    linarith
  calc
    ((Finset.range (min (Fintype.card m) (Fintype.card n))).filter
        (fun j => τ < singularValue A j)).card
        ≤ (Finset.range d).card := Finset.card_le_card hsub
    _ = d := Finset.card_range d
