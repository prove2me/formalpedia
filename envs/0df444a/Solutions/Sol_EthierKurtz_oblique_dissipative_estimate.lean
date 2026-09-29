-- Prove2me | solution 1 for EthierKurtz.oblique_dissipative_estimate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:21:35.674985+00:00
-- url     : https://prove2.me/submissions/d9814b7f-1e31-4da5-8f19-0551aa070296

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

open scoped InnerProductSpace

section aux_oe_matrix
open scoped MatrixOrder
open Matrix

theorem aux_oe_psd {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᵀ * B := by
  refine ⟨CFC.sqrt A, ?_⟩
  have h1 : 0 ≤ A := hA.nonneg
  have h2 := CFC.sqrt_mul_sqrt_self A h1
  have h3 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h4 : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    have := h3.star_eq
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  rw [h4, h2]

theorem aux_oe_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hH : ∀ θ, H θ θ ≤ 0) :
    ∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ 0 := by
  obtain ⟨B, rfl⟩ := aux_oe_psd A hA
  have hB : ∀ i j, (Bᵀ * B) i j = ∑ k, B k i * B k j := by
    intro i j; simp [Matrix.mul_apply]
  set e : Fin d → EuclideanSpace ℝ (Fin d) := fun i => EuclideanSpace.single i 1 with he
  let w : Fin d → EuclideanSpace ℝ (Fin d) := fun k => ∑ i, B k i • e i
  have key : ∑ i, ∑ j, (Bᵀ * B) i j * H (e i) (e j) = ∑ k, H (w k) (w k) := by
    simp only [w, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hB, Finset.sum_mul, Finset.mul_sum]
    calc ∑ i, ∑ j, ∑ k, B k i * B k j * H (e i) (e j)
        = ∑ i, ∑ k, ∑ j, B k i * B k j * H (e i) (e j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, B k i * B k j * H (e i) (e j) := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, B k i * B k j * H (e i) (e j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact Finset.sum_nonpos (fun k _ => hH _)

theorem aux_oe_so {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ) (y θ : E)
    (hh : ContDiffAt ℝ 2 h y) (hmax : IsLocalMax h y) : fderiv ℝ (fderiv ℝ h) y θ θ ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set φ : ℝ → ℝ := fun t => h (y + t • θ) with hφ
  have hev : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ h z :=
    (hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hdiff2 : DifferentiableAt ℝ (fderiv ℝ h) y :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcont : Continuous (fun t : ℝ => y + t • θ) := by fun_prop
  have hline : Tendsto (fun t : ℝ => y + t • θ) (𝓝 0) (𝓝 y) := by
    simpa using hcont.tendsto 0
  have hlineD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + t • θ) θ t := by
    intro t; simpa using ((hasDerivAt_id t).smul_const θ).const_add y
  have hev' : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ h (y + t • θ) := hline.eventually hev
  have hderiv : deriv φ =ᶠ[𝓝 0] fun t => fderiv ℝ h (y + t • θ) θ := by
    filter_upwards [hev'] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlineD t)).deriv
  have h1 : deriv φ 0 = 0 := by
    rw [hderiv.eq_of_nhds]; simp [hmax.fderiv_eq_zero]
  have h2 : deriv (deriv φ) 0 = fderiv ℝ (fderiv ℝ h) y θ θ := by
    rw [hderiv.deriv_eq]
    have hA : HasDerivAt (fun t : ℝ => fderiv ℝ h (y + t • θ)) (fderiv ℝ (fderiv ℝ h) y θ) 0 := by
      exact hdiff2.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hlineD 0) (by simp)
    have hB := hA.clm_apply (hasDerivAt_const (0:ℝ) θ)
    simpa using hB.deriv
  have hmin : IsLocalMin φ 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [h2]; exact hpos) h1
      (hh.continuousAt.comp_of_eq hcont.continuousAt (by simp))
  have hmax' : IsLocalMax φ 0 := by
    have : IsLocalMax h (y + (0:ℝ) • θ) := by simpa using hmax
    exact IsLocalMax.comp_continuous (g := fun t : ℝ => y + t • θ) (b := 0) this hcont.continuousAt
  have hconst : φ =ᶠ[𝓝 0] fun _ => φ 0 := by
    filter_upwards [hmin, hmax'] with t h1 h2
    exact le_antisymm h2 h1
  have h3 : deriv (deriv φ) 0 = 0 := by
    have hd : deriv φ =ᶠ[𝓝 0] deriv (fun _ => φ 0) := hconst.deriv
    rw [hd.deriv_eq]; simp
  linarith

theorem aux_oe_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (y v w : E) (hF : DifferentiableAt ℝ (fderiv ℝ F) y) :
    fderiv ℝ (fun z => fderiv ℝ F z v) y w = fderiv ℝ (fderiv ℝ F) y w v := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

theorem aux_oe_interior {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hopen : IsOpen Ω)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (bv : EuclideanSpace ℝ (Fin d))
    (f ψ : EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ) (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ Ω)
    (hf : ContDiffOn ℝ 2 f Ω) (hψ : ContDiff ℝ 2 ψ)
    (hmax : IsLocalMax (fun x => f x - δ * ψ x) y) :
    (1/2:ℝ) * (∑ i, ∑ j, A i j * fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) y
        (EuclideanSpace.single i 1)) + fderiv ℝ f y bv
    ≤ δ * ((1/2:ℝ) * (∑ i, ∑ j, A i j * fderiv ℝ (fun z => fderiv ℝ ψ z
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single i 1)) + fderiv ℝ ψ y bv) := by
  have hfy : ContDiffAt ℝ 2 f y := hf.contDiffAt (hopen.mem_nhds hy)
  have hψy : ContDiffAt ℝ 2 ψ y := hψ.contDiffAt
  have hhy : ContDiffAt ℝ 2 (fun x => f x - δ * ψ x) y := hfy.sub (contDiffAt_const.mul hψy)
  have hevf : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
    (hfy.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hψd : ∀ z, DifferentiableAt ℝ ψ z := fun z => hψ.differentiable (by norm_num) z
  have hD : ∀ z, DifferentiableAt ℝ f z →
      fderiv ℝ (fun x => f x - δ * ψ x) z = fderiv ℝ f z - δ • fderiv ℝ ψ z := by
    intro z hz
    rw [fderiv_fun_sub hz ((hψd z).const_mul δ), fderiv_const_mul (hψd z)]
  have h1 : fderiv ℝ f y - δ • fderiv ℝ ψ y = 0 := by
    rw [← hD y (hevf.self_of_nhds)]; exact hmax.fderiv_eq_zero
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hfy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ2 : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h2 : fderiv ℝ (fderiv ℝ (fun x => f x - δ * ψ x)) y =
      fderiv ℝ (fderiv ℝ f) y - δ • fderiv ℝ (fderiv ℝ ψ) y := by
    have : fderiv ℝ (fun x => f x - δ * ψ x) =ᶠ[𝓝 y] fun z => fderiv ℝ f z - δ • fderiv ℝ ψ z := by
      filter_upwards [hevf] with z hz using hD z hz
    rw [this.fderiv_eq, fderiv_fun_sub (g := fun z => δ • fderiv ℝ ψ z) hf2 (by exact hψ2.const_smul δ),
      fderiv_fun_const_smul hψ2]
  have htr := aux_oe_trace A hA (fderiv ℝ (fderiv ℝ (fun x => f x - δ * ψ x)) y)
    (fun θ => aux_oe_so _ y θ hhy hmax)
  rw [h2] at htr
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib] at htr
  have hbv : fderiv ℝ f y bv = δ * fderiv ℝ ψ y bv := by
    have := congrArg (fun L => L bv) h1; simpa [sub_eq_zero] using this
  simp only [aux_oe_partial f y _ _ hf2, aux_oe_partial ψ y _ _ hψ2, hbv]
  have e1 : ∑ i, ∑ j, A i j * (δ * fderiv ℝ (fderiv ℝ ψ) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)) = δ * ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ ψ) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1] at htr
  nlinarith

end aux_oe_matrix

theorem aux_oe_psi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n₀ c₀ x₀ : E) (hn : ‖n₀‖ = 1) (hα : 0 < ⟪n₀, c₀⟫_ℝ) :
    ∃ ω₁ > 0, ∃ ω₂ > 0, ∀ s > 0, ∃ ψ : E → ℝ, ∃ Cl : ℝ, 0 ≤ Cl ∧ ContDiff ℝ 2 ψ ∧ ψ x₀ = 0 ∧
      (∀ x, ‖x - x₀‖ ≤ s → -Cl ≤ ψ x) ∧ (∀ x, ‖x - x₀‖ = s → 0 < ψ x) ∧
      (∀ y w, ‖y - x₀‖ < s → -ω₁ * ‖y - x₀‖ ≤ ⟪n₀, y - x₀⟫_ℝ → ‖w - c₀‖ < ω₂ →
        0 < fderiv ℝ ψ y w) := by
  set α := ⟪n₀, c₀⟫_ℝ with hαdef
  set τ : E := α⁻¹ • c₀ - n₀ with hτ
  set L : ℝ := 1 + ‖τ‖ with hL
  have hL1 : 1 ≤ L := by simp [hL]
  have hLpos : 0 < L := by linarith
  set P : ℝ := L ^ 2 with hP
  have hP1 : 1 ≤ P := by nlinarith
  have hPpos : 0 < P := by linarith
  set M : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - (innerSL ℝ n₀).smulRight τ with hM
  have hMapp : ∀ w, M w = w - ⟪n₀, w⟫_ℝ • τ := by intro w; simp [hM]
  have hnn : ⟪n₀, n₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hnτ : ⟪n₀, τ⟫_ℝ = 0 := by
    rw [hτ, inner_sub_right, inner_smul_right, hnn, ← hαdef, inv_mul_cancel₀ hα.ne']; ring
  have hMc : M c₀ = α • n₀ := by
    rw [hMapp, ← hαdef, hτ, smul_sub, smul_smul, mul_inv_cancel₀ hα.ne', one_smul]; abel
  have hnM : ∀ w, ⟪n₀, M w⟫_ℝ = ⟪n₀, w⟫_ℝ := by
    intro w; rw [hMapp, inner_sub_right, inner_smul_right, hnτ]; ring
  have hMle : ∀ w, ‖M w‖ ≤ L * ‖w‖ := by
    intro w
    rw [hMapp]
    have h1 : |⟪n₀, w⟫_ℝ| ≤ ‖w‖ := by
      have := abs_real_inner_le_norm n₀ w; rw [hn, one_mul] at this; exact this
    calc ‖w - ⟪n₀, w⟫_ℝ • τ‖ ≤ ‖w‖ + ‖⟪n₀, w⟫_ℝ • τ‖ := norm_sub_le _ _
      _ = ‖w‖ + |⟪n₀, w⟫_ℝ| * ‖τ‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖w‖ + ‖w‖ * ‖τ‖ := by gcongr
      _ = L * ‖w‖ := by rw [hL]; ring
  have hMge : ∀ w, ‖w‖ ≤ L * ‖M w‖ := by
    intro w
    have hw : w = M w + ⟪n₀, M w⟫_ℝ • τ := by rw [hnM, hMapp]; abel
    have h1 : |⟪n₀, M w⟫_ℝ| ≤ ‖M w‖ := by
      have := abs_real_inner_le_norm n₀ (M w); rw [hn, one_mul] at this; exact this
    calc ‖w‖ = ‖M w + ⟪n₀, M w⟫_ℝ • τ‖ := by rw [← hw]
      _ ≤ ‖M w‖ + ‖⟪n₀, M w⟫_ℝ • τ‖ := norm_add_le _ _
      _ = ‖M w‖ + |⟪n₀, M w⟫_ℝ| * ‖τ‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖M w‖ + ‖M w‖ * ‖τ‖ := by gcongr
      _ = L * ‖M w‖ := by rw [hL]; ring
  refine ⟨1 / (32 * P), by positivity, min (α / 2) (α / (32 * P ^ 2)),
    lt_min (by positivity) (by positivity), fun s hs => ?_⟩
  set η : ℝ := s / (2 * P) with hη
  have hηpos : 0 < η := by positivity
  let ψ : E → ℝ := fun x => η * ⟪n₀, x - x₀⟫_ℝ + ‖M (x - x₀)‖ ^ 2
  have hψd : ∀ y w, fderiv ℝ ψ y w = η * ⟪n₀, w⟫_ℝ + 2 * ⟪M (y - x₀), M w⟫_ℝ := by
    intro y w
    have h1 : HasFDerivAt (fun x : E => x - x₀) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).sub_const x₀
    have h2 : HasFDerivAt (fun x : E => ⟪n₀, x - x₀⟫_ℝ) ((innerSL ℝ n₀).comp
        (ContinuousLinearMap.id ℝ E)) y :=
      (innerSL ℝ n₀).hasFDerivAt.comp y h1
    have h3 : HasFDerivAt (fun x : E => M (x - x₀)) (M.comp (ContinuousLinearMap.id ℝ E)) y :=
      M.hasFDerivAt.comp y h1
    have h4 := h3.norm_sq
    have h5 : HasFDerivAt ψ _ y := (h2.const_mul η).add h4
    rw [h5.fderiv]
    simp [inner_sub_left]
  refine ⟨ψ, η * s, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ 2 (fun x => η * ⟪n₀, x - x₀⟫_ℝ + ‖M (x - x₀)‖ ^ 2)
    have hl : ContDiff ℝ 2 (fun x : E => x - x₀) := contDiff_id.sub contDiff_const
    exact (contDiff_const.mul ((innerSL ℝ n₀).contDiff.comp hl)).add
      ((M.contDiff.comp hl).norm_sq ℝ)
  · simp [ψ]
  · intro x hx
    have h1 : |⟪n₀, x - x₀⟫_ℝ| ≤ ‖x - x₀‖ := by
      have := abs_real_inner_le_norm n₀ (x - x₀); rw [hn, one_mul] at this; exact this
    have h2 : -‖x - x₀‖ ≤ ⟪n₀, x - x₀⟫_ℝ := by linarith [neg_abs_le ⟪n₀, x - x₀⟫_ℝ]
    have h3 : 0 ≤ ‖M (x - x₀)‖ ^ 2 := by positivity
    show -(η * s) ≤ η * ⟪n₀, x - x₀⟫_ℝ + ‖M (x - x₀)‖ ^ 2
    nlinarith
  · intro x hx
    have h1 : |⟪n₀, x - x₀⟫_ℝ| ≤ ‖x - x₀‖ := by
      have := abs_real_inner_le_norm n₀ (x - x₀); rw [hn, one_mul] at this; exact this
    have h2 : -s ≤ ⟪n₀, x - x₀⟫_ℝ := by rw [← hx]; linarith [neg_abs_le ⟪n₀, x - x₀⟫_ℝ]
    have h3 : s ≤ L * ‖M (x - x₀)‖ := hx ▸ hMge (x - x₀)
    have h4 : s ^ 2 ≤ P * ‖M (x - x₀)‖ ^ 2 := by
      rw [hP]; nlinarith [norm_nonneg (M (x - x₀))]
    show 0 < η * ⟪n₀, x - x₀⟫_ℝ + ‖M (x - x₀)‖ ^ 2
    have h5 : η * ⟪n₀, x - x₀⟫_ℝ ≥ -(η * s) := by nlinarith
    have h6 : η * s = s ^ 2 / (2 * P) := by rw [hη]; ring
    have h7 : s ^ 2 / P ≤ ‖M (x - x₀)‖ ^ 2 := by rw [div_le_iff₀ hPpos]; linarith
    have h8 : s ^ 2 / (2 * P) < s ^ 2 / P := by
      apply div_lt_div_of_pos_left (by positivity) hPpos (by linarith)
    linarith
  · intro y w hy hyn hw
    rw [hψd]
    set d := y - x₀ with hd
    have hw1 : ‖w - c₀‖ < α / 2 := lt_of_lt_of_le hw (min_le_left _ _)
    have hw2 : ‖w - c₀‖ < α / (32 * P ^ 2) := lt_of_lt_of_le hw (min_le_right _ _)
    have hnw : α / 2 ≤ ⟪n₀, w⟫_ℝ := by
      have : ⟪n₀, w⟫_ℝ = α + ⟪n₀, w - c₀⟫_ℝ := by rw [inner_sub_right, hαdef]; ring
      have h1 : |⟪n₀, w - c₀⟫_ℝ| ≤ ‖w - c₀‖ := by
        have := abs_real_inner_le_norm n₀ (w - c₀); rw [hn, one_mul] at this; exact this
      linarith [neg_abs_le ⟪n₀, w - c₀⟫_ℝ]
    have hMw : M w = α • n₀ + M (w - c₀) := by rw [map_sub, hMc]; abel
    have hi1 : ⟪M d, α • n₀⟫_ℝ = α * ⟪n₀, d⟫_ℝ := by
      rw [inner_smul_right, real_inner_comm, hnM]
    have hi2 : |⟪M d, M (w - c₀)⟫_ℝ| ≤ P * s * ‖w - c₀‖ := by
      calc |⟪M d, M (w - c₀)⟫_ℝ| ≤ ‖M d‖ * ‖M (w - c₀)‖ := abs_real_inner_le_norm _ _
        _ ≤ (L * ‖d‖) * (L * ‖w - c₀‖) := by
            gcongr
            · exact hMle d
            · exact hMle _
        _ ≤ (L * s) * (L * ‖w - c₀‖) := by gcongr
        _ = P * s * ‖w - c₀‖ := by rw [hP]; ring
    have hPs : P * s * ‖w - c₀‖ ≤ s * α / (32 * P) := by
      have : P * s * ‖w - c₀‖ ≤ P * s * (α / (32 * P ^ 2)) := by gcongr
      calc P * s * ‖w - c₀‖ ≤ P * s * (α / (32 * P ^ 2)) := this
        _ = s * α / (32 * P) := by field_simp
    have hdn : -(1 / (32 * P)) * s ≤ ⟪n₀, d⟫_ℝ := by
      have : (1 / (32 * P)) * ‖d‖ ≤ (1 / (32 * P)) * s := by gcongr
      linarith
    rw [hMw, inner_add_right, hi1]
    have hη1 : η * (α / 2) ≤ η * ⟪n₀, w⟫_ℝ := by gcongr
    have hkey : η * (α / 2) = s * α / (4 * P) := by rw [hη]; field_simp; ring
    have hk2 : α * (-(1 / (32 * P)) * s) = -(s * α / (32 * P)) := by field_simp
    have hk3 : α * (-(1 / (32 * P)) * s) ≤ α * ⟪n₀, d⟫_ℝ := by gcongr
    have hpos : 0 < s * α / (8 * P) := by positivity
    have e1 : s * α / (4 * P) = 8 * (s * α / (32 * P)) := by field_simp; ring
    have e2 : s * α / (8 * P) = 4 * (s * α / (32 * P)) := by field_simp; ring
    linarith [neg_abs_le ⟪M d, M (w - c₀)⟫_ℝ]

theorem aux_oe_inner {d : ℕ} (v h : EuclideanSpace ℝ (Fin d)) :
    ⟪v, h⟫_ℝ = ∑ i, v i * h i := by
  simp [PiLp.inner_apply, mul_comm]

theorem aux_oe_defn {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x₀ v : EuclideanSpace ℝ (Fin d)) (h : IsOutwardUnitNormal Ω x₀ v) :
    ∃ r : EuclideanSpace ℝ (Fin d) → ℝ, ∃ scale : ℝ, 0 < scale ∧ r x₀ = 0 ∧
      ∀ ω > 0, ∃ R > 0, (∀ y ∈ Metric.ball x₀ R, y ∈ Ω ↔ r y < 0) ∧
        ∀ p ∈ Metric.ball x₀ R, ∀ q ∈ Metric.ball x₀ R,
          |r q - r p - scale * ⟪v, q - p⟫_ℝ| ≤ ω * ‖q - p‖ := by
  obtain ⟨_, _, V, hVo, hxV, r, scale, hscale, hr, hr0, hΩ, hder⟩ := h
  refine ⟨r, scale, hscale, hr0, fun ω hω => ?_⟩
  have hcd : ContinuousOn (fderiv ℝ r) V := hr.continuousOn_fderiv_of_isOpen hVo le_rfl
  have hdiff : ∀ z ∈ V, DifferentiableAt ℝ r z := fun z hz =>
    (hr.differentiableOn one_ne_zero z hz).differentiableAt (hVo.mem_nhds hz)
  have hc : ContinuousAt (fderiv ℝ r) x₀ := hcd.continuousAt (hVo.mem_nhds hxV)
  obtain ⟨R1, hR1, hR1'⟩ := Metric.continuousAt_iff.mp hc ω hω
  obtain ⟨R2, hR2, hR2'⟩ := Metric.isOpen_iff.mp hVo x₀ hxV
  have hsub : Metric.ball x₀ (min R1 R2) ⊆ V :=
    fun y hy => hR2' (Metric.ball_subset_ball (min_le_right _ _) hy)
  refine ⟨min R1 R2, lt_min hR1 hR2, fun y hy => hΩ y (hsub hy), ?_⟩
  intro p hp q hq
  have := Convex.norm_image_sub_le_of_norm_fderiv_le' (f := r) (𝕜 := ℝ)
    (s := Metric.ball x₀ (min R1 R2)) (φ := fderiv ℝ r x₀) (C := ω)
    (fun z hz => hdiff z (hsub hz))
    (fun z hz => by
      have := hR1' (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _))
      rw [dist_eq_norm] at this; exact this.le)
    (convex_ball _ _) hp hq
  rw [Real.norm_eq_abs, hder, ← aux_oe_inner] at this
  exact this

theorem aux_oe_lower {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x₀ v : EuclideanSpace ℝ (Fin d)) (h : IsOutwardUnitNormal Ω x₀ v) :
    ∀ ω₁ > 0, ∃ R > 0, ∀ y ∈ Metric.ball x₀ R, y ∉ Ω → -ω₁ * ‖y - x₀‖ ≤ ⟪v, y - x₀⟫_ℝ := by
  obtain ⟨r, scale, hscale, hr0, hr⟩ := aux_oe_defn Ω x₀ v h
  intro ω₁ hω₁
  obtain ⟨R, hR, hΩ, hest⟩ := hr (scale * ω₁) (by positivity)
  refine ⟨R, hR, fun y hy hyΩ => ?_⟩
  have h1 : 0 ≤ r y := by
    by_contra hneg; push_neg at hneg; exact hyΩ ((hΩ y hy).mpr hneg)
  have h2 := hest x₀ (Metric.mem_ball_self hR) y hy
  rw [hr0] at h2
  have h3 := le_abs_self (r y - 0 - scale * ⟪v, y - x₀⟫_ℝ)
  have h4 : -(scale * ω₁ * ‖y - x₀‖) ≤ scale * ⟪v, y - x₀⟫_ℝ := by linarith
  have h5 : scale * (-ω₁ * ‖y - x₀‖) ≤ scale * ⟪v, y - x₀⟫_ℝ := by linarith
  exact le_of_mul_le_mul_left h5 hscale

theorem aux_oe_enter {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (y v w : EuclideanSpace ℝ (Fin d)) (h : IsOutwardUnitNormal Ω y v)
    (hvw : 0 < ⟪v, w⟫_ℝ) :
    ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → y - t • w ∈ Ω := by
  obtain ⟨r, scale, hscale, hr0, hr⟩ := aux_oe_defn Ω y v h
  set κ := scale * ⟪v, w⟫_ℝ with hκ
  have hκpos : 0 < κ := by positivity
  obtain ⟨R, hR, hΩ, hest⟩ := hr (κ / (2 * (‖w‖ + 1))) (by positivity)
  refine ⟨R / (‖w‖ + 1), by positivity, fun t ht htR => ?_⟩
  have hq : y - t • w ∈ Metric.ball y R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    rw [lt_div_iff₀ (by positivity)] at htR
    nlinarith [norm_nonneg w]
  refine (hΩ _ hq).mpr ?_
  have h2 := hest y (Metric.mem_ball_self hR) (y - t • w) hq
  rw [hr0, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    inner_neg_right, inner_smul_right] at h2
  have h3 := le_abs_self (r (y - t • w) - 0 - scale * -(t * ⟪v, w⟫_ℝ))
  have h4 : κ / (2 * (‖w‖ + 1)) * (t * ‖w‖) ≤ κ / 2 * t := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 0 ≤ κ * t := by positivity
    nlinarith [norm_nonneg w]
  have h5 : κ * t = scale * (t * ⟪v, w⟫_ℝ) := by rw [hκ]; ring
  nlinarith

theorem aux_oe_bdd {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ)
    (x₀ v : EuclideanSpace ℝ (Fin d)) (h : IsOutwardUnitNormal Ω x₀ v)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ComponentHolder Ω μ φ) :
    ∃ B, ∀ᶠ y in 𝓝 x₀, y ∈ Ω → |φ y| ≤ B := by
  have hv : ‖v‖ = 1 := h.2.1
  obtain ⟨r, scale, hscale, hr0, hr⟩ := aux_oe_defn Ω x₀ v h
  obtain ⟨R, hR, hΩ, hest⟩ := hr (scale / 4) (by positivity)
  obtain ⟨_, ρ₀, M, hρ₀, hM, hH⟩ := hφ
  set t₁ := min R ρ₀ / 2 with ht₁
  have ht₁pos : 0 < t₁ := by positivity
  set σ := t₁ / 2 with hσ
  have hσpos : 0 < σ := by positivity
  set ρ := t₁ + σ with hρ
  have hρpos : 0 < ρ := by positivity
  have hρR : ρ < R := by have := min_le_left R ρ₀; linarith
  have hρρ₀ : ρ ≤ ρ₀ := by have := min_le_right R ρ₀; linarith
  set q₀ := x₀ - t₁ • v with hq₀
  refine ⟨|φ q₀| + M * ρ ^ μ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ hσpos] with y hy hyΩ
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hyx : ‖y - x₀‖ < σ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hup : ∀ p ∈ Metric.ball x₀ R, ∀ q ∈ Metric.ball x₀ R,
      r q ≤ r p + scale * ⟪v, q - p⟫_ℝ + scale / 4 * ‖q - p‖ := by
    intro p hp q hq
    have h1 := le_abs_self (r q - r p - scale * ⟪v, q - p⟫_ℝ)
    have h2 := hest p hp q hq
    linarith
  have hballR : ∀ z, ‖z - x₀‖ < ρ → z ∈ Metric.ball x₀ R := by
    intro z hz; rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hballρ : ∀ z, ‖z - x₀‖ < ρ → z ∈ Metric.ball x₀ ρ := by
    intro z hz; rw [Metric.mem_ball, dist_eq_norm]; exact hz
  have hry : r y < 0 := (hΩ y (hballR y (by linarith))).mp hyΩ
  set m := y - t₁ • v with hm
  have hseg1 : segment ℝ y m ⊆ Ω ∩ Metric.ball x₀ ρ := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hz' : y + θ • (m - y) = y - (θ * t₁) • v := by
      rw [hm, sub_sub_cancel_left, smul_neg, smul_smul, ← sub_eq_add_neg]
    show y + θ • (m - y) ∈ Ω ∩ Metric.ball x₀ ρ
    rw [hz']
    have hs0 : 0 ≤ θ * t₁ := by positivity
    have hs1 : θ * t₁ ≤ t₁ := by nlinarith
    have hnorm : ‖y - (θ * t₁) • v - x₀‖ < ρ := by
      have : y - (θ * t₁) • v - x₀ = (y - x₀) - (θ * t₁) • v := by abel
      rw [this]
      calc ‖(y - x₀) - (θ * t₁) • v‖ ≤ ‖y - x₀‖ + ‖(θ * t₁) • v‖ := norm_sub_le _ _
        _ = ‖y - x₀‖ + θ * t₁ := by rw [norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hs0]; ring
        _ < ρ := by rw [hρ]; linarith
    refine ⟨(hΩ _ (hballR _ hnorm)).mpr ?_, hballρ _ hnorm⟩
    have h1 := hup y (hballR y (by linarith)) _ (hballR _ hnorm)
    have e1 : y - (θ * t₁) • v - y = -((θ * t₁) • v) := by abel
    rw [e1, inner_neg_right, inner_smul_right, hvv, norm_neg, norm_smul, hv, Real.norm_eq_abs,
      abs_of_nonneg hs0] at h1
    nlinarith
  have hseg2 : segment ℝ m q₀ ⊆ Ω ∩ Metric.ball x₀ ρ := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    set p' := y + θ • (x₀ - y) with hp'
    have hz' : m + θ • (q₀ - m) = p' - t₁ • v := by
      rw [hm, hq₀, hp']
      have : x₀ - t₁ • v - (y - t₁ • v) = x₀ - y := by abel
      rw [this]; abel
    show m + θ • (q₀ - m) ∈ Ω ∩ Metric.ball x₀ ρ
    rw [hz']
    have hp'x : ‖p' - x₀‖ < σ := by
      have : p' - x₀ = (1 - θ) • (y - x₀) := by
        rw [hp', sub_smul, one_smul, smul_sub, smul_sub]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      calc (1 - θ) * ‖y - x₀‖ ≤ 1 * ‖y - x₀‖ := by gcongr; linarith
        _ < σ := by linarith
    have hnorm : ‖p' - t₁ • v - x₀‖ < ρ := by
      have : p' - t₁ • v - x₀ = (p' - x₀) - t₁ • v := by abel
      rw [this]
      calc ‖(p' - x₀) - t₁ • v‖ ≤ ‖p' - x₀‖ + ‖t₁ • v‖ := norm_sub_le _ _
        _ = ‖p' - x₀‖ + t₁ := by rw [norm_smul, hv, Real.norm_eq_abs, abs_of_pos ht₁pos]; ring
        _ < ρ := by rw [hρ]; linarith
    have hp'R : p' ∈ Metric.ball x₀ R := hballR p' (by linarith)
    refine ⟨(hΩ _ (hballR _ hnorm)).mpr ?_, hballρ _ hnorm⟩
    have h1 := hup p' hp'R _ (hballR _ hnorm)
    have e1 : p' - t₁ • v - p' = -(t₁ • v) := by abel
    rw [e1, inner_neg_right, inner_smul_right, hvv, norm_neg, norm_smul, hv, Real.norm_eq_abs,
      abs_of_pos ht₁pos] at h1
    have h2 := hup x₀ (Metric.mem_ball_self hR) p' hp'R
    rw [hr0] at h2
    have h3 : ⟪v, p' - x₀⟫_ℝ ≤ σ := by
      have := real_inner_le_norm v (p' - x₀); rw [hv, one_mul] at this; linarith
    have h4 : scale * ⟪v, p' - x₀⟫_ℝ ≤ scale * σ := by gcongr
    have h5 : scale / 4 * ‖p' - x₀‖ ≤ scale / 4 * σ := by gcongr
    have h6 : scale * σ = scale * t₁ / 2 := by rw [hσ]; ring
    nlinarith
  have hP : IsPreconnected (segment ℝ y m ∪ segment ℝ m q₀) :=
    IsPreconnected.union m (right_mem_segment ℝ y m) (left_mem_segment ℝ m q₀)
      (convex_segment y m).isPreconnected (convex_segment m q₀).isPreconnected
  have hPsub : segment ℝ y m ∪ segment ℝ m q₀ ⊆ Ω ∩ Metric.ball x₀ ρ :=
    Set.union_subset hseg1 hseg2
  have hyP : y ∈ segment ℝ y m ∪ segment ℝ m q₀ := Or.inl (left_mem_segment ℝ y m)
  have hqP : q₀ ∈ segment ℝ y m ∪ segment ℝ m q₀ := Or.inr (right_mem_segment ℝ m q₀)
  have hcc := hP.subset_connectedComponentIn hyP hPsub
  have hmain := hH ρ hρpos hρρ₀ x₀ y (hPsub hyP) y (hcc hyP) q₀ (hcc hqP)
  have := abs_sub_abs_le_abs_sub (φ y) (φ q₀)
  linarith

theorem aux_oe_ccont (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (μ : ℝ)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hφ : BoundaryCOnceHolder Ω μ φ)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (hx₀ : x₀ ∈ frontier Ω) :
    ∀ ε > 0, ∃ R > 0, ∀ y ∈ frontier Ω, ‖y - x₀‖ < R → |φ y - φ x₀| < ε := by
  obtain ⟨ρ, hρ, U, D, u, hDo, h0D, _, hu0, _, _, himg, hC1⟩ := hφ x₀ hx₀
  set Φ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => φ (x₀ + U.symm
    (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)))) with hΦ
  have hcont : ContinuousAt Φ 0 := hC1.1.continuousOn.continuousAt (hDo.mem_nhds h0D)
  have hΦ0 : Φ 0 = φ x₀ := by
    simp only [hΦ, hu0]
    have : (Fin.lastCases (0:ℝ) (fun i => (0 : EuclideanSpace ℝ (Fin n)) i) : Fin (n+1) → ℝ)
        = 0 := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [this]; simp
  intro ε hε
  obtain ⟨σ, hσ, hσ'⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨min ρ σ, lt_min hρ hσ, fun y hy hyR => ?_⟩
  have hyball : y ∈ frontier Ω ∩ Metric.ball x₀ ρ :=
    ⟨hy, by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hyR (min_le_left _ _)⟩
  have hmem : (fun x => U (x - x₀)) y ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) :=
    ⟨y, hyball, rfl⟩
  rw [himg] at hmem
  obtain ⟨z, hzD, hz⟩ := hmem
  simp only at hz
  have hyz : y = x₀ + U.symm (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) := by
    rw [hz]; simp
  have hzn : ‖z‖ ≤ ‖y - x₀‖ := by
    have h1 : ‖(WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
        EuclideanSpace ℝ (Fin (n+1)))‖ = ‖y - x₀‖ := by
      rw [hz, LinearIsometryEquiv.norm_map]
    rw [← h1]
    have h2 : ‖z‖ ^ 2 ≤ ‖(WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
        EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.toLp_apply, Fin.lastCases_castSucc,
        Fin.lastCases_last]
      nlinarith [sq_nonneg (u z)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have := hσ' (show dist z 0 < σ by
    rw [dist_zero_right]; linarith [min_le_right ρ σ])
  rw [Real.dist_eq, hΦ0] at this
  rw [hyz]; exact this

theorem aux_oe_norm_le {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) : ‖w‖ ≤ ∑ i, |w i| := by
  have h1 : ‖w‖ ^ 2 ≤ (∑ i, |w i|) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |w i|)
      (fun _ _ => abs_nonneg _)
    simpa [Real.norm_eq_abs] using this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    two_ne_zero).mp h1

theorem aux_oe_nobdry {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hopen : IsOpen Ω)
    (f ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (J : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (δ : ℝ)
    (hfc : ContinuousOn f (closure Ω)) (hf2 : ContDiffOn ℝ 2 f Ω) (hψ : ContDiff ℝ 2 ψ)
    (hJc : ContinuousOn J (closure Ω)) (hJΩ : ∀ x ∈ Ω, J x = fderiv ℝ f x)
    (y w : EuclideanSpace ℝ (Fin d)) (hy : y ∈ closure Ω) (hJy : J y w = 0)
    (hpos : 0 < δ * fderiv ℝ ψ y w)
    (hent : ∃ t₀ > 0, ∀ t : ℝ, 0 < t → t < t₀ → y - t • w ∈ Ω)
    (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ∀ z ∈ Ω, ‖z - y‖ < ρ → z ∈ K)
    (hmax : ∀ z ∈ K, f z - δ * ψ z ≤ f y - δ * ψ y) : False := by
  obtain ⟨t₀, ht₀, hent⟩ := hent
  set k : EuclideanSpace ℝ (Fin d) → ℝ := fun z => J z w - δ * fderiv ℝ ψ z w with hk
  have hkc : ContinuousWithinAt k (closure Ω) y := by
    have h1 : ContinuousWithinAt (fun z => J z w) (closure Ω) y :=
      (hJc y hy).clm_apply continuousWithinAt_const
    have h2 : Continuous (fun z => fderiv ℝ ψ z w) :=
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact h1.sub (continuous_const.mul h2).continuousWithinAt
  have hky : k y < 0 := by simp only [hk, hJy]; linarith
  obtain ⟨ρ', hρ', hρ''⟩ := Metric.continuousWithinAt_iff.mp hkc (-(k y) / 2) (by linarith)
  have hkneg : ∀ z ∈ closure Ω, ‖z - y‖ < ρ' → k z < 0 := by
    intro z hz hzy
    have := hρ'' hz (by rw [dist_eq_norm]; exact hzy)
    rw [Real.dist_eq] at this
    have := le_abs_self (k z - k y)
    linarith
  set T := min (t₀ / 2) (min ρ ρ' / (‖w‖ + 1)) with hT
  have hmin : 0 < min ρ ρ' := lt_min hρ hρ'
  have hTpos : 0 < T := lt_min (by linarith) (by positivity)
  have hTt₀ : T < t₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hTw : ∀ τ, 0 ≤ τ → τ ≤ T → ‖(y - τ • w) - y‖ < min ρ ρ' := by
    intro τ h0 h1
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    have h2 : τ ≤ min ρ ρ' / (‖w‖ + 1) := le_trans h1 (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith [norm_nonneg w]
  have hmemΩ : ∀ τ, 0 < τ → τ ≤ T → y - τ • w ∈ Ω := fun τ h0 h1 => hent τ h0 (by linarith)
  set φ : ℝ → ℝ := fun τ => f (y - τ • w) - δ * ψ (y - τ • w) with hφ
  have hγ : Continuous (fun τ : ℝ => y - τ • w) := by fun_prop
  have hcont : ContinuousOn φ (Set.Icc 0 T) := by
    have hmaps : Set.MapsTo (fun τ : ℝ => y - τ • w) (Set.Icc 0 T) (closure Ω) := by
      intro τ hτ
      rcases eq_or_lt_of_le hτ.1 with h | h
      · rw [← h]; simpa using hy
      · exact subset_closure (hmemΩ τ h hτ.2)
    exact (hfc.comp hγ.continuousOn hmaps).sub
      (continuous_const.mul (hψ.continuous.comp hγ)).continuousOn
  have hderiv : ∀ τ ∈ Set.Ioo 0 T, 0 < deriv φ τ := by
    intro τ hτ
    have hz : y - τ • w ∈ Ω := hmemΩ τ hτ.1 hτ.2.le
    have hfd : DifferentiableAt ℝ f (y - τ • w) :=
      (hf2.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by norm_num)
    have hψd : DifferentiableAt ℝ ψ (y - τ • w) := hψ.differentiable (by norm_num) _
    have hγd : HasDerivAt (fun τ : ℝ => y - τ • w) (-w) τ := by
      simpa using ((hasDerivAt_id τ).smul_const w).const_sub y
    have h1 := hfd.hasFDerivAt.comp_hasDerivAt τ hγd
    have h2 := hψd.hasFDerivAt.comp_hasDerivAt τ hγd
    have h3 : HasDerivAt φ (fderiv ℝ f (y - τ • w) (-w) - δ * fderiv ℝ ψ (y - τ • w) (-w)) τ :=
      h1.sub (h2.const_mul δ)
    rw [h3.deriv]
    have := hkneg (y - τ • w) (subset_closure hz)
      (lt_of_lt_of_le (hTw τ hτ.1.le hτ.2.le) (min_le_right _ _))
    simp only [hk, hJΩ _ hz, map_neg] at this ⊢
    linarith
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 T) hcont (by
    rw [interior_Icc]; exact hderiv)
  have hlt : φ 0 < φ T := hmono ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩ hTpos
  have hTK : y - T • w ∈ K := hK _ (hmemΩ T hTpos le_rfl)
    (lt_of_lt_of_le (hTw T hTpos.le le_rfl) (min_le_left _ _))
  have := hmax _ hTK
  simp only [hφ, zero_smul, sub_zero] at hlt
  linarith

theorem aux_oe_core (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hopen : IsOpen Ω) (hK : IsCompact (closure Ω))
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haB : ∀ x₀ ∈ frontier Ω, ∀ i j, ∃ B, ∀ᶠ y in 𝓝 x₀, y ∈ Ω → |a y i j| ≤ B)
    (hbB : ∀ x₀ ∈ frontier Ω, ∀ i, ∃ B, ∀ᶠ y in 𝓝 x₀, y ∈ Ω → |b y i| ≤ B)
    (hcC : ∀ x₀ ∈ frontier Ω, ∀ ε > 0, ∃ R > 0, ∀ y ∈ frontier Ω, ‖y - x₀‖ < R →
      ‖c y - c x₀‖ < ε)
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hobl : ∀ x ∈ frontier Ω, 0 < ⟪normal x, c x⟫_ℝ)
    (f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (J : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hfc : ContinuousOn f (closure Ω)) (hf2 : ContDiffOn ℝ 2 f Ω)
    (hg : ∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          a x i j * fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) + fderiv ℝ f x (b x))
    (hJc : ContinuousOn J (closure Ω)) (hJΩ : ∀ x ∈ Ω, J x = fderiv ℝ f x)
    (hJb : ∀ x ∈ frontier Ω, J x (c x) = 0)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (hx₀ : x₀ ∈ closure Ω)
    (hmax : ∀ x ∈ closure Ω, f x ≤ f x₀) :
    ∀ ε > 0, ∃ y ∈ closure Ω, g y ≤ ε ∧ f x₀ - ε ≤ f y := by
  intro ε hε
  by_cases hx₀Ω : x₀ ∈ Ω
  · refine ⟨x₀, hx₀, ?_, by linarith⟩
    have hlm : IsLocalMax (fun x => f x - 0 * (fun _ => (0:ℝ)) x) x₀ := by
      filter_upwards [hopen.mem_nhds hx₀Ω] with x hx
      simp only [zero_mul, sub_zero]
      exact hmax x (subset_closure hx)
    have := aux_oe_interior Ω hopen (a x₀) (ha x₀ hx₀Ω) (b x₀) f (fun _ => (0:ℝ)) 0 x₀ hx₀Ω
      hf2 contDiff_const hlm
    rw [hg x₀ hx₀Ω]
    rw [zero_mul] at this
    linarith
  · have hfr : x₀ ∈ frontier Ω := by rw [hopen.frontier_eq]; exact ⟨hx₀, hx₀Ω⟩
    set n₀ := normal x₀ with hn₀def
    set c₀ := c x₀ with hc₀def
    have hn₀ : ‖n₀‖ = 1 := (hnormal x₀ hfr).2.1
    obtain ⟨ω₁, hω₁, ω₂, hω₂, hpsi⟩ := aux_oe_psi n₀ c₀ x₀ hn₀ (hobl x₀ hfr)
    obtain ⟨R₁, hR₁, hlow⟩ := aux_oe_lower Ω x₀ n₀ (hnormal x₀ hfr) ω₁ hω₁
    obtain ⟨R₂, hR₂, hcR⟩ := hcC x₀ hfr ω₂ hω₂
    choose Ba hBa using haB x₀ hfr
    choose Bb hBb using hbB x₀ hfr
    have hev : ∀ᶠ y in 𝓝 x₀, y ∈ Ω → (∀ i j, |a y i j| ≤ Ba i j) ∧ (∀ i, |b y i| ≤ Bb i) := by
      have h1 : ∀ᶠ y in 𝓝 x₀, ∀ i j, y ∈ Ω → |a y i j| ≤ Ba i j :=
        Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hBa i j
      have h2 : ∀ᶠ y in 𝓝 x₀, ∀ i, y ∈ Ω → |b y i| ≤ Bb i := Filter.eventually_all.mpr hBb
      filter_upwards [h1, h2] with y h1 h2 hy
      exact ⟨fun i j => h1 i j hy, fun i => h2 i hy⟩
    obtain ⟨R₃, hR₃, hR₃'⟩ := Metric.eventually_nhds_iff.mp hev
    set s := min (min R₁ R₂) R₃ / 2 with hsdef
    have hs : 0 < s := by positivity
    have hsR₁ : s < R₁ := by
      have := min_le_left (min R₁ R₂) R₃; have := min_le_left R₁ R₂; linarith
    have hsR₂ : s < R₂ := by
      have := min_le_left (min R₁ R₂) R₃; have := min_le_right R₁ R₂; linarith
    have hsR₃ : s < R₃ := by have := min_le_right (min R₁ R₂) R₃; linarith
    obtain ⟨ψ, Cl, hCl, hψ2, hψ0, hψlow, hψsph, hψder⟩ := hpsi s hs
    have hcD : Continuous (fderiv ℝ ψ) := hψ2.continuous_fderiv (by norm_num)
    have hcD2 : Continuous (fderiv ℝ (fderiv ℝ ψ)) :=
      (hψ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    obtain ⟨C1, hC1⟩ := (isCompact_closedBall x₀ s).exists_bound_of_continuousOn hcD.continuousOn
    obtain ⟨C2, hC2⟩ :=
      IsCompact.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ ψ))
        (isCompact_closedBall x₀ s) (by exact hcD2.continuousOn)
    set CG : ℝ := (1 / 2) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), Ba i j * C2 +
      C1 * ∑ i : Fin (n + 1), Bb i with hCG
    have hG : ∀ y ∈ Ω, ‖y - x₀‖ < s →
        (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), a y i j *
          fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) y
            (EuclideanSpace.single i 1)) + fderiv ℝ ψ y (b y) ≤ CG := by
      intro y hyΩ hys
      have hyb : y ∈ Metric.closedBall x₀ s := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact hys.le
      obtain ⟨hA, hB⟩ := hR₃' (by rw [dist_eq_norm]; linarith) hyΩ
      have hψ2y : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
        (hψ2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y
      have hC1y := hC1 y hyb
      have hC2y := hC2 y hyb
      have hterm : ∀ i j, a y i j * fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1))
          y (EuclideanSpace.single i 1) ≤ Ba i j * C2 := by
        intro i j
        rw [aux_oe_partial ψ y _ _ hψ2y]
        have h1 : |fderiv ℝ (fderiv ℝ ψ) y (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)| ≤ C2 := by
          have := (fderiv ℝ (fderiv ℝ ψ) y).le_opNorm₂ (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)
          rw [EuclideanSpace.norm_single, EuclideanSpace.norm_single, norm_one, mul_one,
            mul_one, Real.norm_eq_abs] at this
          linarith
        have hBa0 : 0 ≤ Ba i j := le_trans (abs_nonneg _) (hA i j)
        calc _ ≤ |a y i j * fderiv ℝ (fderiv ℝ ψ) y (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1)| := le_abs_self _
          _ = |a y i j| * |fderiv ℝ (fderiv ℝ ψ) y (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1)| := abs_mul _ _
          _ ≤ Ba i j * C2 := mul_le_mul (hA i j) h1 (abs_nonneg _) hBa0
      have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), a y i j *
          fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) y
            (EuclideanSpace.single i 1) ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), Ba i j * C2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hbnorm : ‖b y‖ ≤ ∑ i : Fin (n + 1), Bb i :=
        le_trans (aux_oe_norm_le (b y)) (Finset.sum_le_sum fun i _ => hB i)
      have hDb : fderiv ℝ ψ y (b y) ≤ C1 * ∑ i : Fin (n + 1), Bb i := by
        have h1 := (fderiv ℝ ψ y).le_opNorm (b y)
        have h2 := le_abs_self (fderiv ℝ ψ y (b y))
        rw [Real.norm_eq_abs] at h1
        have hC10 : 0 ≤ C1 := le_trans (norm_nonneg _) hC1y
        calc fderiv ℝ ψ y (b y) ≤ ‖fderiv ℝ ψ y‖ * ‖b y‖ := by linarith
          _ ≤ C1 * ∑ i : Fin (n + 1), Bb i := mul_le_mul hC1y hbnorm (norm_nonneg _) hC10
      rw [hCG]; linarith
    set δ : ℝ := min 1 (min (ε / (|CG| + 1)) (ε / (Cl + 1))) / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hδCG : δ * CG ≤ ε := by
      have h1 : δ ≤ ε / (|CG| + 1) := by
        have := min_le_left (ε / (|CG| + 1)) (ε / (Cl + 1))
        have := min_le_right 1 (min (ε / (|CG| + 1)) (ε / (Cl + 1)))
        have : 0 ≤ ε / (|CG| + 1) := by positivity
        linarith
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith [le_abs_self CG, abs_nonneg CG]
    have hδCl : δ * Cl ≤ ε := by
      have h1 : δ ≤ ε / (Cl + 1) := by
        have := min_le_right (ε / (|CG| + 1)) (ε / (Cl + 1))
        have := min_le_right 1 (min (ε / (|CG| + 1)) (ε / (Cl + 1)))
        have : 0 ≤ ε / (Cl + 1) := by positivity
        linarith
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    set K := closure Ω ∩ Metric.closedBall x₀ s with hKdef
    have hKc : IsCompact K := hK.inter_right Metric.isClosed_closedBall
    have hx₀K : x₀ ∈ K := ⟨hx₀, Metric.mem_closedBall_self hs.le⟩
    have hhc : ContinuousOn (fun x => f x - δ * ψ x) K :=
      (hfc.mono Set.inter_subset_left).sub (continuous_const.mul hψ2.continuous).continuousOn
    obtain ⟨y, hyK, hymax⟩ := hKc.exists_isMaxOn ⟨x₀, hx₀K⟩ hhc
    have hymax' : ∀ z ∈ K, f z - δ * ψ z ≤ f y - δ * ψ y := fun z hz => hymax hz
    have hyx₀ : f x₀ ≤ f y - δ * ψ y := by
      have := hymax' x₀ hx₀K; rw [hψ0, mul_zero, sub_zero] at this; exact this
    have hyK2 : ‖y - x₀‖ ≤ s := by
      have := hyK.2; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    have hyball : ‖y - x₀‖ < s := by
      rcases lt_or_eq_of_le hyK2 with h | h
      · exact h
      · exfalso
        have h1 := hψsph y h
        have h2 := hmax y hyK.1
        have h3 : 0 < δ * ψ y := mul_pos hδ h1
        linarith
    have hyΩ : y ∈ Ω := by
      by_contra hyn
      have hyfr : y ∈ frontier Ω := by rw [hopen.frontier_eq]; exact ⟨hyK.1, hyn⟩
      have hyR₁ : y ∈ Metric.ball x₀ R₁ := by
        rw [Metric.mem_ball, dist_eq_norm]; linarith
      have hDpos : 0 < fderiv ℝ ψ y (c y) :=
        hψder y (c y) hyball (hlow y hyR₁ hyn) (hcR y hyfr (by linarith))
      exact aux_oe_nobdry Ω hopen f ψ J δ hfc hf2 hψ2 hJc hJΩ y (c y) hyK.1 (hJb y hyfr)
        (mul_pos hδ hDpos) (aux_oe_enter Ω y (normal y) (c y) (hnormal y hyfr) (hobl y hyfr))
        K (s - ‖y - x₀‖) (by linarith)
        (fun z hz hzy => ⟨subset_closure hz, by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have := norm_sub_le_norm_sub_add_norm_sub z y x₀
          linarith⟩) hymax'
    have hlm : IsLocalMax (fun x => f x - δ * ψ x) y := by
      have hyb : y ∈ Metric.ball x₀ s := by rw [Metric.mem_ball, dist_eq_norm]; exact hyball
      filter_upwards [hopen.mem_nhds hyΩ, Metric.isOpen_ball.mem_nhds hyb] with z hz1 hz2
      exact hymax' z ⟨subset_closure hz1, Metric.ball_subset_closedBall hz2⟩
    have hint := aux_oe_interior Ω hopen (a y) (ha y hyΩ) (b y) f ψ δ y hyΩ hf2 hψ2 hlm
    refine ⟨y, hyK.1, ?_, ?_⟩
    · rw [hg y hyΩ]
      have := hG y hyΩ hyball
      have : δ * ((1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), a y i j *
          fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) y
            (EuclideanSpace.single i 1)) + fderiv ℝ ψ y (b y)) ≤ δ * CG :=
        mul_le_mul_of_nonneg_left this hδ.le
      linarith
    · have h1 := hψlow y hyK2
      have h2 : -(δ * Cl) ≤ δ * ψ y := by nlinarith
      linarith


theorem aux_oe_second_neg {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x v w : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => -f y) y v) x w =
      -(fderiv ℝ (fun y => fderiv ℝ f y v) x w) := by
  have : (fun y => fderiv ℝ (fun y => -f y) y v) = fun y => -(fderiv ℝ f y v) := by
    funext y; rw [fderiv_fun_neg]; rfl
  rw [this, fderiv_fun_neg]; rfl

theorem aux_oe_graph (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (fg : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ))
    (hfg : fg ∈ obliqueDiffusionGraph Ω μ a b c) (lam : ℝ) (hlam : 0 < lam) :
    lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖ := by
  obtain ⟨⟨hf2, -⟩, hg, J, hJc, hJΩ, hJb⟩ := hfg
  set F := fg.1 with hFdef
  set G := fg.2 with hGdef
  set f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := closedRegionRestriction F with hfdef
  set g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := closedRegionRestriction G with hgdef
  have hK : IsCompact (closure Ω) := hbounded.isCompact_closure
  have hne : (closure Ω).Nonempty := hconnected.nonempty.closure
  have hfval : ∀ x (hx : x ∈ closure Ω), f x = F ⟨x, hx⟩ := by
    intro x hx; simp [hfdef, closedRegionRestriction, hx]
  have hgval : ∀ x (hx : x ∈ closure Ω), g x = G ⟨x, hx⟩ := by
    intro x hx; simp [hgdef, closedRegionRestriction, hx]
  have hfc : ContinuousOn f (closure Ω) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (closure Ω).domRestrict f = ⇑F := by
      funext ⟨x, hx⟩; exact hfval x hx
    rw [this]; exact F.continuous
  classical
  set J' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :=
    fun x => if hx : x ∈ closure Ω then J ⟨x, hx⟩ else 0 with hJ'def
  have hJ'val : ∀ x (hx : x ∈ closure Ω), J' x = J ⟨x, hx⟩ := by
    intro x hx; simp [hJ'def, hx]
  have hJ'c : ContinuousOn J' (closure Ω) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (closure Ω).domRestrict J' = J := by
      funext ⟨x, hx⟩; exact hJ'val x hx
    rw [this]; exact hJc
  have hJ'Ω : ∀ x ∈ Ω, J' x = fderiv ℝ f x := by
    intro x hx
    rw [hJ'val x (subset_closure hx)]
    exact hJΩ ⟨x, subset_closure hx⟩ hx
  have hJ'b : ∀ x ∈ frontier Ω, J' x (c x) = 0 := by
    intro x hx
    rw [hJ'val x (frontier_subset_closure hx)]
    exact hJb ⟨x, frontier_subset_closure hx⟩ hx
  have haB : ∀ x₀ ∈ frontier Ω, ∀ i j, ∃ B, ∀ᶠ y in 𝓝 x₀, y ∈ Ω → |a y i j| ≤ B :=
    fun x₀ hx₀ i j => aux_oe_bdd Ω μ x₀ (normal x₀) (hnormal x₀ hx₀) _ (haHolder i j)
  have hbB : ∀ x₀ ∈ frontier Ω, ∀ i, ∃ B, ∀ᶠ y in 𝓝 x₀, y ∈ Ω → |b y i| ≤ B :=
    fun x₀ hx₀ i => aux_oe_bdd Ω μ x₀ (normal x₀) (hnormal x₀ hx₀) _ (hbHolder i)
  have hcC : ∀ x₀ ∈ frontier Ω, ∀ ε > 0, ∃ R > 0, ∀ y ∈ frontier Ω, ‖y - x₀‖ < R →
      ‖c y - c x₀‖ < ε := by
    intro x₀ hx₀ ε hε
    set ε' := ε / (n + 2) with hε'
    have hε'pos : 0 < ε' := by positivity
    have hev : ∀ i, ∀ᶠ y in 𝓝 x₀, y ∈ frontier Ω → |c y i - c x₀ i| < ε' := by
      intro i
      obtain ⟨R, hR, hR'⟩ := aux_oe_ccont n Ω μ _ (hc i) x₀ hx₀ ε' hε'pos
      rw [Metric.eventually_nhds_iff]
      exact ⟨R, hR, fun y hy hyf => hR' y hyf (by rwa [dist_eq_norm] at hy)⟩
    obtain ⟨R, hR, hR'⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hev)
    refine ⟨R, hR, fun y hy hyR => ?_⟩
    have hall := hR' (by rwa [dist_eq_norm]) 
    calc ‖c y - c x₀‖ ≤ ∑ i, |(c y - c x₀) i| := aux_oe_norm_le _
      _ < ∑ _i : Fin (n + 1), ε' := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro i _
          simpa using hall i hy
      _ = (n + 1) * ε' := by simp
      _ ≤ ε := by
          rw [hε', mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have hobl : ∀ x ∈ frontier Ω, 0 < ⟪normal x, c x⟫_ℝ := by
    obtain ⟨ε, hε, hε'⟩ := hoblique
    intro x hx
    rw [aux_oe_inner]
    have := hε' x hx
    have e : ∑ i, normal x i * c x i = ∑ i, c x i * normal x i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]; linarith
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne (continuous_abs.comp_continuousOn hfc)
  have hmax' : ∀ x ∈ closure Ω, |f x| ≤ |f x₀| := fun x hx => hmax hx
  have hFn : ‖F‖ ≤ |f x₀| := by
    refine (BoundedContinuousFunction.norm_le (abs_nonneg _)).mpr fun x => ?_
    rw [Real.norm_eq_abs, ← hfval x x.2]; exact hmax' x x.2
  have hval : ∀ y (hy : y ∈ closure Ω), |lam * f y - g y| ≤ ‖lam • F - G‖ := by
    intro y hy
    have := BoundedContinuousFunction.norm_coe_le_norm (lam • F - G) ⟨y, hy⟩
    rw [hfval y hy, hgval y hy]
    simpa [Real.norm_eq_abs] using this
  have key : ∀ ε > 0, lam * |f x₀| ≤ ‖lam • F - G‖ + (lam + 1) * ε := by
    intro ε hε
    rcases le_or_gt 0 (f x₀) with hpos | hneg
    · obtain ⟨y, hy, hgy, hfy⟩ := aux_oe_core n Ω hopen hK a b c normal ha haB hbB hcC hnormal
        hobl f g J' hfc hf2 hg hJ'c hJ'Ω hJ'b x₀ hx₀
        (fun x hx => (le_abs_self _).trans ((hmax' x hx).trans (abs_of_nonneg hpos).le)) ε hε
      have h1 := hval y hy
      have h2 := le_abs_self (lam * f y - g y)
      rw [abs_of_nonneg hpos]
      nlinarith
    · have hg' : ∀ x ∈ Ω, (fun x => -g x) x = (1 / 2 : ℝ) * (∑ i : Fin (n + 1),
          ∑ j : Fin (n + 1), a x i j * fderiv ℝ (fun y => fderiv ℝ (fun x => -f x) y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
            fderiv ℝ (fun x => -f x) x (b x) := by
        intro x hx
        simp only [aux_oe_second_neg, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
        rw [hg x hx]
        simp only [mul_neg, Finset.sum_neg_distrib]
        ring
      obtain ⟨y, hy, hgy, hfy⟩ := aux_oe_core n Ω hopen hK a b c normal ha haB hbB hcC hnormal
        hobl (fun x => -f x) (fun x => -g x) (fun x => -J' x) hfc.neg hf2.neg hg' hJ'c.neg
        (fun x hx => by simp only [hJ'Ω x hx, fderiv_fun_neg])
        (fun x hx => by simp only [ContinuousLinearMap.neg_apply, hJ'b x hx, neg_zero]) x₀ hx₀
        (fun x hx => (neg_le_abs _).trans ((hmax' x hx).trans (abs_of_neg hneg).le)) ε hε
      have h1 := hval y hy
      have h2 := neg_abs_le (lam * f y - g y)
      rw [abs_of_neg hneg]
      nlinarith
  have hmain : lam * ‖F‖ ≤ lam * |f x₀| := mul_le_mul_of_nonneg_left hFn hlam.le
  by_contra hcon
  push_neg at hcon
  have hgap : 0 < lam * ‖F‖ - ‖lam • F - G‖ := by linarith
  have := key ((lam * ‖F‖ - ‖lam • F - G‖) / (2 * (lam + 1))) (by positivity)
  have e : (lam + 1) * ((lam * ‖F‖ - ‖lam • F - G‖) / (2 * (lam + 1))) =
      (lam * ‖F‖ - ‖lam • F - G‖) / 2 := by field_simp
  rw [e] at this
  linarith

end EthierKurtz

open EthierKurtz

theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖ := by
  intro fg hfg lam hlam
  have hsub : obliqueDiffusionGraph Ω μ a b c ⊆
      {fg : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ) | lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖} :=
    fun fg' hfg' => aux_oe_graph n Ω hbounded hconnected hopen μ a b c normal ha haHolder
      hbHolder hc hnormal hoblique fg' hfg' lam hlam
  have hcl : IsClosed
      {fg : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ) | lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_norm.comp continuous_fst)
    · have h1 : Continuous (fun fg : ((closure Ω) →ᵇ ℝ) × ((closure Ω) →ᵇ ℝ) => lam • fg.1) :=
        (continuous_const_smul lam).comp continuous_fst
      exact continuous_norm.comp (h1.sub continuous_snd)
  exact closure_minimal hsub hcl hfg
