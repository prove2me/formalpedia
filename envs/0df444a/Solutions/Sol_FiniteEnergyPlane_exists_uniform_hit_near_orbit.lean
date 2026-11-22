-- Prove2me | solution 1 for FiniteEnergyPlane.exists_uniform_hit_near_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T13:07:44.054886+00:00
-- url     : https://prove2.me/submissions/1ae99577-dcd2-48d1-81b7-9437d2b75638

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_exists_angle_gain_of_isCZAtLeast_three
import Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_near_linearized
import Theorems.Thm_FiniteEnergyPlane_exists_page_direction_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_exists_mem_Ioc_pos_of_norm_sub_exp_lt
import Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame_hasXiLoopWind_iff
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane



/-!
# Glue for `exists_uniform_hit_near_orbit` (138fff41)

Over the children (A) `exists_angle_gain_of_isCZAtLeast_three`, (B)
`exists_tubeCoords_near_linearized`, (C) `exists_page_direction_of_hasAsymptoticEigenvector`,
(D) `exists_mem_Ioc_pos_of_norm_sub_exp_lt`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real ComplexConjugate

lemma uh_norm_vecToC (a : CauchyRiemannIndex.Vec 1) : ‖vecToC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [vecToC, Fintype.sum_sum_type, sq]

lemma uh_vecToC_sub (a b : CauchyRiemannIndex.Vec 1) : vecToC (a - b) = vecToC a - vecToC b := by
  apply Complex.ext <;> simp [vecToC]

lemma uh_vecToC_smul (r : ℝ) (a : CauchyRiemannIndex.Vec 1) :
    vecToC (r • a) = (r : ℂ) * vecToC a := by
  apply Complex.ext <;> simp [vecToC]

lemma uh_vecToC_cont : Continuous vecToC := by
  have e : vecToC = fun a : CauchyRiemannIndex.Vec 1 =>
      ((a (Sum.inl 0) : ℝ) : ℂ) + ((a (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
    funext fun a => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  rw [e]
  have h1 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inl 0) :=
    (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous
  have h2 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inr 0) :=
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

/-- `‖x/‖x‖ - y/‖y‖‖ ≤ 2‖x - y‖/‖y‖`. -/
lemma uh_unit_sub_le (x y : ℂ) (hy : y ≠ 0) :
    ‖x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ)‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h1 : ‖x / (‖x‖ : ℂ) - x / (‖y‖ : ℂ)‖ ≤ ‖x - y‖ / ‖y‖ := by
    by_cases hx : x = 0
    · simp [hx]; positivity
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hx' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
    have hy' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
    have e : x / (‖x‖ : ℂ) - x / (‖y‖ : ℂ) = (x / (‖x‖ : ℂ)) * (((‖y‖ - ‖x‖) / ‖y‖ : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [e, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hnx, div_self hnx.ne', one_mul, abs_div, abs_of_pos hny]
    gcongr
    exact abs_norm_sub_norm_le y x |>.trans (by rw [norm_sub_rev])
  have h2 : ‖x / (‖y‖ : ℂ) - y / (‖y‖ : ℂ)‖ = ‖x - y‖ / ‖y‖ := by
    rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hny]
  calc ‖x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ)‖
      ≤ ‖x / (‖x‖ : ℂ) - x / (‖y‖ : ℂ)‖ + ‖x / (‖y‖ : ℂ) - y / (‖y‖ : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖x - y‖ / ‖y‖ + ‖x - y‖ / ‖y‖ := by rw [h2]; gcongr
    _ = 2 * ‖x - y‖ / ‖y‖ := by ring

lemma uh_exp_eq_div (z : ℂ) (θ : ℝ) (hz : z ≠ 0)
    (h : z = (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    Complex.exp ((θ : ℂ) * Complex.I) = z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hz).ne'
  rw [eq_div_iff hn, mul_comm]; exact h.symm

lemma uh_conj_exp (x : ℝ) :
    conj (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

lemma uh_eq_one_of_pos (w : ℂ) (hw : ‖w‖ = 1) (hre : 0 < w.re) (him : w.im = 0) : w = 1 := by
  have h : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [h] at hw ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre] at hw
  rw [hw]; simp

/-- The scalar bookkeeping of the glue. -/
lemma uh_arith (K n₀ z an ad τd ρ₀ ρ₁ δ : ℝ) (hK1 : 1 ≤ K) (hn0 : 0 < n₀) (hn1 : n₀ < 1)
    (h6 : 6 * K ^ 2 * n₀ < 1) (hρ0 : 2 * K * n₀ < ρ₀) (hρ1 : 2 * K * n₀ < ρ₁)
    (hδ : 2 * K * n₀ < δ) (hlo : n₀ ≤ K * z) (hhi : z ≤ K * n₀) (hd : ad ≤ K * n₀ ^ 2)
    (hτ : τd ≤ K * n₀) (ht1 : an ≤ z + ad) (ht2 : z - ad ≤ an) :
    0 < an ∧ an < ρ₀ ∧ an < ρ₁ ∧ τd < δ ∧ 0 < z ∧ 2 * ad < 1 / 3 * z := by
  have hK0 : 0 < K := by linarith
  have hsq : n₀ ^ 2 ≤ n₀ := by
    have : n₀ * n₀ ≤ n₀ * 1 := mul_le_mul_of_nonneg_left hn1.le hn0.le
    nlinarith
  have hKsq : K * n₀ ^ 2 ≤ K * n₀ := mul_le_mul_of_nonneg_left hsq hK0.le
  have hKn : K * n₀ ≤ 2 * K * n₀ := by nlinarith
  have hz : 0 < z := by
    by_contra h; push_neg at h
    have : K * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0.le h
    linarith
  -- K n₀² ≤ K n₀ · K z
  have hKz : K * n₀ ^ 2 ≤ K ^ 2 * n₀ * z := by
    have : K * n₀ ^ 2 = (K * n₀) * n₀ := by ring
    rw [this]
    have h' : (K * n₀) * n₀ ≤ (K * n₀) * (K * z) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    have : (K * n₀) * (K * z) = K ^ 2 * n₀ * z := by ring
    linarith
  have hK2z : K ^ 2 * n₀ * z < 1 / 6 * z := by
    have : K ^ 2 * n₀ < 1 / 6 := by linarith
    exact mul_lt_mul_of_pos_right this hz
  refine ⟨by linarith, by linarith, by linarith, by linarith, hz, by linarith⟩

set_option maxHeartbeats 1600000 in
theorem exists_uniform_hit_near_orbit_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧ ∃ L > 0, ∀ y : ℝ → V 1,
      IsReebTrajectory H y → y 0 ∈ W → y 0 ∉ Set.range P.x →
        (∃ t ∈ Set.Ioc 0 L, y t ∈ Set.range (fun z => proj H (u z))) ∧
        (∃ t ∈ Set.Ico (-L) 0, y t ∈ Set.range (fun z => proj H (u z))) := by
  obtain ⟨Z, hZ, hwind⟩ := exists_unitaryXiFrame_hasXiLoopWind_iff H hH J hJ P
  obtain ⟨Sinf, hSym, -, hA, -⟩ := (asympOp_frame_bridge H hH J hJ P).2 Z hZ
  obtain ⟨μ, v, hv, hvw⟩ :=
    exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane H hH J hJ P u hu huP
  obtain ⟨E, hEc, hEp, hE0, hvE, ρ₀, hρ₀, dir, hdirc, hdir, hconv⟩ :=
    exists_page_direction_of_hasAsymptoticEigenvector H hH J P u μ v hv Z hZ
  have hEw : HasLoopWind (fun t => vecToC (E t)) 1 := by
    refine (hwind E hEc hEp hE0 1).1 ?_
    have hv' : (fun t => Z t (E t)) = v := funext fun t => (hvE t).symm
    rw [hv']; exact hvw
  obtain ⟨r, hr, CA, hrot⟩ := exists_angle_gain_of_isCZAtLeast_three H hH J hJ P hcz Z hZ hwind
    Sinf hSym hA _ hEw
  obtain ⟨-, -, -, β, hβc, hβ, -⟩ := hEw
  have hT := P.T_pos
  set L : ℝ := P.T * ((|CA| + 3 * π) / r + 1) with hLdef
  have hL : 0 < L := by positivity
  have hgain : 3 * π ≤ r * (L / P.T) - CA := by
    have : r * (L / P.T) = |CA| + 3 * π + r := by
      rw [hLdef]; field_simp
    rw [this]; linarith [le_abs_self CA]
  obtain ⟨CB, hB⟩ := exists_tubeCoords_near_linearized H hH J hJ P Z hZ Sinf hSym hA L hL
  obtain ⟨ρ₁, hρ₁, δ, hδ, hconv'⟩ := hconv (1 / 3) (by norm_num)
  set K : ℝ := |CB| + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith [abs_nonneg CB]
  have hK0 : 0 < K := by linarith
  have hCBK : CB ≤ K := by rw [hK]; linarith [le_abs_self CB]
  set ε : ℝ := min (min 1 (1 / (6 * K ^ 2))) (min (ρ₀ / (2 * K)) (min (ρ₁ / (2 * K)) (δ / (2 * K))))
    with hεdef
  have hε : 0 < ε := by
    simp only [hεdef, lt_min_iff]; refine ⟨⟨by norm_num, by positivity⟩, by positivity, by positivity,
      by positivity⟩
  obtain ⟨W, hWo, hWx, hW⟩ := hB ε hε
  refine ⟨W, hWo, hWx, L, hL, ?_⟩
  intro y hy hy0 hyx
  obtain ⟨τ₀, a₀, τ, a, ζ, ha₀ε, ha₀ne, hζ, hζ0, hτc, hac, hest⟩ := hW y hy hy0
  have ha₀ : a₀ ≠ 0 := ha₀ne hyx
  have hn0 : 0 < ‖a₀‖ := norm_pos_iff.2 ha₀
  have hζne : ∃ t, ζ t ≠ 0 := ⟨τ₀ / P.T, by rw [hζ0]; exact ha₀⟩
  obtain ⟨θ, hθc, hθ, hθβ⟩ := hrot ζ hζ hζne
  have hgain' := hθβ β hβc hβ
  -- the smallness of `a₀`
  have hε1 : ‖a₀‖ < 1 := lt_of_lt_of_le ha₀ε (by simp only [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ‖a₀‖ < 1 / (6 * K ^ 2) :=
    lt_of_lt_of_le ha₀ε (by simp only [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ‖a₀‖ < ρ₀ / (2 * K) :=
    lt_of_lt_of_le ha₀ε (by simp only [hεdef]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ‖a₀‖ < ρ₁ / (2 * K) := lt_of_lt_of_le ha₀ε (by
    simp only [hεdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε5 : ‖a₀‖ < δ / (2 * K) := lt_of_lt_of_le ha₀ε (by
    simp only [hεdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set n₀ := ‖a₀‖ with hn₀
  -- pointwise estimates on the window
  have key : ∀ σ ∈ Set.Icc (-L) L,
      0 < ‖a σ‖ ∧ ‖a σ‖ < ρ₀ ∧ ‖a σ‖ < ρ₁ ∧ |τ σ - (τ₀ + σ)| < δ ∧
        ζ ((τ₀ + σ) / P.T) ≠ 0 ∧ 2 * ‖a σ - ζ ((τ₀ + σ) / P.T)‖ / ‖ζ ((τ₀ + σ) / P.T)‖ < 1 / 3 := by
    intro σ hσ
    obtain ⟨-, hτ, hlo, hhi, hdiff⟩ := hest σ hσ
    set z := ζ ((τ₀ + σ) / P.T)
    have hlo' : n₀ ≤ K * ‖z‖ := hlo.trans (by gcongr)
    have hhi' : ‖z‖ ≤ K * n₀ := hhi.trans (by gcongr)
    have hdiff' : ‖a σ - z‖ ≤ K * n₀ ^ 2 := hdiff.trans (by gcongr)
    have hτ' : |τ σ - τ₀ - σ| ≤ K * n₀ := hτ.trans (by gcongr)
    have hK2 : 6 * K ^ 2 * n₀ < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * K ^ 2)).1 hε2; linarith
    have h2K : 2 * K * n₀ < ρ₀ := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hε3; linarith
    have h2K' : 2 * K * n₀ < ρ₁ := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hε4; linarith
    have h2K'' : 2 * K * n₀ < δ := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hε5; linarith
    have ht1 : ‖a σ‖ ≤ ‖z‖ + ‖a σ - z‖ := by
      have := norm_add_le z (a σ - z); simpa using this
    have ht2 : ‖z‖ - ‖a σ - z‖ ≤ ‖a σ‖ := by
      have := norm_sub_norm_le z (z - a σ)
      rw [norm_sub_rev z (a σ)] at this
      simpa using this
    have e : τ σ - (τ₀ + σ) = τ σ - τ₀ - σ := by ring
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uh_arith K n₀ ‖z‖ ‖a σ‖ ‖a σ - z‖ |τ σ - τ₀ - σ| ρ₀ ρ₁ δ
      hK1 hn0 hε1 hK2 h2K h2K' h2K'' hlo' hhi' hdiff' hτ' ht1 ht2
    refine ⟨h1, h2, h3, by rw [e]; exact h4, norm_pos_iff.1 h5, ?_⟩
    rw [div_lt_iff₀ h5]; exact h6
  -- the path `g` and the angle `ψ`
  let tt : ℝ → ℝ := fun σ => (τ₀ + σ) / P.T
  let g : ℝ → ℂ := fun σ =>
    vecToC (a σ) / ((‖vecToC (a σ)‖ : ℝ) : ℂ) * conj (vecToC (dir (τ σ, ‖a σ‖)))
  let ψ : ℝ → ℝ := fun σ => θ (tt σ) - β (tt σ)
  have htt : Continuous tt := by fun_prop
  have hψc : Continuous ψ := (hθc.comp htt).sub (hβc.comp htt)
  have hgc : ContinuousOn g (Set.Icc (-L) L) := by
    have hva : ContinuousOn (fun σ => vecToC (a σ)) (Set.Icc (-L) L) :=
      uh_vecToC_cont.comp_continuousOn hac
    have hna : ContinuousOn (fun σ => ‖a σ‖) (Set.Icc (-L) L) := hac.norm
    have hd : ContinuousOn (fun σ => dir (τ σ, ‖a σ‖)) (Set.Icc (-L) L) := by
      refine hdirc.comp (hτc.prodMk hna) ?_
      intro σ hσ
      obtain ⟨h1, h2, -⟩ := key σ hσ
      exact ⟨Set.mem_univ _, h1, h2⟩
    refine ContinuousOn.mul ?_ ((Complex.continuous_conj.comp uh_vecToC_cont).comp_continuousOn hd)
    refine hva.div (Complex.continuous_ofReal.comp_continuousOn hva.norm) ?_
    intro σ hσ
    rw [uh_norm_vecToC]
    exact_mod_cast (key σ hσ).1.ne'
  have hclose : ∀ σ ∈ Set.Icc (-L) L,
      ‖g σ - Complex.exp ((ψ σ : ℂ) * Complex.I)‖ < 1 := by
    intro σ hσ
    obtain ⟨hapos, haρ₀, haρ₁, hτδ, hz0, hunit⟩ := key σ hσ
    set z := ζ ((τ₀ + σ) / P.T)
    have hz0' : vecToC z ≠ 0 := by
      intro h; apply hz0
      have : ‖z‖ = 0 := by rw [← uh_norm_vecToC, h, norm_zero]
      exact norm_eq_zero.1 this
    have hθe : Complex.exp ((θ (tt σ) : ℂ) * Complex.I) = vecToC z / ((‖vecToC z‖ : ℝ) : ℂ) :=
      uh_exp_eq_div _ _ hz0' (hθ _)
    have hE0' : vecToC (E (tt σ)) ≠ 0 := by
      intro h; apply hE0 (tt σ)
      have : ‖E (tt σ)‖ = 0 := by rw [← uh_norm_vecToC, h, norm_zero]
      exact norm_eq_zero.1 this
    have hβe : Complex.exp ((β (tt σ) : ℂ) * Complex.I) =
        vecToC (E (tt σ)) / ((‖vecToC (E (tt σ))‖ : ℝ) : ℂ) :=
      uh_exp_eq_div _ _ hE0' (hβ _)
    have hψe : Complex.exp ((ψ σ : ℂ) * Complex.I) =
        Complex.exp ((θ (tt σ) : ℂ) * Complex.I) * conj (Complex.exp ((β (tt σ) : ℂ) * Complex.I)) := by
      rw [uh_conj_exp, ← Complex.exp_add]; congr 1; simp only [ψ]; push_cast; ring
    have hd1 : ‖vecToC (dir (τ σ, ‖a σ‖))‖ = 1 := by
      rw [uh_norm_vecToC]; exact (hdir (τ σ) ‖a σ‖ ⟨hapos, haρ₀⟩).1
    have hdclose : ‖vecToC (dir (τ σ, ‖a σ‖)) -
        vecToC (E (tt σ)) / ((‖vecToC (E (tt σ))‖ : ℝ) : ℂ)‖ < 1 / 3 := by
      have h := hconv' (τ σ) (τ₀ + σ) hτδ ‖a σ‖ ⟨hapos, haρ₁⟩
      have h' : ‖vecToC (dir (τ σ, ‖a σ‖)) -
          ((‖E ((τ₀ + σ) / P.T)‖⁻¹ : ℝ) : ℂ) * vecToC (E ((τ₀ + σ) / P.T))‖ < 1 / 3 := by
        rw [← uh_vecToC_smul, ← uh_vecToC_sub, uh_norm_vecToC]; exact h
      have e : vecToC (E (tt σ)) / ((‖vecToC (E (tt σ))‖ : ℝ) : ℂ) =
          ((‖E ((τ₀ + σ) / P.T)‖⁻¹ : ℝ) : ℂ) * vecToC (E ((τ₀ + σ) / P.T)) := by
        rw [uh_norm_vecToC]; push_cast; rw [div_eq_inv_mul]
      rw [e]; exact h'
    have hzu : ‖vecToC z / ((‖vecToC z‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 hz0')]
    have hunit' : ‖vecToC (a σ) / ((‖vecToC (a σ)‖ : ℝ) : ℂ) -
        vecToC z / ((‖vecToC z‖ : ℝ) : ℂ)‖ < 1 / 3 := by
      refine lt_of_le_of_lt (uh_unit_sub_le _ _ hz0') ?_
      rw [← uh_vecToC_sub, uh_norm_vecToC, uh_norm_vecToC]; exact hunit
    rw [hψe, hθe, hβe]
    simp only [g]
    set A := vecToC (a σ) / ((‖vecToC (a σ)‖ : ℝ) : ℂ)
    set B := vecToC z / ((‖vecToC z‖ : ℝ) : ℂ)
    set D := vecToC (dir (τ σ, ‖a σ‖))
    set F := vecToC (E (tt σ)) / ((‖vecToC (E (tt σ))‖ : ℝ) : ℂ)
    have e : A * conj D - B * conj F = (A - B) * conj D + B * conj (D - F) := by
      rw [map_sub]; ring
    rw [e]
    calc ‖(A - B) * conj D + B * conj (D - F)‖ ≤ ‖(A - B) * conj D‖ + ‖B * conj (D - F)‖ :=
          norm_add_le _ _
      _ = ‖A - B‖ + ‖D - F‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hd1, hzu, mul_one, one_mul]
      _ < 1 / 3 + 1 / 3 := add_lt_add hunit' hdclose
      _ < 1 := by norm_num
  -- a positive real value of `g` is a hit
  have hhit : ∀ σ ∈ Set.Icc (-L) L, 0 < (g σ).re → (g σ).im = 0 →
      y σ ∈ Set.range (fun z => proj H (u z)) := by
    intro σ hσ hre him
    obtain ⟨hapos, haρ₀, -⟩ := key σ hσ
    obtain ⟨hyσ, -⟩ := hest σ hσ
    have hd := hdir (τ σ) ‖a σ‖ ⟨hapos, haρ₀⟩
    have hd1 : ‖vecToC (dir (τ σ, ‖a σ‖))‖ = 1 := by rw [uh_norm_vecToC]; exact hd.1
    have ha0' : vecToC (a σ) ≠ 0 := by
      intro h; have : ‖a σ‖ = 0 := by rw [← uh_norm_vecToC, h, norm_zero]
      linarith
    have hAu : ‖vecToC (a σ) / ((‖vecToC (a σ)‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 ha0')]
    have hg1 : g σ = 1 := by
      refine uh_eq_one_of_pos _ ?_ hre him
      simp only [g]; rw [norm_mul, Complex.norm_conj, hAu, hd1, one_mul]
    set D := vecToC (dir (τ σ, ‖a σ‖))
    have hDD : D * conj D = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd1]; simp
    have hAD : vecToC (a σ) / ((‖vecToC (a σ)‖ : ℝ) : ℂ) = D := by
      have := congrArg (· * D) hg1
      simp only [g, one_mul] at this
      rw [mul_assoc, mul_comm (conj D) D, hDD, mul_one] at this
      exact this
    have hvec : a σ = ‖a σ‖ • dir (τ σ, ‖a σ‖) := by
      have h0 : vecToC (a σ - ‖a σ‖ • dir (τ σ, ‖a σ‖)) = 0 := by
        have hn : ((‖a σ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hapos.ne'
        rw [uh_vecToC_sub, uh_vecToC_smul, show vecToC (dir (τ σ, ‖a σ‖)) = _ from hAD.symm,
          uh_norm_vecToC, mul_div_left_comm, div_self hn, mul_one, sub_self]
      have : ‖a σ - ‖a σ‖ • dir (τ σ, ‖a σ‖)‖ = 0 := by rw [← uh_norm_vecToC, h0, norm_zero]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    rw [hyσ, hvec]
    exact hd.2
  constructor
  · -- forward hit
    have hsub : Set.Icc 0 L ⊆ Set.Icc (-L) L := Set.Icc_subset_Icc (by linarith) le_rfl
    have hinc : ψ 0 + 3 * π ≤ ψ L := by
      have h := hgain' (tt 0) (tt L) (by simp only [tt]; gcongr)
      have e : tt L - tt 0 = L / P.T := by simp only [tt]; field_simp; ring
      simp only [ψ]; rw [e] at h; linarith
    obtain ⟨σ, hσ, hre, him⟩ := exists_mem_Ioc_pos_of_norm_sub_exp_lt 0 L hL.le g ψ (hgc.mono hsub)
      hψc.continuousOn (fun σ hσ => hclose σ (hsub hσ)) hinc
    exact ⟨σ, hσ, hhit σ (hsub (Set.Ioc_subset_Icc_self hσ)) hre him⟩
  · -- backward hit
    let g' : ℝ → ℂ := fun σ => conj (g (-σ))
    let ψ' : ℝ → ℝ := fun σ => -ψ (-σ)
    have hneg : ∀ σ ∈ Set.Icc 0 L, -σ ∈ Set.Icc (-L) L := by
      intro σ hσ; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hg'c : ContinuousOn g' (Set.Icc 0 L) := by
      refine Complex.continuous_conj.comp_continuousOn (hgc.comp continuous_neg.continuousOn hneg)
    have hψ'c : ContinuousOn ψ' (Set.Icc 0 L) := (hψc.comp continuous_neg).neg.continuousOn
    have hclose' : ∀ σ ∈ Set.Icc 0 L, ‖g' σ - Complex.exp ((ψ' σ : ℂ) * Complex.I)‖ < 1 := by
      intro σ hσ
      have e : g' σ - Complex.exp ((ψ' σ : ℂ) * Complex.I) =
          conj (g (-σ) - Complex.exp ((ψ (-σ) : ℂ) * Complex.I)) := by
        simp only [g', ψ']; rw [map_sub, uh_conj_exp]
      rw [e, Complex.norm_conj]; exact hclose _ (hneg σ hσ)
    have hinc' : ψ' 0 + 3 * π ≤ ψ' L := by
      have h := hgain' (tt (-L)) (tt 0) (by simp only [tt]; gcongr; linarith)
      have e : tt 0 - tt (-L) = L / P.T := by simp only [tt]; field_simp; ring
      simp only [ψ', neg_zero, ψ]; rw [e] at h; linarith
    obtain ⟨σ, hσ, hre, him⟩ := exists_mem_Ioc_pos_of_norm_sub_exp_lt 0 L hL.le g' ψ' hg'c hψ'c
      hclose' hinc'
    refine ⟨-σ, ⟨by linarith [hσ.2], by linarith [hσ.1]⟩, ?_⟩
    have hre' : 0 < (g (-σ)).re := by simpa [g'] using hre
    have him' : (g (-σ)).im = 0 := by simpa [g'] using him
    exact hhit (-σ) (hneg σ (Set.Ioc_subset_Icc_self hσ)) hre' him'

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧ ∃ L > 0, ∀ y : ℝ → V 1,
      IsReebTrajectory H y → y 0 ∈ W → y 0 ∉ Set.range P.x →
        (∃ t ∈ Set.Ioc 0 L, y t ∈ Set.range (fun z => proj H (u z))) ∧
        (∃ t ∈ Set.Ico (-L) 0, y t ∈ Set.range (fun z => proj H (u z))) :=
  FiniteEnergyPlane.exists_uniform_hit_near_orbit_glue H hH J hJ P hcz u hu huP
