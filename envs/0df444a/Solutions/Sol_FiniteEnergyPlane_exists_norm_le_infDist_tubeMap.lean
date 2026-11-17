-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_le_infDist_tubeMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:52:39.883902+00:00
-- url     : https://prove2.me/submissions/0965faf5-c32f-4472-9833-24b775403dc9

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_le_infDist_proj_add_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



/-!
# A3a: the normal coordinate of the tube map is controlled by the distance to the orbit

For `Φ(ζ, w) = u ζ + N ζ w` with the frame asymptotics of a standard tube, for `|ζ|` large and
`|w|` small, `|w| ≤ C (dist(proj Φ(ζ, w), P) + dist(proj u ζ, P))`.
Route: write `Φ = e^{2a}(ũ + e^{-2a} N w)` with `ũ = proj u`, base the comparison at the point
`x(θ)` of `P` nearest to `ũ` (phase `θ` within `T/2` of `T τ`, so `M(θ/T) ≈ M(τ)`), use the
lower bound `c‖h‖ ≤ dist(proj(x(θ) + h), P)` for `h = M(θ/T) w ∈ ξ` and Lipschitz `proj`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma dgn_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- `y = e^{2 a(y)} proj(y)`. -/
lemma dgn_eq_exp_smul_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : y = Real.exp (2 * aCoord H y) • proj H y := by
  have hs := (dgn_scale_spec H hH y hy).1
  unfold aCoord proj
  rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring, Real.exp_neg,
    Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma dgn_vecToC_J₀ (a : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
      dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]

lemma dgn_cToVec_vecToC (a : CauchyRiemannIndex.Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma dgn_vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma dgn_norm_cToVec (z : ℂ) : ‖cToVec z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp [cToVec, Fintype.sum_sum_type]

lemma dgn_cToVec_re_im (z : ℂ) :
    cToVec z = z.re • cToVec 1 + z.im • cToVec Complex.I := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec]

lemma dgn_M_injective {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M) (t : ℝ) :
    Function.Injective (M t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := (hM.2.2 t).2.2.2 a (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)
  rw [ha] at h
  have h0 : omega0 (0 : V 1) (M t (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)) = 0 := by
    simp [omega0, dot, j0]
  rw [h0, eq_comm, real_inner_self_eq_norm_sq] at h
  have hJa : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    exact norm_eq_zero.1 this
  have hc := congrArg vecToC hJa
  rw [dgn_vecToC_J₀] at hc
  have : vecToC a = 0 := by
    have h0' : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
      apply Complex.ext <;> simp [vecToC]
    rw [h0'] at hc
    simpa using hc
  rw [← dgn_cToVec_vecToC a, this]
  ext i; rcases i with i | i <;> simp [cToVec]

/-- Uniform two-sided bounds for a unitary frame. -/
lemma dgn_frame_bounds {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M) :
    ∃ m₀ > 0, ∃ m₁ > 0, ∀ (t : ℝ) (a : CauchyRiemannIndex.Vec 1),
      m₀ * ‖a‖ ≤ ‖M t a‖ ∧ ‖M t a‖ ≤ m₁ * ‖a‖ := by
  have hMc : Continuous M := hM.1.continuous
  have hper : Function.Periodic M 1 := hM.2.1
  have hred : ∀ t, M t = M (Int.fract t) := fun t => by
    rw [Int.fract, show t - ⌊t⌋ = t - (⌊t⌋ : ℤ) * (1 : ℝ) by ring, hper.sub_int_mul_eq]
  set K : Set (ℝ × CauchyRiemannIndex.Vec 1) := Set.Icc (0 : ℝ) 1 ×ˢ sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_sphere _ _)
  have hne : K.Nonempty := by
    obtain ⟨a, ha⟩ := (NormedSpace.sphere_nonempty (E := CauchyRiemannIndex.Vec 1)
      (x := 0) (r := 1)).2 zero_le_one
    exact ⟨(0, a), ⟨⟨le_rfl, zero_le_one⟩, ha⟩⟩
  have hg : Continuous fun p : ℝ × CauchyRiemannIndex.Vec 1 => ‖M p.1 p.2‖ :=
    ((hMc.comp continuous_fst).clm_apply continuous_snd).norm
  obtain ⟨p₀, hp₀K, hp₀⟩ := hKc.exists_isMinOn hne hg.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hMc.norm.continuousOn)
  have hm₀ : 0 < ‖M p₀.1 p₀.2‖ := by
    rw [norm_pos_iff]
    intro h0
    have := dgn_M_injective hM p₀.1 (h0.trans (map_zero _).symm)
    have h1 : ‖p₀.2‖ = 1 := by simpa using hp₀K.2
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨‖M p₀.1 p₀.2‖, hm₀, max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t a => ?_⟩
  have hft : Int.fract t ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  rw [hred t]
  constructor
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
      have hmem : (Int.fract t, ‖a‖⁻¹ • a) ∈ K :=
        ⟨hft, by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hna.ne']⟩
      have h := hp₀ hmem
      simp only [Set.mem_setOf_eq, map_smul, norm_smul, norm_inv, norm_norm] at h
      calc ‖M p₀.1 p₀.2‖ * ‖a‖ ≤ ‖a‖⁻¹ * ‖M (Int.fract t) a‖ * ‖a‖ :=
            mul_le_mul_of_nonneg_right h hna.le
        _ = ‖M (Int.fract t) a‖ := by field_simp
  · have hb := hB (Int.fract t) hft
    rw [Real.norm_eq_abs, abs_norm] at hb
    calc ‖M (Int.fract t) a‖ ≤ ‖M (Int.fract t)‖ * ‖a‖ := (M (Int.fract t)).le_opNorm a
      _ ≤ max B 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _)) (norm_nonneg _)

/-- A smooth `1`-periodic family of linear maps is Lipschitz in `t`. -/
lemma dgn_frame_lipschitz {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t t' : ℝ, ‖M t - M t'‖ ≤ L * |t - t'| := by
  have hd : Differentiable ℝ M := hM.1.differentiable (by simp)
  have hper : Function.Periodic M 1 := hM.2.1
  have hfper : ∀ t, deriv M t = deriv M (Int.fract t) := by
    intro t
    have hfun : (fun r => M (r + (⌊t⌋ : ℝ))) = M := by
      funext r
      have := hper.int_mul ⌊t⌋
      simpa using this r
    have h := deriv_comp_add_const (f := M) (a := (⌊t⌋ : ℝ)) (x := Int.fract t)
    rw [hfun, Int.fract_add_floor] at h
    exact h.symm
  have hcont : Continuous (deriv M) := hM.1.continuous_deriv (by simp)
  have hcn : Continuous fun t => ‖deriv M t‖ := hcont.norm
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t => ‖deriv M t‖) hcn.continuousOn
  set L : ℝ := max B 0
  have hbound : ∀ t, ‖deriv M t‖₊ ≤ L.toNNReal := by
    intro t
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _), hfper t]
    have := hB (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    rw [Real.norm_eq_abs, abs_norm] at this
    exact this.trans (le_max_left _ _)
  have hlip := lipschitzWith_of_nnnorm_deriv_le hd hbound
  refine ⟨L, le_max_right _ _, fun t t' => ?_⟩
  have := hlip.dist_le_mul t t'
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (le_max_right _ _)] at this
  exact this

/-- Eventual smallness from exponential decay. -/
lemma dgn_small {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F} {b : ℝ}
    (hf : ExpDecayCInfty f b) (hb : 0 < b) (η : ℝ) (hη : 0 < η) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ η := by
  obtain ⟨C, s₁, hC⟩ := hf.2 0
  set C' : ℝ := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max s₁ (-Real.log (η / C') / b), fun s hs t => ?_⟩
  have h := hC s (le_trans (le_max_left _ _) hs) t
  rw [norm_iteratedFDeriv_zero] at h
  have hs2 : -Real.log (η / C') / b ≤ s := le_trans (le_max_right _ _) hs
  have hexp : Real.exp (-(b * s)) ≤ η / C' := by
    rw [← Real.exp_log (div_pos hη hC')]
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ hb] at hs2
    linarith
  calc ‖f (s, t)‖ ≤ C * Real.exp (-(b * s)) := h
    _ ≤ C' * Real.exp (-(b * s)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ C' * (η / C') := mul_le_mul_of_nonneg_left hexp hC'.le
    _ = η := by field_simp

lemma dgn_cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  have hπ : (2 * π) ≠ 0 := by positivity
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hπ, mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz)]
  exact Complex.norm_mul_exp_arg_mul_I z

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma dgn_final_arith {cP m₀ D ηK I₁ I₂ nw : ℝ} (hcm : 0 < cP * m₀) (hD0 : 0 ≤ D)
    (hi1 : 0 ≤ I₁) (hi2 : 0 ≤ I₂) (hnw : 0 ≤ nw) (hDK : D * ηK ≤ cP * m₀ / 2)
    (hchain : cP * (m₀ * nw) ≤ I₁ + D * (I₂ + ηK * nw)) :
    nw ≤ 2 * (D + 1) / (cP * m₀) * (I₁ + I₂) := by
  have e1 : D * (ηK * nw) ≤ cP * m₀ / 2 * nw := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hDK hnw
  have e2 : 0 ≤ D * I₁ := mul_nonneg hD0 hi1
  have hkey : cP * m₀ / 2 * nw ≤ (D + 1) * (I₁ + I₂) := by
    have e3 : cP * (m₀ * nw) = cP * m₀ / 2 * nw + cP * m₀ / 2 * nw := by ring
    have e4 : D * (I₂ + ηK * nw) = D * I₂ + D * (ηK * nw) := by ring
    have e5 : (D + 1) * (I₁ + I₂) = I₁ + D * I₂ + D * I₁ + I₂ := by ring
    linarith
  calc nw = (2 / (cP * m₀)) * (cP * m₀ / 2 * nw) := by field_simp; rw [mul_assoc, mul_div_assoc, div_self hcm.ne', mul_one]
    _ ≤ (2 / (cP * m₀)) * ((D + 1) * (I₁ + I₂)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * (D + 1) / (cP * m₀) * (I₁ + I₂) := by ring

/- A3a: for the tube map `Φ(ζ, w) = u ζ + N ζ w` with the asymptotics of a standard tube over a
prime orbit, the normal coordinate is controlled by distances to the orbit, for `|ζ|` large and
`|w|` small. -/
set_option maxHeartbeats 1000000 in
theorem exists_norm_le_infDist_tubeMap_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ r₀ > 0, ∃ C R : ℝ, ∀ ζ w : ℂ, R ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      u ζ + N ζ w ≠ 0 ∧
      ‖w‖ ≤ C * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)) := by
  classical
  obtain ⟨cP, hcP, ρP, hρP, hlowP⟩ := exists_mul_norm_le_infDist_proj_add_of_isPrime H hH J hJ P hP
  obtain ⟨cx, hcx, hxsep⟩ := exists_mul_abs_sub_le_norm_sub_of_isPrime H hH P hP
  obtain ⟨m₀, hm₀, m₁, hm₁, hMb⟩ := dgn_frame_bounds hM
  obtain ⟨LM, hLM, hMlip⟩ := dgn_frame_lipschitz hM
  have hT : 0 < P.T := P.T_pos
  have hxc : Continuous P.x := (ReebOrbit.contDiff_x H hH P).continuous
  have hxper : Function.Periodic P.x P.T := P.periodic
  set K : Set (V 1) := Set.range P.x with hKdef
  have hK : IsCompact K := hxper.compact_of_continuous hT.ne' hxc
  have hKne : K.Nonempty := Set.range_nonempty _
  set O : Set (V 1) := {y | y ≠ 0} with hOdef
  have hO : IsOpen O := isOpen_ne
  have hKO : K ⊆ O := by
    rintro _ ⟨τ, rfl⟩
    show P.x τ ≠ 0
    intro h
    have hm := P.mem τ
    rw [h] at hm
    have := hH.2.2 0 hm
    simp at this
  have hprojC : ContDiffOn ℝ 1 (proj H) O := fun y hy =>
    ((contDiffAt_aCoord_proj H hH y hy).2.of_le (by exact_mod_cast le_top)).contDiffWithinAt
  obtain ⟨δP, hδP, D, hD0, hDlip⟩ := exists_lipschitz_near_compact hO hprojC hK hKO
  -- constants
  set Kc : ℝ := 2 * LM / (cx * P.T) + 2 + m₁ + 2 with hKc
  have hKcpos : 0 < Kc := by positivity
  set η : ℝ := min (min 1 (δP / 4)) (min (1 / Kc) (cP * m₀ / (2 * (D + 1) * Kc))) with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hηδ : η ≤ δP / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hηK : η * Kc ≤ 1 := by
    have : η ≤ 1 / Kc := le_trans (min_le_right _ _) (min_le_left _ _)
    calc η * Kc ≤ 1 / Kc * Kc := mul_le_mul_of_nonneg_right this hKcpos.le
      _ = 1 := by field_simp
  have hηD : (D + 1) * (η * Kc) ≤ cP * m₀ / 2 := by
    have : η ≤ cP * m₀ / (2 * (D + 1) * Kc) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hD1 : 0 < D + 1 := by linarith
    calc (D + 1) * (η * Kc) ≤ (D + 1) * (cP * m₀ / (2 * (D + 1) * Kc) * Kc) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hKcpos.le) hD1.le
      _ = cP * m₀ / 2 := by field_simp
  set r₀ : ℝ := min (ρP / m₁) (δP / (4 * (m₁ + 1))) with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hr₀ρ : m₁ * r₀ ≤ ρP := by
    have : r₀ ≤ ρP / m₁ := min_le_left _ _
    calc m₁ * r₀ ≤ m₁ * (ρP / m₁) := mul_le_mul_of_nonneg_left this hm₁.le
      _ = ρP := by field_simp
  have hr₀δ : (m₁ + 1) * r₀ ≤ δP / 4 := by
    have : r₀ ≤ δP / (4 * (m₁ + 1)) := min_le_right _ _
    calc (m₁ + 1) * r₀ ≤ (m₁ + 1) * (δP / (4 * (m₁ + 1))) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = δP / 4 := by field_simp
  -- decay thresholds
  obtain ⟨sa, hsa⟩ := dgn_small ha hb (η / 4) (by positivity)
  obtain ⟨sw, hsw⟩ := dgn_small hw hb η hηpos
  obtain ⟨s1, hs1⟩ := dgn_small (hNM 1) hb η hηpos
  obtain ⟨sI, hsI⟩ := dgn_small (hNM Complex.I) hb η hηpos
  set s₀ : ℝ := max (max sa sw) (max s1 sI) with hs₀
  refine ⟨r₀, hr₀pos, 2 * (D + 1) / (cP * m₀), Real.exp (2 * π * s₀), fun ζ w hζ hwr => ?_⟩
  have hπ : 0 < 2 * π := by positivity
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le (Real.exp_pos _) hζ
  have hζ0 : ζ ≠ 0 := norm_pos_iff.1 hζpos
  set σ : ℝ := Real.log ‖ζ‖ / (2 * π) with hσ
  set τ : ℝ := Complex.arg ζ / (2 * π) with hτ
  have hcyl : cylInf σ τ = ζ := dgn_cylInf_log_arg hζ0
  have hσs : s₀ ≤ σ := by
    rw [hσ, le_div_iff₀ hπ]
    have := Real.log_le_log (Real.exp_pos _) hζ
    rw [Real.log_exp] at this
    linarith
  have Ea : |aCoord H (u ζ) - P.T * σ - d| ≤ η / 4 := by
    have := hsa σ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hσs) τ
    simpa [endA, hcyl, Real.norm_eq_abs] using this
  have Ew : ‖proj H (u ζ) - P.x (P.T * τ)‖ ≤ η := by
    have := hsw σ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hσs) τ
    simpa [endW, hcyl] using this
  set lam : ℝ := Real.exp (-(2 * (P.T * σ + d))) with hlam
  have E1 : ‖lam • N ζ 1 - M τ (cToVec 1)‖ ≤ η := by
    have := hs1 σ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hσs) τ
    simpa [hcyl] using this
  have EI : ‖lam • N ζ Complex.I - M τ (cToVec Complex.I)‖ ≤ η := by
    have := hsI σ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hσs) τ
    simpa [hcyl] using this
  -- the frame part
  set Q : V 1 := lam • N ζ w with hQ
  have hwdec : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  have hEQ : ‖Q - M τ (cToVec w)‖ ≤ 2 * η * ‖w‖ := by
    have hNw : N ζ w = w.re • N ζ 1 + w.im • N ζ Complex.I := by
      conv_lhs => rw [hwdec]
      rw [map_add, map_smul, map_smul]
    have hid : Q - M τ (cToVec w) = w.re • (lam • N ζ 1 - M τ (cToVec 1)) +
        w.im • (lam • N ζ Complex.I - M τ (cToVec Complex.I)) := by
      rw [hQ, hNw, dgn_cToVec_re_im w, map_add, map_smul, map_smul]
      module
    rw [hid]
    have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    calc ‖w.re • (lam • N ζ 1 - M τ (cToVec 1)) +
          w.im • (lam • N ζ Complex.I - M τ (cToVec Complex.I))‖
        ≤ |w.re| * η + |w.im| * η := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left E1 (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left EI (abs_nonneg _)
      _ ≤ ‖w‖ * η + ‖w‖ * η :=
          add_le_add (mul_le_mul_of_nonneg_right hre hηpos.le)
            (mul_le_mul_of_nonneg_right him hηpos.le)
      _ = 2 * η * ‖w‖ := by ring
  have hMτ : ‖M τ (cToVec w)‖ ≤ m₁ * ‖w‖ := by
    have := (hMb τ (cToVec w)).2
    rwa [dgn_norm_cToVec] at this
  have hQb : ‖Q‖ ≤ (m₁ + 2 * η) * ‖w‖ := by
    calc ‖Q‖ ≤ ‖Q - M τ (cToVec w)‖ + ‖M τ (cToVec w)‖ := norm_le_norm_sub_add _ _
      _ ≤ 2 * η * ‖w‖ + m₁ * ‖w‖ := add_le_add hEQ hMτ
      _ = (m₁ + 2 * η) * ‖w‖ := by ring
  set A : ℝ := aCoord H (u ζ) with hA
  set ut : V 1 := proj H (u ζ) with hut
  set μf : ℝ := Real.exp (-(2 * (A - P.T * σ - d))) with hμf
  have hμf1 : |μf - 1| ≤ η := by
    have hx : |-(2 * (A - P.T * σ - d))| ≤ 1 := by
      rw [abs_neg, abs_mul, abs_two]
      linarith
    have := Real.abs_exp_sub_one_le hx
    rw [abs_neg, abs_mul, abs_two] at this
    linarith
  set Mw : V 1 := Real.exp (-(2 * A)) • N ζ w with hMw
  have hMwQ : Mw = μf • Q := by
    rw [hMw, hQ, hμf, hlam, smul_smul, ← Real.exp_add]
    congr 2
    ring
  have hMwQb : ‖Mw - Q‖ ≤ η * (m₁ + 2 * η) * ‖w‖ := by
    rw [hMwQ, show μf • Q - Q = (μf - 1) • Q by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul hμf1 hQb (norm_nonneg _) hηpos.le
  -- nearest point of the orbit
  obtain ⟨y, hyK, hyd⟩ := hK.exists_infDist_eq_dist hKne ut
  obtain ⟨θ₀, rfl⟩ := hyK
  set k : ℤ := round ((θ₀ - P.T * τ) / P.T) with hk
  set θ : ℝ := θ₀ - k * P.T with hθ
  have hxθ : P.x θ = P.x θ₀ := hxper.sub_int_mul_eq k
  have hθT : |θ - P.T * τ| ≤ P.T / 2 := by
    have h1 := abs_sub_round ((θ₀ - P.T * τ) / P.T)
    have heq : θ - P.T * τ = P.T * ((θ₀ - P.T * τ) / P.T - round ((θ₀ - P.T * τ) / P.T)) := by
      rw [hθ, hk]; field_simp; ring
    rw [heq, abs_mul, abs_of_pos hT]
    calc P.T * |(θ₀ - P.T * τ) / P.T - round ((θ₀ - P.T * τ) / P.T)| ≤ P.T * (1 / 2) :=
          mul_le_mul_of_nonneg_left h1 hT.le
      _ = P.T / 2 := by ring
  have hdist : infDist ut K = ‖ut - P.x θ‖ := by rw [hyd, dist_eq_norm, hxθ]
  have hinf : infDist ut K ≤ η :=
    (infDist_le_dist_of_mem (Set.mem_range_self (P.T * τ))).trans (by rw [dist_eq_norm]; exact Ew)
  have hxx : ‖P.x θ - P.x (P.T * τ)‖ ≤ 2 * η := by
    calc ‖P.x θ - P.x (P.T * τ)‖ ≤ ‖P.x θ - ut‖ + ‖ut - P.x (P.T * τ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η + η := by
          refine add_le_add ?_ Ew
          rw [norm_sub_rev, ← hdist]; exact hinf
      _ = 2 * η := by ring
  have hθτ : |θ / P.T - τ| ≤ 2 * η / (cx * P.T) := by
    have h := hxsep θ (P.T * τ) hθT
    have h2 : cx * |θ - P.T * τ| ≤ 2 * η := h.trans hxx
    have heq : θ / P.T - τ = (θ - P.T * τ) / P.T := by field_simp
    rw [heq, abs_div, abs_of_pos hT, div_le_div_iff₀ hT (by positivity)]
    calc |θ - P.T * τ| * (cx * P.T) = (cx * |θ - P.T * τ|) * P.T := by ring
      _ ≤ 2 * η * P.T := mul_le_mul_of_nonneg_right h2 hT.le
  have hMθ : ‖M (θ / P.T) - M τ‖ ≤ LM * (2 * η / (cx * P.T)) :=
    (hMlip (θ / P.T) τ).trans (mul_le_mul_of_nonneg_left hθτ hLM)
  set h : V 1 := M (θ / P.T) (cToVec w) with hh
  have hxi : IsInXi H (P.x θ) h := by
    have := (hM.2.2 (θ / P.T)).1 (cToVec w)
    rwa [mul_div_cancel₀ _ hT.ne'] at this
  have hhup : ‖h‖ ≤ m₁ * ‖w‖ := by
    have := (hMb (θ / P.T) (cToVec w)).2
    rwa [dgn_norm_cToVec] at this
  have hhlo : m₀ * ‖w‖ ≤ ‖h‖ := by
    have := (hMb (θ / P.T) (cToVec w)).1
    rwa [dgn_norm_cToVec] at this
  have hhρ : ‖h‖ ≤ ρP := hhup.trans ((mul_le_mul_of_nonneg_left hwr hm₁.le).trans hr₀ρ)
  have hlow := hlowP θ h hxi hhρ
  -- `Mw` is close to `h`
  have hMwh : ‖Mw - h‖ ≤ η * Kc * ‖w‖ := by
    have h3 : ‖M τ (cToVec w) - h‖ ≤ LM * (2 * η / (cx * P.T)) * ‖w‖ := by
      rw [hh, ← ContinuousLinearMap.sub_apply]
      calc ‖(M τ - M (θ / P.T)) (cToVec w)‖ ≤ ‖M τ - M (θ / P.T)‖ * ‖cToVec w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ LM * (2 * η / (cx * P.T)) * ‖w‖ := by
            rw [dgn_norm_cToVec, norm_sub_rev]
            exact mul_le_mul_of_nonneg_right hMθ (norm_nonneg _)
    calc ‖Mw - h‖ ≤ ‖Mw - Q‖ + ‖Q - M τ (cToVec w)‖ + ‖M τ (cToVec w) - h‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub Mw Q h
          have h' := norm_sub_le_norm_sub_add_norm_sub Q (M τ (cToVec w)) h
          linarith
      _ ≤ η * (m₁ + 2 * η) * ‖w‖ + 2 * η * ‖w‖ + LM * (2 * η / (cx * P.T)) * ‖w‖ :=
          add_le_add (add_le_add hMwQb hEQ) h3
      _ ≤ η * Kc * ‖w‖ := by
          have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
          have e1 : η * (m₁ + 2 * η) ≤ η * (m₁ + 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hηpos.le
          have e2 : LM * (2 * η / (cx * P.T)) = η * (2 * LM / (cx * P.T)) := by ring
          have e3 : η * (m₁ + 2 * η) * ‖w‖ ≤ η * (m₁ + 2) * ‖w‖ :=
            mul_le_mul_of_nonneg_right e1 hw0
          have e4 : η * (2 * LM / (cx * P.T) + 2 + m₁ + 2) * ‖w‖ =
              η * (m₁ + 2) * ‖w‖ + 2 * η * ‖w‖ + η * (2 * LM / (cx * P.T)) * ‖w‖ := by ring
          rw [e2, hKc, e4]
          linarith
  -- the two points and the Lipschitz bound for `proj`
  set y₁ : V 1 := ut + Mw with hy₁
  set y₀ : V 1 := P.x θ + h with hy₀
  have hxθK : P.x θ ∈ K := Set.mem_range_self θ
  have hw1 : ‖w‖ ≤ r₀ := hwr
  have hy₀b : y₀ ∈ closedBall (P.x θ) δP := by
    rw [mem_closedBall, dist_eq_norm, hy₀, add_sub_cancel_left]
    have : (m₁ + 1) * ‖w‖ ≤ δP / 4 := (mul_le_mul_of_nonneg_left hw1 (by linarith)).trans hr₀δ
    have h' : m₁ * ‖w‖ ≤ (m₁ + 1) * ‖w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w)
    linarith
  have hy₁b : y₁ ∈ closedBall (P.x θ) δP := by
    rw [mem_closedBall, dist_eq_norm]
    have hb1 : ‖ut - P.x θ‖ ≤ η := by rw [← hdist]; exact hinf
    have hb2 : ‖Mw‖ ≤ (m₁ + 1) * ‖w‖ := by
      calc ‖Mw‖ ≤ ‖Mw - h‖ + ‖h‖ := norm_le_norm_sub_add _ _
        _ ≤ η * Kc * ‖w‖ + m₁ * ‖w‖ := add_le_add hMwh hhup
        _ ≤ 1 * ‖w‖ + m₁ * ‖w‖ :=
            add_le_add (mul_le_mul_of_nonneg_right hηK (norm_nonneg _)) le_rfl
        _ = (m₁ + 1) * ‖w‖ := by ring
    have hb3 : (m₁ + 1) * ‖w‖ ≤ δP / 4 := (mul_le_mul_of_nonneg_left hw1 (by linarith)).trans hr₀δ
    calc ‖y₁ - P.x θ‖ = ‖(ut - P.x θ) + Mw‖ := by rw [hy₁]; congr 1; abel
      _ ≤ ‖ut - P.x θ‖ + ‖Mw‖ := norm_add_le _ _
      _ ≤ δP := by linarith
  obtain ⟨hballO, hball⟩ := hDlip (P.x θ) hxθK
  have hlip : ‖proj H y₀ - proj H y₁‖ ≤ D * ‖y₀ - y₁‖ := ((hball y₀ hy₀b).2 y₁ hy₁b)
  have hy₁0 : y₁ ≠ 0 := hballO hy₁b
  -- `Φ(ζ, w) = e^{2A} y₁`
  have hu0' : u ζ ≠ 0 := hu0 ζ
  have heq : u ζ + N ζ w = Real.exp (2 * A) • y₁ := by
    rw [hy₁, smul_add, hMw, smul_smul, ← Real.exp_add, show 2 * A + -(2 * A) = 0 by ring,
      Real.exp_zero, one_smul, hut, hA, ← dgn_eq_exp_smul_proj H hH (u ζ) hu0']
  have hne : u ζ + N ζ w ≠ 0 := by
    rw [heq]; exact smul_ne_zero (Real.exp_pos _).ne' hy₁0
  have hproj : proj H (u ζ + N ζ w) = proj H y₁ := by
    rw [heq]; exact (proj_aCoord_exp_smul H hH A y₁ hy₁0).1
  refine ⟨hne, ?_⟩
  rw [hproj]
  have hy01 : ‖y₀ - y₁‖ ≤ infDist ut K + η * Kc * ‖w‖ := by
    calc ‖y₀ - y₁‖ = ‖(P.x θ - ut) + (h - Mw)‖ := by rw [hy₀, hy₁]; congr 1; abel
      _ ≤ ‖P.x θ - ut‖ + ‖h - Mw‖ := norm_add_le _ _
      _ = infDist ut K + ‖Mw - h‖ := by rw [hdist, norm_sub_rev, norm_sub_rev h]
      _ ≤ infDist ut K + η * Kc * ‖w‖ := add_le_add le_rfl hMwh
  have hchain : cP * (m₀ * ‖w‖) ≤ infDist (proj H y₁) K + D * (infDist ut K + η * Kc * ‖w‖) := by
    calc cP * (m₀ * ‖w‖) ≤ cP * ‖h‖ := mul_le_mul_of_nonneg_left hhlo hcP.le
      _ ≤ infDist (proj H y₀) K := hlow
      _ ≤ infDist (proj H y₁) K + dist (proj H y₀) (proj H y₁) := infDist_le_infDist_add_dist
      _ ≤ infDist (proj H y₁) K + D * (infDist ut K + η * Kc * ‖w‖) := by
          rw [dist_eq_norm]
          exact add_le_add le_rfl (hlip.trans (mul_le_mul_of_nonneg_left hy01 hD0))
  have hDK : D * (η * Kc) ≤ cP * m₀ / 2 :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hηD
  exact dgn_final_arith (mul_pos hcP hm₀) hD0 infDist_nonneg infDist_nonneg (norm_nonneg w) hDK
    hchain

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ r₀ > 0, ∃ C R : ℝ, ∀ ζ w : ℂ, R ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      u ζ + N ζ w ≠ 0 ∧
      ‖w‖ ≤ C * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)) :=
  exists_norm_le_infDist_tubeMap_aux H hH J hJ P hP u hu0 d b hb ha hw N M hM hNM
