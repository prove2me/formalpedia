-- Prove2me | solution 1 for CosmoConstCentury.einstein_static_universe_unstable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:40:02.071882+00:00
-- url     : https://prove2.me/submissions/23555a28-4629-49d0-aa8f-9f50df1025b2

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace S215CC

lemma core (Λ c R₀ e : ℝ) (hc : 0 < c) (hR₀ : 0 < R₀) (he : 0 < e) (hΛ : Λ * R₀ ^ 2 = c ^ 2) :
    ∃ (R : ℝ → ℝ) (T : ℝ), 0 < T ∧ R 0 = R₀ ∧ deriv R 0 = e ∧ R T = R₀ + 1 ∧
      ∀ t ∈ Set.Icc 0 T, 0 < R t ∧ ContDiffAt ℝ 2 R t ∧
        deriv R t ^ 2 / R t ^ 2 + 2 * deriv (deriv R) t / R t + 1 * c ^ 2 / R t ^ 2 - Λ = 0 := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * c ^ 2 * R₀ / 3 + R₀ * e ^ 2 := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => Λ * u ^ 2 / 3 - c ^ 2 + C / u := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, F' = fun u => 2 * Λ * u / 3 - C / u ^ 2 := ⟨_, rfl⟩
  have F_eq : ∀ u, 0 < u → F u = (Λ / 3 * (u - R₀) ^ 2 * (u + 2 * R₀) + R₀ * e ^ 2) / u := by
    intro u hu
    subst hF hC
    rw [← hΛ]
    field_simp
    ring
  have F_pos : ∀ u, 0 < u → 0 < F u := by
    have hΛpos : 0 < Λ := by
      have h1 : 0 < Λ * R₀ ^ 2 := by rw [hΛ]; positivity
      exact pos_of_mul_pos_left h1 (by positivity)
    intro u hu; rw [F_eq u hu]; positivity
  have F_deriv : ∀ u, 0 < u → HasDerivAt F (F' u) u := by
    intro u hu
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
    rw [hF, hF']
    refine ((((hp.const_mul Λ).div_const 3).sub_const (c ^ 2)).add
      ((hasDerivAt_const u C).div (hasDerivAt_id' u) hu.ne')).congr_deriv ?_
    field_simp
    ring
  have F_cd : ∀ u, 0 < u → ContDiffAt ℝ 1 F u := by
    intro u hu
    subst hF
    exact ((contDiffAt_const.mul (contDiffAt_id.pow 2)).div_const 3).sub contDiffAt_const |>.add
      (contDiffAt_const.div contDiffAt_id hu.ne')
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u => Real.sqrt (F u) := ⟨_, rfl⟩
  have g_pos : ∀ u, 0 < u → 0 < g u := fun u hu => by
    rw [hg]; exact Real.sqrt_pos.2 (F_pos u hu)
  have g_sq : ∀ u, 0 < u → g u ^ 2 = F u := fun u hu => by
    rw [hg]; exact Real.sq_sqrt (F_pos u hu).le
  have g_deriv : ∀ u, 0 < u → HasDerivAt g (F' u / (2 * g u)) u := by
    intro u hu
    have := (F_deriv u hu).sqrt (F_pos u hu).ne'
    subst hg; exact this
  have g_cd : ∀ u, 0 < u → ContDiffAt ℝ 1 g u := by
    intro u hu
    have := (F_cd u hu).sqrt (F_pos u hu).ne'
    subst hg; exact this
  have g_ca : ∀ u, 0 < u → ContinuousAt g u := fun u hu => (g_cd u hu).continuousAt
  set α := R₀ / 2 with hα
  have hαpos : 0 < α := by positivity
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun u => 1 / g (max u α) := ⟨_, rfl⟩
  have h_pos : ∀ u, 0 < h u := fun u => by
    rw [hh]; exact one_div_pos.2 (g_pos _ (lt_max_of_lt_right hαpos))
  have h_cont : Continuous h := by
    rw [hh]
    refine continuous_iff_continuousAt.2 fun u => ?_
    have hm : 0 < max u α := lt_max_of_lt_right hαpos
    refine continuousAt_const.div ?_ (g_pos _ hm).ne'
    exact ContinuousAt.comp (f := fun u => max u α) (g_ca _ hm)
      (continuous_id.max continuous_const).continuousAt
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun s => ∫ u in R₀..s, h u := ⟨_, rfl⟩
  have φ_deriv : ∀ s, HasDerivAt φ (h s) s := fun s => by
    rw [hφ]; exact (h_cont.integral_hasStrictDerivAt R₀ s).hasDerivAt
  have φ_mono : StrictMono φ := strictMono_of_deriv_pos fun x => by
    rw [(φ_deriv x).deriv]; exact h_pos x
  have φ_cont : Continuous φ := continuous_iff_continuousAt.2 fun x => (φ_deriv x).continuousAt
  have φ0 : φ R₀ = 0 := by rw [hφ]; simp
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = Function.invFun φ := ⟨_, rfl⟩
  have R_left : ∀ s, R (φ s) = s := fun s => by
    rw [hR]; exact Function.leftInverse_invFun φ_mono.injective s
  set a' := 3 * R₀ / 4 with ha'
  set b' := R₀ + 2 with hb'
  have hab : a' ≤ b' := by rw [ha', hb']; linarith
  set U := Set.Ioo (φ a') (φ b') with hU
  have R_mem : ∀ t ∈ U, R t ∈ Set.Ioo a' b' ∧ φ (R t) = t := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := intermediate_value_Icc hab φ_cont.continuousOn (Set.Ioo_subset_Icc_self ht)
    rw [R_left]
    exact ⟨⟨φ_mono.lt_iff_lt.1 ht.1, φ_mono.lt_iff_lt.1 ht.2⟩, rfl⟩
  have R_pos : ∀ t ∈ U, 0 < R t := fun t ht => by
    have := (R_mem t ht).1.1; rw [ha'] at this; linarith
  have R_gt : ∀ t ∈ U, α < R t := fun t ht => by
    have := (R_mem t ht).1.1; rw [ha'] at this; rw [hα]; linarith
  have R_cont : ∀ t ∈ U, ContinuousAt R t := by
    intro t ht
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := U) ?_ (isOpen_Ioo.mem_nhds ht) ?_
    · intro x hx y hy hxy
      rw [← φ_mono.le_iff_le, (R_mem x hx).2, (R_mem y hy).2]; exact hxy
    · exact mem_of_superset (isOpen_Ioo.mem_nhds (R_mem t ht).1)
        (fun s hs => ⟨φ s, ⟨φ_mono hs.1, φ_mono hs.2⟩, R_left s⟩)
  have R_deriv : ∀ t ∈ U, HasDerivAt R (g (R t)) t := by
    intro t ht
    have := HasDerivAt.of_local_left_inverse (R_cont t ht) (φ_deriv (R t)) (h_pos _).ne'
      (by filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy using (R_mem y hy).2)
    refine this.congr_deriv ?_
    rw [hh]; simp only
    rw [max_eq_left (R_gt t ht).le, one_div, inv_inv]
  have deriv_eq : ∀ t ∈ U, deriv R t = g (R t) := fun t ht => (R_deriv t ht).deriv
  have R_C1 : ContDiffOn ℝ 1 R U := by
    show ContDiffOn ℝ (0 + 1) R U
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
      ⟨fun t ht => (R_deriv t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine contDiffOn_zero.2 fun t ht => ?_
    have e1 : (fun y => g (R y)) =ᶠ[𝓝 t] deriv R := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy using (deriv_eq y hy).symm
    exact (ContinuousAt.congr (ContinuousAt.comp (f := R) (g_ca _ (R_pos t ht)) (R_cont t ht))
      e1).continuousWithinAt
  have R_C2 : ContDiffOn ℝ 2 R U := by
    show ContDiffOn ℝ (1 + 1) R U
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
      ⟨fun t ht => (R_deriv t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr (f := fun y => g (R y)) ?_ deriv_eq
    intro t ht
    exact ((g_cd (R t) (R_pos t ht)).comp t
      (R_C1.contDiffAt (isOpen_Ioo.mem_nhds ht))).contDiffWithinAt
  have second : ∀ t ∈ U, deriv (deriv R) t = F' (R t) / 2 := by
    intro t ht
    have e1 : deriv R =ᶠ[𝓝 t] g ∘ R := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy using deriv_eq y hy
    have e2 := (g_deriv (R t) (R_pos t ht)).comp t (R_deriv t ht)
    rw [e1.deriv_eq, e2.deriv]
    have := (g_pos _ (R_pos t ht)).ne'
    field_simp
  refine ⟨R, φ (R₀ + 1), ?_, ?_, ?_, R_left _, ?_⟩
  · rw [← φ0]; exact φ_mono (by linarith)
  · rw [← φ0, R_left]
  · have h0U : (0 : ℝ) ∈ U := by
      rw [← φ0]; exact ⟨φ_mono (by rw [ha']; linarith), φ_mono (by rw [hb']; linarith)⟩
    rw [deriv_eq 0 h0U, ← φ0, R_left, hg]
    simp only
    rw [F_eq R₀ hR₀]
    have : (Λ / 3 * (R₀ - R₀) ^ 2 * (R₀ + 2 * R₀) + R₀ * e ^ 2) / R₀ = e ^ 2 := by
      field_simp; ring
    rw [this, Real.sqrt_sq he.le]
  · intro t ht
    have htU : t ∈ U := by
      refine ⟨lt_of_lt_of_le ?_ ht.1, lt_of_le_of_lt ht.2 (φ_mono (by rw [hb']; linarith))⟩
      rw [← φ0]; exact φ_mono (by rw [ha']; linarith)
    refine ⟨R_pos t htU, R_C2.contDiffAt (isOpen_Ioo.mem_nhds htU), ?_⟩
    rw [deriv_eq t htU, second t htU, g_sq _ (R_pos t htU)]
    have hr := (R_pos t htU).ne'
    subst hF hF'
    simp only
    field_simp
    ring

end S215CC

open CosmoConstCentury in
theorem solution (G c Λ R₀ ρ₀ : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hR₀ : 0 < R₀)
    (hstatic : IsFriedmannSolution G c Λ 1 Set.univ (fun _ => R₀) (fun _ => ρ₀)) :
    ∃ δ > 0, ∀ ε > 0, ∃ (R ρ : ℝ → ℝ) (T : ℝ), 0 < T ∧
      IsFriedmannSolution G c Λ 1 (Set.Icc 0 T) R ρ ∧
      |R 0 - R₀| < ε ∧ |deriv R 0| < ε ∧ |ρ 0 - ρ₀| < ε ∧ δ ≤ |R T - R₀| := by
  obtain ⟨-, -, eq1, eq2⟩ := hstatic 0 (Set.mem_univ 0)
  simp only [deriv_const', deriv_const] at eq1 eq2
  have hR2 : R₀ ^ 2 ≠ 0 := by positivity
  have hΛ : Λ * R₀ ^ 2 = c ^ 2 := by
    field_simp at eq2; linarith
  have hK : 0 < einsteinKappa G c * c ^ 2 := by unfold einsteinKappa; positivity
  set K := einsteinKappa G c * c ^ 2 with hKdef
  refine ⟨1, one_pos, fun ε hε => ?_⟩
  set e := min (1 / 2) (min (ε / 2) (ε * R₀ ^ 2 * K / 6)) with he
  have he0 : 0 < e := by
    rw [he]; refine lt_min (by norm_num) (lt_min (by linarith) (by positivity))
  have he1 : e ≤ 1 / 2 := min_le_left _ _
  have he2 : e ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have he3 : e ≤ ε * R₀ ^ 2 * K / 6 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨R, T, hT, hR0, hdR0, hRT, hsol⟩ := S215CC.core Λ c R₀ e hc hR₀ he0 hΛ
  refine ⟨R, fun t => (3 * deriv R t ^ 2 / R t ^ 2 + 3 * 1 * c ^ 2 / R t ^ 2 - Λ) / K, T, hT,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := hsol t ht
    refine ⟨h1, h2, ?_, h3⟩
    rw [← hKdef]; field_simp
  · rw [hR0]; simpa using hε
  · rw [hdR0, abs_of_pos he0]; linarith
  · simp only
    rw [hR0, hdR0]
    have hρ : ρ₀ = (3 * 1 * c ^ 2 / R₀ ^ 2 - Λ) / K := by
      rw [eq_div_iff hK.ne']; norm_num at eq1 ⊢; linarith
    have : (3 * e ^ 2 / R₀ ^ 2 + 3 * 1 * c ^ 2 / R₀ ^ 2 - Λ) / K - ρ₀
        = 3 * e ^ 2 / (R₀ ^ 2 * K) := by
      rw [hρ]; field_simp; ring
    rw [this, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
    have hee : e * e ≤ 1 / 2 * e := mul_le_mul_of_nonneg_right he1 he0.le
    nlinarith
  · rw [hRT]; norm_num
