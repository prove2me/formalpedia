-- Prove2me | solution 1 for EthierKurtz.gaussian_density_perturbation_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:06:13.887634+00:00
-- url     : https://prove2.me/submissions/bbed8faa-9309-4aba-929e-083fa9fa20b0

import Mathlib.Tactic
import Mathlib

open MeasureTheory

lemma norm_aux_exp_neg_le (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [le_div_iff₀ hy]
  have h1 := Real.add_one_le_exp y
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-y)
  nlinarith

lemma norm_aux_s_le : (√((2 : ℝ) * Real.pi))⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])

lemma norm_aux_key (c0 ε0 ε x : ℝ) (hc0 : 0 ≤ c0) (hε : 0 < ε) (hcε : c0 * ε ≤ 1)
    (hc : c0 * ε0 ≤ 1 / 16) (hx : |x| ≤ ε0 / ε) :
    (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) *
      (Real.exp (c0 * ε * (1 + |x| ^ 3)) - 1) ≤ ε * (600 * c0) * Real.exp (-(1/4) * x ^ 2) := by
  rw [← sq_abs x]
  set t := |x| with ht_def
  have ht : 0 ≤ t := abs_nonneg x
  have htε : ε * t ≤ ε0 := by rw [le_div_iff₀ hε] at hx; linarith
  set u := c0 * ε * (1 + t ^ 3) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hct : c0 * (ε * t) * t ^ 2 ≤ c0 * ε0 * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left htε hc0
    exact mul_le_mul_of_nonneg_right this (sq_nonneg t)
  have hu1 : u ≤ 1 + t ^ 2 / 16 := by
    have : u = c0 * ε + c0 * (ε * t) * t ^ 2 := by rw [hu_def]; ring
    have h2 : c0 * ε0 * t ^ 2 ≤ 1 / 16 * t ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg t)
    linarith
  have hexpu : Real.exp u - 1 ≤ u * Real.exp u := by
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos u
    nlinarith
  have hexpu0 : 0 ≤ Real.exp u - 1 := by
    have := Real.add_one_le_exp u; linarith
  have hE : Real.exp u ≤ 3 * Real.exp (t ^ 2 / 16) := by
    calc Real.exp u ≤ Real.exp (1 + t ^ 2 / 16) := Real.exp_le_exp.mpr hu1
      _ = Real.exp 1 * Real.exp (t ^ 2 / 16) := Real.exp_add _ _
      _ ≤ 3 * Real.exp (t ^ 2 / 16) := by
        gcongr; have := Real.exp_one_lt_d9; linarith
  have hpoly : 1 + t ^ 3 ≤ 200 * Real.exp (3 * t ^ 2 / 16) := by
    set y := 3 * t ^ 2 / 16 with hy
    have hy0 : 0 ≤ y := by positivity
    have e1 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 1 + y / 2 ≤ Real.exp (y / 2) := by
      have := Real.add_one_le_exp (y / 2); linarith
    have e3 : (1 + y / 2) * (1 + y / 2) ≤ Real.exp y := by
      rw [e1]; exact mul_le_mul e2 e2 (by positivity) (Real.exp_pos _).le
    have e4 : t ^ 3 ≤ 1 + t ^ 4 := by
      nlinarith [sq_nonneg (t ^ 2 - t), sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 1)]
    have e5 : (1 + y / 2) * (1 + y / 2) = 1 + y + 9 / 1024 * t ^ 4 := by rw [hy]; ring
    nlinarith
  have hsplit : Real.exp (-(t ^ 2 / 2)) = Real.exp (-(1/4) * t ^ 2) * Real.exp (-(t ^ 2 / 16))
      * Real.exp (-(3 * t ^ 2 / 16)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have haa : Real.exp (-(t ^ 2 / 16)) * Real.exp (t ^ 2 / 16) = 1 := by
    rw [← Real.exp_add]; simp
  have hbb : Real.exp (-(3 * t ^ 2 / 16)) * Real.exp (3 * t ^ 2 / 16) = 1 := by
    rw [← Real.exp_add]; simp
  have hs := norm_aux_s_le
  have hs0 : 0 ≤ (√((2 : ℝ) * Real.pi))⁻¹ := by positivity
  calc (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(t ^ 2 / 2)) * (Real.exp u - 1)
      ≤ 1 * Real.exp (-(t ^ 2 / 2)) * (u * Real.exp u) := by gcongr
    _ ≤ 1 * Real.exp (-(t ^ 2 / 2)) * (u * (3 * Real.exp (t ^ 2 / 16))) := by gcongr
    _ = 3 * c0 * ε * Real.exp (-(1/4) * t ^ 2) * (Real.exp (-(t ^ 2 / 16)) * Real.exp (t ^ 2 / 16))
          * (Real.exp (-(3 * t ^ 2 / 16)) * (1 + t ^ 3)) := by rw [hsplit, hu_def]; ring
    _ ≤ 3 * c0 * ε * Real.exp (-(1/4) * t ^ 2) * 1
          * (Real.exp (-(3 * t ^ 2 / 16)) * (200 * Real.exp (3 * t ^ 2 / 16))) := by
        rw [haa]; gcongr
    _ = ε * (600 * c0) * Real.exp (-(1/4) * t ^ 2) := by
        rw [show Real.exp (-(3 * t ^ 2 / 16)) * (200 * Real.exp (3 * t ^ 2 / 16))
          = 200 * (Real.exp (-(3 * t ^ 2 / 16)) * Real.exp (3 * t ^ 2 / 16)) by ring, hbb]; ring

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (C3 : ℝ) (ε1 : ℝ),
                  (0 : ℝ) < C3 ∧
                    (0 : ℝ) < ε1 ∧
                      ε1 ≤ (1 : ℝ) ∧
                        ε1 * c0 ≤ (1 : ℝ) ∧
                          ∀ (h : ℝ → ℝ) (K0 ε : ℝ),
                            (0 : ℝ) < ε ∧
                                (0 : ℝ) < K0 ∧
                                  (∀ (x : ℝ), (0 : ℝ) ≤ h x) ∧
                                    MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume ∧
                                      ∫ (x : ℝ), h x = (1 : ℝ) ∧
                                        (∀ (x : ℝ),
                                            |x| ≤ ε0 / ε →
                                              h x ≤
                                                K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                  Real.exp (c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ∧
                                          (∀ (x : ℝ),
                                              |x| ≤ ε0 / ε →
                                                K0 * ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))) *
                                                    Real.exp (-(c0 * ε * ((1 : ℝ) + |x| ^ (3 : ℕ)))) ≤
                                                  h x) ∧
                                            ∫ (x : ℝ) in (Set.Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤
                                              A * Real.exp (-(b / ε ^ (2 : ℕ))) →
                              ε ≤ ε1 →
                                |K0 - (1 : ℝ)| ≤ C3 * ε ∧
                                  K0 ≤ (2 : ℝ) ∧
                                    ∫ (x : ℝ), |h x - (√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-(x ^ (2 : ℕ) / (2 : ℝ)))| ≤
                                      C3 * ε := by
  intro c0 ε0 A b hc0 hε0 hc hA hb
  set B : ℝ := 2400 * c0 + 16 / ε0 ^ 2 with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hAb : 0 ≤ A / b := by positivity
  refine ⟨2 * (A / b) + 5 * B + 1, 1 / (2 * B + c0 + 1), by positivity, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
  rintro h K0 ε ⟨hε, hK0, hh0, hhi, hh1, hU, hL, hT⟩ hεε1
  have hεB' : ε * (2 * B + c0 + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hεε1; linarith
  have hε1 : ε ≤ 1 := by nlinarith
  have hcε : c0 * ε ≤ 1 := by nlinarith
  have hεB : ε * B ≤ 1 / 2 := by nlinarith
  set s := (√((2 : ℝ) * Real.pi))⁻¹ with hs_def
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := norm_aux_s_le
  set φ : ℝ → ℝ := fun x => s * Real.exp (-(x ^ 2 / 2)) with hφ_def
  set g : ℝ → ℝ := fun x => Real.exp (-(1/4) * x ^ 2) with hg_def
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => by positivity
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hφ_eq : φ = fun x => s * Real.exp (-(1/2) * x ^ 2) := by
    funext x; simp only [hφ_def]; ring_nf
  have hφi : Integrable φ := by
    rw [hφ_eq]; exact (integrable_exp_neg_mul_sq (by norm_num)).const_mul s
  have hgi : Integrable g := integrable_exp_neg_mul_sq (by norm_num)
  have hφ1 : ∫ x, φ x = 1 := by
    rw [hφ_eq, integral_const_mul, integral_gaussian]
    rw [show Real.pi / (1/2) = 2 * Real.pi by ring, hs_def]
    exact inv_mul_cancel₀ (by positivity)
  have hg4 : ∫ x, g x ≤ 4 := by
    simp only [hg_def]
    rw [integral_gaussian, Real.sqrt_le_left (by norm_num)]
    have := Real.pi_le_four
    linarith [show Real.pi / (1/4) = 4 * Real.pi by ring]
  set R := ε0 / ε with hR_def
  have hR : 0 < R := by positivity
  set I := Set.Icc (-R) R with hI_def
  have hI : MeasurableSet I := measurableSet_Icc
  -- tail of φ
  set Q := ∫ x in Iᶜ, φ x with hQ_def
  have hQ0 : 0 ≤ Q := setIntegral_nonneg hI.compl (fun x _ => hφ0 x)
  have hexpR : Real.exp (-(R ^ 2 / 4)) ≤ 4 * ε ^ 2 / ε0 ^ 2 := by
    have := norm_aux_exp_neg_le (R ^ 2 / 4) (by positivity)
    convert this using 1
    rw [hR_def]; field_simp
  have hQ : Q ≤ 16 / ε0 ^ 2 * ε := by
    have h1 : Q ≤ ∫ x in Iᶜ, Real.exp (-(R ^ 2 / 4)) * g x := by
      apply setIntegral_mono_on hφi.integrableOn (hgi.const_mul _).integrableOn hI.compl
      intro x hx
      simp only [hI_def, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      have hx2 : R ^ 2 ≤ x ^ 2 := by rcases hx with hx | hx <;> nlinarith
      simp only [hφ_def, hg_def]
      calc s * Real.exp (-(x ^ 2 / 2)) ≤ 1 * Real.exp (-(x ^ 2 / 2)) := by gcongr
        _ ≤ Real.exp (-(R ^ 2 / 4) + -(1/4) * x ^ 2) := by
          rw [one_mul]; exact Real.exp_le_exp.mpr (by nlinarith)
        _ = _ := Real.exp_add _ _
    have h2 : ∫ x in Iᶜ, Real.exp (-(R ^ 2 / 4)) * g x ≤ ∫ x, Real.exp (-(R ^ 2 / 4)) * g x :=
      setIntegral_le_integral (hgi.const_mul _) (Filter.Eventually.of_forall fun x => by positivity)
    have h2' : ∫ x, Real.exp (-(R ^ 2 / 4)) * g x = Real.exp (-(R ^ 2 / 4)) * ∫ x, g x :=
      integral_const_mul _ _
    have h3 : Real.exp (-(R ^ 2 / 4)) * ∫ x, g x ≤ 4 * ε ^ 2 / ε0 ^ 2 * 4 :=
      mul_le_mul hexpR hg4 (integral_nonneg hg0) (by positivity)
    have h4 : 4 * ε ^ 2 / ε0 ^ 2 * 4 ≤ 16 / ε0 ^ 2 * ε := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    linarith
  have hPQ : (∫ x in I, φ x) + Q = 1 := by rw [hQ_def, integral_add_compl hI hφi, hφ1]
  set P := ∫ x in I, φ x with hP_def
  -- tail of h
  set T := ∫ x in Iᶜ, h x with hT_def
  have hT0 : 0 ≤ T := setIntegral_nonneg hI.compl (fun x _ => hh0 x)
  have hT' : T ≤ A / b * ε := by
    have h1 := norm_aux_exp_neg_le (b / ε ^ 2) (by positivity)
    have h2 : 1 / (b / ε ^ 2) ≤ ε / b := by
      rw [one_div_div, div_le_div_iff_of_pos_right hb]; nlinarith
    have h3 : A * Real.exp (-(b / ε ^ 2)) ≤ A * (ε / b) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hA
    have : A * (ε / b) = A / b * ε := by ring
    linarith
  have hHT : (∫ x in I, h x) + T = 1 := by rw [hT_def, integral_add_compl hI hhi, hh1]
  set H := ∫ x in I, h x with hH_def
  -- main local estimate
  have hpt : ∀ x ∈ I, |h x - K0 * φ x| ≤ K0 * (ε * (600 * c0) * g x) := by
    intro x hx
    have hxR : |x| ≤ ε0 / ε := abs_le.mpr ⟨hx.1, hx.2⟩
    have hk := norm_aux_key c0 ε0 ε x hc0 hε hcε hc hxR
    have hu := hU x hxR
    have hl := hL x hxR
    set u := c0 * ε * (1 + |x| ^ 3)
    have hu0 : 0 ≤ u := by positivity
    have hφx := hφ0 x
    have hm1 : 1 - Real.exp (-u) ≤ Real.exp u - 1 := by
      have := Real.add_one_le_exp (-u); have := Real.add_one_le_exp u; linarith
    have hKφ : 0 ≤ K0 * φ x := by positivity
    have hm : K0 * φ x * (1 - Real.exp (-u)) ≤ K0 * φ x * (Real.exp u - 1) :=
      mul_le_mul_of_nonneg_left hm1 hKφ
    have hk' : K0 * (φ x * (Real.exp u - 1)) ≤ K0 * (ε * (600 * c0) * g x) :=
      mul_le_mul_of_nonneg_left hk hK0.le
    change h x ≤ K0 * φ x * Real.exp u at hu
    change K0 * φ x * Real.exp (-u) ≤ h x at hl
    rw [abs_le]; constructor
    · have : K0 * φ x * (1 - Real.exp (-u)) = K0 * φ x - K0 * φ x * Real.exp (-u) := by ring
      have : K0 * (φ x * (Real.exp u - 1)) = K0 * φ x * (Real.exp u - 1) := by ring
      linarith
    · have : K0 * (φ x * (Real.exp u - 1)) = K0 * φ x * Real.exp u - K0 * φ x := by ring
      linarith
  have hdi : Integrable (fun x => |h x - K0 * φ x|) := (hhi.sub (hφi.const_mul K0)).abs
  have hwi : Integrable (fun x => K0 * (ε * (600 * c0) * g x)) :=
    (hgi.const_mul _).const_mul K0
  have hD : ∫ x in I, |h x - K0 * φ x| ≤ K0 * (ε * (2400 * c0)) := by
    have h1 := setIntegral_mono_on hdi.integrableOn hwi.integrableOn hI hpt
    have h2 : ∫ x in I, K0 * (ε * (600 * c0) * g x) ≤ ∫ x, K0 * (ε * (600 * c0) * g x) :=
      setIntegral_le_integral hwi (Filter.Eventually.of_forall fun x => by
        have := hg0 x; positivity)
    have h2' : ∫ x, K0 * (ε * (600 * c0) * g x) = K0 * (ε * (600 * c0) * ∫ x, g x) := by
      rw [integral_const_mul, integral_const_mul]
    have h3 : K0 * (ε * (600 * c0) * ∫ x, g x) ≤ K0 * (ε * (600 * c0) * 4) := by
      gcongr
    have : K0 * (ε * (600 * c0) * 4) = K0 * (ε * (2400 * c0)) := by ring
    linarith
  have hHP : |H - K0 * P| ≤ K0 * (ε * (2400 * c0)) := by
    have e : H - K0 * P = ∫ x in I, (h x - K0 * φ x) := by
      rw [integral_sub hhi.integrableOn (hφi.const_mul K0).integrableOn, integral_const_mul]
    rw [e]
    refine le_trans ?_ hD
    have := norm_integral_le_integral_norm (μ := volume.restrict I) (fun x => h x - K0 * φ x)
    simpa [Real.norm_eq_abs] using this
  have hP1 : P ≤ 1 := by linarith
  have hP0 : 0 ≤ P := setIntegral_nonneg hI (fun x _ => hφ0 x)
  rw [abs_le] at hHP
  have hK1 : K0 * (1 - ε * B) ≤ 1 := by
    have e1 : K0 * P - K0 * (ε * (2400 * c0)) ≤ 1 := by linarith [hHP.1]
    have e2 : K0 * (1 - 16 / ε0 ^ 2 * ε) ≤ K0 * P :=
      mul_le_mul_of_nonneg_left (by linarith) hK0.le
    have e3 : K0 * (1 - ε * B) = K0 * (1 - 16 / ε0 ^ 2 * ε) - K0 * (ε * (2400 * c0)) := by
      rw [hB_def]; ring
    linarith
  have hK2 : K0 ≤ 2 := by
    have e4 : K0 * (1 / 2) ≤ K0 * (1 - ε * B) := mul_le_mul_of_nonneg_left (by linarith) hK0.le
    linarith
  have hD' : K0 * (ε * (2400 * c0)) ≤ 2 * (ε * B) := by
    have h1 : ε * (2400 * c0) ≤ ε * B := by
      apply mul_le_mul_of_nonneg_left _ hε.le; have : 0 ≤ 16 / ε0 ^ 2 := by positivity
      linarith
    have h3 : K0 * (ε * (2400 * c0)) ≤ 2 * (ε * (2400 * c0)) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    linarith
  have hK3 : |K0 - 1| ≤ ε * (A / b + 2 * B) := by
    have hAbε : 0 ≤ A / b * ε := by positivity
    rw [abs_le]; constructor
    · have : K0 * P ≤ K0 * 1 := mul_le_mul_of_nonneg_left hP1 hK0.le
      linarith [hHP.2]
    · have e1 : K0 * (ε * B) ≤ 2 * (ε * B) :=
        mul_le_mul_of_nonneg_right hK2 (by positivity)
      linarith
  refine ⟨?_, hK2, ?_⟩
  · calc |K0 - 1| ≤ ε * (A / b + 2 * B) := hK3
      _ ≤ (2 * (A / b) + 5 * B + 1) * ε := by
        have h0 : 0 ≤ ε * (A / b + 3 * B + 1) :=
          mul_nonneg hε.le (by linarith)
        have e : (2 * (A / b) + 5 * B + 1) * ε = ε * (A / b + 2 * B) + ε * (A / b + 3 * B + 1) := by
          ring
        rw [e]; exact le_add_of_nonneg_right h0
  -- L1 bound
  have hai : Integrable (fun x => |h x - φ x|) volume := (hhi.sub hφi).abs
  have hsplit := integral_add_compl hI hai
  have hin : ∫ x in I, |h x - φ x| ≤ (∫ x in I, |h x - K0 * φ x|) + |K0 - 1| * P := by
    have hi2 : Integrable (fun x => |h x - K0 * φ x| + |K0 - 1| * φ x) volume :=
      hdi.add (hφi.const_mul _)
    have := integral_mono (μ := volume.restrict I) hai.integrableOn hi2.integrableOn (fun x => by
      show |h x - φ x| ≤ |h x - K0 * φ x| + |K0 - 1| * φ x
      have e : h x - φ x = (h x - K0 * φ x) + (K0 - 1) * φ x := by ring
      rw [e]
      calc |(h x - K0 * φ x) + (K0 - 1) * φ x| ≤ |h x - K0 * φ x| + |(K0 - 1) * φ x| :=
            abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg (hφ0 x)])
    rw [integral_add hdi.integrableOn (hφi.const_mul _).integrableOn, integral_const_mul] at this
    exact this
  have hout : ∫ x in Iᶜ, |h x - φ x| ≤ T + Q := by
    have := integral_mono (μ := volume.restrict Iᶜ) (g := fun x => h x + φ x) hai.integrableOn (hhi.add hφi).integrableOn (fun x => by
      show |h x - φ x| ≤ h x + φ x
      rw [abs_le]; constructor <;> linarith [hh0 x, hφ0 x])
    rw [integral_add hhi.integrableOn hφi.integrableOn] at this
    exact this
  have hKP : |K0 - 1| * P ≤ ε * (A / b + 2 * B) := by
    calc |K0 - 1| * P ≤ |K0 - 1| * 1 := mul_le_mul_of_nonneg_left hP1 (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hK3
  have hQB : 16 / ε0 ^ 2 * ε ≤ B * ε := by
    apply mul_le_mul_of_nonneg_right _ hε.le; have : 0 ≤ c0 := hc0; linarith
  show ∫ x, |h x - φ x| ≤ _
  rw [← hsplit]
  have hD := hD
  linarith only [hin, hout, hD, hD', hKP, hQB, hQ, hT', hε]
