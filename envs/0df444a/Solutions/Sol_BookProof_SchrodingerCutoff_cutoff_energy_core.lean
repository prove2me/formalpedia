-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.cutoff_energy_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:26.796068+00:00
-- url     : https://prove2.me/submissions/7bb48328-e85d-4a00-ba14-5f513319d191

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.cutoff_energy_core
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_integral_deriv_eq_zero_of_hasCompactSupport
import Theorems.Thm_BookProof_SchrodingerCutoff_exists_scaled_cutoff
import Theorems.Thm_BookProof_SchrodingerCutoff_hasDerivAt_reInner
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution
    (V : ℝ → ℝ) (hV : Continuous V) (z : ℂ)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (V x : ℂ) * u x = z * u x)
    (hVz : ∀ x, 0 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2)
    {C : ℝ} (hC : ∀ y, |deriv chi y| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    (∫ x in Set.Icc (-R) R, (V x - z.re) * ‖u x‖ ^ 2)
        ≤ 2 * C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) ∧
      (∫ x in Set.Icc (-R) R, ‖u' x‖ ^ 2) ≤ 4 * C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) := by

  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have heq' : ∀ x, u'' x = ((V x : ℂ) - z) * u x := by
    intro x; linear_combination -heq x
  have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
  have hu'd : Differentiable ℝ u' := fun x => (h2 x).differentiableAt
  have hucont : Continuous u := hud.continuous
  have hu'cont : Continuous u' := hu'd.continuous
  obtain ⟨w, wd, hwderiv, hwcont, hwdcont, hwzero, hwdzero, hwone, hwdbound⟩ :=
    exists_scaled_cutoff hC hR
  -- pieces of the energy identity
  set Rf : ℝ → ℝ := fun y => ((starRingEnd ℂ) (u y) * u' y).re with hRfdef
  set P : ℝ → ℝ := fun x => (V x - z.re) * ‖u x‖ ^ 2 with hPdef
  have hP : ∀ x, ((starRingEnd ℂ) (u x) * u'' x).re = P x := by
    intro x
    have hcm : (starRingEnd ℂ) (u x) * u x = (Complex.normSq (u x) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    have hstep : (starRingEnd ℂ) (u x) * u'' x =
        ((V x : ℂ) - z) * (Complex.normSq (u x) : ℂ) := by
      rw [heq' x, ← hcm]; ring
    rw [hstep, hPdef]
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.sq_norm]
  have hRfcont : Continuous Rf := Complex.continuous_re.comp (hucont.star.mul hu'cont)
  have hPcont : Continuous P := by fun_prop
  set g : ℝ → ℝ := fun x => w x ^ 2 * Rf x with hgdef
  set G : ℝ → ℝ := fun x => 2 * w x * wd x * Rf x + w x ^ 2 * (‖u' x‖ ^ 2 + P x) with hGdef
  have hg : ∀ x, HasDerivAt g (G x) x := by
    intro x
    have hR' := hasDerivAt_reInner u u' u'' x (h1 x) (h2 x)
    rw [hP x] at hR'
    have hw2 : HasDerivAt (fun y => w y ^ 2) (2 * w x * wd x) x := by
      convert (hwderiv x).pow 2 <;> first | rfl | norm_num | (funext y; rfl)
    exact hw2.mul hR'
  have hGcont : Continuous G := by fun_prop
  -- compact support of everything built from the cutoff
  have suppOf : ∀ f : ℝ → ℝ, (∀ x : ℝ, 2 * R < |x| → f x = 0) → HasCompactSupport f := by
    intro f hf
    apply HasCompactSupport.intro (isCompact_Icc (a := -(2 * R)) (b := 2 * R))
    intro x hx
    refine hf x ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hgsupp : HasCompactSupport g := suppOf g fun x hx => by simp [hgdef, hwzero x hx]
  have hGzero : ∫ x, G x = 0 := integral_deriv_eq_zero_of_hasCompactSupport hg hGcont hgsupp
  -- the three terms of the energy identity
  set T1 : ℝ → ℝ := fun x => 2 * w x * wd x * Rf x with hT1def
  set T2 : ℝ → ℝ := fun x => w x ^ 2 * ‖u' x‖ ^ 2 with hT2def
  set T3 : ℝ → ℝ := fun x => w x ^ 2 * P x with hT3def
  have hGsum : ∀ x, G x = T1 x + T2 x + T3 x := by
    intro x; simp only [hGdef, hT1def, hT2def, hT3def]; ring
  have hT1cont : Continuous T1 := by fun_prop
  have hT2cont : Continuous T2 := by fun_prop
  have hT3cont : Continuous T3 := by fun_prop
  have hI1 : Integrable T1 :=
    hT1cont.integrable_of_hasCompactSupport (suppOf T1 fun x hx => by simp [hT1def, hwzero x hx])
  have hI2 : Integrable T2 :=
    hT2cont.integrable_of_hasCompactSupport (suppOf T2 fun x hx => by simp [hT2def, hwzero x hx])
  have hI3 : Integrable T3 :=
    hT3cont.integrable_of_hasCompactSupport (suppOf T3 fun x hx => by simp [hT3def, hwzero x hx])
  have hsplit : (∫ x, T1 x) + (∫ x, T2 x) + (∫ x, T3 x) = 0 := by
    have hI12 : Integrable fun x => T1 x + T2 x := hI1.add hI2
    have e1 : (∫ x, G x) = (∫ x, T1 x + T2 x) + ∫ x, T3 x := by
      rw [← integral_add hI12 hI3]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hGsum x)
    have e2 : (∫ x, T1 x + T2 x) = (∫ x, T1 x) + ∫ x, T2 x := integral_add hI1 hI2
    rw [e2] at e1
    rw [← e1, hGzero]
  -- Young's inequality on the cross term
  set Q : ℝ → ℝ := fun x => wd x ^ 2 * ‖u x‖ ^ 2 with hQdef
  have hQcont : Continuous Q := by fun_prop
  have hIQ : Integrable Q :=
    hQcont.integrable_of_hasCompactSupport (suppOf Q fun x hx => by simp [hQdef, hwdzero x hx])
  set B : ℝ → ℝ := fun x => 2 * Q x + 1 / 2 * T2 x with hBdef
  have hIB : Integrable B := (hIQ.const_mul 2).add (hI2.const_mul (1 / 2))
  have hyoung : ∀ x, -T1 x ≤ B x := by
    intro x
    have habs : |Rf x| ≤ ‖u x‖ * ‖u' x‖ := by
      calc |Rf x| ≤ ‖(starRingEnd ℂ) (u x) * u' x‖ := Complex.abs_re_le_norm _
        _ = ‖u x‖ * ‖u' x‖ := by rw [norm_mul, RCLike.norm_conj]
    have hb : |T1 x| ≤ 2 * (|wd x| * ‖u x‖) * (|w x| * ‖u' x‖) := by
      have hnn : (0 : ℝ) ≤ 2 * |w x| * |wd x| := by positivity
      calc |T1 x| = 2 * |w x| * |wd x| * |Rf x| := by
            simp only [hT1def, abs_mul, abs_two]
        _ ≤ 2 * |w x| * |wd x| * (‖u x‖ * ‖u' x‖) := by nlinarith [habs]
        _ = 2 * (|wd x| * ‖u x‖) * (|w x| * ‖u' x‖) := by ring
    have hsq : 2 * (|wd x| * ‖u x‖) * (|w x| * ‖u' x‖) ≤
        2 * (|wd x| * ‖u x‖) ^ 2 + 1 / 2 * (|w x| * ‖u' x‖) ^ 2 := by
      nlinarith [sq_nonneg (2 * (|wd x| * ‖u x‖) - (|w x| * ‖u' x‖))]
    have hrw : B x = 2 * (|wd x| * ‖u x‖) ^ 2 + 1 / 2 * (|w x| * ‖u' x‖) ^ 2 := by
      simp only [hBdef, hQdef, hT2def, mul_pow, sq_abs]
    have := le_trans (neg_le_abs (T1 x)) (le_trans hb hsq)
    linarith [hrw]
  have hT1bound : -(∫ x, T1 x) ≤ ∫ x, B x := by
    rw [← integral_neg]
    exact integral_mono hI1.neg hIB hyoung
  have hIBval : (∫ x, B x) = 2 * (∫ x, Q x) + 1 / 2 * (∫ x, T2 x) := by
    rw [hBdef, integral_add (hIQ.const_mul 2) (hI2.const_mul (1 / 2)), integral_const_mul,
      integral_const_mul]
  have hT2nonneg : 0 ≤ ∫ x, T2 x := integral_nonneg fun x => by rw [hT2def]; positivity
  have hT3nonneg : ∀ x, 0 ≤ T3 x := by
    intro x
    have hVpos : 0 ≤ V x - z.re := hVz x
    rw [hT3def, hPdef]; positivity
  have hT3int : 0 ≤ ∫ x, T3 x := integral_nonneg hT3nonneg
  rw [hIBval] at hT1bound
  have hT3le : (∫ x, T3 x) ≤ 2 * (∫ x, Q x) := by
    linarith [hsplit, hT1bound, hT2nonneg]
  have hT2le : (∫ x, T2 x) ≤ 4 * (∫ x, Q x) := by
    linarith [hsplit, hT1bound, hT3int]
  -- bound the gradient term
  have hQle : (∫ x, Q x) ≤ C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) := by
    have hptwise : ∀ x, Q x ≤ C ^ 2 / R ^ 2 * ‖u x‖ ^ 2 := by
      intro x
      have hwd2 : wd x ^ 2 ≤ C ^ 2 / R ^ 2 := by
        have h0 := hwdbound x
        have hCR : (0 : ℝ) ≤ C / R := by positivity
        have : wd x ^ 2 = |wd x| ^ 2 := (sq_abs _).symm
        rw [this]
        calc |wd x| ^ 2 ≤ (C / R) ^ 2 := by nlinarith [abs_nonneg (wd x)]
          _ = C ^ 2 / R ^ 2 := by rw [div_pow]
      rw [hQdef]
      nlinarith [sq_nonneg ‖u x‖, norm_nonneg (u x)]
    calc (∫ x, Q x) ≤ ∫ x, C ^ 2 / R ^ 2 * ‖u x‖ ^ 2 :=
          integral_mono hIQ (hL2.const_mul _) hptwise
      _ = C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) := integral_const_mul _ _
  -- the two left-hand sides
  have hwone' : ∀ x ∈ Set.Icc (-R) R, w x = 1 := by
    intro x hx
    refine hwone x ?_
    rcases hx with ⟨hx1, hx2⟩
    rw [abs_le]; constructor <;> linarith
  have hlhs1 : (∫ x in Set.Icc (-R) R, (V x - z.re) * ‖u x‖ ^ 2) ≤ ∫ x, T3 x := by
    have hIon : IntegrableOn (fun x => (V x - z.re) * ‖u x‖ ^ 2) (Set.Icc (-R) R) :=
      (by fun_prop : Continuous fun x => (V x - z.re) * ‖u x‖ ^ 2).integrableOn_Icc
    have hstep : (∫ x in Set.Icc (-R) R, (V x - z.re) * ‖u x‖ ^ 2)
        ≤ ∫ x in Set.Icc (-R) R, T3 x := by
      refine setIntegral_mono_on hIon hI3.integrableOn measurableSet_Icc fun x hx => le_of_eq ?_
      simp only [hT3def, hPdef, hwone' x hx, one_pow, one_mul]
    exact le_trans hstep
      (setIntegral_le_integral hI3 (Filter.Eventually.of_forall hT3nonneg))
  have hlhs2 : (∫ x in Set.Icc (-R) R, ‖u' x‖ ^ 2) ≤ ∫ x, T2 x := by
    have hIon : IntegrableOn (fun x => ‖u' x‖ ^ 2) (Set.Icc (-R) R) :=
      (by fun_prop : Continuous fun x => ‖u' x‖ ^ 2).integrableOn_Icc
    have hstep : (∫ x in Set.Icc (-R) R, ‖u' x‖ ^ 2) ≤ ∫ x in Set.Icc (-R) R, T2 x := by
      refine setIntegral_mono_on hIon hI2.integrableOn measurableSet_Icc fun x hx => le_of_eq ?_
      simp only [hT2def, hwone' x hx, one_pow, one_mul]
    refine le_trans hstep (setIntegral_le_integral hI2 (Filter.Eventually.of_forall ?_))
    intro x
    rw [hT2def]
    positivity
  have hfinal2 : (2 : ℝ) * (C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2)) =
      2 * C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) := by ring
  have hfinal4 : (4 : ℝ) * (C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2)) =
      4 * C ^ 2 / R ^ 2 * (∫ x, ‖u x‖ ^ 2) := by ring
  exact ⟨by linarith [hlhs1, hT3le, hQle, hfinal2],
    by linarith [hlhs2, hT2le, hQle, hfinal4]⟩
