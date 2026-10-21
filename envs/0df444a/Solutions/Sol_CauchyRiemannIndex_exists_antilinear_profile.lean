-- Prove2me | solution 1 for CauchyRiemannIndex.exists_antilinear_profile
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T14:04:19.51899+00:00
-- url     : https://prove2.me/submissions/dc05e093-f0de-46f3-a7d8-a091c8998e46

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log



/-!
# Elementary cutoffs and periodic coordinates on the cylinder
-/

namespace CauchyRiemannIndex

noncomputable section

open Real

/-- Smooth cutoff, `1` on `(-∞, 1]` and `0` on `[4, ∞)`. -/
def crpPsi (y : ℝ) : ℝ := Real.smoothTransition ((4 - y) / 3)

lemma crpPsi_contDiff {n : ℕ∞} : ContDiff ℝ n crpPsi :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

lemma crpPsi_one {y : ℝ} (h : y ≤ 1) : crpPsi y = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

lemma crpPsi_zero {y : ℝ} (h : 4 ≤ y) : crpPsi y = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

lemma crpPsi_nonneg (y : ℝ) : 0 ≤ crpPsi y := Real.smoothTransition.nonneg _

lemma crpPsi_le_one (y : ℝ) : crpPsi y ≤ 1 := Real.smoothTransition.le_one _

/-- A smooth periodic substitute for `y²`. -/
def crpQ (y : ℝ) : ℝ := sin (π * y) ^ 2 / π ^ 2

lemma crpQ_nonneg (y : ℝ) : 0 ≤ crpQ y := by unfold crpQ; positivity

lemma crpQ_contDiff {n : ℕ∞} : ContDiff ℝ n crpQ := by
  unfold crpQ
  exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2).div_const _

lemma crpQ_add_int (y : ℝ) (n : ℤ) : crpQ (y + n) = crpQ y := by
  unfold crpQ
  rw [show π * (y + n) = π * y + n * π by ring, sin_add_int_mul_pi, mul_pow]
  rcases Int.even_or_odd n with h | h <;> simp [h.neg_one_zpow]

lemma crpQ_le_sq (y : ℝ) : crpQ y ≤ y ^ 2 := by
  unfold crpQ
  have hπ : 0 < π ^ 2 := by positivity
  rw [div_le_iff₀ hπ]
  have := Real.sin_sq_le_sq (x := π * y)
  nlinarith

lemma crp_two_abs_le_abs_sin {y : ℝ} (h : |y| ≤ 1 / 2) : 2 * |y| ≤ |sin (π * y)| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy] at h ⊢
    have := Real.mul_le_sin (x := π * y) (by positivity) (by nlinarith [pi_pos])
    rw [show 2 / π * (π * y) = 2 * y by field_simp] at this
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos hy] at h ⊢
    have := Real.mul_le_sin (x := π * -y) (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
    rw [show 2 / π * (π * -y) = 2 * -y by field_simp, show π * -y = -(π * y) by ring,
      Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

lemma crpQ_lower {y : ℝ} (h : |y| ≤ 1 / 2) : 4 * y ^ 2 / π ^ 2 ≤ crpQ y := by
  unfold crpQ
  have h1 := crp_two_abs_le_abs_sin h
  have h2 : (2 * |y|) ^ 2 ≤ |sin (π * y)| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow, sq_abs, sq_abs] at h2
  gcongr
  linarith

/-- The periodic coordinate `t - t₀` normalised to `(-1/2, 1/2]`. -/
def crpD (t₀ t : ℝ) : ℝ :=
  Complex.arg (Complex.exp (((2 * π * (t - t₀) : ℝ) : ℂ) * Complex.I)) / (2 * π)

lemma crpD_eq (t₀ t : ℝ) :
    crpD t₀ t = toIocMod Real.two_pi_pos (-π) (2 * π * (t - t₀)) / (2 * π) := by
  rw [crpD, Complex.arg_exp_mul_I]

lemma crpD_mem (t₀ t : ℝ) : -(1 / 2) < crpD t₀ t ∧ crpD t₀ t ≤ 1 / 2 := by
  rw [crpD_eq]
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) (2 * π * (t - t₀))
  have hπ := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith [h.1]
  · rw [div_le_iff₀ (by positivity)]; linarith [h.2]

lemma crpD_abs_le (t₀ t : ℝ) : |crpD t₀ t| ≤ 1 / 2 := by
  have := crpD_mem t₀ t
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

lemma crpD_sub_int (t₀ t : ℝ) : ∃ n : ℤ, t - t₀ = crpD t₀ t + n := by
  refine ⟨toIocDiv Real.two_pi_pos (-π) (2 * π * (t - t₀)), ?_⟩
  have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-π) (2 * π * (t - t₀))
  rw [zsmul_eq_mul] at h
  rw [crpD_eq]
  have hπ := Real.pi_pos
  have : toIocMod Real.two_pi_pos (-π) (2 * π * (t - t₀)) / (2 * π) = (t - t₀) - (toIocDiv Real.two_pi_pos (-π) (2 * π * (t - t₀)) : ℝ) := by
    rw [div_eq_iff (by positivity)]
    linarith
  rw [this]; ring

lemma crpD_self {t₀ t : ℝ} (h : |t - t₀| < 1 / 2) : crpD t₀ t = t - t₀ := by
  rw [crpD_eq]
  have hπ := Real.pi_pos
  rw [(toIocMod_eq_self Real.two_pi_pos).2]
  · field_simp
  · rw [abs_lt] at h
    constructor <;> nlinarith [h.1, h.2]

lemma crpD_add_one (t₀ t : ℝ) : crpD t₀ (t + 1) = crpD t₀ t := by
  rw [crpD_eq, crpD_eq, show 2 * π * (t + 1 - t₀) = 2 * π * (t - t₀) + 2 * π by ring,
    toIocMod_add_right]

lemma crpD_contDiffAt {n : ℕ∞} {t₀ t : ℝ} (h : sin (π * (t - t₀)) ^ 2 ≤ 1 / 2) :
    ContDiffAt ℝ n (crpD t₀) t := by
  set z : ℝ → ℂ := fun t => Complex.exp (((2 * π * (t - t₀) : ℝ) : ℂ) * Complex.I) with hz
  have hzc : ContDiff ℝ n z := by
    rw [hz]
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
        contDiff_const)
  have hmem : z t ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_contra hne
    push_neg at hne
    simp only [hz, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hne
    have hs := hne.2
    have hc : cos (2 * π * (t - t₀)) = -1 := by
      have := Real.sin_sq_add_cos_sq (2 * π * (t - t₀))
      rw [hs] at this
      have h2 : (cos (2 * π * (t - t₀)) + 1) * (cos (2 * π * (t - t₀)) - 1) = 0 := by
        linear_combination this
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · linarith [hne.1]
    have := Real.sin_sq_eq_half_sub (π * (t - t₀))
    rw [show 2 * (π * (t - t₀)) = 2 * π * (t - t₀) by ring, hc] at this
    linarith
  have hlog : ContDiffAt ℝ n (fun t => (Complex.log (z t)).im / (2 * π)) t := by
    have h1 : ContDiffAt ℝ n (fun t => Complex.log (z t)) t :=
      ((Complex.contDiffAt_log hmem).restrict_scalars ℝ).comp t hzc.contDiffAt
    exact (Complex.imCLM.contDiff.contDiffAt.comp t h1).div_const _
  refine hlog.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [crpD, hz, Complex.log_im]

lemma crp_abs_sin_add_le (a b : ℝ) : |sin (a + b)| ≤ |sin a| + |sin b| := by
  rw [Real.sin_add]
  calc |sin a * cos b + cos a * sin b| ≤ |sin a * cos b| + |cos a * sin b| := abs_add_le _ _
    _ ≤ |sin a| + |sin b| := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      · exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

lemma crp_sin_sep (N : ℕ) (j : ℤ) (h0 : j ≠ 0) (hN : |j| < N) :
    2 / N ≤ |sin (π * j / N)| := by
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := lt_of_le_of_lt (abs_nonneg j) hN
    exact_mod_cast this
  -- reduce to `j > 0`
  wlog hj : 0 < j generalizing j
  · have := this (-j) (neg_ne_zero.2 h0) (by rwa [abs_neg]) (by omega)
    rwa [Int.cast_neg, show π * -(j : ℝ) / N = -(π * j / N) by ring, Real.sin_neg,
      abs_neg] at this
  have hjN : j < N := by rw [abs_of_pos hj] at hN; exact hN
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjN' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
  have hπ := Real.pi_pos
  rcases le_total (π * j / N) (π / 2) with hle | hle
  · have := Real.mul_le_sin (x := π * j / N) (by positivity) hle
    rw [show 2 / π * (π * j / N) = 2 * j / N by field_simp] at this
    refine le_trans ?_ (this.trans (le_abs_self _))
    gcongr; linarith
  · rw [← Real.sin_pi_sub]
    have hx : π - π * j / N = π * (N - j) / N := by field_simp
    rw [hx]
    have h1 : 0 ≤ π * (N - j) / N := by
      apply div_nonneg _ hNpos.le; nlinarith
    have h2 : π * (N - j) / N ≤ π / 2 := by rw [← hx]; linarith
    have := Real.mul_le_sin h1 h2
    rw [show 2 / π * (π * (N - j) / N) = 2 * (N - j) / N by field_simp] at this
    refine le_trans ?_ (this.trans (le_abs_self _))
    gcongr; linarith

end

end CauchyRiemannIndex

/-!
# Putting the zeros of a periodic function in normal form
-/

namespace CauchyRiemannIndex

noncomputable section

open Real Filter Topology
open scoped ContDiff

/-- `z` or `z̄`. -/
def crpLz (cj : Bool) (z : ℂ) : ℂ := if cj then (starRingEnd ℂ) z else z

lemma crpLz_norm (cj : Bool) (z : ℂ) : ‖crpLz cj z‖ = ‖z‖ := by
  cases cj <;> simp [crpLz]

/-- The real-linear map `(x, y) ↦ x + iy` or `(x, y) ↦ x - iy`. -/
def crpLmap (cj : Bool) : ℝ × ℝ →L[ℝ] ℂ :=
  if cj then (Complex.conjCLE.toContinuousLinearMap).comp
    Complex.equivRealProdCLM.symm.toContinuousLinearMap
  else Complex.equivRealProdCLM.symm.toContinuousLinearMap

lemma crpLmap_apply (cj : Bool) (v : ℝ × ℝ) : crpLmap cj v = crpLz cj ⟨v.1, v.2⟩ := by
  cases cj <;> apply Complex.ext <;>
    simp [crpLmap, crpLz, Complex.equivRealProdCLM_symm_apply]

/-- Zero locations `t_m = (m + 1/2)/N`. -/
def crpT (N : ℕ) (m : Fin N) : ℝ := ((m : ℝ) + 1 / 2) / N

def crpRho (t₀ : ℝ) (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + crpQ (x.2 - t₀)

def crpChi (r t₀ : ℝ) (x : ℝ × ℝ) : ℝ := crpPsi (crpRho t₀ x / r ^ 2)

def crpW (cj : Bool) (t₀ : ℝ) (x : ℝ × ℝ) : ℂ := crpLmap cj (x.1, crpD t₀ x.2)

lemma crpRho_add_one (t₀ s t : ℝ) : crpRho t₀ (s, t + 1) = crpRho t₀ (s, t) := by
  simp only [crpRho]
  rw [show t + 1 - t₀ = (t - t₀) + ((1 : ℤ) : ℝ) by push_cast; ring, crpQ_add_int]

lemma crpRho_contDiff {n : ℕ∞} (t₀ : ℝ) : ContDiff ℝ n (crpRho t₀) := by
  unfold crpRho
  exact (contDiff_fst.pow 2).add (crpQ_contDiff.comp (contDiff_snd.sub contDiff_const))

lemma crpChi_contDiff {n : ℕ∞} (r t₀ : ℝ) : ContDiff ℝ n (crpChi r t₀) := by
  unfold crpChi
  exact crpPsi_contDiff.comp ((crpRho_contDiff t₀).div_const _)

lemma crpChi_one {r t₀ : ℝ} (hr : 0 < r) {x : ℝ × ℝ} (h : crpRho t₀ x ≤ r ^ 2) :
    crpChi r t₀ x = 1 :=
  crpPsi_one (by rw [div_le_iff₀ (by positivity)]; linarith)

lemma crpChi_zero {r t₀ : ℝ} (hr : 0 < r) {x : ℝ × ℝ} (h : 4 * r ^ 2 ≤ crpRho t₀ x) :
    crpChi r t₀ x = 0 :=
  crpPsi_zero (by rw [le_div_iff₀ (by positivity)]; linarith)

lemma crpChi_add_one (r t₀ s t : ℝ) : crpChi r t₀ (s, t + 1) = crpChi r t₀ (s, t) := by
  simp only [crpChi, crpRho_add_one]

lemma crpW_add_one (cj : Bool) (t₀ s t : ℝ) : crpW cj t₀ (s, t + 1) = crpW cj t₀ (s, t) := by
  simp only [crpW, crpD_add_one]

lemma crpRho_ge_fst (t₀ : ℝ) (x : ℝ × ℝ) : x.1 ^ 2 ≤ crpRho t₀ x := by
  unfold crpRho; linarith [crpQ_nonneg (x.2 - t₀)]

lemma crp_chiW_contDiff (cj : Bool) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 20) (t₀ : ℝ) :
    ContDiff ℝ ∞ (fun x => (crpChi r t₀ x : ℂ) * crpW cj t₀ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h : 1 / 2 < sin (π * (x.2 - t₀)) ^ 2
  · have hU : IsOpen {y : ℝ × ℝ | 1 / 2 < sin (π * (y.2 - t₀)) ^ 2} :=
      isOpen_lt continuous_const (by fun_prop)
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds h] with y hy
    have hπ := Real.pi_pos
    have hπ2 := Real.pi_lt_d2
    have hq : 1 / (2 * π ^ 2) < crpQ (y.2 - t₀) := by
      unfold crpQ
      calc 1 / (2 * π ^ 2) = (1 / 2) / π ^ 2 := by ring
        _ < _ := div_lt_div_of_pos_right hy (by positivity)
    have h4 : 4 * r ^ 2 ≤ crpRho t₀ y := by
      have : 4 * r ^ 2 ≤ 1 / (2 * π ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have hr2 : r ^ 2 ≤ 1 / 400 := by nlinarith
        have hp2 : π ^ 2 ≤ 10 := by nlinarith
        nlinarith [mul_le_mul hr2 hp2 (by positivity) (by norm_num)]
      unfold crpRho
      nlinarith [sq_nonneg y.1]
    simp [crpChi_zero hr h4]
  · push_neg at h
    have hd : ContDiffAt ℝ ∞ (crpD t₀) x.2 := crpD_contDiffAt h
    have hw : ContDiffAt ℝ ∞ (crpW cj t₀) x :=
      (crpLmap cj).contDiff.contDiffAt.comp x
        (contDiffAt_fst.prodMk (hd.comp x contDiffAt_snd))
    exact ((Complex.ofRealCLM.contDiff.comp (crpChi_contDiff r t₀)).contDiffAt).mul hw

lemma crp_sep (N : ℕ) (m m' : Fin N) (hmm : m ≠ m') {r : ℝ} (hr : 0 < r)
    (hrN : r ≤ 1 / (16 * N)) (x : ℝ × ℝ) (h : crpRho (crpT N m) x < 4 * r ^ 2) :
    64 * r ^ 2 ≤ crpRho (crpT N m') x := by
  have hNpos : (0 : ℝ) < N := by
    have := m.pos; exact_mod_cast this
  have hπ := Real.pi_pos
  have hπ2 := Real.pi_lt_d2
  set A := |sin (π * (x.2 - crpT N m))|
  set B := |sin (π * (x.2 - crpT N m'))|
  have hA : A < 2 * π * r := by
    have h1 : crpQ (x.2 - crpT N m) < 4 * r ^ 2 := by
      have := crpRho_ge_fst (crpT N m) x; unfold crpRho at h; nlinarith [sq_nonneg x.1]
    unfold crpQ at h1
    rw [div_lt_iff₀ (by positivity)] at h1
    have h2 : A ^ 2 < (2 * π * r) ^ 2 := by rw [sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hj : (2 : ℝ) / N ≤ |sin (π * ((m : ℤ) - (m' : ℤ) : ℤ) / N)| := by
    apply crp_sin_sep N _ (by
      intro h0; apply hmm; ext; omega)
    rw [abs_lt]; constructor <;> push_cast <;> omega
  have hsplit : π * (((m : ℤ) - (m' : ℤ) : ℤ) : ℝ) / N =
      π * (x.2 - crpT N m') + -(π * (x.2 - crpT N m)) := by
    simp only [crpT]; push_cast; field_simp; ring
  rw [hsplit] at hj
  have h3 := crp_abs_sin_add_le (π * (x.2 - crpT N m')) (-(π * (x.2 - crpT N m)))
  rw [Real.sin_neg, abs_neg] at h3
  have hB : 8 * π * r ≤ B := by
    have : 10 * π * r ≤ 2 / N := by
      rw [le_div_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_left hrN (by positivity : (0:ℝ) ≤ 10 * π * N)
      have e : 10 * π * N * (1 / (16 * N)) = 10 * π / 16 := by field_simp
      rw [e] at this
      nlinarith
    linarith
  have hq : 64 * r ^ 2 ≤ crpQ (x.2 - crpT N m') := by
    unfold crpQ
    rw [le_div_iff₀ (by positivity)]
    have : (8 * π * r) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    rw [sq_abs] at this
    nlinarith
  unfold crpRho
  nlinarith [sq_nonneg x.1]

/-- `|w|² ≤ (π²/4) ρ`. -/
lemma crpW_sq_le (cj : Bool) (t₀ : ℝ) (x : ℝ × ℝ) :
    ‖crpW cj t₀ x‖ ^ 2 ≤ π ^ 2 / 4 * crpRho t₀ x := by
  rw [crpW, crpLmap_apply, crpLz_norm, Complex.sq_norm, Complex.normSq_mk]
  obtain ⟨n, hn⟩ := crpD_sub_int t₀ x.2
  have hq : crpQ (x.2 - t₀) = crpQ (crpD t₀ x.2) := by rw [hn, crpQ_add_int]
  have hl := crpQ_lower (crpD_abs_le t₀ x.2)
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  unfold crpRho
  rw [hq]
  have : 4 * crpD t₀ x.2 ^ 2 ≤ π ^ 2 * crpQ (crpD t₀ x.2) := by
    have := (div_le_iff₀ (by positivity)).1 hl
    linarith [mul_comm (crpQ (crpD t₀ x.2)) (π ^ 2)]
  have hπsq : 4 ≤ π ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hπsq (sq_nonneg x.1)]

lemma crp_norm_le_crpW (cj : Bool) (t₀ : ℝ) (x : ℝ × ℝ) :
    ‖((x.1, crpD t₀ x.2) : ℝ × ℝ)‖ ≤ ‖crpW cj t₀ x‖ := by
  rw [crpW, crpLmap_apply, crpLz_norm]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · have := Complex.abs_re_le_norm (⟨x.1, crpD t₀ x.2⟩ : ℂ)
    simpa using this
  · have := Complex.abs_im_le_norm (⟨x.1, crpD t₀ x.2⟩ : ℂ)
    simpa using this

theorem crp_glue (N : ℕ) (hN : 0 < N) (cj : Bool) (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (hzero : ∀ m : Fin N, f (0, crpT N m) = 0)
    (c : Fin N → ℂ) (hc : ∀ m, c m ≠ 0)
    (hD : ∀ m, HasFDerivAt f (c m • crpLmap cj) (0, crpT N m)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 20 ∧ ∃ β : ℝ × ℝ → ℂ, ContDiff ℝ ∞ β ∧
      (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∀ x : ℝ × ℝ, 1 / 2 ≤ |x.1| → β x = f x) ∧ (∀ x, β x = 0 ↔ f x = 0) ∧
      ∀ m : Fin N, ∀ z : ℂ, ‖z‖ < r → β (0 + z.re, crpT N m + z.im) = crpLz cj z := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hπ2 := Real.pi_lt_d2
  have hperZ : ∀ s t (n : ℤ), f (s, t + n) = f (s, t) := by
    intro s t n
    have hp : Function.Periodic (fun t => f (s, t)) 1 := fun t => hper s t
    simpa using (hp.int_mul n) t
  -- uniform first-order expansion at the zeros
  have hev : ∀ᶠ v in 𝓝 (0 : ℝ × ℝ), ∀ m : Fin N,
      ‖f ((0, crpT N m) + v) - f (0, crpT N m) - (c m • crpLmap cj) v‖ ≤ ‖c m‖ / 2 * ‖v‖ := by
    rw [Filter.eventually_all]
    intro m
    have := (hasFDerivAt_iff_isLittleO_nhds_zero.1 (hD m)).def
      (by have := norm_pos_iff.2 (hc m); positivity : 0 < ‖c m‖ / 2)
    exact this
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.1 hev
  set r : ℝ := min (δ / 4) (1 / (20 * N)) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r ≤ δ / 4 := min_le_left _ _
  have hrN : r ≤ 1 / (20 * N) := min_le_right _ _
  have hr20 : r ≤ 1 / 20 := by
    refine hrN.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hrN16 : r ≤ 1 / (16 * N) := by
    refine hrN.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  set χ : Fin N → ℝ × ℝ → ℝ := fun m => crpChi r (crpT N m) with hχ
  set X : Fin N → ℝ × ℝ → ℝ := fun m => crpChi (4 * r) (crpT N m) with hX
  set u : ℝ × ℝ → ℂ := fun x =>
    Complex.exp (-∑ m, (X m x : ℂ) * Complex.log (c m)) with hu
  set β : ℝ × ℝ → ℂ := fun x =>
    ∑ m, (χ m x : ℂ) * crpW cj (crpT N m) x + (1 - ∑ m, (χ m x : ℂ)) * (u x * f x) with hβ
  have hX0 : ∀ m x, 64 * r ^ 2 ≤ crpRho (crpT N m) x → X m x = 0 := by
    intro m x h
    exact crpChi_zero (by positivity) (by nlinarith)
  -- far from the zeros nothing changes
  have hfar : ∀ x : ℝ × ℝ, (∀ m, 4 * r ^ 2 ≤ crpRho (crpT N m) x) → β x = u x * f x := by
    intro x h
    simp [hβ, hχ, crpChi_zero hr (h _)]
  -- local formula near the zero `m`
  have hloc : ∀ (m : Fin N) (x : ℝ × ℝ), crpRho (crpT N m) x < 4 * r ^ 2 →
      β x = crpW cj (crpT N m) x + (1 - (χ m x : ℂ)) *
        (f x / c m - crpW cj (crpT N m) x) ∧
      ‖f x / c m - crpW cj (crpT N m) x‖ ≤ ‖crpW cj (crpT N m) x‖ / 2 := by
    intro m x hx
    have hoth : ∀ m', m' ≠ m → χ m' x = 0 ∧ X m' x = 0 := by
      intro m' hm'
      have := crp_sep N m m' (Ne.symm hm') hr hrN16 x hx
      exact ⟨crpChi_zero hr (by nlinarith), hX0 m' x this⟩
    have hXm : X m x = 1 := crpChi_one (by positivity) (by nlinarith)
    have hsumχ : ∑ m', (χ m' x : ℂ) = χ m x :=
      Finset.sum_eq_single m (fun m' _ hm' => by simp [(hoth m' hm').1]) (by simp)
    have hsumW : ∑ m', (χ m' x : ℂ) * crpW cj (crpT N m') x = χ m x * crpW cj (crpT N m) x :=
      Finset.sum_eq_single m (fun m' _ hm' => by simp [(hoth m' hm').1]) (by simp)
    have hsumX : ∑ m', (X m' x : ℂ) * Complex.log (c m') = Complex.log (c m) :=
      (Finset.sum_eq_single m (fun m' _ hm' => by simp [(hoth m' hm').2]) (by simp)).trans
        (by simp [hXm])
    have hux : u x = (c m)⁻¹ := by
      simp only [hu, hsumX, Complex.exp_neg, Complex.exp_log (hc m)]
    -- first-order estimate
    set w := crpW cj (crpT N m) x with hw
    set v : ℝ × ℝ := (x.1, crpD (crpT N m) x.2) with hv
    have hwv : crpLmap cj v = w := rfl
    have hnorm_w : ‖w‖ < δ := by
      have h1 := crpW_sq_le cj (crpT N m) x
      have h2 : ‖w‖ ^ 2 < (π * r) ^ 2 := by
        calc ‖w‖ ^ 2 ≤ π ^ 2 / 4 * crpRho (crpT N m) x := h1
          _ < π ^ 2 / 4 * (4 * r ^ 2) := by gcongr
          _ = (π * r) ^ 2 := by ring
      have h3 : ‖w‖ < π * r := lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
      nlinarith
    have hvw : ‖v‖ ≤ ‖w‖ := crp_norm_le_crpW cj (crpT N m) x
    have hfx : f x = f ((0, crpT N m) + v) := by
      obtain ⟨n, hn⟩ := crpD_sub_int (crpT N m) x.2
      have : x = (x.1, (crpT N m + crpD (crpT N m) x.2) + n) := by
        ext
        · rfl
        · simp only; linarith
      rw [this, hperZ]
      simp [hv]
    have hest := hδv (show dist v 0 < δ by rw [dist_zero_right]; linarith) m
    rw [hzero m, sub_zero, ← hfx, ContinuousLinearMap.smul_apply, smul_eq_mul, hwv] at hest
    have hcpos : 0 < ‖c m‖ := norm_pos_iff.2 (hc m)
    have he : ‖f x / c m - w‖ ≤ ‖w‖ / 2 := by
      have : f x / c m - w = (f x - c m * w) / c m := by field_simp [hc m]
      rw [this, norm_div, div_le_iff₀ hcpos]
      calc ‖f x - c m * w‖ ≤ ‖c m‖ / 2 * ‖v‖ := hest
        _ ≤ ‖c m‖ / 2 * ‖w‖ := by gcongr
        _ = ‖w‖ / 2 * ‖c m‖ := by ring
    refine ⟨?_, he⟩
    simp only [hβ, hsumχ, hsumW, hux]
    field_simp [hc m]
    ring
  refine ⟨r, hr, hr20, β, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContDiff ℝ ∞ (fun x => ∑ m, (χ m x : ℂ) * crpW cj (crpT N m) x) :=
      ContDiff.sum fun m _ => crp_chiW_contDiff cj hr hr20 (crpT N m)
    have hχc : ∀ m, ContDiff ℝ ∞ (fun x => (χ m x : ℂ)) := fun m =>
      Complex.ofRealCLM.contDiff.comp (crpChi_contDiff r (crpT N m))
    have hXc : ∀ m, ContDiff ℝ ∞ (fun x => (X m x : ℂ)) := fun m =>
      Complex.ofRealCLM.contDiff.comp (crpChi_contDiff (4 * r) (crpT N m))
    have h2 : ContDiff ℝ ∞ (fun x => ∑ m, (χ m x : ℂ)) := ContDiff.sum fun m _ => hχc m
    have h3 : ContDiff ℝ ∞ u :=
      Complex.contDiff_exp.comp (ContDiff.neg (ContDiff.sum fun m _ => (hXc m).mul contDiff_const))
    exact h1.add ((contDiff_const.sub h2).mul (h3.mul hf))
  · intro s t
    simp only [hβ, hu, hχ, hX, crpChi_add_one, crpW_add_one, hper]
  · intro x hx
    have h : ∀ m, 4 * r ^ 2 ≤ crpRho (crpT N m) x ∧ 64 * r ^ 2 ≤ crpRho (crpT N m) x := by
      intro m
      have h1 := crpRho_ge_fst (crpT N m) x
      have h2 : (1 / 2 : ℝ) ^ 2 ≤ x.1 ^ 2 := by
        rw [← sq_abs x.1]; exact pow_le_pow_left₀ (by norm_num) hx 2
      constructor <;> nlinarith
    rw [hfar x fun m => (h m).1]
    simp [hu, hX0 _ x (h _).2]
  · intro x
    by_cases hA : ∃ m, crpRho (crpT N m) x < 4 * r ^ 2
    · obtain ⟨m, hm⟩ := hA
      obtain ⟨hβx, he⟩ := hloc m x hm
      set w := crpW cj (crpT N m) x
      set e := f x / c m - w
      have hχ01 : 0 ≤ χ m x ∧ χ m x ≤ 1 := ⟨crpPsi_nonneg _, crpPsi_le_one _⟩
      have hfx : f x = c m * (w + e) := by simp only [e]; field_simp [hc m]; ring
      by_cases hw0 : w = 0
      · have he0 : e = 0 := by
          rw [hw0, norm_zero, zero_div] at he; exact norm_le_zero_iff.1 he
        rw [hβx, hfx]
        simp [hw0, he0]
      · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
        have h1 : ‖(1 - (χ m x : ℂ)) * e‖ ≤ ‖w‖ / 2 := by
          rw [norm_mul]
          have : ‖(1 - (χ m x : ℂ))‖ ≤ 1 := by
            rw [show (1 - (χ m x : ℂ)) = ((1 - χ m x : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hχ01.1, hχ01.2]
          calc ‖1 - (χ m x : ℂ)‖ * ‖e‖ ≤ 1 * (‖w‖ / 2) :=
                mul_le_mul this he (norm_nonneg _) zero_le_one
            _ = ‖w‖ / 2 := one_mul _
        have hb : β x ≠ 0 := by
          rw [hβx]
          intro h0
          have : ‖w‖ ≤ ‖(1 - (χ m x : ℂ)) * e‖ := by
            rw [show w = -((1 - (χ m x : ℂ)) * e) by linear_combination h0, norm_neg]
          linarith
        have hf : f x ≠ 0 := by
          rw [hfx]
          refine mul_ne_zero (hc m) ?_
          intro h0
          have : ‖w‖ ≤ ‖e‖ := by rw [show w = -e by linear_combination h0, norm_neg]
          linarith
        exact ⟨fun h => absurd h hb, fun h => absurd h hf⟩
    · push_neg at hA
      rw [hfar x hA]
      simp [hu, Complex.exp_ne_zero]
  · intro m z hz
    have hzim : |z.im| < 1 / 2 := by
      have := Complex.abs_im_le_norm z; linarith
    have hρ : crpRho (crpT N m) (0 + z.re, crpT N m + z.im) ≤ r ^ 2 := by
      simp only [crpRho, zero_add, add_sub_cancel_left]
      have h1 := crpQ_le_sq z.im
      have h2 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      nlinarith [norm_nonneg z]
    obtain ⟨hβx, -⟩ := hloc m _ (by nlinarith)
    rw [hβx, show χ m (0 + z.re, crpT N m + z.im) = 1 from crpChi_one hr hρ]
    simp only [Complex.ofReal_one, sub_self, zero_mul, add_zero, crpW, crpLmap_apply]
    rw [crpD_self (by simpa using hzim)]
    simp

end

end CauchyRiemannIndex

/-!
# The explicit profile `E(s) e^{2πiat} + (1 - E(s)) e^{2πibt}`
-/

namespace CauchyRiemannIndex

noncomputable section

open Real Filter Topology
open scoped ContDiff

/-- Logistic function `1 / (1 + e^{-l s})`. -/
def crpE (l s : ℝ) : ℝ := (1 + Real.exp (-(l * s)))⁻¹

def crpA (a : ℤ) (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * a * t * Complex.I)

def crpF (a b : ℤ) (l : ℝ) (x : ℝ × ℝ) : ℂ :=
  (crpE l x.1 : ℂ) * crpA a x.2 + ((1 - crpE l x.1 : ℝ) : ℂ) * crpA b x.2

lemma crpE_pos (l s : ℝ) : 0 < crpE l s := by unfold crpE; positivity

lemma crpE_lt_one (l s : ℝ) : crpE l s < 1 := by
  unfold crpE
  rw [inv_lt_one₀ (by positivity)]
  linarith [Real.exp_pos (-(l * s))]

lemma one_sub_crpE (l s : ℝ) : 1 - crpE l s = Real.exp (-(l * s)) * crpE l s := by
  unfold crpE
  field_simp
  ring

lemma crpE_zero (l : ℝ) : crpE l 0 = 1 / 2 := by
  unfold crpE; norm_num

lemma crpE_eq_half {l s : ℝ} (hl : 0 < l) (h : crpE l s = 1 / 2) : s = 0 := by
  unfold crpE at h
  have h1 : Real.exp (-(l * s)) = 1 := by
    have : (1 + Real.exp (-(l * s))) = 2 := by
      have h2 := congrArg (·⁻¹) h
      simp only [inv_inv] at h2
      rw [h2]; norm_num
    linarith
  have h2 : -(l * s) = 0 := by
    have := Real.exp_eq_one_iff (-(l * s)) |>.1 h1
    exact this
  have : l * s = 0 := by linarith
  rcases mul_eq_zero.1 this with h3 | h3
  · linarith
  · exact h3

lemma crpE_hasDerivAt (l s : ℝ) :
    HasDerivAt (crpE l) (l * Real.exp (-(l * s)) / (1 + Real.exp (-(l * s))) ^ 2) s := by
  have h0 : HasDerivAt (fun s => -(l * s)) (-(l * 1)) s := ((hasDerivAt_id' s).const_mul l).neg
  have h1 := (h0.exp).const_add 1
  have h2 := h1.inv (by beta_reduce; positivity)
  beta_reduce at h2
  unfold crpE
  exact h2.congr_deriv (by ring)

lemma crpE_deriv_le {l : ℝ} (hl : 0 ≤ l) (s : ℝ) :
    |l * Real.exp (-(l * s)) / (1 + Real.exp (-(l * s))) ^ 2| ≤ l := by
  have he := Real.exp_pos (-(l * s))
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hl he.le) (by positivity)),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hl (sq_nonneg (Real.exp (-(l * s))))]

lemma crpE_contDiff {n : ℕ∞} (l : ℝ) : ContDiff ℝ n (crpE l) := by
  unfold crpE
  exact (contDiff_const.add (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)).inv
    fun s => by simp only [Function.comp_apply]; positivity

lemma crpA_norm (a : ℤ) (t : ℝ) : ‖crpA a t‖ = 1 := by
  unfold crpA
  rw [show (2 * Real.pi * a * t * Complex.I : ℂ) = ((2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma crpA_ne_zero (a : ℤ) (t : ℝ) : crpA a t ≠ 0 := Complex.exp_ne_zero _

lemma crpA_hasDerivAt (a : ℤ) (t : ℝ) :
    HasDerivAt (crpA a) (crpA a t * (2 * Real.pi * a * Complex.I)) t := by
  have h : HasDerivAt (fun t : ℝ => (2 * Real.pi * a * (t : ℂ) * Complex.I))
      (2 * Real.pi * a * Complex.I) t := by
    have := (((hasDerivAt_id t).ofReal_comp).const_mul (2 * Real.pi * a : ℂ)).mul_const Complex.I
    simpa using this
  exact h.cexp

lemma crpA_contDiff {n : ℕ∞} (a : ℤ) : ContDiff ℝ n (crpA a) := by
  unfold crpA
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

lemma crpA_add_one (a : ℤ) (t : ℝ) : crpA a (t + 1) = crpA a t := by
  unfold crpA
  have : (2 * Real.pi * a * ((t + 1 : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * a * (t : ℂ) * Complex.I + (a : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma crpA_mul (a b : ℤ) (t : ℝ) : crpA a t = crpA b t * crpA (a - b) t := by
  unfold crpA
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma crpF_contDiff (a b : ℤ) (l : ℝ) : ContDiff ℝ ∞ (crpF a b l) := by
  unfold crpF
  have hE : ContDiff ℝ ∞ (fun x : ℝ × ℝ => crpE l x.1) := (crpE_contDiff l).comp contDiff_fst
  exact ((Complex.ofRealCLM.contDiff.comp hE).mul ((crpA_contDiff a).comp contDiff_snd)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hE)).mul
      ((crpA_contDiff b).comp contDiff_snd))

lemma crpF_add_one (a b : ℤ) (l s t : ℝ) : crpF a b l (s, t + 1) = crpF a b l (s, t) := by
  simp [crpF, crpA_add_one]

/-- The derivative of `crpF`. -/
def crpDF (a b : ℤ) (l : ℝ) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (((l * Real.exp (-(l * x.1)) / (1 + Real.exp (-(l * x.1))) ^ 2 : ℝ) : ℂ) *
        (crpA a x.2 - crpA b x.2)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      ((crpE l x.1 : ℂ) * (crpA a x.2 * (2 * Real.pi * a * Complex.I)) +
        ((1 - crpE l x.1 : ℝ) : ℂ) * (crpA b x.2 * (2 * Real.pi * b * Complex.I)))

lemma crpF_hasFDerivAt (a b : ℤ) (l : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (crpF a b l) (crpDF a b l x) x := by
  have hE := ((crpE_hasDerivAt l x.1).ofReal_comp).hasFDerivAt.comp x hasFDerivAt_fst
  have hE' := (((crpE_hasDerivAt l x.1).const_sub 1).ofReal_comp).hasFDerivAt.comp x
    hasFDerivAt_fst
  have hA := (crpA_hasDerivAt a x.2).hasFDerivAt.comp x hasFDerivAt_snd
  have hB := (crpA_hasDerivAt b x.2).hasFDerivAt.comp x hasFDerivAt_snd
  have h := (hE.mul hA).add (hE'.mul hB)
  refine h.congr_fderiv ?_
  ext v <;> simp [crpDF] <;> push_cast <;> ring

lemma crpDF_norm_le (a b : ℤ) {l : ℝ} (hl : 0 ≤ l) (x : ℝ × ℝ) :
    ‖crpDF a b l x‖ ≤ 2 * l + 2 * Real.pi * |(a : ℝ)| + 2 * Real.pi * |(b : ℝ)| := by
  have hπ := Real.pi_pos
  have hE0 := (crpE_pos l x.1).le
  have hE1 := (crpE_lt_one l x.1).le
  set P : ℂ := ((l * Real.exp (-(l * x.1)) / (1 + Real.exp (-(l * x.1))) ^ 2 : ℝ) : ℂ) *
        (crpA a x.2 - crpA b x.2) with hP
  set Q : ℂ := (crpE l x.1 : ℂ) * (crpA a x.2 * (2 * Real.pi * a * Complex.I)) +
        ((1 - crpE l x.1 : ℝ) : ℂ) * (crpA b x.2 * (2 * Real.pi * b * Complex.I)) with hQ
  have hPn : ‖P‖ ≤ 2 * l := by
    rw [hP, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖crpA a x.2 - crpA b x.2‖ ≤ 2 := by
      calc _ ≤ ‖crpA a x.2‖ + ‖crpA b x.2‖ := norm_sub_le _ _
        _ = 2 := by rw [crpA_norm, crpA_norm]; norm_num
    calc _ ≤ l * 2 := mul_le_mul (crpE_deriv_le hl x.1) h1 (norm_nonneg _) hl
      _ = 2 * l := by ring
  have hQn : ‖Q‖ ≤ 2 * Real.pi * |(a : ℝ)| + 2 * Real.pi * |(b : ℝ)| := by
    rw [hQ]
    have hna : ‖crpA a x.2 * (2 * Real.pi * a * Complex.I)‖ = 2 * Real.pi * |(a : ℝ)| := by
      rw [norm_mul, crpA_norm, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
      rw [show ((2 * Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hnb : ‖crpA b x.2 * (2 * Real.pi * b * Complex.I)‖ = 2 * Real.pi * |(b : ℝ)| := by
      rw [norm_mul, crpA_norm, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
      rw [show ((2 * Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc _ ≤ ‖(crpE l x.1 : ℂ) * (crpA a x.2 * (2 * Real.pi * a * Complex.I))‖ +
          ‖((1 - crpE l x.1 : ℝ) : ℂ) * (crpA b x.2 * (2 * Real.pi * b * Complex.I))‖ :=
          norm_add_le _ _
      _ ≤ 1 * (2 * Real.pi * |(a : ℝ)|) + 1 * (2 * Real.pi * |(b : ℝ)|) := by
        rw [norm_mul (crpE l x.1 : ℂ), norm_mul ((1 - crpE l x.1 : ℝ) : ℂ), hna, hnb,
          Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE0, abs_of_nonneg (sub_nonneg.2 hE1)]
        gcongr <;> linarith
      _ = _ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [crpDF, ← hP, ← hQ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  have h1 : |v.1| ≤ ‖v‖ := by
    have := norm_fst_le v; rwa [Real.norm_eq_abs] at this
  have h2 : |v.2| ≤ ‖v‖ := by
    have := norm_snd_le v; rwa [Real.norm_eq_abs] at this
  calc ‖v.1 • P + v.2 • Q‖ ≤ ‖v.1 • P‖ + ‖v.2 • Q‖ := norm_add_le _ _
    _ = |v.1| * ‖P‖ + |v.2| * ‖Q‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs]
    _ ≤ ‖v‖ * (2 * l) + ‖v‖ * (2 * Real.pi * |(a : ℝ)| + 2 * Real.pi * |(b : ℝ)|) := by
        gcongr
    _ = _ := by ring

end

end CauchyRiemannIndex

/-!
# Smooth antilinear profiles with normal-form zeros
-/

namespace CauchyRiemannIndex

noncomputable section

open Real Filter Topology
open scoped ContDiff

lemma crpA_eq_neg_one_iff (k : ℤ) (t : ℝ) :
    crpA k t = -1 ↔ ∃ j : ℤ, (k : ℝ) * t = j + 1 / 2 := by
  unfold crpA
  rw [← Complex.exp_pi_mul_I, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg Complex.im hn
    simp at h
    have h2 : (2 * π) * ((k : ℝ) * t - (n + 1 / 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (by positivity)
    · linarith
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hr : ((((k : ℝ) * t : ℝ)) : ℂ) = (((j : ℝ) + 1 / 2 : ℝ) : ℂ) := by rw [hj]
    push_cast at hr
    linear_combination (2 * (π : ℂ) * Complex.I) * hr

lemma crpF_eq_mul (a b : ℤ) (l : ℝ) (x : ℝ × ℝ) :
    crpF a b l x = crpA b x.2 * ((crpE l x.1 : ℂ) * crpA (a - b) x.2 +
      ((1 - crpE l x.1 : ℝ) : ℂ)) := by
  rw [crpF, crpA_mul a b]; ring

lemma crpF_eq_zero_iff (a b : ℤ) {l : ℝ} (hl : 0 < l) (x : ℝ × ℝ) :
    crpF a b l x = 0 ↔ x.1 = 0 ∧ crpA (a - b) x.2 = -1 := by
  rw [crpF_eq_mul, mul_eq_zero, or_iff_right (crpA_ne_zero _ _)]
  constructor
  · intro h
    have h1 : (crpE l x.1 : ℂ) * crpA (a - b) x.2 = -((1 - crpE l x.1 : ℝ) : ℂ) := by
      linear_combination h
    have h2 := congrArg norm h1
    rw [norm_mul, norm_neg, crpA_norm, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (crpE_pos l x.1),
      abs_of_pos (sub_pos.2 (crpE_lt_one l x.1))] at h2
    have he2 : crpE l x.1 = 1 / 2 := by linarith
    refine ⟨crpE_eq_half hl he2, ?_⟩
    rw [he2] at h
    push_cast at h
    linear_combination 2 * h
  · rintro ⟨h1, h2⟩
    rw [h1, crpE_zero, h2]
    push_cast; ring

lemma crp_int_split (N : ℕ) (hN : 0 < N) (j : ℤ) :
    ∃ (m : Fin N) (n : ℤ), ((j : ℝ) + 1 / 2) / N = crpT N m + n := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg j hNz.ne'
  have h1 := Int.emod_lt_of_pos j hNz
  refine ⟨⟨(j % N).toNat, by omega⟩, j / N, ?_⟩
  have hc : (((j % N).toNat : ℕ) : ℝ) = ((j % N : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hj : (j : ℝ) = ((j % N : ℤ) : ℝ) + N * ((j / N : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod j N
    have h' : (j : ℝ) = ((N * (j / N) + j % N : ℤ) : ℝ) := by rw [this]
    rw [h']; push_cast; ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [crpT, Fin.val_mk, hc]
  rw [hj]
  field_simp
  ring

lemma crp_zero_t_iff (k : ℤ) (hk : k ≠ 0) (t : ℝ) :
    (∃ j : ℤ, (k : ℝ) * t = j + 1 / 2) ↔
      ∃ (m : Fin k.natAbs) (n : ℤ), t = crpT k.natAbs m + n := by
  have hN : 0 < k.natAbs := Int.natAbs_pos.2 hk
  have hNr : (0 : ℝ) < k.natAbs := by exact_mod_cast hN
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hkN : (k : ℝ) = -(k.natAbs : ℝ) := by
      have : (k.natAbs : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hneg.le
      have : ((k.natAbs : ℤ) : ℝ) = -(k : ℝ) := by exact_mod_cast this
      rw [Int.cast_natCast] at this; linarith
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨m, n, hmn⟩ := crp_int_split k.natAbs hN (-j - 1)
      refine ⟨m, n, ?_⟩
      rw [← hmn, eq_div_iff hNr.ne']
      rw [hkN] at hj
      push_cast
      linear_combination -hj
    · rintro ⟨m, n, hmn⟩
      refine ⟨-(m : ℤ) - 1 + k * n, ?_⟩
      rw [hmn]
      simp only [crpT]
      push_cast
      rw [hkN]
      field_simp
      ring
  · have hkN : (k : ℝ) = (k.natAbs : ℝ) := by
      have : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hpos.le
      have : ((k.natAbs : ℤ) : ℝ) = (k : ℝ) := by exact_mod_cast this
      rw [Int.cast_natCast] at this; linarith
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨m, n, hmn⟩ := crp_int_split k.natAbs hN j
      refine ⟨m, n, ?_⟩
      rw [← hmn, eq_div_iff hNr.ne']
      rw [hkN] at hj
      linear_combination hj
    · rintro ⟨m, n, hmn⟩
      refine ⟨(m : ℤ) + k * n, ?_⟩
      rw [hmn]
      simp only [crpT]
      push_cast
      rw [hkN]
      field_simp
      ring

lemma crpT_mem (N : ℕ) (m : Fin N) : 0 ≤ crpT N m ∧ crpT N m < 1 := by
  have hN : (0 : ℝ) < N := by have := m.pos; exact_mod_cast this
  have hm : (m : ℝ) + 1 ≤ N := by exact_mod_cast m.isLt
  unfold crpT
  constructor
  · positivity
  · rw [div_lt_one hN]; linarith

lemma crpT_injective (N : ℕ) : Function.Injective (crpT N) := by
  intro m m' h
  have hN : (0 : ℝ) < N := by have := m.pos; exact_mod_cast this
  unfold crpT at h
  rw [div_left_inj' hN.ne'] at h
  ext
  exact_mod_cast (by linarith : (m : ℝ) = m')

lemma crpDF_apply (a b : ℤ) (l : ℝ) (x v : ℝ × ℝ) :
    crpDF a b l x v = (v.1 : ℂ) *
        (((l * Real.exp (-(l * x.1)) / (1 + Real.exp (-(l * x.1))) ^ 2 : ℝ) : ℂ) *
          (crpA a x.2 - crpA b x.2)) +
      (v.2 : ℂ) * ((crpE l x.1 : ℂ) * (crpA a x.2 * (2 * Real.pi * a * Complex.I)) +
        ((1 - crpE l x.1 : ℝ) : ℂ) * (crpA b x.2 * (2 * Real.pi * b * Complex.I))) := by
  simp only [crpDF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.real_smul]

/-- The derivative at the zeros is complex-linear or antilinear. -/
lemma crpDF_at_zero (a b : ℤ) (hk : a - b ≠ 0) (m : Fin (a - b).natAbs) :
    crpDF a b (2 * π * (a - b).natAbs) (0, crpT (a - b).natAbs m) =
      (-(π * (a - b).natAbs : ℂ) * crpA b (crpT (a - b).natAbs m)) •
        crpLmap (decide (a - b < 0)) := by
  have hω : crpA (a - b) (crpT (a - b).natAbs m) = -1 :=
    (crpA_eq_neg_one_iff _ _).2 ((crp_zero_t_iff (a - b) hk _).2
      ⟨m, 0, by rw [Int.cast_zero, add_zero]⟩)
  have hAB : crpA a (crpT (a - b).natAbs m) = -crpA b (crpT (a - b).natAbs m) := by
    rw [crpA_mul a b, hω]; ring
  have hkN : decide (a - b < 0) = false → ((a : ℂ) = b + ((a - b).natAbs : ℂ)) := by
    intro h
    have h1 : 0 ≤ a - b := by simpa using h
    have : (((a - b).natAbs : ℤ)) = a - b := Int.natAbs_of_nonneg h1
    have : (((a - b).natAbs : ℤ) : ℂ) = ((a - b : ℤ) : ℂ) := by rw [this]
    rw [Int.cast_natCast, Int.cast_sub] at this; linear_combination -this
  have hkN' : decide (a - b < 0) = true → ((a : ℂ) = b - ((a - b).natAbs : ℂ)) := by
    intro h
    have h1 : a - b < 0 := by simpa using h
    have : (((a - b).natAbs : ℤ)) = -(a - b) := Int.ofNat_natAbs_of_nonpos h1.le
    have : (((a - b).natAbs : ℤ) : ℂ) = ((-(a - b) : ℤ) : ℂ) := by rw [this]
    rw [Int.cast_natCast, Int.cast_neg, Int.cast_sub] at this; linear_combination this
  apply ContinuousLinearMap.ext
  intro v
  rw [crpDF_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, crpLmap_apply, hAB]
  simp only [crpE_zero, mul_zero, neg_zero, Real.exp_zero]
  rcases hc : decide (a - b < 0)
  · have := hkN hc
    simp only [crpLz, Bool.false_eq_true, ↓reduceIte, Complex.mk_eq_add_mul_I]
    push_cast
    linear_combination (-(π : ℂ) * Complex.I * crpA b (crpT (a - b).natAbs m) * v.2) * this
  · have := hkN' hc
    simp only [crpLz, ↓reduceIte, Complex.mk_eq_add_mul_I, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    push_cast
    linear_combination (-(π : ℂ) * Complex.I * crpA b (crpT (a - b).natAbs m) * v.2) * this

lemma crp_fderiv_bound (β f : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hper : ∀ s t, β (s, t + 1) = β (s, t)) (heq : ∀ x : ℝ × ℝ, 1 / 2 ≤ |x.1| → β x = f x)
    (Cf : ℝ) (hf : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf) : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fderiv ℝ β) := hβ.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hperZ : ∀ s t (n : ℤ), β (s, t + n) = β (s, t) := by
    intro s t n
    have hp : Function.Periodic (fun t => β (s, t)) 1 := fun t => hper s t
    simpa using (hp.int_mul n) t
  have hfp : ∀ s t (n : ℤ), fderiv ℝ β (s, t + n) = fderiv ℝ β (s, t) := by
    intro s t n
    have hb : (fun y : ℝ × ℝ => β (y + ((0 : ℝ), (n : ℝ)))) = β := by
      funext y
      have : y + ((0 : ℝ), (n : ℝ)) = (y.1, y.2 + n) := by ext <;> simp
      rw [this, hperZ]
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := β) (x := ((s, t) : ℝ × ℝ)) ((0 : ℝ), (n : ℝ))
    rw [hb] at this
    rw [this]; simp
  refine ⟨max M Cf, fun x => ?_⟩
  by_cases hx : |x.1| ≤ 1
  · have h1 : fderiv ℝ β x = fderiv ℝ β (x.1, Int.fract x.2) := by
      have := hfp x.1 (Int.fract x.2) ⌊x.2⌋
      rw [Int.fract_add_floor] at this
      exact this
    rw [h1]
    have hmem : ((x.1, Int.fract x.2) : ℝ × ℝ) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨(abs_le.1 hx).1, (abs_le.1 hx).2⟩, ⟨Int.fract_nonneg x.2, (Int.fract_lt_one x.2).le⟩⟩
    exact (hM _ hmem).trans (le_max_left _ _)
  · push_neg at hx
    have hU : IsOpen {y : ℝ × ℝ | 1 / 2 < |y.1|} := isOpen_lt continuous_const (by fun_prop)
    have hev : β =ᶠ[𝓝 x] f := by
      filter_upwards [hU.mem_nhds (show 1 / 2 < |x.1| by linarith)] with y hy
      exact heq y (le_of_lt hy)
    rw [hev.fderiv_eq]
    exact (hf x).trans (le_max_right _ _)

lemma crpE_tendsto_bounds {l : ℝ} (hl : 0 < l) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ s, (R ≤ s → 2 * (1 - crpE l s) ≤ ε) ∧ (s ≤ -R → 2 * crpE l s ≤ ε) := by
  refine ⟨Real.log (2 / ε) / l, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · have h1 : Real.log (2 / ε) ≤ l * s := by
      rwa [div_le_iff₀ hl, mul_comm] at hs
    have h2 : Real.exp (-(l * s)) ≤ ε / 2 := by
      calc Real.exp (-(l * s)) ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.2 (by linarith)
        _ = ε / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    rw [one_sub_crpE]
    have := (crpE_lt_one l s).le
    have := crpE_pos l s
    nlinarith [Real.exp_pos (-(l * s))]
  · have h1 : l * s ≤ -Real.log (2 / ε) := by
      have := mul_le_mul_of_nonneg_left hs hl.le
      rw [mul_neg, mul_div_cancel₀ _ hl.ne'] at this
      exact this
    have h2 : crpE l s ≤ Real.exp (l * s) := by
      unfold crpE
      rw [inv_le_comm₀ (by positivity) (by positivity), ← Real.exp_neg]
      linarith [Real.exp_pos (-(l * s))]
    have h3 : Real.exp (l * s) ≤ ε / 2 := by
      calc Real.exp (l * s) ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.2 h1
        _ = ε / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    linarith

lemma crpF_sub_A (a b : ℤ) (l s t : ℝ) :
    ‖crpF a b l (s, t) - crpA a t‖ ≤ 2 * (1 - crpE l s) := by
  have h : crpF a b l (s, t) - crpA a t = ((1 - crpE l s : ℝ) : ℂ) * (crpA b t - crpA a t) := by
    simp only [crpF]; push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 (crpE_lt_one l s))]
  have : ‖crpA b t - crpA a t‖ ≤ 2 := by
    calc _ ≤ ‖crpA b t‖ + ‖crpA a t‖ := norm_sub_le _ _
      _ = 2 := by rw [crpA_norm, crpA_norm]; norm_num
  nlinarith [crpE_lt_one l s]

lemma crpF_sub_B (a b : ℤ) (l s t : ℝ) :
    ‖crpF a b l (s, t) - crpA b t‖ ≤ 2 * crpE l s := by
  have h : crpF a b l (s, t) - crpA b t = (crpE l s : ℂ) * (crpA a t - crpA b t) := by
    simp only [crpF]; push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (crpE_pos l s)]
  have : ‖crpA a t - crpA b t‖ ≤ 2 := by
    calc _ ≤ ‖crpA a t‖ + ‖crpA b t‖ := norm_sub_le _ _
      _ = 2 := by rw [crpA_norm, crpA_norm]; norm_num
  nlinarith [crpE_pos l s]

lemma crpF_norm_le (a b : ℤ) (l s t : ℝ) : ‖crpF a b l (s, t)‖ ≤ 1 := by
  unfold crpF
  have n1 : ‖(crpE l s : ℂ) * crpA a t‖ = crpE l s := by
    rw [norm_mul, crpA_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (crpE_pos l s)]
  have n2 : ‖((1 - crpE l s : ℝ) : ℂ) * crpA b t‖ = 1 - crpE l s := by
    rw [norm_mul, crpA_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.2 (crpE_lt_one l s))]
  calc _ ≤ ‖(crpE l s : ℂ) * crpA a t‖ + ‖((1 - crpE l s : ℝ) : ℂ) * crpA b t‖ :=
        norm_add_le _ _
    _ = 1 := by rw [n1, n2]; ring

lemma crpF_norm_ge (a b : ℤ) (l s t : ℝ) : |2 * crpE l s - 1| ≤ ‖crpF a b l (s, t)‖ := by
  rw [crpF_eq_mul, norm_mul, crpA_norm, one_mul]
  have n1 : ‖(crpE l s : ℂ) * crpA (a - b) t‖ = crpE l s := by
    rw [norm_mul, crpA_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (crpE_pos l s)]
  have n2 : ‖((1 - crpE l s : ℝ) : ℂ)‖ = 1 - crpE l s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.2 (crpE_lt_one l s))]
  have := abs_norm_sub_norm_le ((crpE l s : ℂ) * crpA (a - b) t) (-((1 - crpE l s : ℝ) : ℂ))
  rw [norm_neg, n1, n2, sub_neg_eq_add] at this
  calc |2 * crpE l s - 1| = |crpE l s - (1 - crpE l s)| := by ring_nf
    _ ≤ _ := this

lemma crpE_mono {l : ℝ} (hl : 0 ≤ l) {s s' : ℝ} (h : s ≤ s') : crpE l s ≤ crpE l s' := by
  unfold crpE
  apply inv_anti₀ (by positivity)
  have : Real.exp (-(l * s')) ≤ Real.exp (-(l * s)) := Real.exp_le_exp.2 (by nlinarith)
  linarith

lemma one_sub_crpE_eq (l s : ℝ) : 1 - crpE l s = crpE l (-s) := by
  unfold crpE
  rw [show -(l * -s) = l * s by ring, Real.exp_neg]
  have := Real.exp_pos (l * s)
  field_simp
  ring

lemma crpE_pinch {l : ℝ} (hl : 0 < l) (s : ℝ) (hs : 1 ≤ |s|) :
    2 * crpE l 1 - 1 ≤ |2 * crpE l s - 1| := by
  rcases le_or_gt 0 s with h0 | h0
  · rw [abs_of_nonneg h0] at hs
    have h1 := crpE_mono hl.le hs
    exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_of_neg h0] at hs
    have h1 : crpE l s ≤ crpE l (-1) := crpE_mono hl.le (by linarith)
    rw [← one_sub_crpE_eq] at h1
    exact le_trans (by linarith) (neg_le_abs _)

lemma crpE_one_gt {l : ℝ} (hl : 0 < l) : 0 < 2 * crpE l 1 - 1 := by
  have h2 : crpE l 0 < crpE l 1 := by
    unfold crpE
    apply inv_strictAnti₀ (by positivity)
    have : Real.exp (-(l * 1)) < Real.exp (-(l * 0)) := Real.exp_lt_exp.2 (by linarith)
    linarith
  rw [crpE_zero] at h2
  linarith

theorem exists_antilinear_profile_aux (a b : ℤ) :
    ∃ (β : ℝ × ℝ → ℂ) (Zplus Zminus : Finset (ℝ × ℝ)) (r : ℝ),
      ContDiff ℝ ∞ β ∧ (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C) ∧
      (∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ s t,
        (R ≤ s → ‖β (s, t) - Complex.exp (2 * Real.pi * a * t * Complex.I)‖ ≤ ε) ∧
        (s ≤ -R → ‖β (s, t) - Complex.exp (2 * Real.pi * b * t * Complex.I)‖ ≤ ε)) ∧
      (∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1) ∧ Disjoint Zplus Zminus ∧
      (∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m)) ∧
      0 < r ∧ (∀ ζ ∈ Zplus ∪ Zminus, |ζ.1| + r ≤ 1) ∧
      (∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z) ∧
      (∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z) ∧
      (b ≤ a → Zminus = ∅ ∧ (Zplus.card : ℤ) = a - b) ∧
      (a ≤ b → Zplus = ∅ ∧ (Zminus.card : ℤ) = b - a) := by
  have hπ := Real.pi_pos
  by_cases hab : a = b
  · -- no zeros: `β = e^{2πiat}`
    subst hab
    have hβ : ∀ x : ℝ × ℝ, crpF a a 0 x = crpA a x.2 := by
      intro x; simp only [crpF]; push_cast; ring
    refine ⟨crpF a a 0, ∅, ∅, 1, crpF_contDiff a a 0, crpF_add_one a a 0, ?_, ?_, ?_,
      by simp, by simp, ?_, one_pos, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨_, fun x => by
        rw [(crpF_hasFDerivAt a a 0 x).fderiv]; exact crpDF_norm_le a a le_rfl x⟩
    · refine ⟨0, 1, one_pos, fun s t _ => ?_⟩
      rw [hβ, crpA_norm]; norm_num
    · intro ε hε
      refine ⟨0, fun s t => ⟨fun _ => ?_, fun _ => ?_⟩⟩ <;>
        rw [hβ] <;> simp only [crpA, sub_self, norm_zero] <;> exact hε.le
    · intro x
      simp [hβ, crpA_ne_zero]
  · have hk : a - b ≠ 0 := sub_ne_zero.2 hab
    have hN : 0 < (a - b).natAbs := Int.natAbs_pos.2 hk
    have hNr : (0 : ℝ) < (a - b).natAbs := by exact_mod_cast hN
    have hl : 0 < 2 * π * (a - b).natAbs := by positivity
    have hfz : ∀ m : Fin (a - b).natAbs,
        crpF a b (2 * π * (a - b).natAbs) (0, crpT (a - b).natAbs m) = 0 := by
      intro m
      rw [crpF_eq_zero_iff a b hl]
      exact ⟨rfl, (crpA_eq_neg_one_iff _ _).2
        ((crp_zero_t_iff (a - b) hk _).2 ⟨m, 0, by rw [Int.cast_zero, add_zero]⟩)⟩
    obtain ⟨r, hr, hr20, β, hβ, hβper, hβf, hβz, hβnf⟩ :=
      crp_glue (a - b).natAbs hN (decide (a - b < 0)) (crpF a b (2 * π * (a - b).natAbs))
        (crpF_contDiff a b _) (crpF_add_one a b _) hfz
        (fun m => -(π * (a - b).natAbs : ℂ) * crpA b (crpT (a - b).natAbs m))
        (fun m => mul_ne_zero (neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hπ.ne')
          (by exact_mod_cast hN.ne'))) (crpA_ne_zero _ _))
        (fun m => by
          rw [← crpDF_at_zero a b hk m]
          exact crpF_hasFDerivAt a b _ _)
    set l : ℝ := 2 * π * (a - b).natAbs with hl_def
    set Z : Finset (ℝ × ℝ) :=
      Finset.univ.image (fun m : Fin (a - b).natAbs => ((0 : ℝ), crpT (a - b).natAbs m)) with hZ
    have hZcard : Z.card = (a - b).natAbs := by
      rw [hZ, Finset.card_image_of_injective _ (fun m m' h => crpT_injective _
        (congrArg Prod.snd h))]
      simp
    have hZmem : ∀ ζ ∈ Z, ∃ m : Fin (a - b).natAbs, ζ = (0, crpT (a - b).natAbs m) := by
      intro ζ hζ
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hζ
      exact ⟨m, rfl⟩
    -- common properties
    have hfd : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C :=
      crp_fderiv_bound β _ hβ hβper hβf _ (fun x => by
        rw [(crpF_hasFDerivAt a b l x).fderiv]; exact crpDF_norm_le a b hl.le x)
    have hpinch : ∃ (R c : ℝ), 0 < c ∧
        ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c := by
      refine ⟨1, 2 * crpE l 1 - 1, crpE_one_gt hl, fun s t hs => ?_⟩
      rw [hβf (s, t) (show 1 / 2 ≤ |s| by linarith)]
      refine ⟨(crpE_pinch hl s hs).trans (crpF_norm_ge a b l s t), ?_⟩
      have hc1 : 2 * crpE l 1 - 1 ≤ 1 := by linarith [crpE_lt_one l 1]
      have hc0 := crpE_one_gt hl
      refine (crpF_norm_le a b l s t).trans ?_
      rw [le_div_iff₀ hc0]; linarith
    have hends : ∀ ε > 0, ∃ R : ℝ, ∀ s t,
        (R ≤ s → ‖β (s, t) - Complex.exp (2 * Real.pi * a * t * Complex.I)‖ ≤ ε) ∧
        (s ≤ -R → ‖β (s, t) - Complex.exp (2 * Real.pi * b * t * Complex.I)‖ ≤ ε) := by
      intro ε hε
      obtain ⟨R, hR⟩ := crpE_tendsto_bounds hl ε hε
      refine ⟨max R 1, fun s t => ⟨fun hs => ?_, fun hs => ?_⟩⟩
      · have h1 := le_max_right R 1
        have hs' : 1 / 2 ≤ |s| := by rw [abs_of_pos (by linarith)]; linarith
        rw [hβf (s, t) hs']
        exact (crpF_sub_A a b l s t).trans ((hR s).1 (le_trans (le_max_left _ _) hs))
      · have h1 := le_max_right R 1
        have hs' : 1 / 2 ≤ |s| := by rw [abs_of_neg (by linarith)]; linarith
        rw [hβf (s, t) hs']
        exact (crpF_sub_B a b l s t).trans ((hR s).2 (by linarith [le_max_left R 1]))
    have hzeroZ : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Z, ∃ m : ℤ, x = (ζ.1, ζ.2 + m) := by
      intro x
      rw [hβz, crpF_eq_zero_iff a b hl, crpA_eq_neg_one_iff, crp_zero_t_iff _ hk]
      constructor
      · rintro ⟨h1, m, n, hmn⟩
        exact ⟨(0, crpT (a - b).natAbs m), Finset.mem_image.2 ⟨m, Finset.mem_univ _, rfl⟩, n,
          Prod.ext h1 hmn⟩
      · rintro ⟨ζ, hζ, n, rfl⟩
        obtain ⟨m, rfl⟩ := hZmem ζ hζ
        exact ⟨rfl, m, n, rfl⟩
    have hZ01 : ∀ ζ ∈ Z, 0 ≤ ζ.2 ∧ ζ.2 < 1 := by
      intro ζ hζ; obtain ⟨m, rfl⟩ := hZmem ζ hζ; exact crpT_mem _ m
    have hZband : ∀ ζ ∈ Z, |ζ.1| + r ≤ 1 := by
      intro ζ hζ; obtain ⟨m, rfl⟩ := hZmem ζ hζ; simp; linarith
    have hZnf : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r →
        β (ζ.1 + z.re, ζ.2 + z.im) = crpLz (decide (a - b < 0)) z := by
      intro ζ hζ z hz; obtain ⟨m, rfl⟩ := hZmem ζ hζ; exact hβnf m z hz
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · have hcjt : decide (a - b < 0) = true := by simp [hneg]
      have hNab : ((a - b).natAbs : ℤ) = b - a := by
        rw [Int.ofNat_natAbs_of_nonpos hneg.le]; ring
      refine ⟨β, ∅, Z, r, hβ, hβper, hfd, hpinch, hends, by simpa using hZ01, by simp,
        by simpa using hzeroZ, hr, by simpa using hZband, by simp, ?_, ?_, ?_⟩
      · intro ζ hζ z hz; rw [hZnf ζ hζ z hz, hcjt]; rfl
      · intro h; omega
      · intro _; exact ⟨rfl, by rw [hZcard, hNab]⟩
    · have hcjf : decide (a - b < 0) = false := by simp; omega
      have hNab : ((a - b).natAbs : ℤ) = a - b := Int.natAbs_of_nonneg hpos.le
      refine ⟨β, Z, ∅, r, hβ, hβper, hfd, hpinch, hends, by simpa using hZ01, by simp,
        by simpa using hzeroZ, hr, by simpa using hZband, ?_, by simp, ?_, ?_⟩
      · intro ζ hζ z hz; rw [hZnf ζ hζ z hz, hcjf]; rfl
      · intro _; exact ⟨rfl, by rw [hZcard, hNab]⟩
      · intro h; omega

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (a b : ℤ) :
    ∃ (β : ℝ × ℝ → ℂ) (Zplus Zminus : Finset (ℝ × ℝ)) (r : ℝ),
      ContDiff ℝ ∞ β ∧ (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C) ∧
      (∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ s t,
        (R ≤ s → ‖β (s, t) - Complex.exp (2 * Real.pi * a * t * Complex.I)‖ ≤ ε) ∧
        (s ≤ -R → ‖β (s, t) - Complex.exp (2 * Real.pi * b * t * Complex.I)‖ ≤ ε)) ∧
      (∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1) ∧ Disjoint Zplus Zminus ∧
      (∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m)) ∧
      0 < r ∧ (∀ ζ ∈ Zplus ∪ Zminus, |ζ.1| + r ≤ 1) ∧
      (∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z) ∧
      (∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z) ∧
      (b ≤ a → Zminus = ∅ ∧ (Zplus.card : ℤ) = a - b) ∧
      (a ≤ b → Zplus = ∅ ∧ (Zminus.card : ℤ) = b - a) :=
  CauchyRiemannIndex.exists_antilinear_profile_aux a b
