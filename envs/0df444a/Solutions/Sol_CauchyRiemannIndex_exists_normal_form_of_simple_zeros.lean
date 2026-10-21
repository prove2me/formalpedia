-- Prove2me | solution 1 for CauchyRiemannIndex.exists_normal_form_of_simple_zeros
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T14:08:02.889791+00:00
-- url     : https://prove2.me/submissions/5079a416-ccf1-4e48-92b6-8fb06e8eba68

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds



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

namespace CauchyRiemannIndex

open scoped ContDiff

theorem exists_normal_form_of_simple_zeros_aux (N : ℕ) (hN : 0 < N) (cj : Bool) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (hzero : ∀ m : Fin N, f (0, ((m : ℝ) + 1 / 2) / N) = 0)
    (c : Fin N → ℂ) (hc : ∀ m, c m ≠ 0)
    (hD : ∀ m : Fin N, HasFDerivAt f (c m • (if cj then
        (Complex.conjCLE.toContinuousLinearMap).comp
          Complex.equivRealProdCLM.symm.toContinuousLinearMap
      else Complex.equivRealProdCLM.symm.toContinuousLinearMap)) (0, ((m : ℝ) + 1 / 2) / N)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 20 ∧ ∃ β : ℝ × ℝ → ℂ, ContDiff ℝ ∞ β ∧
      (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∀ x : ℝ × ℝ, 1 / 2 ≤ |x.1| → β x = f x) ∧ (∀ x, β x = 0 ↔ f x = 0) ∧
      ∀ m : Fin N, ∀ z : ℂ, ‖z‖ < r →
        β (0 + z.re, ((m : ℝ) + 1 / 2) / N + z.im) = if cj then (starRingEnd ℂ) z else z :=
  crp_glue N hN cj f hf hper hzero c hc hD

end CauchyRiemannIndex

open CauchyRiemannIndex

open scoped ContDiff

theorem solution (N : ℕ) (hN : 0 < N) (cj : Bool) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (hzero : ∀ m : Fin N, f (0, ((m : ℝ) + 1 / 2) / N) = 0)
    (c : Fin N → ℂ) (hc : ∀ m, c m ≠ 0)
    (hD : ∀ m : Fin N, HasFDerivAt f (c m • (if cj then
        (Complex.conjCLE.toContinuousLinearMap).comp
          Complex.equivRealProdCLM.symm.toContinuousLinearMap
      else Complex.equivRealProdCLM.symm.toContinuousLinearMap)) (0, ((m : ℝ) + 1 / 2) / N)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 20 ∧ ∃ β : ℝ × ℝ → ℂ, ContDiff ℝ ∞ β ∧
      (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∀ x : ℝ × ℝ, 1 / 2 ≤ |x.1| → β x = f x) ∧ (∀ x, β x = 0 ↔ f x = 0) ∧
      ∀ m : Fin N, ∀ z : ℂ, ‖z‖ < r →
        β (0 + z.re, ((m : ℝ) + 1 / 2) / N + z.im) = if cj then (starRingEnd ℂ) z else z :=
  CauchyRiemannIndex.exists_normal_form_of_simple_zeros_aux N hN cj f hf hper hzero c hc hD
