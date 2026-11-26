-- Prove2me | solution 1 for GRH.nonnegative_mellin_continuation_from_real_axis
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:55:44.352444+00:00
-- url     : https://prove2.me/submissions/7aff1eb5-055e-42bb-9c07-594cb9345051

import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Order.Group.Lattice

/- The Mellin convergence proof is adapted from pitimespi's public Lean formalization,
   https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7
   licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
   The auxiliary namespace and imports have been changed. The final declaration
   transfers the result to the transform used for the one-sided Mertens bound. -/
open Complex MeasureTheory Filter Topology Set Metric GRH.OneSidedMoebius
noncomputable section
namespace OneSidedLandauAux


/-- `mellinK A k s = ∫_{x>1} A(x) (-log x)^k x^{-s-1} dx`; for `k = 0` this is the Mellin-type
transform `F(s) = ∫_{x>1} A(x) x^{-s-1} dx`, and `mellinK A k` is its `k`-th derivative. -/
def mellinK (A : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1)

/-- Convergence of the real Mellin integral `∫_{x>1} A(x) x^{-σ-1} dx`. -/
def Conv (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => A x * x ^ (-σ - 1)) (Ioi 1)

lemma log_pow_le (k : ℕ) {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ k ≤ ((k:ℝ) / η) ^ k * x ^ η := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using Real.one_le_rpow hx hη.le
  · have hk' : (0:ℝ) < k := by exact_mod_cast hk
    have hε : 0 < η / k := div_pos hη hk'
    have h1 : Real.log x ≤ x ^ (η / k) / (η / k) := Real.log_le_rpow_div (by linarith) hε
    have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hx0 : 0 ≤ x := by linarith
    calc Real.log x ^ k ≤ (x ^ (η / k) / (η / k)) ^ k := pow_le_pow_left₀ h0 h1 k
      _ = ((k:ℝ) / η) ^ k * x ^ η := by
        rw [div_pow, ← Real.rpow_natCast (x ^ (η / k)), ← Real.rpow_mul hx0,
          div_mul_cancel₀ η hk'.ne', div_eq_mul_inv, ← inv_pow, inv_div, mul_comm]

lemma conv_mono {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ}
    (h : Conv A σ) (hσ : σ ≤ σ') : Conv A σ' := by
  refine h.mono' ((hA.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 x hx') (Real.rpow_nonneg (by linarith) _))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (hA0 x hx')

/-- Absolute convergence of the real Mellin integral `∫_{x>1} |A(x)| x^{-σ-1} dx`. -/
def ConvAbs (A : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => |A x| * x ^ (-σ - 1)) (Ioi 1)

lemma convAbs_of_conv {A : ℝ → ℝ} (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ : ℝ} (h : Conv A σ) :
    ConvAbs A σ := by
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

/-- Domination: absolute convergence at `σ` gives integrability of
`|A(x)| (log x)^k x^{-σ'-1}` for every `σ' > σ`. -/
lemma integrableOn_log_pow {A : ℝ → ℝ} (hA : Measurable A)
    {σ σ' : ℝ} (hσ : σ < σ') (hc : ConvAbs A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => |A x| * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  have hη : 0 < σ' - σ := sub_pos.mpr hσ
  refine (hc.const_mul (((k:ℝ) / (σ' - σ)) ^ k)).mono'
    (((hA.abs.mul (Real.measurable_log.pow_const k)).mul
      (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (1:ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  have hAx := abs_nonneg (A x)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have key := log_pow_le k hη hx'.le
  calc |A x| * Real.log x ^ k * x ^ (-σ' - 1)
      ≤ |A x| * (((k:ℝ) / (σ' - σ)) ^ k * x ^ (σ' - σ)) * x ^ (-σ' - 1) := by gcongr
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * (x ^ (σ' - σ) * x ^ (-σ' - 1))) := by ring
    _ = ((k:ℝ) / (σ' - σ)) ^ k * (|A x| * x ^ (-σ - 1)) := by
        rw [← Real.rpow_add hx0]; ring_nf

lemma integrableOn_log_pow_of_nonneg {A : ℝ → ℝ} (hA : Measurable A)
    (hA0 : ∀ x, 1 < x → 0 ≤ A x) {σ σ' : ℝ} (hσ : σ < σ') (hc : Conv A σ) (k : ℕ) :
    IntegrableOn (fun x : ℝ => A x * Real.log x ^ k * x ^ (-σ' - 1)) (Ioi 1) := by
  refine IntegrableOn.congr_fun (integrableOn_log_pow hA hσ (convAbs_of_conv hA0 hc) k)
    (fun x hx => ?_) measurableSet_Ioi
  simp only [abs_of_nonneg (hA0 x hx)]

lemma norm_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    ‖(A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1)‖ =
      |A x| * Real.log x ^ k * x ^ (-z.re - 1) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp [abs_of_nonneg hlog]

lemma hasDerivAt_integrand (A : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun s : ℂ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1)) z := by
  have h1 : HasDerivAt (fun s : ℂ => -s - 1) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const 1
  have h2 := h1.const_cpow (c := (x:ℂ)) (Or.inl (by exact_mod_cast hx.ne'))
  have h3 := h2.const_mul ((A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k)
  refine h3.congr_deriv ?_
  rw [← Complex.ofReal_log hx.le]
  push_cast
  ring

lemma aestronglyMeasurable_integrand {A : ℝ → ℝ} (hA : Measurable A) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := by
  refine Measurable.aestronglyMeasurable ?_
  refine ((Complex.measurable_ofReal.comp hA).mul ?_).mul ?_
  · exact (Complex.measurable_ofReal.comp Real.measurable_log.neg).pow_const k
  · exact Complex.measurable_ofReal.pow_const _

lemma integrable_integrand {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    Integrable (fun x : ℝ => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi 1)) := by
  have hI := integrableOn_log_pow hA (σ := (τ + s.re) / 2) (σ' := s.re) (by linarith)
    (hconv _ (by linarith)) k
  refine hI.mono' (aestronglyMeasurable_integrand hA k s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_integrand A k hx]

lemma hasDerivAt_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) {s : ℂ} (hs : τ < s.re) :
    HasDerivAt (mellinK A k) (mellinK A (k+1) s) s := by
  set δ := (s.re - τ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set σ₁ := s.re - δ with hσ₁
  have hτσ₁ : τ < σ₁ := by rw [hσ₁, hδ]; linarith
  have hbound := integrableOn_log_pow hA (σ := (τ + σ₁) / 2) (σ' := σ₁) (by linarith)
    (hconv _ (by linarith)) (k + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ k * (x : ℂ) ^ (-z - 1))
    (F' := fun z x => (A x : ℂ) * ((-Real.log x : ℝ) : ℂ) ^ (k + 1) * (x : ℂ) ^ (-z - 1))
    (x₀ := s) (s := ball s δ)
    (bound := fun x => |A x| * Real.log x ^ (k + 1) * x ^ (-σ₁ - 1))
    (ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => aestronglyMeasurable_integrand hA k z)
    (integrable_integrand hA hconv k hs)
    (aestronglyMeasurable_integrand hA (k + 1) s) ?_ hbound ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    have hx' : (1:ℝ) < x := hx
    rw [norm_integrand A (k + 1) hx']
    have hzre : σ₁ ≤ z.re := by
      have h1 : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa using Complex.abs_re_le_norm (z - s)
      have h2 : ‖z - s‖ < δ := by simpa [dist_eq_norm] using hz
      have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
      rw [hσ₁]; linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx'.le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    exact hasDerivAt_integrand A k (by linarith [show (1:ℝ) < x from hx]) z

lemma iteratedDeriv_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) :
    ∀ s : ℂ, τ < s.re → iteratedDeriv k (mellinK A 0) s = mellinK A k s := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | τ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : iteratedDeriv k (mellinK A 0) =ᶠ[𝓝 s] mellinK A k := by
      filter_upwards [hopen.mem_nhds hs] with z hz using ih z hz
    rw [hev.deriv_eq]
    exact (hasDerivAt_mellinK hA hconv k hs).deriv

lemma differentiableOn_mellinK {A : ℝ → ℝ} (hA : Measurable A)
    {τ : ℝ} (hconv : ∀ σ, τ < σ → ConvAbs A σ) (k : ℕ) :
    DifferentiableOn ℂ (mellinK A k) {z : ℂ | τ < z.re} := fun _ hz =>
  (hasDerivAt_mellinK hA hconv k hz).differentiableAt.differentiableWithinAt

/-! ### Landau's theorem for Mellin transforms of nonnegative functions -/

/-- At a real point, `mellinK A k a` is (the coercion of) a real integral. -/
lemma mellinK_ofReal (A : ℝ → ℝ) (k : ℕ) (a : ℝ) :
    mellinK A k (a : ℂ) =
      (((-1:ℝ) ^ k * ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1) : ℝ) : ℂ) := by
  rw [mellinK, ← integral_const_mul, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0:ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  rw [show (-(a:ℂ) - 1) = ((-a - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hx0]
  push_cast
  ring

/-- Monotone convergence step: summability of the (nonnegative) Taylor coefficients at `a`,
evaluated at distance `t`, gives convergence of the Mellin integral at `a - t`. -/
lemma conv_of_summable {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x)
    {a t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ k : ℕ, IntegrableOn (fun x => A x * Real.log x ^ k * x ^ (-a - 1)) (Ioi 1))
    (hsum : Summable (fun k : ℕ => t ^ k / k.factorial *
        ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1))) :
    Conv A (a - t) := by
  set f : ℕ → ℝ → ℝ := fun k x => t ^ k / k.factorial * (A x * Real.log x ^ k * x ^ (-a - 1))
    with hf
  have hf_nonneg : ∀ k, ∀ x ∈ Ioi (1:ℝ), 0 ≤ f k x := by
    intro k x hx
    have hx' : (1:ℝ) < x := hx
    have := hA0 x hx'
    have := Real.log_nonneg hx'.le
    simp only [hf]
    positivity
  have hpt : ∀ x ∈ Ioi (1:ℝ), HasSum (fun k => f k x) (A x * x ^ (-(a - t) - 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have he := NormedSpace.expSeries_div_hasSum_exp (t * Real.log x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have h2 := he.mul_left (A x * x ^ (-a - 1))
    have e1 : (fun k => f k x) =
        (fun i => A x * x ^ (-a - 1) * ((t * Real.log x) ^ i / i.factorial)) := by
      funext k
      simp only [hf]
      rw [mul_pow]
      ring
    have e2 : A x * x ^ (-(a - t) - 1) = A x * x ^ (-a - 1) * Real.exp (t * Real.log x) := by
      rw [show -(a - t) - 1 = (-a - 1) + t by ring, Real.rpow_add hx0,
        Real.rpow_def_of_pos hx0 t]
      ring_nf
    rw [e1, e2]
    exact h2
  have hmeas : AEStronglyMeasurable (fun x => A x * x ^ (-(a - t) - 1))
      (volume.restrict (Ioi 1)) :=
    (hA.mul (measurable_id.pow_const _)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 1)] (fun x => A x * x ^ (-(a - t) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (1:ℝ) < x := hx
    have := hA0 x hx'
    have : 0 ≤ x := by linarith
    positivity
  have hfint : ∀ k, IntegrableOn (f k) (Ioi 1) := fun k => (hint k).const_mul _
  have hfmeas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (f k x)) (volume.restrict (Ioi 1)) :=
    fun k => (hfint k).aemeasurable.ennreal_ofReal
  have hIk : ∀ k, ∫ x in Ioi (1:ℝ), f k x =
      t ^ k / k.factorial * ∫ x in Ioi (1:ℝ), A x * Real.log x ^ k * x ^ (-a - 1) := by
    intro k; simp only [hf]; rw [integral_const_mul]
  have hInn : ∀ k, 0 ≤ ∫ x in Ioi (1:ℝ), f k x := fun k =>
    setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)
  have hsum' : Summable (fun k => ∫ x in Ioi (1:ℝ), f k x) := by
    simp_rw [hIk]; exact hsum
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
  calc ∫⁻ x in Ioi 1, ENNReal.ofReal (A x * x ^ (-(a - t) - 1))
      = ∫⁻ x in Ioi 1, ∑' k, ENNReal.ofReal (f k x) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        rw [← (hpt x hx).tsum_eq,
          ENNReal.ofReal_tsum_of_nonneg (fun k => hf_nonneg k x hx) (hpt x hx).summable]
    _ = ∑' k, ∫⁻ x in Ioi 1, ENNReal.ofReal (f k x) := lintegral_tsum hfmeas
    _ = ∑' k, ENNReal.ofReal (∫ x in Ioi 1, f k x) := by
        congr 1; funext k
        rw [ofReal_integral_eq_lintegral_ofReal (hfint k)]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hf_nonneg k x hx
    _ = ENNReal.ofReal (∑' k, ∫ x in Ioi 1, f k x) :=
        (ENNReal.ofReal_tsum_of_nonneg hInn hsum').symm
    _ < ⊤ := ENNReal.ofReal_lt_top

lemma norm_sub_ofReal_re (z : ℂ) : ‖z - (z.re : ℂ)‖ = |z.im| := by
  have : z - (z.re : ℂ) = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Landau's theorem** for Mellin transforms of nonnegative functions.
Let `A ≥ 0` on `(1, ∞)` with `∫_{x>1} A(x) x^{-σ-1} dx < ∞` for `σ > c`. If the transform
`F(s) = ∫_{x>1} A(x) x^{-s-1} dx` agrees on `Re s > c` with a function `G` that is holomorphic
on an open set containing the half-plane `Re s > c` and the real half-line `(σ₀, ∞)`, then the
integral converges for every real `σ > σ₀`. -/
theorem landau {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 1 < x → 0 ≤ A x)
    {σ₀ c : ℝ} (hc : ∀ σ, c < σ → Conv A σ)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hUc : ∀ s : ℂ, c < s.re → s ∈ U) (hUr : ∀ σ : ℝ, σ₀ < σ → (σ : ℂ) ∈ U)
    (hFG : ∀ s : ℂ, c < s.re → mellinK A 0 s = G s) :
    ∀ σ, σ₀ < σ → Conv A σ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨σ₁, hσ₁, hnot⟩ := hcon
  set S : Set ℝ := {σ | Conv A σ} with hS
  have hlow : ∀ σ ∈ S, σ₁ ≤ σ := fun σ hσ => by
    by_contra h; push Not at h; exact hnot (conv_mono hA hA0 hσ h.le)
  have hSbdd : BddBelow S := ⟨σ₁, hlow⟩
  have hSne : S.Nonempty := ⟨c + 1, hc _ (by linarith)⟩
  set τ := sInf S with hτ
  have hσ₁τ : σ₁ ≤ τ := le_csInf hSne hlow
  have hτc : τ ≤ c := by
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    exact (csInf_le hSbdd (show c + ε / 2 ∈ S from hc _ (by linarith))).trans_lt (by linarith)
  have hright : ∀ σ, τ < σ → Conv A σ := fun σ hσ => by
    obtain ⟨σ', hσ'S, hσ'lt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact conv_mono hA hA0 hσ'S hσ'lt.le
  have hleft : ∀ σ, σ < τ → ¬ Conv A σ := fun σ hσ hS' =>
    absurd (csInf_le hSbdd hS') (not_le.mpr hσ)
  have hσ₀τ : σ₀ < τ := lt_of_lt_of_le hσ₁ hσ₁τ
  -- the compact segment `K` and a uniform width `δ`
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc ((σ₀ + τ) / 2) (c + 1) with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hUr x (by linarith [hx.1])
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hU hKU
  set r := min δ 1 / 3 with hr
  have hr0 : 0 < r := by positivity
  have hrδ : r ≤ δ / 3 := by rw [hr]; gcongr; exact min_le_left _ _
  have hr1 : r ≤ 1 / 3 := by rw [hr]; gcongr; exact min_le_right _ _
  set a : ℝ := τ + r with ha
  have haK : (a : ℂ) ∈ K := ⟨a, ⟨by linarith, by linarith⟩, rfl⟩
  have hGball : DifferentiableOn ℂ G (ball (a : ℂ) δ) :=
    hG.mono ((ball_subset_thickening haK δ).trans hthick)
  -- the region `W` on which `F = G`
  set W₁ : Set ℂ := {z | τ < z.re} ∩ ({z | z.re < c + 1} ∩ ({z | -δ < z.im} ∩ {z | z.im < δ}))
    with hW₁
  set W : Set ℂ := W₁ ∪ {z | c < z.re} with hW
  have hWU : W ⊆ U := by
    rintro z (⟨h1, h2, h3, h4⟩ | h)
    · apply hthick
      rw [mem_thickening_iff]
      refine ⟨(z.re : ℂ), ⟨z.re, ⟨by simp only [Set.mem_ofPred_eq] at h1; linarith,
        by simp only [Set.mem_ofPred_eq] at h2; linarith⟩, rfl⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_ofReal_re]
      simp only [Set.mem_ofPred_eq] at h3 h4
      exact abs_lt.mpr ⟨h3, h4⟩
    · exact hUc z h
  have hWopen : IsOpen W := by
    refine IsOpen.union ?_ (isOpen_lt continuous_const Complex.continuous_re)
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hz₀W₁ : ((c + 1/2 : ℝ) : ℂ) ∈ W₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq, ofReal_re, ofReal_im] <;> linarith
  have hz₀W₂ : ((c + 1/2 : ℝ) : ℂ) ∈ {z : ℂ | c < z.re} := by
    simp only [Set.mem_ofPred_eq, ofReal_re]; linarith
  have hWconn : IsPreconnected W := by
    refine IsPreconnected.union ((c + 1/2 : ℝ) : ℂ) hz₀W₁ hz₀W₂ ?_
      (convex_halfSpace_re_gt c).isPreconnected
    exact ((convex_halfSpace_re_gt τ).inter ((convex_halfSpace_re_lt (c + 1)).inter
      ((convex_halfSpace_im_gt (-δ)).inter (convex_halfSpace_im_lt δ)))).isPreconnected
  have hright' : ∀ σ, τ < σ → ConvAbs A σ := fun σ hσ => convAbs_of_conv hA0 (hright σ hσ)
  have hFdiff := differentiableOn_mellinK hA hright' 0
  have hWsub : W ⊆ {z : ℂ | τ < z.re} := by
    rintro z (⟨h1, _, _⟩ | h)
    · exact h1
    · exact lt_of_le_of_lt hτc h
  have hFW : EqOn (mellinK A 0) G W := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hFdiff.mono hWsub).analyticOnNhd hWopen) ((hG.mono hWU).analyticOnNhd hWopen) hWconn
      (z₀ := ((c + 1/2 : ℝ) : ℂ)) (Or.inr hz₀W₂) ?_
    have : {z : ℂ | c < z.re} ∈ 𝓝 (((c + 1/2 : ℝ) : ℂ)) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀W₂
    filter_upwards [this] with z hz using hFG z hz
  have hballW : ball (a : ℂ) r ⊆ W := by
    intro z hz
    left
    have hz' : ‖z - a‖ < r := by simpa [dist_eq_norm] using hz
    have h1 : |z.re - a| < r :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - a)) hz'
    have h2 : |z.im| < r :=
      lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (z - a)) hz'
    have h1' := abs_lt.mp h1
    have h2' := abs_lt.mp h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq] <;> linarith
  have hev : mellinK A 0 =ᶠ[𝓝 (a : ℂ)] G := by
    filter_upwards [ball_mem_nhds (a : ℂ) hr0] with z hz using hFW (hballW hz)
  -- Taylor expansion of `G` at `a`, evaluated at `a - 2r`
  have hzmem : ((a - 2 * r : ℝ) : ℂ) ∈ ball (a : ℂ) δ := by
    rw [mem_ball, dist_eq_norm,
      show ((a - 2 * r : ℝ) : ℂ) - (a : ℂ) = ((-(2 * r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball hGball hzmem
  set I : ℕ → ℝ := fun n => ∫ x in Ioi (1:ℝ), A x * Real.log x ^ n * x ^ (-a - 1) with hI
  have hterm : ∀ n : ℕ, (n.factorial : ℂ)⁻¹ • (((a - 2 * r : ℝ) : ℂ) - (a : ℂ)) ^ n •
      iteratedDeriv n G (a : ℂ) = (((2 * r) ^ n / n.factorial * I n : ℝ) : ℂ) := by
    intro n
    have hare : τ < (a : ℂ).re := by simp only [ofReal_re]; linarith
    rw [← hev.iteratedDeriv_eq n, iteratedDeriv_mellinK hA hright' n (a : ℂ) hare,
      mellinK_ofReal, show ((a - 2 * r : ℝ) : ℂ) - (a : ℂ) = ((-(2 * r) : ℝ) : ℂ) by
        push_cast; ring]
    simp only [smul_eq_mul]
    rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; ring,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have h1 : ((-1:ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [neg_pow]
    have e : ∀ X : ℝ, ((n.factorial : ℝ))⁻¹ * ((-1) ^ n * (2 * r) ^ n * ((-1) ^ n * X)) =
        (2 * r) ^ n / n.factorial * X := by
      intro X
      calc _ = ((n.factorial : ℝ))⁻¹ * (2 * r) ^ n * X * ((-1) ^ n * (-1) ^ n) := by ring
        _ = _ := by rw [h1]; ring
    exact e _
  have hsum : Summable (fun n : ℕ => (2 * r) ^ n / n.factorial * I n) := by
    have := htaylor.summable
    simp_rw [hterm] at this
    exact Complex.summable_ofReal.mp this
  have hconv := conv_of_summable hA hA0 (a := a) (t := 2 * r) (by positivity)
    (fun k => integrableOn_log_pow_of_nonneg hA hA0 (σ := (τ + a) / 2) (σ' := a) (by linarith)
      (hright _ (by linarith)) k) hsum
  exact hleft (a - 2 * r) (by linarith) hconv


end OneSidedLandauAux

theorem solution (A : ℝ → ℝ) (hA : Measurable A) (h0 : ∀ x, 1 < x → 0 ≤ A x)
    {θ c : ℝ} (hc : ∀ σ, c < σ → IntegrableOn (fun x : ℝ => A x * x ^ (-σ-1)) (Ioi 1))
    {G : ℂ → ℂ} {U : Set ℂ} (ho : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hu : ∀ s : ℂ, c < s.re → s ∈ U) (hr : ∀ t : ℝ, θ < t → (t : ℂ) ∈ U)
    (he : ∀ s : ℂ, c < s.re → transform A s = G s) :
    DifferentiableOn ℂ (transform A) {s : ℂ | θ < s.re} := by
  have eq : OneSidedLandauAux.mellinK A 0 = transform A := by
    funext s
    simp [OneSidedLandauAux.mellinK, transform]
  have h := OneSidedLandauAux.landau hA h0 hc ho hG hu hr (fun s hs => by rw [eq]; exact he s hs)
  rw [← eq]
  exact OneSidedLandauAux.differentiableOn_mellinK hA
    (fun t ht => OneSidedLandauAux.convAbs_of_conv h0 (h t ht)) 0

/- License for the attributed portions above.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
