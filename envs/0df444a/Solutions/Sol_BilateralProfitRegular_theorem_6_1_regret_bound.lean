-- Prove2me | solution 1 for BilateralProfitRegular.theorem_6_1_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T17:05:25.904727+00:00
-- url     : https://prove2.me/submissions/91c60e10-7398-4136-a73a-40f8092e8475

import Theorems.Thm_BilateralProfitRegular_eq_55
import Theorems.Thm_BilateralProfitRegular_eq_42
import Theorems.Thm_BilateralProfitRegular_eq_47
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_ConvexBandit
import Definitions.Def_BilateralProfitRegular_InitRegular
import Definitions.Def_BilateralProfitRegular_Refinement
import Theorems.Thm_BilateralProfitRegular_lemma_6_6
import Mathlib
import Definitions.Def_BilateralProfitRegular_Proc
import Theorems.Thm_BilateralProfitRegular_lemma_6_2
import Definitions.Def_BilateralProfitMHR_BinaryControl
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_BilateralProfitMHR_binary_controller_regret_bridge
import Mathlib.Probability.ProductMeasure
import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Theorems.Thm_BilateralProfitRegular_lemma_6_4


section BundlePart000






namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade BilateralProfit MeasureTheory

private theorem intT_subset_unitSq : intT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem onUnit_facts (E : Environment) (hE : OnUnit E) :
    (∀ a, 0 ≤ P E a ∧ P E a ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, P E a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, 0 < mu E a ↔ a ∈ intT) ∧
    (0 < muStar E ∧ muStar E ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, mu E a ≤ muStar E) ∧
    (∃ a ∈ intT, mu E a = muStar E) := by
  obtain ⟨_, _, hp, hf, _, _, _, _, hm, hs, hu, he, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  exact ⟨hp, hf, hm, hs, hu, he⟩

private theorem P_factor (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) :
    P E x = E.cdfS x.1 * (1 - E.cdfB x.2) :=
  (onUnit_facts E hE).2.1 x hx

private theorem mu_formula (E : Environment) (x : ℝ × ℝ) :
    mu E x = (x.2 - x.1) * P E x := rfl

private theorem mu_le_muStar (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) : mu E x ≤ muStar E :=
  (onUnit_facts E hE).2.2.2.2.1 x hx

private theorem cdfS_pos (E : Environment) (hE : OnUnit E) {p : ℝ} (hp : p ∈ Ioc 0 1) :
    0 < E.cdfS p := by
  have hf := E.fS_intervalIntegrable
  rw [hE.1, hE.2.1] at hf
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hp.1
  · apply hf.mono_set
    rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hp.2
  · intro t ht
    exact E.fS_pos t (by rw [hE.1, hE.2.1]; exact ⟨ht.1.le, ht.2.le.trans hp.2⟩)

private theorem tailB_eq_integral (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    1 - E.cdfB q = ∫ t in q..1, E.fB t := by
  have hf := E.fB_intervalIntegrable
  have ht := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at hf ht
  have h₁ := hf.mono_set (show uIcc 0 q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have h₂ := hf.mono_set (show uIcc q 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl)
  rw [Environment.cdfB, hE.2.2.1]
  linarith [intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private theorem tailB_pos (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Ico 0 1) :
    0 < 1 - E.cdfB q := by
  rw [tailB_eq_integral E hE ⟨hq.1, hq.2.le⟩]
  have hf := E.fB_intervalIntegrable
  rw [hE.2.2.1, hE.2.2.2] at hf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hq.2
  · apply hf.mono_set
    rw [uIcc_of_le hq.2.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl
  · intro t ht
    exact E.fB_pos t (by rw [hE.2.2.1, hE.2.2.2]; exact ⟨hq.1.trans ht.1.le, ht.2.le⟩)

private theorem intT_cdf_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < E.cdfS x.1 ∧ 0 < 1 - E.cdfB x.2 :=
  ⟨cdfS_pos E hE ⟨hx.1, (intT_subset_unitSq hx).1.2⟩,
    tailB_pos E hE ⟨(intT_subset_unitSq hx).2.1, hx.2.2⟩⟩

private theorem balance_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < balance E x :=
  Real.sqrt_pos.2 (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2)

private theorem balance_sq (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    balance E x ^ 2 = E.cdfS x.1 / (1 - E.cdfB x.2) :=
  Real.sq_sqrt (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2).le

private theorem auxProfit_pos (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < auxProfit E lam x := by
  have hm := intT_cdf_pos E hE hx
  unfold auxProfit
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hx.2.1))
    (pow_pos (add_pos (div_pos hlam hm.1) (div_pos (inv_pos.mpr hlam) hm.2)) _)

end BilateralProfitRegular
end BundlePart000


section BundlePart001


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have he : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  simpa only [← pow_two, Real.cosh_sq_sub_sinh_sq] using hd

private theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_tanh t).differentiableAt)
  intro t
  rw [(hasDerivAt_tanh t).deriv]
  change ‖(1 / Real.cosh t ^ 2 : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos (Real.cosh_pos t) _)).mpr
  nlinarith only [Real.one_le_cosh t, sq_nonneg (Real.cosh t - 1)]

private theorem sech_sq_add_tanh_sq (t : ℝ) :
    (2 / (Real.exp t + Real.exp (-t))) ^ 2 + Real.tanh t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  -- The exponential denominator is twice the hyperbolic cosine.
  have hc : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by rw [Real.cosh_eq]; ring
  rw [hc]
  have ht := (Real.cosh_pos t).ne'
  field_simp
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

private theorem auxProfit_sech (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    auxProfit E lam x =
      mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
        Real.exp (-Real.log (lam / balance E x)))) ^ 2 := by
  obtain ⟨hs, hb⟩ := intT_cdf_pos E hE hx
  have hl := balance_pos E hE hx
  have hsq := balance_sq E hE hx
  let t := Real.log (lam / balance E x)
  have he : Real.exp t + Real.exp (-t) = lam / balance E x + balance E x / lam := by
    rw [Real.exp_neg, show Real.exp t = lam / balance E x from Real.exp_log (div_pos hlam hl),
      inv_div]
  have hdivide :
      balance E x ^ 2 / E.cdfS x.1 = (1 - E.cdfB x.2)⁻¹ := by
    rw [hsq]
    field_simp [hs.ne']
  have hinv :
      lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2) =
        balance E x / E.cdfS x.1 * (Real.exp t + Real.exp (-t)) := by
    rw [he, mul_add]
    congr 1
    · field_simp
    · calc
        lam⁻¹ / (1 - E.cdfB x.2) = (balance E x ^ 2 / E.cdfS x.1) / lam := by
          rw [hdivide]
          ring
        _ = balance E x / E.cdfS x.1 * (balance E x / lam) := by ring
  have hnorm : (balance E x / E.cdfS x.1) ^ 2 = (E.cdfS x.1 * (1 - E.cdfB x.2))⁻¹ := by
    calc
      (balance E x / E.cdfS x.1) ^ 2 =
          (balance E x ^ 2 / E.cdfS x.1) / E.cdfS x.1 := by ring
      _ = _ := by rw [hdivide, mul_inv]; ring
  change auxProfit E lam x = mu E x * (2 / (Real.exp t + Real.exp (-t))) ^ 2
  rw [auxProfit, hinv, mul_pow, hnorm, mu_formula, P_factor E hE (intT_subset_unitSq hx),
    inv_mul_eq_div, div_div_eq_mul_div, div_pow]
  ring

private theorem auxProfit_tanh_gap (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) :
    mu E x - auxProfit E lam x = mu E x * Real.tanh (Real.log (lam / balance E x)) ^ 2 := by
  rw [auxProfit_sech E hE hlam hx]
  have he := sech_sq_add_tanh_sq (Real.log (lam / balance E x))
  nlinarith only [congrArg (fun t => mu E x * t) he]

private theorem auxProfit_values (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 ≤ mu E x - auxProfit E lam x ∧
    mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
    0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
    auxProfit E (balance E x) x = mu E x := by
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have he := auxProfit_tanh_gap E hE hlam hx
  have hg : 0 ≤ mu E x - auxProfit E lam x := he.symm ▸ mul_nonneg hmu.le (sq_nonneg _)
  refine ⟨hg, ?_, auxProfit_pos E hE hlam hx, sub_nonneg.mp hg, ?_⟩
  · rw [he]
    let t := Real.log (lam / balance E x)
    have hd : |Real.tanh t| ≤ |t| := by
      simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul t 0
    apply mul_le_mul_of_nonneg_left _ hmu.le
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Real.tanh t)) hd 2
  · have hb := balance_pos E hE hx
    have ht := auxProfit_tanh_gap E hE hb hx
    rw [div_self hb.ne', Real.log_one, Real.tanh_zero] at ht
    linarith

private theorem auxProfit_perturbation (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) (θ : ℝ) :
    muStar E - auxProfit E (lam * Real.exp θ) x ≤
      2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  let t := Real.log (lam / balance E x)
  have hb := balance_pos E hE hx
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have he : Real.log ((lam * Real.exp θ) / balance E x) = t + θ := by
    rw [mul_div_right_comm, Real.log_mul (div_pos hlam hb).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hgap := auxProfit_tanh_gap E hE (mul_pos hlam (Real.exp_pos θ)) hx
  rw [he] at hgap
  have hbase := auxProfit_tanh_gap E hE hlam hx
  change mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 at hbase
  have hdiff : |Real.tanh (t + θ) - Real.tanh t| ≤ |θ| := by
    simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul (t + θ) t
  have hsq : (Real.tanh (t + θ) - Real.tanh t)^2 ≤ θ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hsq' : Real.tanh (t + θ) ^ 2 ≤ 2 * Real.tanh t ^ 2 + 2 * θ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (Real.tanh (t + θ) - 2 * Real.tanh t)]
  have hquad := mul_le_mul_of_nonneg_left hsq' hmu.le
  have hscale := mul_le_mul_of_nonneg_right hmuStar (sq_nonneg θ)
  linarith only [hgap, hbase, hmuStar, hquad, hscale]

/-- High auxiliary profit bounds the logarithmic displacement of the balance. -/
private theorem auxProfit_implies_balance_bound (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) {d : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1)
    (hr : (1 - d ^ 2) * muStar E ≤ auxProfit E lam x) :
    |Real.log (balance E x / lam)| ≤ Real.artanh d := by
  let t := Real.log (lam / balance E x)
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have hd₂ : 0 ≤ 1 - d ^ 2 := by
    have hh := pow_le_pow_left₀ hd hd₁.le 2
    linarith only [hh]
  have hbase : mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 :=
    auxProfit_tanh_gap E hE hlam hx
  have hbound : Real.tanh t ^ 2 ≤ d ^ 2 := by
    apply le_of_mul_le_mul_left _ hmu
    linarith only [hbase, hr, mul_le_mul_of_nonneg_left hmuStar hd₂]
  rw [← sq_abs (Real.tanh t)] at hbound
  obtain ⟨htl, htr⟩ := abs_le.mp (le_of_pow_le_pow_left₀ (by decide) hd hbound)
  have htu : t ≤ Real.artanh d := by
    rw [← Real.artanh_tanh t]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh t) hd₁ htr
  have htl' : -t ≤ Real.artanh d := by
    have hneg : Real.tanh (-t) ≤ d := by rw [Real.tanh_neg]; linarith only [htl]
    rw [← Real.artanh_tanh (-t)]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh _) hd₁ hneg
  rw [← inv_div, Real.log_inv]
  exact abs_le.mpr ⟨by linarith only [htu], htl'⟩

/-- The offset interval used to form the regular candidates has a universal numerical bound. -/
private theorem regular_offset_halfwidth :
    0 < Real.artanh (1 / Real.sqrt 2000) ∧ Real.artanh (1 / Real.sqrt 2000) ≤ 1 / 40 := by
  let d := 1 / Real.sqrt 2000
  have hroot : 41 ≤ Real.sqrt 2000 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hpos : 0 < d := by dsimp [d]; positivity
  have hdu : d ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hroot
  have hdlt : d < 1 := by linarith only [hdu]
  change 0 < Real.artanh d ∧ Real.artanh d ≤ 1 / 40
  refine ⟨Real.artanh_pos ⟨hpos, hdlt⟩, ?_⟩
  have h1 : 0 < 1 - d := sub_pos.mpr hdlt
  have harg : 0 < (1 + d) / (1 - d) := div_pos (by linarith only [hpos]) h1
  rw [Real.artanh_eq_half_log ⟨by linarith only [hpos], hdlt.le⟩]
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquot : (1 + d) / (1 - d) - 1 ≤ 1 / 20 := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ h1).mpr
    linarith only [hdu]
  linarith only [hlog, hquot]

end BilateralProfitRegular
end BundlePart001


section BundlePart002


namespace BilateralProfitRegular.BanditAlg

open MeasureTheory ProbabilityTheory ENNReal Classical

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
variable (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω)

@[fun_prop]
private theorem measurable_snoc_pair {m : ℕ} :
    Measurable (fun p : (Fin m → X × ℝ) × (X × ℝ) => Fin.snoc (α := fun _ => X × ℝ) p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd :
      Measurable (Prod.snd : (Fin m → X × ℝ) × (X × ℝ) → X × ℝ))
  · simp only [Fin.snoc_castSucc]
    fun_prop

private theorem measurable_go (hν : ∀ τ, IsMarkovKernel (ν τ))
    {c : X → ℝ≥0∞} (hc : Measurable c)
    {f : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (hf : ∀ τ, Measurable (f τ))
    (k τ : ℕ) :
    Measurable (fun p : Ω × (Fin τ → X × ℝ) => alg.go ν c f k τ p.1 p.2) := by
  induction k generalizing τ with
  | zero =>
    exact (hf τ).comp measurable_snd
  | succ k ih =>
    simp only [go]
    let κ := (ν τ).comap (fun p : Ω × (Fin τ → X × ℝ) => (p.2, alg.query τ p.1 p.2))
      (measurable_snd.prodMk (alg.measurable_query τ))
    apply (hc.comp (alg.measurable_query τ)).add
    have hmap : Measurable (fun p : (Ω × (Fin τ → X × ℝ)) × ℝ =>
        (p.1.1, Fin.snoc (α := fun _ => X × ℝ) p.1.2 (alg.query τ p.1.1 p.1.2, p.2))) :=
      measurable_fst.fst.prodMk (measurable_snoc_pair.comp
        (measurable_fst.snd.prodMk (((alg.measurable_query τ).comp measurable_fst).prodMk
          measurable_snd)))
    have hm := Measurable.lintegral_kernel_prod_right' (κ := κ) ((ih (τ + 1)).comp hmap)
    simpa only [κ, Kernel.comap_apply, Function.comp_apply] using hm

private theorem go_zero_mono_on (K : Set X) (hK : alg.QueriesIn K)
    {f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (k τ : ℕ) (ω : Ω)
    (h : Fin τ → X × ℝ) (hh : ∀ i, (h i).1 ∈ K)
    (hfg : ∀ τ h, (∀ i, (h i).1 ∈ K) → f τ h ≤ g τ h) :
    alg.go ν 0 f k τ ω h ≤ alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero => simpa only [go] using hfg τ h hh
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    apply lintegral_mono
    intro v
    apply ih
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hK τ ω h
    · simpa only [Fin.snoc_castSucc] using hh j

private theorem measurable_terminal {n : ℕ} {f : (Fin n → X × ℝ) → ℝ≥0∞}
    (hf : Measurable f) (τ : ℕ) :
    Measurable (fun h : Fin τ → X × ℝ =>
      if hτ : τ = n then f (fun i => h (Fin.cast hτ.symm i)) else 0) := by
  split <;> rename_i h
  · subst τ
    simpa only [Fin.cast_eq_self] using hf
  · exact measurable_const

private theorem trajExp_mono_on (K : Set X) (hK : alg.QueriesIn K) {n : ℕ}
    {f g : (Fin n → X × ℝ) → ℝ≥0∞} (hfg : ∀ h, (∀ i, (h i).1 ∈ K) → f h ≤ g h) :
    alg.trajExp ν P n f ≤ alg.trajExp ν P n g := by
  unfold trajExp
  apply lintegral_mono
  intro ω
  apply alg.go_zero_mono_on ν K hK
  · exact fun i => i.elim0
  · intro τ h hh
    by_cases hτ : τ = n
    · simpa only [dif_pos hτ] using (hfg _ (fun i => hh (Fin.cast hτ.symm i)))
    · simp [hτ]

private theorem go_zero_const {f : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞}
    (hν : ∀ τ, IsMarkovKernel (ν τ))
    (d : ℝ≥0∞) (n k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ)
    (ht : k + τ = n) (hf : ∀ h, f n h = d) : alg.go ν 0 f k τ ω h = d := by
  induction k generalizing τ with
  | zero =>
    simp only [zero_add] at ht
    subst τ
    exact hf h
  | succ k ih =>
    have := hν τ
    have ht' : k + (τ + 1) = n := by omega
    simp only [go, Pi.zero_apply, zero_add, ih (τ + 1) _ ht', lintegral_const, measure_univ, mul_one]

private theorem trajExp_const (hν : ∀ τ, IsMarkovKernel (ν τ)) [IsProbabilityMeasure P]
    (n : ℕ) (d : ℝ≥0∞) : alg.trajExp ν P n (fun _ => d) = d := by
  unfold trajExp
  have hω : ∀ ω, alg.go ν 0 (fun τ _ => if τ = n then d else 0) n 0 ω Fin.elim0 = d :=
    fun ω => alg.go_zero_const ν hν d n n 0 ω Fin.elim0 (by simp) (by simp)
  simp only [dite_eq_ite]
  change ∫⁻ ω, alg.go ν 0 (fun τ _ => if τ = n then d else 0) n 0 ω Fin.elim0 ∂P = d
  simp only [hω, lintegral_const, measure_univ, mul_one]

private theorem go_zero_upper (k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ)
    (f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞) (a : ℝ≥0∞)
    (hf : ∀ τ, Measurable (f τ)) (hg : ∀ τ, Measurable (g τ))
    (hν : ∀ τ, IsMarkovKernel (ν τ)) :
    alg.go ν 0 (fun s h => a * f s h + g s h) k τ ω h ≤
      a * alg.go ν 0 f k τ ω h + alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero => rfl
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    refine (lintegral_mono (fun v => ih _ _)).trans ?_
    have hh : Measurable fun v : ℝ =>
        (ω, Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v)) := by
      apply measurable_const.prodMk
      exact measurable_snoc_pair.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hmf := (alg.measurable_go ν hν (c := 0) measurable_const hf k (τ + 1)).comp hh
    have hmg := (alg.measurable_go ν hν (c := 0) measurable_const hg k (τ + 1)).comp hh
    change Measurable (fun v => alg.go ν 0 f k (τ + 1) ω
      (Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v))) at hmf
    change Measurable (fun v => alg.go ν 0 g k (τ + 1) ω
      (Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v))) at hmg
    rw [lintegral_add_right _ hmg, lintegral_const_mul _ hmf]

private theorem trajExp_upper (hν : ∀ τ, IsMarkovKernel (ν τ))
    {n : ℕ} {f g : (Fin n → X × ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (a : ℝ≥0∞) :
    alg.trajExp ν P n (fun h => a * f h + g h) ≤
      a * alg.trajExp ν P n f + alg.trajExp ν P n g := by
  let F (τ : ℕ) (h : Fin τ → X × ℝ) :=
    if hτ : τ = n then f (fun i => h (Fin.cast hτ.symm i)) else 0
  let G (τ : ℕ) (h : Fin τ → X × ℝ) :=
    if hτ : τ = n then g (fun i => h (Fin.cast hτ.symm i)) else 0
  have hlift : (fun τ (h : Fin τ → X × ℝ) =>
      if hτ : τ = n then
        a * f (fun i => h (Fin.cast hτ.symm i)) + g (fun i => h (Fin.cast hτ.symm i))
      else 0) = fun τ h => a * F τ h + G τ h := by
    ext τ h
    by_cases ht : τ = n <;> simp [F, G, ht]
  unfold trajExp
  rw [hlift]
  let EF (ω : Ω) := alg.go ν 0 F n 0 ω Fin.elim0
  let EG (ω : Ω) := alg.go ν 0 G n 0 ω Fin.elim0
  calc
    _ ≤ ∫⁻ ω, a * EF ω + EG ω ∂P :=
      lintegral_mono fun ω => alg.go_zero_upper ν n 0 ω Fin.elim0 F G a
        (measurable_terminal hf) (measurable_terminal hg) hν
    _ = _ := by
      change _ = a * (∫⁻ ω, EF ω ∂P) + (∫⁻ ω, EG ω ∂P)
      rw [lintegral_add_right, lintegral_const_mul]
      · exact (alg.measurable_go ν hν (c := 0) measurable_const (measurable_terminal hf) n 0).comp
          (measurable_id.prodMk (measurable_const (a := Fin.elim0)))
      · exact (alg.measurable_go ν hν (c := 0) measurable_const (measurable_terminal hg) n 0).comp
          (measurable_id.prodMk (measurable_const (a := Fin.elim0)))

private theorem go_zero_mono_terminal
    {f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (n k τ : ℕ) (ω : Ω)
    (h : Fin τ → X × ℝ) (ht : k + τ = n) (hfg : ∀ h, f n h ≤ g n h) :
    alg.go ν 0 f k τ ω h ≤ alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero =>
    simp only [zero_add] at ht
    subst τ
    exact hfg h
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    exact lintegral_mono fun v => ih _ _ (by omega)

private theorem go_cost_sum (hν : ∀ τ, IsMarkovKernel (ν τ)) {c : X → ℝ≥0∞}
    (k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ) :
    alg.go ν 0 (fun τ h => ∑ i : Fin τ, c (h i).1) k τ ω h =
      (∑ i : Fin τ, c (h i).1) + alg.go ν c (fun _ _ => 0) k τ ω h := by
  induction k generalizing τ with
  | zero => simp [go]
  | succ k ih =>
    have := hν τ
    simp only [go, Pi.zero_apply, zero_add, ih, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, add_assoc]

private theorem trajExp_sum_eq_regret (hν : ∀ τ, IsMarkovKernel (ν τ)) {L : X → ℝ}
    (n : ℕ) (K : Set X) :
    alg.trajExp ν P n (fun h => ∑ i, ENNReal.ofReal (L (h i).1 - sInf (L '' K))) =
      alg.regret ν P n L K := by
  let c := fun x => ENNReal.ofReal (L x - sInf (L '' K))
  unfold trajExp regret
  apply lintegral_congr
  intro ω
  have hs := alg.go_cost_sum ν hν (c := c) n 0 ω Fin.elim0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hs
  rw [← hs]
  apply le_antisymm
  all_goals
    apply alg.go_zero_mono_terminal ν n n 0 ω Fin.elim0 (by simp)
    intro h
    simp [c]

end BilateralProfitRegular.BanditAlg
end BundlePart002


section BundlePart003



namespace BilateralProfitRegular

/-- The target accuracy as a function of the trading horizon. -/
private noncomputable def mainEta (T : ℕ) : ℝ := (T : ℝ) ^ (-(2 : ℝ) / 5)

/-- The logarithm used in the schedule. -/
private noncomputable def mainLog (T : ℕ) : ℝ := Real.log (2 * (T : ℝ))

private theorem mainEta_pos {T : ℕ} (hT : 2 ≤ T) : 0 < mainEta T :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _

private theorem mainEta_lt_one {T : ℕ} (hT : 2 ≤ T) : mainEta T < 1 := by
  have ht : (1 : ℝ) < T := by exact_mod_cast (show 1 < T by omega)
  unfold mainEta
  rw [← Real.rpow_zero (T : ℝ)]
  exact Real.rpow_lt_rpow_of_exponent_lt ht (by norm_num)

private theorem mainLog_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ mainLog T := by
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ 2 * T by linarith)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  change 1 ≤ Real.log (2 * (T : ℝ))
  linarith only [hh, h4, Real.log_two_gt_d9]

private theorem mainLog_le_two_log {T : ℕ} (hT : 2 ≤ T) :
    mainLog T ≤ 2 * Real.log (T : ℝ) := by
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have ht' : 0 < (T : ℝ) := by linarith
  unfold mainLog
  rw [Real.log_mul (by norm_num) ht'.ne']
  linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht]

private theorem mainEta_inv {T : ℕ} (_hT : 2 ≤ T) :
    1 / mainEta T = (T : ℝ) ^ ((2 : ℝ) / 5) := by
  unfold mainEta
  rw [show -(2 : ℝ) / 5 = -(2 / 5) by ring,
    Real.rpow_neg (Nat.cast_nonneg T), one_div, inv_inv]

private theorem mainEta_inv_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ 1 / mainEta T := by
  apply (le_div_iff₀ (mainEta_pos hT)).mpr
  simpa only [one_mul] using (mainEta_lt_one hT).le

private theorem mainEta_grid_le_T {T : ℕ} (hT : 2 ≤ T) : gridK (mainEta T) ≤ T := by
  change ⌈1 / mainEta T⌉₊ ≤ T
  apply Nat.ceil_le.mpr
  have hbase : 1 ≤ (T : ℝ) := by exact_mod_cast (show 1 ≤ T by omega)
  rw [mainEta_inv hT]
  simpa using (Real.rpow_le_rpow_of_exponent_le hbase (show (2 / 5 : ℝ) ≤ 1 by norm_num))

private theorem main_numCopies_bound {C₀ : ℝ} {T : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀) :
    1 ≤ numCopies C₀ T ∧ (numCopies C₀ T : ℝ) ≤ (C₀ + 1) * mainLog T := by
  have hL := mainLog_ge_one hT
  have hp : 0 < C₀ * mainLog T := mul_pos hC₀ (by linarith)
  change 0 < ⌈C₀ * mainLog T⌉₊ ∧ (⌈C₀ * mainLog T⌉₊ : ℝ) ≤ _
  exact ⟨Nat.ceil_pos.mpr hp, by linarith only [Nat.ceil_lt_add_one hp.le, hL]⟩

end BilateralProfitRegular
end BundlePart003


section BundlePart004






namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade

/-- The deterministic conditions checked before selecting an optimizer. -/
private def MainOptimizerFeasible (δ : ℝ) (K : Set (ℝ × ℝ)) (n : ℕ) : Prop :=
  0 < δ ∧ K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧ K ⊆ intT ∧ 1 ≤ n

/-- A choice of optimizer and seed law based only on its numerical parameters and region. -/
private structure MainOptimizerChoice (C₁ C δ : ℝ) (K : Set (ℝ × ℝ)) (n : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  seedLaw : @Measure Seed seedSpace
  seedProbability : @IsProbabilityMeasure Seed seedSpace seedLaw
  alg : @BanditAlg (ℝ × ℝ) Seed inferInstance seedSpace
  legal : alg.QueriesIn triT
  guarantee : MainOptimizerFeasible δ K n →
    alg.QueriesIn K ∧
      ∀ E : Environment, RegularUnit E → ∀ lam : ℝ, 0 < lam →
        (∀ x ∈ K, 99 / 100 * δ ≤ auxProfit E lam x ∧ auxProfit E lam x ≤ 6 * δ) →
        ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) K →
          ν.ValuesIn K (Set.Icc 0 (C₁ / δ)) →
          alg.regret ν seedLaw n (fun x => 1 / auxProfit E lam x) K ≤
            ENNReal.ofReal (C / δ * Real.sqrt n * Real.log (2 * n) ^ 2)
  fallback : ¬ MainOptimizerFeasible δ K n →
    ∀ τ ω h, alg.query τ ω h = (0, 0)

attribute [instance] MainOptimizerChoice.seedSpace MainOptimizerChoice.seedProbability

/-- Fix the constant in Eq. (55) before selecting any of the optimizers. -/
private noncomputable def mainOptimizerConstant (C₁ : ℝ) (hC₁ : 0 < C₁) : ℝ :=
  Classical.choose (eq_55 C₁ hC₁)

private theorem mainOptimizerConstant_pos {C₁ : ℝ} (hC₁ : 0 < C₁) :
    0 < mainOptimizerConstant C₁ hC₁ :=
  (Classical.choose_spec (eq_55 C₁ hC₁)).1

private theorem mainOptimizer_feasible_choice {C₁ δ : ℝ} (hC₁ : 0 < C₁)
    {K : Set (ℝ × ℝ)} {n : ℕ} (h : MainOptimizerFeasible δ K n) :
    Nonempty (MainOptimizerChoice C₁ (mainOptimizerConstant C₁ hC₁) δ K n) := by
  obtain ⟨hδ, hne, hcompact, hcv, hSub, hn⟩ := h
  have hExists := (Classical.choose_spec (eq_55 C₁ hC₁)).2 δ hδ K hne hcompact hcv hSub n hn
  obtain ⟨Ω, mΩ, P, hP, alg, hq, hreg⟩ := hExists
  refine ⟨{ Seed := Ω, seedSpace := mΩ, seedLaw := P, seedProbability := hP, alg := alg
            legal := ?_, guarantee := fun _ => ⟨hq, hreg⟩, fallback := ?_ }⟩
  · intro τ ω hist
    have hx := hSub (hq τ ω hist)
    exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  · exact fun hbad => (hbad ⟨hδ, hne, hcompact, hcv, hSub, hn⟩).elim

private noncomputable def mainOptimizer_fallback {C₁ C δ : ℝ} {K : Set (ℝ × ℝ)} {n : ℕ}
    (hbad : ¬ MainOptimizerFeasible δ K n) : MainOptimizerChoice C₁ C δ K n where
  Seed := Unit
  seedSpace := ⊤
  seedLaw := @Measure.dirac Unit ⊤ ()
  seedProbability := by infer_instance
  alg := { query := fun _ _ _ => (0,0), measurable_query := fun _ => measurable_const }
  legal := by intro τ ω h; norm_num [triT]
  guarantee := fun h => (hbad h).elim
  fallback := by intros; rfl

/-- Use the optimizer supplied by Eq. (55) when its deterministic hypotheses hold.
Every other geometry uses the price `(0,0)` at all queries. -/
private noncomputable def mainOptimizerChoice {C₁ : ℝ} (hC₁ : 0 < C₁)
    (δ : ℝ) (K : Set (ℝ × ℝ)) (n : ℕ) :
    MainOptimizerChoice C₁ (mainOptimizerConstant C₁ hC₁) δ K n := by
  classical
  exact if h : MainOptimizerFeasible δ K n then
    Classical.choice (mainOptimizer_feasible_choice hC₁ h) else mainOptimizer_fallback h

/-- A valid calibrated parameter inherits the auxiliary-profit bounds required by Eq. (55). -/
private theorem mainCalib_safe_auxProfit {E : Environment} {η δ : ℝ} {c : Candidate}
    {z : ℝ × ℝ} {ρ : ℝ} (hE : RegularUnit E) (hη : 0 < η) (hηδ : η < δ)
    (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6 * δ)
    (hc : c.Valid E δ) (hz : z ∈ c.region) (hCalib : CalibValid E η δ c z ρ) :
    0 < ρ * balance E z ∧ ∀ x ∈ c.region,
      99 / 100 * δ ≤ auxProfit E (ρ * balance E z) x ∧ auxProfit E (ρ * balance E z) x ≤ 6 * δ := by
  have hparam : 0 < c.param E :=
    mul_pos (Real.exp_pos _) (balance_pos E hE.1 (hc.1 hc.2.2.2.1))
  have hlam : 0 < ρ * balance E z := mul_pos hCalib.1 (balance_pos E hE.1 (hc.1 hz))
  let u := Real.log (ρ * balance E z / c.param E)
  have hδ : 0 < δ := hη.trans hηδ
  have hroot : Real.sqrt (η / δ) ≤ 1 := by
    have hh := Real.sqrt_le_sqrt ((div_le_one hδ).2 hηδ.le)
    simpa only [Real.sqrt_one] using hh
  have hu : |u| ≤ 1 / 1000 :=
    hCalib.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 1/1000))
  have he : c.param E * Real.exp u = ρ * balance E z := by
    rw [show Real.exp u = ρ * balance E z / c.param E from Real.exp_log (div_pos hlam hparam),
      mul_comm, div_mul_cancel₀ _ hparam.ne']
  refine ⟨hlam, fun x hx => ⟨?_, ?_⟩⟩
  · have hb := hc.2.2.2.2.1 u hu x hx
    rw [he] at hb
    exact (mul_le_mul_of_nonneg_left hδopt (by norm_num)).trans hb
  · have h := ((auxProfit_values E hE.1 hlam (hc.1 hx)).2.2.2.1).trans
      (mu_le_muStar E hE.1 (intT_subset_unitSq (hc.1 hx)))
    exact h.trans hoptδ.le

end BilateralProfitRegular
end BundlePart004


section BundlePart005




namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade

private abbrev MainPhaseReport (N : ℕ) := Fin N → ℝ × (ℝ × ℝ) × ℝ
private abbrev MainPhaseState (N : ℕ) := Finset (Fin N) × (Fin N → ℝ × ℝ)

/-- Initially all candidates are active at their root prices. -/
private def mainPhaseStart (cs : List Candidate) : MainPhaseState cs.length :=
  (Finset.univ, fun i => (cs.get i).root)

/-- Retain candidates within the elimination tolerance of every active candidate, then
update the references of the survivors. -/
private noncomputable def mainPhaseUpdate {N : ℕ} (η δ : ℝ) (j : ℕ)
    (s : MainPhaseState N) (R : MainPhaseReport N) : MainPhaseState N := by
  classical
  let survivors := s.1.filter fun i => ∀ l ∈ s.1, (R l).2.2 - 10 * (η + acc δ j) ≤ (R i).2.2
  exact (survivors, fun i => if i ∈ survivors then (R i).2.1 else s.2 i)

private theorem mainPhaseUpdate_mem {N : ℕ} (η δ : ℝ) (j : ℕ)
    (s : MainPhaseState N) (R : MainPhaseReport N) (i : Fin N) :
    i ∈ (mainPhaseUpdate η δ j s R).1 ↔
      i ∈ s.1 ∧ ∀ l ∈ s.1, (R l).2.2 - 10 * (η + acc δ j) ≤ (R i).2.2 := by
  classical
  simp only [mainPhaseUpdate, Finset.mem_filter]

private theorem mainPhaseUpdate_ref {N : ℕ} (η δ : ℝ) (j : ℕ)
    (s : MainPhaseState N) (R : MainPhaseReport N) (i : Fin N)
    (hi : i ∈ (mainPhaseUpdate η δ j s R).1) :
    (mainPhaseUpdate η δ j s R).2 i = (R i).2.1 := by
  classical
  exact if_pos hi

private theorem mainPhaseUpdate_inactive_ref {N : ℕ} (η δ : ℝ) (j : ℕ)
    (s : MainPhaseState N) (R : MainPhaseReport N) (i : Fin N)
    (hi : i ∉ (mainPhaseUpdate η δ j s R).1) :
    (mainPhaseUpdate η δ j s R).2 i = s.2 i := by
  classical
  exact if_neg hi

private theorem measurable_mainPhaseUpdate {N : ℕ} (η δ : ℝ) (j : ℕ) :
    Measurable (fun p : MainPhaseState N × MainPhaseReport N =>
      mainPhaseUpdate η δ j p.1 p.2) := by
  have hsurvive : Measurable (fun p : MainPhaseState N × MainPhaseReport N =>
      (mainPhaseUpdate η δ j p.1 p.2).1) := by
    apply measurable_finset_iff.mpr
    intro i
    simp only [mainPhaseUpdate_mem]
    refine ((measurable_finset_mem i).comp measurable_fst.fst).and (Measurable.forall fun l => ?_)
    refine ((measurable_finset_mem l).comp measurable_fst.fst).imp ?_
    exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) (by fun_prop))
  refine hsurvive.prodMk (measurable_pi_lambda _ fun i => ?_)
  have hm := (measurable_finset_mem i).comp hsurvive
  have hpj : Measurable (fun p : MainPhaseState N × MainPhaseReport N => (p.2 i).2.1) := by
    fun_prop
  have hpr : Measurable (fun p : MainPhaseState N × MainPhaseReport N => p.1.2 i) := by
    fun_prop
  classical
  let Q (p : MainPhaseState N × MainPhaseReport N) : Prop :=
    i ∈ (mainPhaseUpdate η δ j p.1 p.2).1
  let decQ : DecidablePred Q := fun p => Classical.propDecidable (Q p)
  have hQ : MeasurableSet {p | Q p} := measurableSet_setOfPred.mpr hm
  have heq :
      (fun p : MainPhaseState N × MainPhaseReport N => (mainPhaseUpdate η δ j p.1 p.2).2 i) =
      (fun p : MainPhaseState N × MainPhaseReport N => if Q p then (p.2 i).2.1 else p.1.2 i) := by
    funext p
    by_cases h : Q p
    · exact (mainPhaseUpdate_ref η δ j p.1 p.2 i h).trans (if_pos h).symm
    · exact (mainPhaseUpdate_inactive_ref η δ j p.1 p.2 i h).trans (if_neg h).symm
  change Measurable (fun p : MainPhaseState N × MainPhaseReport N => (mainPhaseUpdate η δ j p.1 p.2).2 i)
  rw [heq]
  exact hpj.ite hQ hpr

/-- State at the beginning of a phase, obtained by processing exactly the preceding reports. -/
private noncomputable def mainPhaseTimeline (η δ : ℝ) (cs : List Candidate)
    (H : ℕ → MainPhaseReport cs.length) : ℕ → MainPhaseState cs.length
  | 0 => mainPhaseStart cs
  | j + 1 => mainPhaseUpdate η δ j (mainPhaseTimeline η δ cs H j) (H j)

private theorem mainPhaseTimeline_congr {η δ : ℝ} {cs : List Candidate}
    {H H' : ℕ → MainPhaseReport cs.length} {j : ℕ}
    (h : ∀ k < j, H k = H' k) :
    mainPhaseTimeline η δ cs H j = mainPhaseTimeline η δ cs H' j := by
  induction j with
  | zero => rfl
  | succ k ih =>
    simp only [mainPhaseTimeline]
    rw [ih (fun l hl => h l (Nat.lt_succ_of_lt hl)), h k (Nat.lt_succ_self k)]

@[fun_prop]
private theorem measurable_mainPhaseTimeline (η δ : ℝ) (cs : List Candidate) (j : ℕ) :
    Measurable (fun H : ℕ → MainPhaseReport cs.length => mainPhaseTimeline η δ cs H j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact (measurable_mainPhaseUpdate η δ j).comp (ih.prodMk (measurable_pi_apply j))

private theorem measurable_mainPhaseActive (η δ : ℝ) (cs : List Candidate) (j : ℕ) :
    Measurable (fun H : ℕ → MainPhaseReport cs.length => (mainPhaseTimeline η δ cs H j).1) :=
  measurable_fst.comp (measurable_mainPhaseTimeline η δ cs j)

private theorem measurable_mainPhaseRef (η δ : ℝ) (cs : List Candidate) (j : ℕ) (i : Fin cs.length) :
    Measurable (fun H : ℕ → MainPhaseReport cs.length => (mainPhaseTimeline η δ cs H j).2 i) :=
  (measurable_pi_apply i).comp (measurable_snd.comp (measurable_mainPhaseTimeline η δ cs j))

/-- A phase report is clean when its calibration and refinement conclusions hold on every
active candidate. -/
private def MainPhaseReportClean (E : Environment) (η δ : ℝ) (cs : List Candidate) (j : ℕ)
    (s : MainPhaseState cs.length) (R : MainPhaseReport cs.length) : Prop :=
  ∀ i ∈ s.1,
    CalibValid E η δ (cs.get i) (s.2 i) (R i).1 ∧
    (R i).2.1 ∈ (cs.get i).region ∧
    (∀ x ∈ (cs.get i).region,
      auxProfit E ((R i).1 * balance E (s.2 i)) x - acc δ j ≤ (R i).2.2) ∧
    (R i).2.2 ≤ auxProfit E ((R i).1 * balance E (s.2 i)) (R i).2.1 + acc δ j

/-- Cleanliness of the reports preceding phase `j`. -/
private def MainPhaseClean (E : Environment) (η δ : ℝ) (cs : List Candidate)
    (H : ℕ → MainPhaseReport cs.length) (j : ℕ) : Prop :=
  ∀ k < j, MainPhaseReportClean E η δ cs k (mainPhaseTimeline η δ cs H k) (H k)

private theorem mainPhaseClean_succ {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {H : ℕ → MainPhaseReport cs.length} {j : ℕ} :
    MainPhaseClean E η δ cs H (j + 1) ↔
      MainPhaseClean E η δ cs H j ∧
        MainPhaseReportClean E η δ cs j (mainPhaseTimeline η δ cs H j) (H j) := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h j (Nat.lt_succ_self j)⟩
  · rintro ⟨h, hj⟩ k hk
    obtain hlt | rfl := Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk)
    · exact h k hlt
    · exact hj

/-- Deterministic invariant at the start of a phase. It includes phase zero. -/
private theorem mainPhaseTimeline_guarantee {E : Environment} {η δ : ℝ} {cs : List Candidate}
    (hE : RegularUnit E) (hη : 0 < η) (hη₁ : η < 1) (hηδ : η < δ)
    (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6 * δ)
    (hValid : ∀ i : Fin cs.length, (cs.get i).Valid E δ)
    (istar : Fin cs.length) (hNear : (cs.get istar).NearOpt E η δ)
    (H : ℕ → MainPhaseReport cs.length) (j : ℕ) (hClean : MainPhaseClean E η δ cs H j) :
    let s := mainPhaseTimeline η δ cs H j
    istar ∈ s.1 ∧ (∀ i ∈ s.1, s.2 i ∈ (cs.get i).region) ∧
      ∀ i ∈ s.1, ∀ ρ' : ℝ, CalibValid E η δ (cs.get i) (s.2 i) ρ' →
        muStar E - auxProfit E (ρ' * balance E (s.2 i)) (s.2 i) ≤ 65 * (η + acc δ j) := by
  let A k := (mainPhaseTimeline η δ cs H k).1
  let z k := (mainPhaseTimeline η δ cs H k).2
  let y (k : ℕ) (i : Fin cs.length) := (H k i).2.1
  let ρ (k : ℕ) (i : Fin cs.length) := (H k i).1
  let rhat (k : ℕ) (i : Fin cs.length) := (H k i).2.2
  have hstep (k : ℕ) (i : Fin cs.length) :
      i ∈ A (k + 1) ↔ i ∈ A k ∧ ∀ l ∈ A k, rhat k l - 10 * (η + acc δ k) ≤ rhat k i :=
    mainPhaseUpdate_mem η δ k (mainPhaseTimeline η δ cs H k) (H k) i
  have href (k : ℕ) (i : Fin cs.length) (hi : i ∈ A (k+1)) : z (k+1) i = y k i :=
    mainPhaseUpdate_ref η δ k (mainPhaseTimeline η δ cs H k) (H k) i hi
  have helim := lemma_6_6.2 η hη hη₁ E hE δ cs.length cs.get hηδ hδopt hoptδ hValid
    istar hNear A z y ρ rhat rfl (fun _ => rfl) hstep href
  cases j with
  | zero =>
    change istar ∈ Finset.univ ∧
      (∀ i ∈ Finset.univ, (cs.get i).root ∈ (cs.get i).region) ∧ _
    exact ⟨Finset.mem_univ _, fun i _ => (hValid i).2.2.2.1, fun i _ => helim.1 i⟩
  | succ k =>
    have hgood := helim.2 k (fun k' hk' => hClean k' (Nat.lt_succ_of_le hk'))
    refine ⟨hgood.1, ?_, hgood.2⟩
    intro i hi
    change z (k+1) i ∈ (cs.get i).region
    rw [href k i hi]
    exact (hClean k (Nat.lt_succ_self k) i ((hstep k i).mp hi).1).2.1

/-- Terminal regret of any survivor. The exact multiplier is used only in the proof. -/
private theorem mainPhaseTimeline_actual_gap {E : Environment} {η δ : ℝ} {cs : List Candidate}
    (hE : RegularUnit E) (hη : 0 < η) (hη₁ : η < 1) (hηδ : η < δ)
    (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6 * δ)
    (hValid : ∀ i : Fin cs.length, (cs.get i).Valid E δ)
    (istar : Fin cs.length) (hNear : (cs.get istar).NearOpt E η δ)
    (H : ℕ → MainPhaseReport cs.length) (j : ℕ) (hClean : MainPhaseClean E η δ cs H j)
    (i : Fin cs.length) (hi : i ∈ (mainPhaseTimeline η δ cs H j).1) :
    muStar E - mu E ((mainPhaseTimeline η δ cs H j).2 i) ≤ 65 * (η + acc δ j) := by
  let z := (mainPhaseTimeline η δ cs H j).2 i
  let c := cs.get i
  have h := mainPhaseTimeline_guarantee hE hη hη₁ hηδ hδopt hoptδ hValid istar hNear H j hClean
  have hz := (hValid i).1 (h.2.1 i hi)
  have hbz := balance_pos E hE.1 hz
  have hparam : 0 < c.param E :=
    mul_pos (Real.exp_pos _) (balance_pos E hE.1 ((hValid i).1 (hValid i).2.2.2.1))
  let ρ := c.param E / balance E z
  have heq : ρ * balance E z = c.param E := div_mul_cancel₀ _ hbz.ne'
  have hCalib : CalibValid E η δ c z ρ := by
    refine ⟨div_pos hparam hbz, ?_⟩
    rw [heq, div_self hparam.ne', Real.log_one, abs_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hg := h.2.2 i hi ρ hCalib
  change muStar E - auxProfit E (ρ * balance E z) z ≤ _ at hg
  rw [heq] at hg
  have hlu : auxProfit E (c.param E) z ≤ mu E z := (auxProfit_values E hE.1 hparam hz).2.2.2.1
  exact (sub_le_sub_left hlu _).trans hg

end BilateralProfitRegular
end BundlePart005


section BundlePart006


namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade

private instance mainOptionFinMeasurable (N : ℕ) : MeasurableSpace (Option (Fin N)) := ⊤

private instance mainOptionFinDiscrete (N : ℕ) : DiscreteMeasurableSpace (Option (Fin N)) :=
  (inferInstance : @DiscreteMeasurableSpace (Option (Fin N)) ⊤)

/-- Select the least index in a finite set, and return none for the empty set. -/
private noncomputable def mainPhaseMin {N : ℕ} (s : Finset (Fin N)) : Option (Fin N) := by
  classical
  exact if h : s.Nonempty then some (s.min' h) else none

private theorem mainPhaseMin_exists {N : ℕ} {s : Finset (Fin N)} (hs : s.Nonempty) :
    ∃ i ∈ s, mainPhaseMin s = some i := by
  classical
  exact ⟨s.min' hs, Finset.min'_mem s hs, dif_pos hs⟩

private theorem mainPhaseMin_mem {N : ℕ} {s : Finset (Fin N)} {i : Fin N}
    (hi : mainPhaseMin s = some i) : i ∈ s := by
  classical
  unfold mainPhaseMin at hi
  split at hi
  · have heq := Option.some.inj hi
    rw [← heq]
    apply Finset.min'_mem
  · simp at hi

@[fun_prop]
private theorem measurable_mainPhaseMin {N : ℕ} : Measurable (@mainPhaseMin N) :=
  measurable_of_countable _

private noncomputable def mainPhaseExploitRaw {N : ℕ} (s : MainPhaseState N) : ℝ × ℝ :=
  match mainPhaseMin s.1 with
  | some i => s.2 i
  | none => (0,0)

private theorem measurable_mainPhaseExploitRaw {N : ℕ} : Measurable (@mainPhaseExploitRaw N) := by
  apply measurable_from_prod_countable_right
  intro A
  change Measurable (fun y : Fin N → ℝ × ℝ =>
    match mainPhaseMin A with | some i => y i | none => (0,0))
  cases mainPhaseMin A with
  | none => exact measurable_const
  | some i => exact measurable_pi_apply i

private theorem measurableSet_mainTri : MeasurableSet triT :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

/-- Exploit the least surviving reference, with a legal fallback for empty or invalid states. -/
private noncomputable def mainPhaseExploit {N : ℕ} (s : MainPhaseState N) : ℝ × ℝ := by
  classical
  exact if mainPhaseExploitRaw s ∈ triT then mainPhaseExploitRaw s else (0,0)

private theorem mainPhaseExploit_eq_ref {N : ℕ} {s : MainPhaseState N} {i : Fin N}
    (hi : mainPhaseMin s.1 = some i) (href : s.2 i ∈ triT) : mainPhaseExploit s = s.2 i := by
  classical
  unfold mainPhaseExploit mainPhaseExploitRaw
  rw [hi]
  exact if_pos href

private theorem mainPhaseExploit_legal {N : ℕ} (s : MainPhaseState N) :
    mainPhaseExploit s ∈ triT := by
  classical
  unfold mainPhaseExploit
  split
  · assumption
  · norm_num [triT]

private theorem mainPhaseExploit_square {N : ℕ} (s : MainPhaseState N) :
    mainPhaseExploit s ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  have h := mainPhaseExploit_legal s
  exact ⟨⟨h.1, h.2.1.trans h.2.2⟩, ⟨h.1.trans h.2.1, h.2.2⟩⟩

@[fun_prop]
private theorem measurable_mainPhaseExploit {N : ℕ} : Measurable (@mainPhaseExploit N) := by
  classical
  exact measurable_mainPhaseExploitRaw.ite
    (measurable_mainPhaseExploitRaw measurableSet_mainTri) measurable_const

private theorem mainPhaseExploit_actual_gap {E : Environment} {η δ : ℝ} {cs : List Candidate}
    (hE : RegularUnit E) (hη : 0 < η) (hη₁ : η < 1) (hηδ : η < δ)
    (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6 * δ)
    (hValid : ∀ i : Fin cs.length, (cs.get i).Valid E δ)
    (istar : Fin cs.length) (hNear : (cs.get istar).NearOpt E η δ)
    (H : ℕ → MainPhaseReport cs.length) (j : ℕ) (hClean : MainPhaseClean E η δ cs H j) :
    muStar E - mu E (mainPhaseExploit (mainPhaseTimeline η δ cs H j)) ≤ 65 * (η + acc δ j) := by
  let s := mainPhaseTimeline η δ cs H j
  have hInv := mainPhaseTimeline_guarantee hE hη hη₁ hηδ hδopt hoptδ hValid istar hNear H j hClean
  obtain ⟨i, hi, hsel⟩ := mainPhaseMin_exists (s := s.1) ⟨istar, hInv.1⟩
  have href := (hValid i).1 (hInv.2.1 i hi)
  have htri : s.2 i ∈ triT := ⟨href.1.le, href.2.1.le, href.2.2.le⟩
  change muStar E - mu E (mainPhaseExploit s) ≤ _
  rw [mainPhaseExploit_eq_ref hsel htri]
  exact mainPhaseTimeline_actual_gap hE hη hη₁ hηδ hδopt hoptδ hValid istar hNear H j hClean i hi

private abbrev MainRefineTrajs (M n : ℕ) := Fin M → Fin n → (ℝ × ℝ) × ℝ
private abbrev MainRefinementEntry := ℝ × (ℝ × ℝ) × ℝ

@[fun_prop]
private theorem measurable_mainAvgObs {n : ℕ} :
    Measurable (avgObs : (Fin n → (ℝ × ℝ) × ℝ) → ℝ) := by
  unfold avgObs
  fun_prop

@[fun_prop]
private theorem measurable_mainAvgQuery {n : ℕ} :
    Measurable (avgQuery : (Fin n → (ℝ × ℝ) × ℝ) → ℝ × ℝ) := by
  unfold avgQuery
  fun_prop

@[fun_prop]
private theorem measurable_mainRhat (δ : ℝ) : Measurable (rhatOf δ) := by
  unfold rhatOf
  fun_prop

/-- All optimizer copies which attain the smallest empirical average loss. -/
private noncomputable def mainRefinementMinimizers {M n : ℕ} (hs : MainRefineTrajs M n) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun m => ∀ ℓ, avgObs (hs m) ≤ avgObs (hs ℓ))

private theorem mainRefinementMinimizers_mem {M n : ℕ} (hs : MainRefineTrajs M n) (m : Fin M) :
    m ∈ mainRefinementMinimizers hs ↔ ∀ ℓ, avgObs (hs m) ≤ avgObs (hs ℓ) := by
  classical
  simp [mainRefinementMinimizers]

private theorem mainRefinementMinimizers_nonempty {M n : ℕ} (hM : 0 < M) (hs : MainRefineTrajs M n) :
    (mainRefinementMinimizers hs).Nonempty := by
  classical
  have hN : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0,hM⟩, Finset.mem_univ _⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ (fun m => avgObs (hs m)) hN
  exact ⟨m, (mainRefinementMinimizers_mem hs m).mpr (fun ℓ => hm ℓ (Finset.mem_univ _))⟩

@[fun_prop]
private theorem measurable_mainRefinementMinimizers {M n : ℕ} :
    Measurable (@mainRefinementMinimizers M n) := by
  apply measurable_finset_iff.mpr
  intro m
  simp only [mainRefinementMinimizers_mem]
  apply Measurable.forall
  intro ℓ
  exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) (by fun_prop))

private noncomputable def mainRefinementFromPick {M n : ℕ} (δ : ℝ) (o : Option (Fin M))
    (ρ : ℝ) (hs : MainRefineTrajs M n) : MainRefinementEntry :=
  match o with
  | some m => (ρ, avgQuery (hs m), rhatOf δ (avgObs (hs m)))
  | none => (ρ, (0,0), 0)

/-- Turn completed copy trajectories into a report using the least empirical minimizer. -/
private noncomputable def mainRefinementReport {M n : ℕ} (δ ρ : ℝ)
    (hs : MainRefineTrajs M n) : MainRefinementEntry :=
  mainRefinementFromPick δ (mainPhaseMin (mainRefinementMinimizers hs)) ρ hs

private theorem measurable_mainRefinementFromPick {M n : ℕ} (δ : ℝ) :
    Measurable (fun p : Option (Fin M) × (ℝ × MainRefineTrajs M n) =>
      mainRefinementFromPick δ p.1 p.2.1 p.2.2) := by
  apply measurable_from_prod_countable_right
  intro o
  cases o with
  | none =>
    exact measurable_fst.prodMk measurable_const
  | some m =>
    change Measurable (fun p : ℝ × MainRefineTrajs M n =>
      (p.1, avgQuery (p.2 m), rhatOf δ (avgObs (p.2 m))))
    fun_prop

@[fun_prop]
private theorem measurable_mainRefinementReport {M n : ℕ} (δ : ℝ) :
    Measurable (fun p : ℝ × MainRefineTrajs M n => mainRefinementReport δ p.1 p.2) := by
  have hp : Measurable (fun p : ℝ × MainRefineTrajs M n =>
      mainPhaseMin (mainRefinementMinimizers p.2)) := by fun_prop
  exact (measurable_mainRefinementFromPick δ).comp (hp.prodMk measurable_id)

private theorem mainRefinementReport_rho {M n : ℕ} (δ ρ : ℝ) (hs : MainRefineTrajs M n) :
    (mainRefinementReport δ ρ hs).1 = ρ := by
  unfold mainRefinementReport
  cases mainPhaseMin (mainRefinementMinimizers hs) <;> rfl

private theorem mainRefinementReport_good {M n : ℕ} {E : Environment} {lam δ ε ρ : ℝ}
    {K : Set (ℝ × ℝ)} (hM : 0 < M) {hs : MainRefineTrajs M n}
    (h : RefineGood E lam δ ε K hs) :
    let R := mainRefinementReport δ ρ hs
    R.2.1 ∈ K ∧ (∀ x ∈ K, auxProfit E lam x - ε ≤ R.2.2) ∧
      R.2.2 ≤ auxProfit E lam R.2.1 + ε := by
  obtain ⟨m, hm, hpick⟩ := mainPhaseMin_exists (mainRefinementMinimizers_nonempty hM hs)
  have hh := h m ((mainRefinementMinimizers_mem hs m).mp hm)
  dsimp only
  unfold mainRefinementReport
  rw [hpick]
  exact hh

private theorem mainPhaseReportClean_of_refineGood {M n : ℕ} {E : Environment} {η δ : ℝ}
    {cs : List Candidate} {j : ℕ} {s : MainPhaseState cs.length}
    (ρ : Fin cs.length → ℝ) (hs : Fin cs.length → MainRefineTrajs M n)
    (hM : 0 < M)
    (h : ∀ i ∈ s.1, CalibValid E η δ (cs.get i) (s.2 i) (ρ i) ∧
      RefineGood E (ρ i * balance E (s.2 i)) δ (acc δ j) (cs.get i).region (hs i)) :
    MainPhaseReportClean E η δ cs j s (fun i => mainRefinementReport δ (ρ i) (hs i)) := by
  intro i hi
  change CalibValid E η δ (cs.get i) (s.2 i) (mainRefinementReport δ (ρ i) (hs i)).1 ∧ _
  rw [mainRefinementReport_rho]
  exact ⟨(h i hi).1, mainRefinementReport_good hM (h i hi).2⟩

end BilateralProfitRegular
end BundlePart006


section BundlePart007


namespace BilateralProfitRegular.Factory

/-- The upper endpoint of the walk at stage `j`. -/
private def boundary (j : ℕ) : ℕ := 24 * 2 ^ j

/-- The multiplier of the target odds at stage `j`. -/
private noncomputable def scale (j : ℕ) : ℝ := 3 / 2 - 1 / (2 * 2 ^ j)

@[simp]
private theorem boundary_succ (j : ℕ) : boundary (j + 1) = 2 * boundary j := by
  simp only [boundary, pow_succ]
  ring

private theorem boundary_pos (j : ℕ) : 0 < boundary j := by unfold boundary; positivity

@[simp]
private theorem scale_zero : scale 0 = 1 := by norm_num [scale]

private theorem scale_one_le (j : ℕ) : 1 ≤ scale j := by
  have h : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  unfold scale
  have h' : 1 / (2 * (2 : ℝ) ^ j) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

private theorem scale_le (j : ℕ) : scale j ≤ 3 / 2 := by
  unfold scale
  have : 0 ≤ 1 / (2 * (2 : ℝ) ^ j) := by positivity
  linarith

private theorem scale_pos (j : ℕ) : 0 < scale j := lt_of_lt_of_le zero_lt_one (scale_one_le j)

private theorem scale_succ_sub (j : ℕ) : scale (j + 1) - scale j = 1 / (4 * 2 ^ j) := by
  unfold scale
  rw [pow_succ]
  have h : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

/-- Probability of reaching the next stage, conditional on reaching the upper endpoint. -/
private noncomputable def survival (j : ℕ) : ℝ := (scale j / scale (j + 1)) ^ boundary j

private theorem survival_nonneg (j : ℕ) : 0 ≤ survival j := by
  unfold survival
  exact pow_nonneg (div_nonneg (scale_pos j).le (scale_pos (j + 1)).le) _

private theorem survival_le (j : ℕ) : survival j ≤ 1 / 5 := by
  have hpos := scale_pos j
  have hpos' := scale_pos (j + 1)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hdelta : 1 / (6 * 2 ^ j) ≤ scale (j + 1) / scale j - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hpos, add_mul, one_mul]
    rw [← le_sub_iff_add_le, scale_succ_sub]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ j)).mpr
    calc
      1 / (6 * (2 : ℝ) ^ j) * scale j * (4 * 2 ^ j)
        = scale j * (2 / 3) := by field_simp; ring
      _ ≤ 1 := by linarith [scale_le j]
  have hd : 0 ≤ scale (j + 1) / scale j - 1 :=
    (by positivity : 0 ≤ 1 / (6 * (2 : ℝ) ^ j)).trans hdelta
  have hBern := one_add_mul_le_pow (by linarith : -2 ≤ scale (j + 1) / scale j - 1) (boundary j)
  have hb : (5 : ℝ) ≤ (scale (j + 1) / scale j) ^ boundary j := by
    calc
      5 = 1 + (boundary j : ℝ) * (1 / (6 * (2 : ℝ) ^ j)) := by
        simp only [boundary, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
        ring
      _ ≤ 1 + (boundary j : ℝ) * (scale (j + 1) / scale j - 1) := by gcongr
      _ ≤ _ := by simpa using hBern
  rw [survival, ← inv_div, inv_pow, one_div]
  exact (inv_le_inv₀ (pow_pos (div_pos hpos' hpos) _) (by norm_num)).2 hb

/-- States are completed answers or a stage and a walk position. -/
private abbrev State := Bool ⊕ (ℕ × ℕ)

private def admissible : State → Prop
  | .inl _ => True
  | .inr (j, k) => 0 < k ∧ k < boundary j

/-- Downward moves hit the successful endpoint at zero. -/
private def down (j k : ℕ) : State :=
  if k = 1 then .inl true else .inr (j, k - 1)

/-- Upward moves reaching the upper endpoint either go up a stage or terminate. -/
private def up (j k : ℕ) : State :=
  if k + 1 = boundary j then .inr (j + 1, k + 1) else .inr (j, k + 1)

private noncomputable def continueUp (j k : ℕ) : ℝ :=
  if k + 1 = boundary j then survival j else 1

private theorem continueUp_nonneg (j k : ℕ) : 0 ≤ continueUp j k := by
  unfold continueUp
  split
  · exact survival_nonneg j
  · norm_num

private theorem continueUp_le_one (j k : ℕ) : continueUp j k ≤ 1 := by
  unfold continueUp
  split
  · linarith [survival_le j]
  · rfl

private theorem admissible_down {j k : ℕ} (hk : admissible (.inr (j,k))) :
    admissible (down j k) := by
  rcases hk with ⟨hpos, hlt⟩
  unfold down
  split <;> simp only [admissible]
  exact ⟨by omega, by omega⟩

private theorem admissible_up {j k : ℕ} (hk : admissible (.inr (j,k))) :
    admissible (up j k) := by
  rcases hk with ⟨hpos, hlt⟩
  unfold up
  split <;> simp only [admissible, boundary_succ] <;> omega

/-- The function whose expectation is preserved at each update. -/
private noncomputable def value (a b : ℝ) : State → ℝ
  | .inl true => 1
  | .inl false => 0
  | .inr (j,k) => (scale j * a / b) ^ k

/-- A bound on remaining expected physical queries. -/
private noncomputable def budget (b : ℝ) : State → ℝ
  | .inl _ => 0
  | .inr (j,k) => 6 / b * (2 * boundary j - k)

private theorem value_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (s : State) :
    0 ≤ value a b s := by
  rcases s with (d | ⟨j,k⟩)
  · cases d <;> norm_num [value]
  · exact pow_nonneg (div_nonneg (mul_nonneg (scale_pos j).le ha) hb.le) _

private theorem value_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : 2 * a ≤ b)
    (s : State) : value a b s ≤ 1 := by
  rcases s with (d | ⟨j,k⟩)
  · cases d <;> norm_num [value]
  · simp only [value]
    apply pow_le_one₀ (div_nonneg (mul_nonneg (scale_pos j).le ha) hb.le)
    apply (div_le_iff₀ hb).mpr
    calc
      scale j * a ≤ (3 / 2) * a := mul_le_mul_of_nonneg_right (scale_le j) ha
      _ ≤ 1 * b := by linarith

private theorem budget_nonneg {b : ℝ} (hb : 0 < b) {s : State} (hs : admissible s) :
    0 ≤ budget b s := by
  rcases s with (_ | ⟨j,k⟩)
  · norm_num [budget]
  · have hk : (k : ℝ) ≤ boundary j := by exact_mod_cast hs.2.le
    have hN : (0 : ℝ) ≤ boundary j := by positivity
    exact mul_nonneg (by positivity) (by linarith)

private theorem value_down {a b : ℝ} {j k : ℕ} :
    value a b (down j k) = (scale j * a / b) ^ (k - 1) := by
  unfold down
  split
  · simp_all [value]
  · rfl

private theorem value_up {a b : ℝ} {j k : ℕ} :
    continueUp j k * value a b (up j k) = (scale j * a / b) ^ (k + 1) := by
  unfold continueUp up
  split
  · rename_i hk
    simp only [hk, survival, value]
    rw [← hk, ← mul_pow]
    have := (scale_pos (j + 1)).ne'
    congr 1
    field_simp
  · rename_i hk
    simp [value]

private theorem budget_down {b : ℝ} (hb : 0 < b) {j k : ℕ} :
    budget b (down j k) ≤ 6 / b * (2 * boundary j - (k - 1 : ℕ)) := by
  unfold down
  split
  · rename_i hk
    subst k
    simpa [budget] using (by positivity : 0 ≤ (6 / b) * (2 * (boundary j : ℝ)))
  · rfl

private theorem budget_up {b : ℝ} (hb : 0 < b) {j k : ℕ} :
    continueUp j k * budget b (up j k) ≤ 6 / b * (2 * boundary j - (k + 1 : ℕ)) := by
  unfold continueUp up
  split
  · rename_i hk
    simp only [hk, budget, Nat.cast_ofNat, boundary_succ, Nat.cast_mul]
    have hN : (0 : ℝ) ≤ boundary j := by positivity
    have hs := survival_le j
    have h₆ : 0 ≤ 6 / b := by positivity
    calc
      survival j * (6 / b * (2 * (2 * boundary j) - boundary j))
        ≤ (1 / 5) * (6 / b * (2 * (2 * boundary j) - boundary j)) := by
          gcongr
          exact mul_nonneg h₆ (by linarith)
      _ ≤ _ := by
        nlinarith [mul_nonneg h₆ hN]
  · rename_i hk
    simp [budget]

/-- Real-valued one-step expectation for the stopped walk. -/
private noncomputable def expectation (a b : ℝ) (f : State → ℝ) : State → ℝ
  | .inl d => f (.inl d)
  | .inr (j,k) =>
    a * f (down j k) +
    b / scale j * (continueUp j k * f (up j k) + (1 - continueUp j k) * f (.inl false)) +
    (1 - a - b / scale j) * f (.inr (j,k))

private theorem expectation_value {a b : ℝ} (hb : 0 < b) {s : State} (hs : admissible s) :
    expectation a b (value a b) s = value a b s := by
  rcases s with (_ | ⟨j,k⟩)
  · rfl
  · have hk : 0 < k := hs.1
    rw [expectation, value_down]
    simp only [show value a b (.inl false) = 0 from rfl, mul_zero, add_zero, value_up]
    change _ * _ + _ * _ + _ * (scale j * a / b) ^ k = (scale j * a / b) ^ k
    have hh : (scale j * a / b) ^ k =
        (scale j * a / b) ^ (k - 1) * (scale j * a / b) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [pow_succ, hh]
    have hsj := (scale_pos j).ne'
    field_simp
    ring

private noncomputable def running : State → ℝ
  | .inl _ => 0
  | .inr _ => 1

private theorem expectation_budget {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : 2 * a ≤ b)
    {s : State} (hs : admissible s) :
    expectation a b (budget b) s + running s ≤ budget b s := by
  rcases s with (_ | ⟨j,k⟩)
  · simp [expectation, budget, running]
  · have hk : 0 < k := hs.1
    have hq : 0 ≤ b / scale j := div_nonneg hb.le (scale_pos j).le
    have hdiff : b / 6 ≤ b / scale j - a := by
      have h : (2 / 3 : ℝ) * b ≤ b / scale j := by
        apply (le_div_iff₀ (scale_pos j)).mpr
        calc
          (2 / 3) * b * scale j ≤ (2 / 3) * b * (3 / 2) := by gcongr; exact scale_le j
          _ = b := by ring
      linarith
    rw [expectation]
    simp only [running, show budget b (.inl false) = 0 from rfl, mul_zero, add_zero]
    change _ * _ + _ * _ + _ * (6 / b * (2 * boundary j - k)) + 1 ≤
      6 / b * (2 * boundary j - k)
    have h₁ := mul_le_mul_of_nonneg_left (budget_down (j := j) (k := k) hb) ha
    have h₂ := mul_le_mul_of_nonneg_left (budget_up (j := j) (k := k) hb) hq
    have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ k by omega))
    rw [hkm] at h₁
    push_cast at h₂
    have hbudget : 1 ≤ 6 / b * (b / scale j - a) := by
      calc
        1 = 6 / b * (b / 6) := by field_simp
        _ ≤ _ := by gcongr
    calc
      _ ≤ a * (6 / b * (2 * boundary j - ((k : ℝ) - 1))) +
          b / scale j * (6 / b * (2 * boundary j - (k + 1))) +
          (1 - a - b / scale j) * (6 / b * (2 * boundary j - k)) + 1 := by linarith
      _ = 6 / b * (2 * boundary j - k) - 6 / b * (b / scale j - a) + 1 := by ring
      _ ≤ _ := by linarith

end BilateralProfitRegular.Factory
end BundlePart007


section BundlePart008



namespace BilateralProfitRegular.Factory

open MeasureTheory ProbabilityTheory

private abbrev Uniform := unitInterval
private abbrev Stream := ℕ → Uniform
private abbrev Input := Uniform × Uniform

private instance : MeasurableSingletonClass State where
  measurableSet_singleton s := by
    rcases s with (d | jk) <;> simp [measurableSet_sum_iff, Set.preimage]


private noncomputable def inputLaw : Measure Input :=
  (volume : Measure Uniform).prod volume

private instance : IsProbabilityMeasure inputLaw := by
  unfold inputLaw
  infer_instance

private instance : IsProbabilityMeasure Proc.coinLaw := by
  unfold Proc.coinLaw
  infer_instance

private def pairAt (x : Stream × Stream) (n : ℕ) : Input := (x.1 n, x.2 n)

@[fun_prop]
private theorem measurable_pairAt : Measurable pairAt := by
  unfold pairAt
  fun_prop

private theorem paired_law : (Proc.law Proc.coinLaw).map pairAt =
    Measure.infinitePi (fun _ : ℕ => inputLaw) := by
  have e₁ := (measurePreserving_finTwoArrow Proc.coinLaw).map_eq
  rw [← Measure.infinitePi_eq_pi] at e₁
  rw [Proc.law, ← e₁, Measure.map_map measurable_pairAt (by fun_prop)]
  have hcomp : pairAt ∘ MeasurableEquiv.finTwoArrow =
      (fun (x : ℕ → Fin 2 → Uniform) n => MeasurableEquiv.finTwoArrow (x n)) ∘
      (MeasurableEquiv.curry ℕ (Fin 2) Uniform) ∘
      (MeasurableEquiv.piCongrLeft (fun _ => Uniform) (Equiv.prodComm (Fin 2) ℕ)) ∘
      (MeasurableEquiv.curry (Fin 2) ℕ Uniform).symm := by
    ext x n <;> rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold Proc.coinLaw
  rw [Measure.infinitePi_map_curry_symm,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ × Fin 2 => (volume : Measure Uniform))
      (Equiv.prodComm (Fin 2) ℕ),
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) => (volume : Measure Uniform)),
    Measure.infinitePi_map_pi (f := fun (_ : ℕ) => MeasurableEquiv.finTwoArrow) _ (by fun_prop)]
  congr 1
  funext n
  rw [Measure.infinitePi_eq_pi]
  exact (measurePreserving_finTwoArrow (volume : Measure Uniform)).map_eq

/-- A mixing rule takes a fresh observed bit and specifies the weights for the two
possible directions before applying the stage-dependent scaling. -/
private structure Mixing where
  downWeight : Bool → ℝ
  upWeight : Bool → ℝ
  down_nonneg : ∀ t, 0 ≤ downWeight t
  up_nonneg : ∀ t, 0 ≤ upWeight t
  sum_le_one : ∀ t, downWeight t + upWeight t ≤ 1

private noncomputable def mix (p : ℝ) (f : Bool → ℝ) : ℝ := p * f true + (1 - p) * f false

/-- Use one seed uniform to select the move and implement the thinning at a boundary. -/
private noncomputable def select (m : Mixing) (r : Uniform) (t : Bool) : State → State
  | .inl d => .inl d
  | .inr (j,k) =>
    let d := m.downWeight t
    let u := m.upWeight t / scale j
    if (r : ℝ) < d then down j k
    else if (r : ℝ) < d + u * continueUp j k then up j k
    else if (r : ℝ) < d + u then .inl false
    else .inr (j,k)

private theorem select_admissible (m : Mixing) (r : Uniform) (t : Bool) {s : State}
    (hs : admissible s) : admissible (select m r t s) := by
  rcases s with (d | ⟨j,k⟩)
  · trivial
  · simp only [select]
    split
    · exact admissible_down hs
    · split
      · exact admissible_up hs
      · split
        · trivial
        · exact hs

@[fun_prop]
private theorem measurable_select (m : Mixing) (t : Bool) (s : State) :
    Measurable (fun r => select m r t s) := by
  rcases s with (_ | ⟨j,k⟩)
  · exact measurable_const
  · simp only [select]
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const
      (Measurable.ite ?_ measurable_const measurable_const))
    all_goals exact measurableSet_lt (by fun_prop) measurable_const

/-- Interpret a uniform input as one seed value and one trade bit. -/
private noncomputable def update (m : Mixing) (p : ℝ) (s : State) (r : Input) : State :=
  select m r.1 (decide ((r.2 : ℝ) < p)) s

@[fun_prop]
private theorem measurable_update (m : Mixing) (p : ℝ) :
    Measurable (fun sr : State × Input => update m p sr.1 sr.2) := by
  refine measurable_from_prod_countable_right ?_
  intro s
  have heq : (fun r => update m p s r) =
      fun r : Input => if (r.2 : ℝ) < p then select m r.1 true s else select m r.1 false s := by
    funext r
    by_cases h : (r.2 : ℝ) < p <;> simp [update, h]
  rw [heq]
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

private theorem volume_lt {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (volume : Measure Uniform) {r | (r : ℝ) < a} = ENNReal.ofReal a :=
  unitInterval.volume_Iio (⟨a, ha, ha'⟩ : Uniform)

private theorem integral_indicator_lt {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (v : ℝ) :
    ∫ r : Uniform, (if (r : ℝ) < a then v else 0) = a * v := by
  change ∫ r : Uniform, ({r : Uniform | (r : ℝ) < a} : Set Uniform).indicator (fun _ => v) r = _
  rw [integral_indicator (measurableSet_lt (by fun_prop) measurable_const), setIntegral_const,
    Measure.real, volume_lt ha ha', ENNReal.toReal_ofReal ha, smul_eq_mul]

private theorem integrable_select (m : Mixing) (t : Bool) (s : State) (f : State → ℝ) :
    Integrable (fun r : Uniform => f (select m r t s)) volume := by
  have hf : Measurable (fun r : Uniform => f (select m r t s)) :=
    (measurable_of_countable f).comp (measurable_select m t s)
  rcases s with (d | ⟨j,k⟩)
  · simpa only [select] using (integrable_const (μ := volume) (f (.inl d)) : Integrable _ (volume : Measure Uniform))
  · apply Integrable.of_bound hf.aestronglyMeasurable
      (max (max ‖f (down j k)‖ ‖f (up j k)‖) (max ‖f (.inl false)‖ ‖f (.inr (j,k))‖))
    refine Filter.Eventually.of_forall fun r => ?_
    simp only [select]
    split
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · split
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · split
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem integral_select (m : Mixing) (t : Bool) (f : State → ℝ) (s : State) :
    (∫ r : Uniform, f (select m r t s)) =
      expectation (m.downWeight t) (m.upWeight t) f s := by
  rcases s with (d | ⟨j,k⟩)
  · simp [select, expectation]
  · let d := m.downWeight t
    let u := m.upWeight t / scale j
    let h := continueUp j k
    have hd : 0 ≤ d := m.down_nonneg t
    have hu : 0 ≤ u := div_nonneg (m.up_nonneg t) (scale_pos j).le
    have hh : 0 ≤ h := continueUp_nonneg j k
    have hh' : h ≤ 1 := continueUp_le_one j k
    have hdu : d + u ≤ 1 := by
      have hu' : u ≤ m.upWeight t := div_le_self (m.up_nonneg t) (scale_one_le j)
      linarith [m.sum_le_one t]
    have hh₁ : d ≤ d + u*h := by nlinarith
    have hh₂ : d + u*h ≤ d+u := by nlinarith
    let k₁ := f (down j k) - f (up j k)
    let k₂ := f (up j k) - f (.inl false)
    let k₃ := f (.inl false) - f (.inr (j,k))
    have heq : (fun r : Uniform => f (select m r t (.inr (j,k)))) = fun r : Uniform =>
        (if (r : ℝ) < d then k₁ else 0) + (if (r : ℝ) < d + u*h then k₂ else 0) +
        (if (r : ℝ) < d + u then k₃ else 0) + f (.inr (j,k)) := by
      funext r
      change f (if (r : ℝ) < d then down j k else if (r : ℝ) < d + u*h then up j k
        else if (r : ℝ) < d+u then .inl false else .inr (j,k)) = _
      by_cases h₁ : (r : ℝ) < d
      · simp [h₁, h₁.trans_le hh₁, h₁.trans_le (hh₁.trans hh₂), k₁, k₂, k₃]
      · by_cases h₂ : (r : ℝ) < d+u*h
        · simp [h₁, h₂, h₂.trans_le hh₂, k₂, k₃]
        · by_cases h₃ : (r : ℝ) < d+u <;> simp [h₁, h₂, h₃, k₃]
    have hi (a v : ℝ) : Integrable (fun r : Uniform => if (r : ℝ) < a then v else 0) volume := by
      change Integrable (({r : Uniform | (r : ℝ) < a} : Set Uniform).indicator (fun _ => v)) volume
      exact (integrable_const v).indicator (measurableSet_lt (by fun_prop) measurable_const)
    have hAdd₁ := integral_add (hi d k₁) (hi (d+u*h) k₂)
    have hAdd₂ := integral_add ((hi d k₁).add (hi (d+u*h) k₂)) (hi (d+u) k₃)
    have hAdd₃ := integral_add ((hi d k₁).add (hi (d+u*h) k₂) |>.add (hi (d+u) k₃))
      (integrable_const (f (.inr (j,k))))
    simp only [Pi.add_apply] at hAdd₁ hAdd₂ hAdd₃
    rw [heq, hAdd₃, hAdd₂, hAdd₁]
    rw [integral_indicator_lt hd ((hh₁.trans hh₂).trans hdu),
      integral_indicator_lt (hd.trans hh₁) (hh₂.trans hdu),
      integral_indicator_lt (hd.trans (hh₁.trans hh₂)) hdu]
    simp only [integral_const, probReal_univ, one_smul, expectation]
    change d*k₁ + (d+u*h)*k₂ + (d+u)*k₃ + f (.inr (j,k)) = _
    change _ = d * f (down j k) + u * (h * f (up j k) + (1 - h) * f (.inl false)) +
      (1 - d - u) * f (.inr (j,k))
    dsimp [k₁, k₂, k₃]
    ring

private theorem integral_update (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (f : State → ℝ)
    (s : State) :
    (∫ r, f (update m p s r) ∂inputLaw) =
      expectation (mix p m.downWeight) (mix p m.upWeight) f s := by
  let F := fun r : Input => f (select m r.1 true s)
  let G := fun r : Input => f (select m r.1 false s)
  have hF : Integrable F inputLaw := (integrable_select m true s f).comp_fst volume
  have hG : Integrable G inputLaw := (integrable_select m false s f).comp_fst volume
  have heq : (fun r => f (update m p s r)) =
      fun r : Input => (if (r.2 : ℝ) < p then F r - G r else 0) + G r := by
    funext r
    by_cases h : (r.2 : ℝ) < p <;> simp [update, h, F, G]
  have hdiff : Integrable (fun r : Input => if (r.2 : ℝ) < p then F r - G r else 0) inputLaw := by
    change Integrable (({r : Input | (r.2 : ℝ) < p} : Set Input).indicator (fun r => F r - G r)) inputLaw
    exact (hF.sub hG).indicator (measurableSet_lt (by fun_prop) measurable_const)
  have hfg : Integrable (fun r => f (update m p s r)) inputLaw := heq ▸ (hdiff.add hG)
  unfold inputLaw at hfg ⊢
  rw [integral_prod _ hfg]
  have inner (r : Uniform) :
      (∫ t : Uniform, f (update m p s (r,t))) =
        p * f (select m r true s) + (1 - p) * f (select m r false s) := by
    change (∫ t : Uniform, (fun r => f (update m p s r)) (r,t)) = _
    rw [heq]
    simp only [F, G]
    rw [integral_add _ (integrable_const _), integral_indicator_lt hp hp']
    · simp [integral_const]; ring
    · change Integrable (({t : Uniform | (t : ℝ) < p} : Set Uniform).indicator (fun _ =>
        f (select m r true s) - f (select m r false s))) volume
      exact (integrable_const _).indicator (measurableSet_lt (by fun_prop) measurable_const)
  simp_rw [inner]
  rw [integral_add ((integrable_select m true s f).const_mul p)
    ((integrable_select m false s f).const_mul (1 - p)),
    integral_const_mul, integral_const_mul, integral_select, integral_select]
  rcases s with (d | ⟨j,k⟩) <;> simp only [expectation, mix] <;> ring

end BilateralProfitRegular.Factory
end BundlePart008


section BundlePart009


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

private abbrev Inputs := ℕ → Input

private noncomputable def streamLaw : Measure Inputs := Measure.infinitePi fun _ => inputLaw

private instance : IsProbabilityMeasure streamLaw := by
  unfold streamLaw
  infer_instance

private def initial : State := .inr (0, 1)

private theorem initial_admissible : admissible initial := by norm_num [admissible, initial, boundary]

private noncomputable def follow (m : Mixing) (p : ℝ) :
    (n : ℕ) → (Fin n → Input) → State
  | 0, _ => initial
  | n + 1, v => update m p (follow m p n (fun i => v i.castSucc)) (v (Fin.last n))

@[fun_prop]
private theorem measurable_follow (m : Mixing) (p : ℝ) (n : ℕ) :
    Measurable (follow m p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_update m p).comp ((ih.comp (by fun_prop)).prodMk (by fun_prop))

private noncomputable def run (m : Mixing) (p : ℝ) (n : ℕ) (x : Inputs) : State :=
  follow m p n (fun i => x i)

private theorem run_zero (m : Mixing) (p : ℝ) (x : Inputs) : run m p 0 x = initial := rfl

private theorem run_succ (m : Mixing) (p : ℝ) (n : ℕ) (x : Inputs) :
    run m p (n + 1) x = update m p (run m p n x) (x n) := rfl

@[fun_prop]
private theorem measurable_run (m : Mixing) (p : ℝ) (n : ℕ) :
    Measurable (run m p n) := by
  unfold run
  exact (measurable_follow m p n).comp (by fun_prop)

private theorem run_admissible (m : Mixing) (p : ℝ) (x : Inputs) (n : ℕ) :
    admissible (run m p n x) := by
  induction n with
  | zero => exact initial_admissible
  | succ n ih =>
    rw [run_succ]
    exact select_admissible _ _ _ ih

private theorem run_absorbed (m : Mixing) (p : ℝ) (x : Inputs) {n : ℕ} {d : Bool}
    (h : run m p n x = .inl d) {k : ℕ} (hnk : n ≤ k) : run m p k x = .inl d := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k hk ih => rw [run_succ, ih]; rfl

private theorem run_stage_le (m : Mixing) (p : ℝ) (x : Inputs) (n : ℕ) {j k : ℕ}
    (h : run m p n x = .inr (j,k)) : j ≤ n := by
  induction n generalizing j k with
  | zero =>
    simp only [run_zero, initial, Sum.inr.injEq, Prod.mk.injEq] at h
    omega
  | succ n ih =>
    rw [run_succ] at h
    cases hs : run m p n x with
    | inl d => simp [hs, update, select] at h
    | inr jk =>
      rcases jk with ⟨j',k'⟩
      have hj := ih hs
      rw [hs] at h
      simp only [update, select] at h
      split at h
      · unfold down at h
        split at h <;> simp_all
        omega
      · split at h
        · unfold up at h
          split at h <;> simp_all <;> omega
        · split at h <;> simp_all
          omega

private theorem run_indep (m : Mixing) (p : ℝ) (n : ℕ) :
    IndepFun (run m p n) (fun x : Inputs => x n) streamLaw := by
  have hi : iIndepFun (fun i (x : Inputs) => x i) streamLaw :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hd : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd (by fun_prop)
  let f : ((i : Finset.range n) → Input) → State :=
    fun r => follow m p n (fun (i : Fin n) => r ⟨i, Finset.mem_range.mpr i.isLt⟩)
  let g : ((i : ({n} : Finset ℕ)) → Input) → Input :=
    fun r => r ⟨n, Finset.mem_singleton_self n⟩
  have hf : Measurable f := (measurable_follow m p n).comp (by fun_prop)
  have hg : Measurable g := by unfold g; fun_prop
  exact h.comp hf hg

private theorem integral_run_succ (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (n : ℕ)
    (f : State → ℝ) (hf : Integrable (fun x => f (run m p (n+1) x)) streamLaw) :
    (∫ x, f (run m p (n+1) x) ∂streamLaw) =
      ∫ x, expectation (mix p m.downWeight) (mix p m.upWeight) f (run m p n x) ∂streamLaw := by
  let G := fun x : Inputs => (run m p n x, x n)
  let F := fun sr : State × Input => f (update m p sr.1 sr.2)
  have hG : Measurable G := by unfold G; fun_prop
  have hF : Measurable F := (measurable_of_countable f).comp (measurable_update m p)
  have hcomp : Integrable (F ∘ G) streamLaw := by simpa [F, G, Function.comp_def, run_succ] using hf
  have hprod : streamLaw.map G = (streamLaw.map (run m p n)).prod inputLaw := by
    rw [(run_indep m p n).map_prod_eq_prod_map_map (measurable_run m p n).aemeasurable
      (measurable_pi_apply n).aemeasurable]
    exact congrArg _ (Measure.infinitePi_map_eval _ _)
  have hFint : Integrable F ((streamLaw.map (run m p n)).prod inputLaw) := by
    rw [← hprod]
    exact (integrable_map_measure hF.aestronglyMeasurable hG.aemeasurable).2 hcomp
  calc
    _ = ∫ sr, F sr ∂(streamLaw.map G) := by
      rw [integral_map hG.aemeasurable hF.aestronglyMeasurable]
      simp only [G, F, run_succ]
    _ = ∫ s, (∫ r, f (update m p s r) ∂inputLaw) ∂(streamLaw.map (run m p n)) := by
      rw [hprod, integral_prod _ hFint]
    _ = _ := by
      simp_rw [integral_update m hp hp']
      rw [integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]

private noncomputable def historyStep (m : Mixing) (ω : Stream) :
    State × ℕ → Unit × Bool → State × ℕ :=
  fun z q => (select m (ω z.2) q.2 z.1, z.2 + 1)

private noncomputable def replay (m : Mixing) (ω : Stream) (h : List (Unit × Bool)) : State :=
  (h.foldl (historyStep m ω) (initial, 0)).1

private theorem fold_length (m : Mixing) (ω : Stream) (z : State × ℕ) (h : List (Unit × Bool)) :
    (h.foldl (historyStep m ω) z).2 = z.2 + h.length := by
  induction h generalizing z with
  | nil => simp
  | cons q h ih => rw [List.foldl_cons, ih]; simp [historyStep]; omega

private theorem replay_append (m : Mixing) (ω : Stream) (h : List (Unit × Bool)) (t : Bool) :
    replay m ω (h ++ [((),t)]) = select m (ω h.length) t (replay m ω h) := by
  simp [replay, List.foldl_append, historyStep, fold_length]

@[fun_prop]
private theorem measurable_replay (m : Mixing) (h : List (Unit × Bool)) :
    Measurable (fun ω => replay m ω h) := by
  induction h using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton h q ih =>
    rcases q with ⟨⟨⟩,t⟩
    simp only [replay_append]
    exact (measurable_from_prod_countable_right (f := fun sr : State × Uniform =>
      select m sr.2 t sr.1) (fun s => measurable_select m t s)).comp
      (ih.prodMk (measurable_pi_apply h.length))

private def queryOrFinish : State → Unit ⊕ Bool
  | .inl d => .inr d
  | .inr _ => .inl ()

private noncomputable def procedure (m : Mixing) : Proc Unit Bool Stream where
  step ω h := queryOrFinish (replay m ω h)
  measurable_step h := (measurable_of_countable queryOrFinish).comp (measurable_replay m h)

private theorem run_eq_replay (m : Mixing) (p : ℝ) (ω U : Stream) (n : ℕ) :
    let h := (procedure m).hist (fun _ => p) ω U n
    let s := run m p n (pairAt (ω,U))
    replay m ω h = s ∧ (s.isRight = true → h.length = n) := by
  induction n with
  | zero => simp [Proc.hist, replay, run_zero]
  | succ n ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨ih,hlen⟩
    have hstep : (procedure m).step ω ((procedure m).hist (fun _ => p) ω U n) =
        queryOrFinish (run m p n (pairAt (ω,U))) := by
      change queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U n)) = _
      rw [ih]
    rw [Proc.hist, run_succ, hstep]
    cases hs : run m p n (pairAt (ω,U)) with
    | inl d =>
      simp [queryOrFinish, update, select, ih]
      exact hs
    | inr jk =>
      have hl := hlen (by simp [hs])
      rw [queryOrFinish, replay_append, hl]
      simp [update, pairAt, ih, hs, hl]
      rfl

private theorem stopped_iff (m : Mixing) (p : ℝ) (ω U : Stream) (n : ℕ) :
    (procedure m).stopped (fun _ => p) ω U n ↔
      ∃ d, run m p n (pairAt (ω,U)) = .inl d := by
  unfold Proc.stopped
  change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U n))).isRight = true ↔ _
  rw [(run_eq_replay m p ω U n).1]
  cases run m p n (pairAt (ω,U)) <;> simp [queryOrFinish]

private theorem rounds_eq_find (m : Mixing) (p : ℝ) (ω U : Stream)
    (h : ∃ n, (procedure m).stopped (fun _ => p) ω U n) :
    (procedure m).rounds (fun _ => p) ω U = (Nat.find h : ℕ∞) := by
  unfold Proc.rounds
  apply le_antisymm
  · exact iInf_le_of_le (Nat.find h) (iInf_le _ (Nat.find_spec h))
  · refine le_iInf fun n => le_iInf fun hn => ?_
    exact_mod_cast Nat.find_min' h hn

private theorem rounds_eq_top (m : Mixing) (p : ℝ) (ω U : Stream)
    (h : ¬ ∃ n, (procedure m).stopped (fun _ => p) ω U n) :
    (procedure m).rounds (fun _ => p) ω U = ⊤ := by
  unfold Proc.rounds
  simp [not_exists.mp h]

private theorem rounds_eq_sum (m : Mixing) (p : ℝ) (ω U : Stream) :
    ((procedure m).rounds (fun _ => p) ω U : ENNReal) =
      ∑' n : ℕ, ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) := by
  by_cases h : ∃ n, (procedure m).stopped (fun _ => p) ω U n
  · rw [rounds_eq_find m p ω U h]
    have hr (n : ℕ) : ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) =
        if n < Nat.find h then 1 else 0 := by
      by_cases hn : n < Nat.find h
      · have hstop := Nat.find_min h hn
        rw [stopped_iff] at hstop
        cases hs : run m p n (pairAt (ω,U)) with
        | inl d => exact (hstop ⟨d,hs⟩).elim
        | inr jk => simp [running, hn]
      · rcases (stopped_iff m p ω U _).mp (Nat.find_spec h) with ⟨d,hd⟩
        rw [run_absorbed _ _ _ hd (Nat.le_of_not_gt hn)]
        simp [running, hn]
    simp_rw [hr]
    have hr' : (fun n => if n < Nat.find h then (1 : ENNReal) else 0) =
        (Finset.range (Nat.find h) : Set ℕ).indicator (fun _ => 1) := by
      ext n
      simp [Set.indicator]
    rw [hr']
    have hsum (k : ℕ) :
        (∑' n, (Finset.range k : Set ℕ).indicator (fun _ => (1 : ENNReal)) n) = k := by
      rw [tsum_eq_sum (s := Finset.range k)]
      · calc
          _ = ∑ j ∈ Finset.range k, (1 : ENNReal) := by
            exact Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem hj _)
          _ = k := by simp
      · exact fun j hj => Set.indicator_of_notMem hj _
    rw [hsum]
    simp
  · rw [rounds_eq_top m p ω U h]
    have hr (n : ℕ) : ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) = 1 := by
      cases hs : run m p n (pairAt (ω,U)) with
      | inl d => exact (h ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,hs⟩⟩).elim
      | inr jk => simp [running]
    simp_rw [hr]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm

end BilateralProfitRegular.Factory
end BundlePart009


section BundlePart010


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators

private theorem boundary_mono : Monotone boundary :=
  monotone_nat_of_le_succ (fun j => by rw [boundary_succ]; omega)

private theorem run_budget_bound (m : Mixing) (p : ℝ) {b : ℝ} (hb : 0 < b) (n : ℕ) (x : Inputs) :
    budget b (run m p n x) ≤ 6 / b * (2 * boundary n) := by
  cases hs : run m p n x with
  | inl d =>
    simp only [budget]
    positivity
  | inr jk =>
    rcases jk with ⟨j,k⟩
    have hj := boundary_mono (run_stage_le m p x n hs)
    have : (boundary j : ℝ) ≤ boundary n := by exact_mod_cast hj
    simp only [budget]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith

private theorem running_nonneg (s : State) : 0 ≤ running s := by cases s <;> norm_num [running]
private theorem running_le_one (s : State) : running s ≤ 1 := by cases s <;> norm_num [running]

private theorem integrable_bounded_run (m : Mixing) (p : ℝ) (n : ℕ) (f : State → ℝ) (K : ℝ)
    (h : ∀ x : Inputs, 0 ≤ f (run m p n x) ∧ f (run m p n x) ≤ K) :
    Integrable (fun x => f (run m p n x)) streamLaw := by
  have hf : Measurable (fun x => f (run m p n x)) :=
    (measurable_of_countable f).comp (measurable_run m p n)
  apply Integrable.of_bound hf.aestronglyMeasurable K
  exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (h x).1] using (h x).2

private theorem expectation_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (f : State → ℝ) (hf : ∀ s, admissible s → 0 ≤ f s)
    {s : State} (hs : admissible s) : 0 ≤ expectation a b f s := by
  rcases s with (d | ⟨j,k⟩)
  · exact hf _ hs
  · have hu : 0 ≤ b / scale j := div_nonneg hb (scale_pos j).le
    have hu' : b / scale j ≤ b := div_le_self hb (scale_one_le j)
    rw [expectation]
    exact add_nonneg
      (add_nonneg (mul_nonneg ha (hf _ (admissible_down hs)))
        (mul_nonneg hu
          (add_nonneg (mul_nonneg (continueUp_nonneg j k) (hf _ (admissible_up hs)))
            (mul_nonneg (sub_nonneg.mpr (continueUp_le_one j k)) (hf _ trivial)))))
      (mul_nonneg (by linarith) (hf _ hs))

private noncomputable def totalRounds (m : Mixing) (p : ℝ) (x : Inputs) : ENNReal :=
  ∑' n, ENNReal.ofReal (running (run m p n x))

@[fun_prop]
private theorem measurable_totalRounds (m : Mixing) (p : ℝ) :
    Measurable (totalRounds m p) := by
  unfold totalRounds
  exact Measurable.tsum fun n =>
    ENNReal.measurable_ofReal.comp ((measurable_of_countable running).comp (measurable_run m p n))

private theorem never_finishes_iff (m : Mixing) (p : ℝ) (x : Inputs) :
    (¬ ∃ n d, run m p n x = .inl d) ↔ totalRounds m p x = ⊤ := by
  constructor
  · intro h
    have hn (n : ℕ) : ENNReal.ofReal (running (run m p n x)) = 1 := by
      cases hs : run m p n x with
      | inl d => exact (h ⟨n,d,hs⟩).elim
      | inr jk => simp [running]
    unfold totalRounds
    simp_rw [hn]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  · intro h hx
    rcases hx with ⟨n,d,hd⟩
    have hm : totalRounds m p x ≤ n := by
      unfold totalRounds
      rw [tsum_eq_sum (s := Finset.range n)]
      · calc
          _ ≤ ∑ _ ∈ Finset.range n, (1 : ENNReal) := by
            gcongr with j _
            simpa using ENNReal.ofReal_le_ofReal (running_le_one (run m p j x))
          _ = n := by simp
      · intro k hk
        have hnk : n ≤ k := by simpa [Finset.mem_range] using hk
        rw [run_absorbed _ _ _ hd hnk]
        simp [running]
    simp [h] at hm

private theorem lintegral_rounds_le (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    (∫⁻ x, totalRounds m p x ∂streamLaw) ≤ ENNReal.ofReal (282 / mix p m.upWeight) := by
  let a := mix p m.downWeight
  let b := mix p m.upWeight
  have ha : 0 ≤ a := add_nonneg (mul_nonneg hp (m.down_nonneg true))
    (mul_nonneg (sub_nonneg.mpr hp') (m.down_nonneg false))
  have hab' : a + b ≤ 1 := by
    change mix p m.downWeight + mix p m.upWeight ≤ 1
    have ht := mul_le_mul_of_nonneg_left (m.sum_le_one true) hp
    have hf := mul_le_mul_of_nonneg_left (m.sum_le_one false) (sub_nonneg.mpr hp')
    unfold mix
    linarith
  let R := fun n x => running (run m p n x)
  let B := fun n x => budget b (run m p n x)
  have hR₀ (n : ℕ) (x : Inputs) : 0 ≤ R n x := running_nonneg _
  have hB₀ (n : ℕ) (x : Inputs) : 0 ≤ B n x :=
    budget_nonneg hb (run_admissible m p x n)
  have hR (n : ℕ) : Integrable (R n) streamLaw :=
    integrable_bounded_run m p n running 1 (fun _ => ⟨running_nonneg _, running_le_one _⟩)
  have hB (n : ℕ) : Integrable (B n) streamLaw :=
    integrable_bounded_run m p n (budget b) _ (fun x => ⟨hB₀ n x, run_budget_bound m p hb n x⟩)
  have hstep (n : ℕ) :
      (∫ x, B (n+1) x ∂streamLaw) + (∫ x, R n x ∂streamLaw) ≤ ∫ x, B n x ∂streamLaw := by
    rw [integral_run_succ m hp hp' n (budget b) (hB (n+1))]
    have hE : Integrable (fun x => expectation a b (budget b) (run m p n x)) streamLaw := by
      refine integrable_bounded_run m p n _ (6 / b * (2 * boundary n)) fun x => ⟨?_,?_⟩
      · exact expectation_nonneg ha hb.le hab' _ (fun _ hs => budget_nonneg hb hs)
          (run_admissible m p x n)
      · have hd := expectation_budget ha hb hab (run_admissible m p x n)
        have hbound := run_budget_bound m p hb n x
        linarith [hR₀ n x]
    rw [← integral_add hE (hR n)]
    apply integral_mono (hE.add (hR n)) (hB n)
    intro x
    exact expectation_budget ha hb hab (run_admissible m p x n)
  have hbase : (∫ x, B 0 x ∂streamLaw) = 282 / b := by
    simp only [B, run_zero, initial, budget, boundary, pow_zero, mul_one, Nat.cast_ofNat,
      Nat.cast_one, integral_const, probReal_univ, one_smul]
    ring
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, ∫ x, R i x ∂streamLaw) + (∫ x, B n x ∂streamLaw) ≤ 282 / b := by
    induction n with
    | zero => simp [hbase]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  unfold totalRounds
  rw [lintegral_tsum (fun n => ((hR n).aemeasurable.ennreal_ofReal)), ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hR _) (Eventually.of_forall (hR₀ _))]
  have hRInt₀ (i : ℕ) : 0 ≤ ∫ x, R i x ∂streamLaw := integral_nonneg (hR₀ i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hRInt₀ i)]
  apply ENNReal.ofReal_le_ofReal
  have hBI : 0 ≤ ∫ x, B n x ∂streamLaw := integral_nonneg (hB₀ n)
  linarith [hsum n]

private theorem stream_finishes_ae (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    ∀ᵐ x ∂streamLaw, ∃ n d, run m p n x = .inl d := by
  have hbound := lintegral_rounds_le m hp hp' hb hab
  have hfinite : (∫⁻ x, totalRounds m p x ∂streamLaw) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  filter_upwards [ae_lt_top (measurable_totalRounds m p) hfinite] with x hx
  by_contra h
  exact hx.ne ((never_finishes_iff m p x).mp h)

private def success (m : Mixing) (p : ℝ) : Set Inputs := {x | ∃ n, run m p n x = .inl true}

private theorem measurable_success (m : Mixing) (p : ℝ) : MeasurableSet (success m p) := by
  have he : success m p = ⋃ n, (run m p n) ⁻¹' {Sum.inl true} := by
    ext x
    simp [success]
  rw [he]
  exact MeasurableSet.iUnion fun n => (measurable_run m p n) (measurableSet_singleton _)

private theorem stream_success (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    streamLaw (success m p) = ENNReal.ofReal (mix p m.downWeight / mix p m.upWeight) := by
  let a := mix p m.downWeight
  let b := mix p m.upWeight
  have ha : 0 ≤ a := add_nonneg (mul_nonneg hp (m.down_nonneg true))
    (mul_nonneg (sub_nonneg.mpr hp') (m.down_nonneg false))
  let F := fun n x => value a b (run m p n x)
  have hFm (n : ℕ) : Measurable (F n) :=
    (measurable_of_countable (value a b)).comp (measurable_run m p n)
  have hFnorm (n : ℕ) (x : Inputs) : ‖F n x‖ ≤ 1 := by
    have h₀ : 0 ≤ F n x := value_nonneg ha hb (run m p n x)
    rw [Real.norm_eq_abs, abs_of_nonneg h₀]
    exact value_le_one ha hb hab (run m p n x)
  have hFin (n : ℕ) : Integrable (F n) streamLaw :=
    Integrable.of_bound (hFm n).aestronglyMeasurable 1 (Eventually.of_forall (hFnorm n))
  have hmean (n : ℕ) : (∫ x, F n x ∂streamLaw) = a/b := by
    induction n with
    | zero => simp [F, run_zero, initial, value]
    | succ n ih =>
      rw [integral_run_succ m hp hp' n _ (hFin (n+1)), ← ih]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => expectation_value hb (run_admissible m p x n)
  let f : Inputs → ℝ := (success m p).indicator (fun _ => 1)
  have hpoint : ∀ᵐ x ∂streamLaw, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    filter_upwards [stream_finishes_ae m hp hp' hb hab] with x hx
    rcases hx with ⟨n,d,hd⟩
    have he : ∀ k ≥ n, F k x = f x := by
      intro k hk
      rw [show F k x = value a b (run m p k x) from rfl, run_absorbed _ _ _ hd hk]
      cases d
      · have hx' : x ∉ success m p := by
          rintro ⟨j,hj⟩
          have hf₁ := run_absorbed m p x hd (le_max_left n j)
          have hf₂ := run_absorbed m p x hj (le_max_right n j)
          rw [hf₁] at hf₂
          cases hf₂
        simp [f, hx', value]
      · have hx' : x ∈ success m p := ⟨n,hd⟩
        simp [f, hx', value]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    exact (eventually_ge_atTop n).mono (fun k hk => (he k hk).symm)
  have hl := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (hFm n).aestronglyMeasurable) (integrable_const _) (fun n => Eventually.of_forall (hFnorm n))
    hpoint
  simp only [hmean] at hl
  have hm := tendsto_nhds_unique tendsto_const_nhds hl
  have hfm : (∫ x, f x ∂streamLaw) = (streamLaw (success m p)).toReal := by
    simp [f, integral_indicator (measurable_success m p), Measure.real]
  rw [hfm] at hm
  rw [hm, ENNReal.ofReal_toReal (measure_ne_top streamLaw _)]

end BilateralProfitRegular.Factory
end BundlePart010


section BundlePart011


namespace BilateralProfitRegular

open Classical MeasureTheory
open scoped ENNReal

namespace Factory

private theorem out_none_iff (m : Mixing) (p : ℝ) (ω U : Stream) :
    (procedure m).out (fun _ => p) ω U = none ↔ totalRounds m p (pairAt (ω,U)) = ⊤ := by
  rw [← never_finishes_iff]
  constructor
  · intro h hx
    rcases hx with ⟨n,d,hd⟩
    have hstop : ∃ k, (procedure m).stopped (fun _ => p) ω U k :=
      ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,hd⟩⟩
    rw [Proc.out, dif_pos hstop] at h
    change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U (Nat.find hstop)))).getRight? = none at h
    rw [(run_eq_replay m p ω U (Nat.find hstop)).1] at h
    obtain ⟨b,hb⟩ := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hstop)
    simp [hb, queryOrFinish] at h
  · intro h
    have hstop : ¬ ∃ k, (procedure m).stopped (fun _ => p) ω U k := by
      rintro ⟨k,hk⟩
      obtain ⟨d,hd⟩ := (stopped_iff _ _ _ _ _).mp hk
      exact h ⟨k,d,hd⟩
    simp [Proc.out, hstop]

private theorem out_true_iff (m : Mixing) (p : ℝ) (ω U : Stream) :
    (procedure m).out (fun _ => p) ω U = some true ↔ pairAt (ω,U) ∈ success m p := by
  by_cases hstop : ∃ k, (procedure m).stopped (fun _ => p) ω U k
  · rw [Proc.out, dif_pos hstop]
    change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U (Nat.find hstop)))).getRight? = some true ↔ _
    rw [(run_eq_replay m p ω U (Nat.find hstop)).1]
    obtain ⟨d,hd⟩ := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hstop)
    rw [hd]
    simp only [queryOrFinish, Sum.getRight?, Option.some.injEq]
    constructor
    · intro h
      exact ⟨Nat.find hstop, h ▸ hd⟩
    · rintro ⟨n,hn⟩
      have hs : (procedure m).stopped (fun _ => p) ω U n :=
        (stopped_iff _ _ _ _ _).mpr ⟨true,hn⟩
      have he := run_absorbed m p _ hd (Nat.find_min' hstop hs)
      rw [he, Sum.inl.injEq] at hn
      exact hn
  · have hnot : pairAt (ω,U) ∉ success m p := by
      rintro ⟨n,hn⟩
      exact hstop ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨true,hn⟩⟩
    simp [Proc.out, hstop, hnot]

/-- A common implementation of the two factories. The down and up probabilities
are the mixture of their corresponding seed weights over the unknown bias. -/
private theorem procedure_spec (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    Proc.law Proc.coinLaw {x | (procedure m).out (fun _ => p) x.1 x.2 = none} = 0 ∧
      Proc.law Proc.coinLaw {x | (procedure m).out (fun _ => p) x.1 x.2 = some true} =
        ENNReal.ofReal (mix p m.downWeight / mix p m.upWeight) ∧
      (procedure m).expRounds (fun _ => p) Proc.coinLaw ≤ ENNReal.ofReal (282 / mix p m.upWeight) := by
  have hnever : MeasurableSet {x | totalRounds m p x = ⊤} :=
    (measurable_totalRounds m p) (measurableSet_singleton ⊤)
  have hmap : (Proc.law Proc.coinLaw).map pairAt = streamLaw := paired_law
  refine ⟨?_, ?_, ?_⟩
  · have he : {x : Stream × Stream | (procedure m).out (fun _ => p) x.1 x.2 = none}
        = pairAt ⁻¹' {x | totalRounds m p x = ⊤} := by
      ext x
      exact out_none_iff m p x.1 x.2
    rw [he, ← Measure.map_apply measurable_pairAt hnever, hmap]
    have := stream_finishes_ae m hp hp' hb hab
    rw [ae_iff] at this
    simpa only [never_finishes_iff] using this
  · have he : {x : Stream × Stream | (procedure m).out (fun _ => p) x.1 x.2 = some true}
        = pairAt ⁻¹' success m p := by
      ext x
      exact out_true_iff m p x.1 x.2
    rw [he, ← Measure.map_apply measurable_pairAt (measurable_success m p), hmap]
    exact stream_success m hp hp' hb hab
  · unfold Proc.expRounds
    simp_rw [rounds_eq_sum]
    change (∫⁻ x, totalRounds m p (pairAt x) ∂(Proc.law Proc.coinLaw)) ≤ _
    rw [← lintegral_map (measurable_totalRounds m p) measurable_pairAt, hmap]
    exact lintegral_rounds_le m hp hp' hb hab

private noncomputable def linearMixing (c : ℝ) (hc : 0 < c) : Mixing where
  downWeight t := if t then c / (1 + c) else 0
  upWeight _ := 1 / (1 + c)
  down_nonneg t := by cases t <;> simp <;> positivity
  up_nonneg _ := by positivity
  sum_le_one t := by
    have hd : 0 < 1 + c := by positivity
    cases t
    · simpa using ((div_le_iff₀ hd).2 (by linarith) : 1 / (1 + c) ≤ 1)
    · change c / (1 + c) + 1 / (1 + c) ≤ 1
      rw [← add_div, add_comm _ (1 : ℝ), div_self hd.ne']

private theorem linear_down {c p : ℝ} (hc : 0 < c) :
    mix p (linearMixing c hc).downWeight = c * p / (1+c) := by
  simp [mix, linearMixing]
  ring

private theorem linear_up {c p : ℝ} (hc : 0 < c) :
    mix p (linearMixing c hc).upWeight = 1/(1+c) := by
  simp [mix, linearMixing]
  ring

private noncomputable def reciprocalMixing (m : ℝ) (hm : 0 < m) : Mixing where
  downWeight _ := m / (1 + m)
  upWeight t := if t then 1 / (1 + m) else 0
  down_nonneg _ := by positivity
  up_nonneg t := by cases t <;> simp <;> positivity
  sum_le_one t := by
    have hd : 0 < 1 + m := by positivity
    cases t
    · simpa using ((div_le_iff₀ hd).2 (by linarith) : m / (1 + m) ≤ 1)
    · change m / (1 + m) + 1 / (1 + m) ≤ 1
      rw [← add_div, add_comm _ (1 : ℝ), div_self hd.ne']

private theorem reciprocal_down {m p : ℝ} (hm : 0 < m) :
    mix p (reciprocalMixing m hm).downWeight = m / (1+m) := by
  simp [mix, reciprocalMixing]
  ring

private theorem reciprocal_up {m p : ℝ} (hm : 0 < m) :
    mix p (reciprocalMixing m hm).upWeight = p/(1+m) := by
  simp [mix, reciprocalMixing, div_eq_mul_inv]

end Factory

open Factory

/-- Linear Bernoulli factory, with the guarantee of Huber (2016), Theorem 1 at
slack `1/2`. The proof uses a common two-direction walk for both factories. -/
private theorem huber_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 → c * p ≤ 1 / 2 →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (c * p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C * max 1 c) := by
  refine ⟨564, by norm_num, fun c hc => ⟨Stream, inferInstance, Proc.coinLaw, inferInstance,
    procedure (linearMixing c hc), ?_⟩⟩
  intro p hp hp' hcp
  have hd : 0 < 1 + c := by positivity
  have hb : 0 < mix p (linearMixing c hc).upWeight := by rw [linear_up hc]; positivity
  have hab : 2 * mix p (linearMixing c hc).downWeight ≤ mix p (linearMixing c hc).upWeight := by
    rw [linear_down hc, linear_up hc]
    calc
      2 * (c * p / (1 + c)) = (2 * (c * p)) / (1+c) := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hd).2 (by linarith)
  obtain ⟨hn,ht,hcst⟩ := procedure_spec (linearMixing c hc) hp hp' hb hab
  rw [linear_down hc, linear_up hc] at ht
  rw [show (c * p / (1+c)) / (1/(1+c)) = c*p by field_simp] at ht
  refine ⟨hn,ht,hcst.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [linear_up hc]
  have hm : 1 + c ≤ 2 * max 1 c := by
    linarith [le_max_left (1 : ℝ) c, le_max_right (1 : ℝ) c]
  calc
    282 / (1 / (1 + c)) = 282 * (1+c) := by simp
    _ ≤ _ := by linarith

/-- Scaled reciprocal Bernoulli factory, as in Lee–Doucet–Łatuszyński,
arXiv:1407.5770v1, Propositions 1, 2, and 4. -/
private theorem lee_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m → m ≤ 1 / 20 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 2 * m ≤ p → p ≤ 1 → p ≤ 200 * m →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (m / p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C / p) := by
  refine ⟨300, by norm_num, fun m hm hm' => ⟨Stream, inferInstance, Proc.coinLaw, inferInstance,
    procedure (reciprocalMixing m hm), ?_⟩⟩
  intro p hmp hp' _
  have hp : 0 < p := by linarith
  have hd : 0 < 1 + m := by positivity
  have hb : 0 < mix p (reciprocalMixing m hm).upWeight := by rw [reciprocal_up hm]; positivity
  have hab : 2 * mix p (reciprocalMixing m hm).downWeight ≤
      mix p (reciprocalMixing m hm).upWeight := by
    rw [reciprocal_down hm, reciprocal_up hm]
    calc
      2 * (m / (1 + m)) = (2*m) / (1+m) := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hd).2 hmp
  obtain ⟨hn,ht,hcst⟩ := procedure_spec (reciprocalMixing m hm) hp.le hp' hb hab
  rw [reciprocal_down hm, reciprocal_up hm] at ht
  rw [show (m / (1+m)) / (p/(1+m)) = m/p by field_simp] at ht
  refine ⟨hn,ht,hcst.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [reciprocal_up hm]
  calc
    282 / (p/(1+m)) = (282 * (1+m)) / p := by field_simp
    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right hp).mpr
      linarith

end BilateralProfitRegular
end BundlePart011


section BundlePart012


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem lemma_6_3 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by
  let M := muStar E
  have hM : 0 < M := (onUnit_facts E hE.1).2.2.2.1.1
  let A (t : ℝ × ℝ) := lam / E.cdfS t.1
  let B (t : ℝ × ℝ) := lam⁻¹ / (1 - E.cdfB t.2)
  let H (t : ℝ × ℝ) := (A t + B t) / 2
  let D (t : ℝ × ℝ) := (A t - B t) / 2
  let Δ (t : ℝ × ℝ) := M - auxProfit E lam t
  have hA {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < A t :=
    div_pos hlam (intT_cdf_pos E hE.1 ht).1
  have hB {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < B t :=
    div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 ht).2
  have hH {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < H t :=
    div_pos (add_pos (hA ht) (hB ht)) (by norm_num)
  have hmem {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      (s.1, t.2) ∈ BilateralProfitMHR.unitSq :=
    ⟨(intT_subset_unitSq hs).1, (intT_subset_unitSq ht).2⟩
  have hP {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      P E (s.1,t.2) * (A s * B t) = 1 := by
    rw [P_factor E hE.1 (hmem hs ht)]
    dsimp [A, B]
    have hs' := (intT_cdf_pos E hE.1 hs).1.ne'
    have ht' := (intT_cdf_pos E hE.1 ht).2.ne'
    field_simp [hlam.ne']
  have hPpos {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      0 < P E (s.1,t.2) := by
    rw [P_factor E hE.1 (hmem hs ht)]
    exact mul_pos (intT_cdf_pos E hE.1 hs).1 (intT_cdf_pos E hE.1 ht).2
  have hspread {t : ℝ × ℝ} (ht : t ∈ intT) :
      auxProfit E lam t * H t ^ 2 = t.2 - t.1 := by
    change (4 * (t.2 - t.1) / (A t + B t) ^ 2) * ((A t + B t) / 2) ^ 2 = _
    have hp := (add_pos (hA ht) (hB ht)).ne'
    field_simp
    ring
  have hdev {t : ℝ × ℝ} (ht : t ∈ intT) : M * D t ^ 2 ≤ Δ t * H t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (mu_le_muStar E hE.1 (intT_subset_unitSq ht))
      (mul_pos (hA ht) (hB ht)).le
    rw [mu_formula, mul_assoc, hP ht ht, mul_one] at hh
    have he : A t * B t = H t ^ 2 - D t ^ 2 := by unfold H D; ring
    rw [he, ← hspread ht] at hh
    dsimp [Δ]
    linarith only [hh]
  have hΔ {t : ℝ × ℝ} (ht : t ∈ intT) : 0 ≤ Δ t :=
    nonneg_of_mul_nonneg_left
      ((mul_nonneg hM.le (sq_nonneg _)).trans (hdev ht)) (pow_pos (hH ht) _)
  have hbds {t : ℝ × ℝ} (ht : t ∈ intT) (hr : 99 / 100 * M ≤ auxProfit E lam t) :
      9 / 10 * H t ≤ A t ∧ A t ≤ 11 / 10 * H t ∧
      9 / 10 * H t ≤ B t ∧ B t ≤ 11 / 10 * H t := by
    have hd : Δ t ≤ M / 100 := by dsimp [Δ]; linarith
    have hs := (hdev ht).trans (mul_le_mul_of_nonneg_right hd (sq_nonneg (H t)))
    have hh : D t ^ 2 ≤ (H t / 10) ^ 2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hs]
    have habs : |D t| ≤ H t / 10 := by
      rw [← sq_abs (D t)] at hh
      exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hH ht]) hh
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    unfold D H at hl hu
    unfold H
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  let G (s t : ℝ × ℝ) := M - mu E (s.1,t.2)
  have hG {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) : 0 ≤ G s t :=
    sub_nonneg.mpr (mu_le_muStar E hE.1 (hmem hs ht))
  have hG_eq {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      G s t * (A s * B t) = M * (A s * B t) - (t.2 - s.1) := by
    change (M - mu E (s.1,t.2)) * _ = _
    rw [sub_mul, mu_formula, mul_assoc, hP hs ht, mul_one]
  let S := G x z * (A x * B z) + G z x * (A z * B x)
  have hS0 : 0 ≤ S := add_nonneg (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le)
    (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le)
  have hS :
      S = Δ x * H x ^ 2 + Δ z * H z ^ 2 - M * (H x - H z) ^ 2 - 2 * M * D x * D z := by
    unfold S
    rw [hG_eq hx hz, hG_eq hz hx]
    have he : (z.2 - x.1) + (x.2 - z.1) = (x.2 - x.1) + (z.2 - z.1) := by ring
    rw [sub_add_sub_comm, he, ← hspread hx, ← hspread hz]
    unfold Δ D H
    ring
  have hcross : -(2 * M * D x * D z) ≤ M * D x ^ 2 + M * D z ^ 2 := by
    nlinarith only [mul_nonneg hM.le (sq_nonneg (D x + D z))]
  let m := max (H x) (H z)
  have hm : 0 < m := (hH hx).trans_le (le_max_left _ _)
  have hm₁ : H x ≤ m := le_max_left _ _
  have hm₂ : H z ≤ m := le_max_right _ _
  have hΔm : Δ x + Δ z ≤ M / 50 := by dsimp [Δ]; linarith only [hrx, hrz]
  have hSle : S ≤ 2 * (Δ x + Δ z) * m ^ 2 - M * (H x - H z) ^ 2 := by
    have hh₁ : H x ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hx).le hm₁ 2
    have hh₂ : H z ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hz).le hm₂ 2
    rw [hS]
    linarith only [hcross, hdev hx, hdev hz, mul_le_mul_of_nonneg_left hh₁ (hΔ hx),
      mul_le_mul_of_nonneg_left hh₂ (hΔ hz)]
  have hdiff : |H x - H z| ≤ m / 5 := by
    have hb := mul_le_mul_of_nonneg_right hΔm (sq_nonneg m)
    have ht : (H x - H z)^2 ≤ (m / 5)^2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hS0, hSle, hb]
    rw [← sq_abs (H x - H z)] at ht
    exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hm]) ht
  obtain ⟨hmd₁, hmd₂⟩ := abs_le.mp hdiff
  have hmin₁ : 4 / 5 * m ≤ H x := by
    dsimp [m] at hmd₁ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h] at hmd₁ ⊢
      linarith only [hmd₁]
    · rw [max_eq_left h]
      linarith only [hH hx]
  have hmin₂ : 4 / 5 * m ≤ H z := by
    dsimp [m] at hmd₂ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h]
      linarith only [hH hz]
    · rw [max_eq_left h] at hmd₂ ⊢
      linarith only [hmd₂]
  have hprod : 4 / 5 * m ^ 2 ≤ H x * H z := by
    by_cases h : H x ≤ H z
    · have he : m = H z := max_eq_right h
      calc
        (4 / 5) * m ^ 2 = (4 / 5 * m) * H z := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_right hmin₁ (hH hz).le
    · have he : m = H x := max_eq_left (le_of_not_ge h)
      calc
        (4 / 5) * m ^ 2 = H x * (4 / 5 * m) := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_left hmin₂ (hH hx).le
  obtain ⟨hax₁, hax₂, hbx₁, hbx₂⟩ := hbds hx hrx
  obtain ⟨haz₁, haz₂, hbz₁, hbz₂⟩ := hbds hz hrz
  have hab₁ : 16 / 25 * m ^ 2 ≤ A x * B z := by
    have he := mul_le_mul hax₁ hbz₁ (by linarith only [hH hz]) (hA hx).le
    nlinarith only [he, hprod]
  have hab₂ : 16 / 25 * m ^ 2 ≤ A z * B x := by
    have he := mul_le_mul haz₁ hbx₁ (by linarith only [hH hx]) (hA hz).le
    nlinarith only [he, hprod]
  have hGle {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hab : 16 / 25 * m ^ 2 ≤ A s * B t) (hg : G s t * (A s * B t) ≤ S) :
      G s t ≤ 4 * (Δ x + Δ z) := by
    have hlow := mul_le_mul_of_nonneg_left hab (hG hs ht)
    have hpos : 0 < m ^ 2 := pow_pos hm _
    have hd := add_nonneg (hΔ hx) (hΔ hz)
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hlow, hg, hSle, mul_nonneg hM.le (sq_nonneg (H x - H z)),
      mul_nonneg hd hpos.le]
  have hG₁ := hGle hx hz hab₁
    (le_add_of_nonneg_right (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le))
  have hG₂ := hGle hz hx hab₂
    (le_add_of_nonneg_left (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le))
  have htri {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hg : G s t ≤ 4 * (Δ x + Δ z)) : (s.1, t.2) ∈ triT := by
    have hp : 0 < mu E (s.1,t.2) := by dsimp [G] at hg; linarith only [hM, hg, hΔm]
    exact ⟨hs.1.le, le_of_lt ((onUnit_facts E hE.1).2.2.1 _ (hmem hs ht) |>.mp hp).2.1,
      ht.2.2.le⟩
  refine ⟨htri hx hz hG₁, htri hz hx hG₂, hG₁, hG₂, ?_⟩
  have hProb {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (ha₁ : 9 / 10 * H s ≤ A s) (ha₂ : A s ≤ 11 / 10 * H s)
      (hb₁ : 9 / 10 * H t ≤ B t) (hb₂ : B t ≤ 11 / 10 * H t)
      (hm_s : 4 / 5 * m ≤ H s) (hm_t : 4 / 5 * m ≤ H t)
      (hs_m : H s ≤ m) (ht_m : H t ≤ m) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E (s.1,t.2) ∧
        P E (s.1,t.2) ≤ 1 / ((18 / 25 * m) ^ 2) := by
    have hloA : 18 / 25 * m ≤ A s := by linarith only [ha₁, hm_s]
    have hloB : 18 / 25 * m ≤ B t := by linarith only [hb₁, hm_t]
    have hhiA : A s ≤ 11 / 10 * m := by linarith only [ha₂, hs_m]
    have hhiB : B t ≤ 11 / 10 * m := by linarith only [hb₂, ht_m]
    have he := hP hs ht
    have hv := (hPpos hs ht).le
    constructor
    · have hbound := mul_le_mul hhiA hhiB (hB ht).le (by linarith only [hm])
      apply (div_le_iff₀ (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
      simpa only [sq, mul_comm (P E (s.1,t.2))] using
        he.symm.le.trans (mul_le_mul_of_nonneg_left hbound hv)
    · have hbound := mul_le_mul hloA hloB (by linarith only [hm]) (hA hs).le
      apply (le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)).mpr
      simpa only [sq] using
        (mul_le_mul_of_nonneg_left hbound hv).trans he.le
  have hPall (a : ℝ × ℝ) (ha : a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ))) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E a ∧ P E a ≤ 1 / ((18 / 25 * m) ^ 2) := by
    simp only [mem_insert_iff, mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hProb hx hx hax₁ hax₂ hbx₁ hbx₂ hmin₁ hmin₁ hm₁ hm₁
    · exact hProb hz hz haz₁ haz₂ hbz₁ hbz₂ hmin₂ hmin₂ hm₂ hm₂
    · exact hProb hx hz hax₁ hax₂ hbz₁ hbz₂ hmin₁ hmin₂ hm₁ hm₂
    · exact hProb hz hx haz₁ haz₂ hbx₁ hbx₂ hmin₂ hmin₁ hm₂ hm₁
  intro a ha b hb
  apply (hPall a ha).2.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (hPall b hb).1 (by norm_num))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)
    (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
  nlinarith only [sq_nonneg m]

end BilateralProfitRegular
end BundlePart012


section BundlePart013



namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

/-- The known factor multiplying the product of the three Bernoulli outputs in (53). -/
private noncomputable def observationScale (c : Candidate) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  2000 * (ρ + ρ⁻¹)^2 / ((x.2 - x.1) * c.est)

/-- The conditional mean of one reciprocal bit, after selection between the crossed pairs. -/
private noncomputable def observationReciprocalMean (E : Environment) (c : Candidate) (ρ : ℝ)
    (x z : ℝ × ℝ) : ℝ :=
  (ρ / (ρ + ρ⁻¹)) * (c.est / (20 * P E (x.1,z.2))) +
  (1 - ρ / (ρ + ρ⁻¹)) * (c.est / (20 * P E (z.1,x.2)))

private theorem calibrated_candidate_profit (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (hc : c.Valid E δ) (z : ℝ × ℝ) (hz : z ∈ c.region)
    (ρ : ℝ) (hρ : CalibValid E η δ c z ρ) :
    ∀ x ∈ c.region, 99 / 100 * muStar E ≤ auxProfit E (ρ * balance E z) x ∧
      auxProfit E (ρ * balance E z) x ≤ mu E x ∧ mu E x ≤ muStar E := by
  rcases hc with ⟨hK, _, _, hw, haux, _⟩
  have hlam : 0 < ρ * balance E z := mul_pos hρ.1 (balance_pos E hE.1 (hK hz))
  have hp : 0 < c.param E := mul_pos (Real.exp_pos _) (balance_pos E hE.1 (hK hw))
  have hδ := hη.trans hηδ
  have hs : Real.sqrt (η / δ) ≤ 1 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨zero_le_one, by norm_num; exact (div_le_one hδ).2 hηδ.le⟩
  let u := Real.log (ρ * balance E z / c.param E)
  have hu : |u| ≤ 1 / 1000 := by
    have := hρ.2
    change |u| ≤ 1 / 1000 * Real.sqrt (η / δ) at this
    linarith
  have he : c.param E * Real.exp u = ρ * balance E z := by
    rw [Real.exp_log (div_pos hlam hp)]
    field_simp
  intro x hx
  exact ⟨he ▸ haux u hu x hx, (auxProfit_values E hE.1 hlam (hK hx)).2.2.2.1,
    mu_le_muStar E hE.1 (intT_subset_unitSq (hK hx))⟩

private theorem observation_mean_identity (E : Environment) (hE : RegularUnit E)
    (δ : ℝ) (hδ : 0 < δ) (c : Candidate) (hc : c.Valid E δ)
    (ρ : ℝ) (hρ : 0 < ρ) (x z : ℝ × ℝ) (hx : x ∈ c.region) (hz : z ∈ c.region) :
    observationScale c ρ x * (P E z / (20 * c.est)) *
      observationReciprocalMean E c ρ x z ^ 2 = 1 / auxProfit E (ρ * balance E z) x := by
  rcases hc with ⟨hK, _, _, _, _, hcross, hest, _⟩
  have hest' : 0 < c.est := hδ.trans_le hest
  have hspread : 0 < x.2 - x.1 := sub_pos.mpr (hK hx).2.1
  have hp₁ : 0 < P E (x.1,z.2) := lt_of_lt_of_le (by positivity)
    ((hcross x hx z hz).2.2 _ (by simp)).1
  have hp₂ : 0 < P E (z.1,x.2) := lt_of_lt_of_le (by positivity)
    ((hcross x hx z hz).2.2 _ (by simp)).1
  have ht : 0 < ρ + ρ⁻¹ := by positivity
  rw [eq_42 E hE x z (hK hx) (hK hz) ρ hρ]
  unfold observationScale observationReciprocalMean
  field_simp [hp₁.ne', hp₂.ne', hest'.ne', ht.ne', hρ.ne', hspread.ne']
  ring

private theorem observationScale_bounds (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (hc : c.Valid E δ)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (ρ : ℝ) (hρ : CalibValid E η δ c z ρ)
    (x : ℝ × ℝ) (hx : x ∈ c.region) :
    0 ≤ observationScale c ρ x ∧ observationScale c ρ x ≤ 81000 / δ := by
  have hCal := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ z hz
  rcases hc with ⟨hK, _, _, _, _, _, hest, _, hwidth⟩
  have hδ := hη.trans hηδ
  have hest' := hδ.trans_le hest
  have hspread : 0 < x.2 - x.1 := sub_pos.mpr (hK hx).2.1
  have hb := balance_pos E hE.1 (hK hz)
  have hlam := mul_pos hρ.1 hb
  have hsech := auxProfit_sech E hE.1 hlam (hK hz)
  have hr : ρ * balance E z / balance E z = ρ := mul_div_cancel_right₀ _ hb.ne'
  rw [hr, Real.exp_neg, Real.exp_log hρ.1] at hsech
  have ht : 0 < ρ + ρ⁻¹ := by have := hρ.1; positivity
  have hiden : auxProfit E (ρ * balance E z) z * (ρ + ρ⁻¹)^2 = 4 * mu E z := by
    rw [hsech]
    field_simp [hρ.1.ne'] <;> ring
  have hm := (onUnit_facts E hE.1).2.2.2.1.1
  have hsq : (ρ + ρ⁻¹)^2 ≤ 400 / 99 := by
    have hmul := mul_le_mul_of_nonneg_right hCal.1 (sq_nonneg (ρ + ρ⁻¹))
    rw [hiden] at hmul
    apply (le_of_mul_le_mul_right ?_ hm)
    nlinarith [hCal.2.2]
  have hW : 1 / ((x.2 - x.1) * c.est) ≤ 10 / δ := by
    have hineq := (div_le_iff₀ hspread).1 (hwidth x hx)
    apply (div_le_div_iff₀ (mul_pos hspread hest') hδ).2
    linarith
  constructor
  · unfold observationScale
    positivity
  · unfold observationScale
    calc
      _ = 2000 * ((ρ + ρ⁻¹)^2 * (1 / ((x.2 - x.1) * c.est))) := by ring
      _ ≤ 2000 * ((400 / 99) * (10 / δ)) := by gcongr
      _ ≤ _ := by
        rw [show 2000 * (400 / 99 * (10 / δ)) = (8000000 / 99) / δ by ring]
        exact (div_le_div_iff_of_pos_right hδ).2 (by norm_num)

private theorem observation_query_gap (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (hδmax : muStar E < 6 * δ) (hc : c.Valid E δ)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (ρ : ℝ) (hρ : CalibValid E η δ c z ρ)
    (x : ℝ × ℝ) (hx : x ∈ c.region) :
    ∀ y ∈ ({z, (x.1,z.2), (z.1,x.2)} : Set (ℝ × ℝ)),
      y ∈ triT ∧ muStar E - mu E y ≤
        8 * (muStar E - auxProfit E (ρ * balance E z) z) +
        144 * δ^2 * (1 / auxProfit E (ρ * balance E z) x -
          sInf ((fun a => 1 / auxProfit E (ρ * balance E z) a) '' c.region)) := by
  have hCal := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ
  have hK := hc.1
  have hlam := mul_pos hρ.1 (balance_pos E hE.1 (hK hz))
  let r := auxProfit E (ρ * balance E z)
  let L := fun y => 1 / r y
  let Lmin := sInf (L '' c.region)
  have hrpos : ∀ y ∈ c.region, 0 < r y := fun y hy => auxProfit_pos E hE.1 hlam (hK hy)
  have hrub : ∀ y ∈ c.region, r y ≤ muStar E := fun y hy => (hCal y hy).2.1.trans (hCal y hy).2.2
  have hLmin : ∀ y ∈ c.region, Lmin ≤ L y := by
    intro y hy
    apply csInf_le _ (mem_image_of_mem L hy)
    refine ⟨0, ?_⟩
    rintro _ ⟨a,ha,rfl⟩
    exact (one_div_pos.mpr (hrpos a ha)).le
  have hg : 0 ≤ L x - Lmin := sub_nonneg.mpr (hLmin x hx)
  have hr : r z - r x ≤ 36 * δ^2 * (L x - Lmin) := by
    have hid : r z - r x = r x * r z * (L x - L z) := by
      dsimp only [L]
      field_simp [(hrpos x hx).ne', (hrpos z hz).ne']
    have hδ := hη.trans hηδ
    have hprod : r x * r z ≤ 36 * δ^2 := by
      calc
        _ ≤ (6 * δ) * (6 * δ) := by
          exact mul_le_mul ((hrub x hx).trans hδmax.le) ((hrub z hz).trans hδmax.le)
            (hrpos z hz).le (by positivity)
        _ = _ := by ring
    rw [hid]
    calc
      _ ≤ r x * r z * (L x - Lmin) :=
        mul_le_mul_of_nonneg_left (by linarith [hLmin z hz]) (mul_nonneg (hrpos x hx).le (hrpos z hz).le)
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hg
  have hcross := lemma_6_3 E hE _ hlam x z (hK hx) (hK hz) (hCal x hx).1 (hCal z hz).1
  have hg' : 0 ≤ 144 * δ^2 * (L x - Lmin) := by positivity
  change ∀ y ∈ ({z, (x.1,z.2), (z.1,x.2)} : Set (ℝ × ℝ)),
    y ∈ triT ∧ muStar E - mu E y ≤ 8 * (muStar E - r z) + 144 * δ^2 * (L x - Lmin)
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with (rfl | rfl | rfl)
  · exact ⟨⟨(hK hz).1.le, (hK hz).2.1.le, (hK hz).2.2.le⟩,
      by linarith [(hCal y hz).2.1, hrub y hz]⟩
  · exact ⟨hcross.1, by linarith [hcross.2.2.1]⟩
  · exact ⟨hcross.2.1, by linarith [hcross.2.2.2.1]⟩

end BilateralProfitRegular
end BundlePart013


section BundlePart014



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set
open scoped ENNReal

set_option maxHeartbeats 900000

private abbrev Prices := ℝ × ℝ
private abbrev ObservationSeed := (Fin 3 → Uniform) × Stream
private abbrev ObservationHistory := List (Prices × Bool)
private abbrev ObservationState := Fin 3 → State

private noncomputable def selectorLaw : Measure (Fin 3 → Uniform) :=
  Measure.infinitePi fun _ => (volume : Measure Uniform)

private instance : IsProbabilityMeasure selectorLaw := by unfold selectorLaw; infer_instance

private noncomputable def observationSeedLaw : Measure ObservationSeed := selectorLaw.prod Proc.coinLaw

private instance : IsProbabilityMeasure observationSeedLaw := by unfold observationSeedLaw; infer_instance

private def observationSlot (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

private def slotTime (i : Fin 3) (n : ℕ) : ℕ := 3 * n + (i : ℕ)

private theorem slotTime_injective : Function.Injective (fun j : Fin 3 × ℕ => slotTime j.1 j.2) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  simp only [slotTime] at h
  have hi := i.isLt
  have hj := j.isLt
  have hjk : i = j := Fin.ext (by omega)
  have hks : k = l := by omega
  simp [hjk, hks]

private def slotCount (n : ℕ) (i : Fin 3) : ℕ := (n + 2 - (i : ℕ)) / 3

@[simp]
private theorem slotCount_zero (i : Fin 3) : slotCount 0 i = 0 := by
  unfold slotCount
  omega

@[simp]
private theorem slotCount_cycle (i : Fin 3) (k : ℕ) : slotCount (3*k) i = k := by
  have := i.isLt
  unfold slotCount
  omega

private theorem slotCount_succ (i : Fin 3) (n : ℕ) :
    slotCount (n+1) i = slotCount n i + if observationSlot n = i then 1 else 0 := by
  have hi := i.isLt
  by_cases h : observationSlot n = i
  · have hmod : n % 3 = i := congrArg Fin.val h
    simp only [slotCount, h, ↓reduceIte]
    omega
  · have hmod : n % 3 ≠ i := fun e => h (Fin.ext e)
    simp only [slotCount, h, ↓reduceIte, add_zero]
    omega

private theorem slotTime_slotCount (n : ℕ) :
    slotTime (observationSlot n) (slotCount n (observationSlot n)) = n := by
  unfold slotTime slotCount observationSlot
  dsimp
  omega

/-- A positive extension outside the parameter range of Lemma 6.5. -/
private noncomputable def positiveEstimate (est : ℝ) : ℝ := if 0 < est then est else 1

private theorem positiveEstimate_pos (est : ℝ) : 0 < positiveEstimate est := by
  unfold positiveEstimate
  split <;> simp_all

@[fun_prop]
private theorem measurable_positiveEstimate : Measurable positiveEstimate := by
  unfold positiveEstimate
  exact measurable_id.ite measurableSet_Ioi measurable_const

private noncomputable def observationMixing (est : ℝ) (i : Fin 3) : Mixing :=
  if i = 0 then linearMixing (1/(20 * positiveEstimate est))
    (one_div_pos.mpr (mul_pos (by norm_num) (positiveEstimate_pos _)))
  else reciprocalMixing (positiveEstimate est / 20)
    (div_pos (positiveEstimate_pos _) (by norm_num))

@[fun_prop]
private theorem measurable_obs_downWeight (i : Fin 3) (t : Bool) :
    Measurable (fun e => (observationMixing e i).downWeight t) := by
  by_cases hi : i = 0 <;> cases t
  all_goals simp only [observationMixing, hi, if_true, if_false, linearMixing, reciprocalMixing,
    Bool.false_eq_true] <;> try norm_num <;> fun_prop

@[fun_prop]
private theorem measurable_obs_upWeight (i : Fin 3) (t : Bool) :
    Measurable (fun e => (observationMixing e i).upWeight t) := by
  by_cases hi : i = 0 <;> cases t
  all_goals simp only [observationMixing, hi, if_true, if_false, linearMixing, reciprocalMixing,
    Bool.false_eq_true] <;> try norm_num <;> fun_prop

@[fun_prop]
private theorem measurable_obs_select (i : Fin 3) (t : Bool) :
    Measurable (fun es : (ℝ × Uniform) × State =>
      select (observationMixing es.1.1 i) es.1.2 t es.2) := by
  refine measurable_from_prod_countable_left ?_
  rintro (d | ⟨j,k⟩)
  · exact measurable_const
  · simp only [select]
    have hd : Measurable (fun es : ℝ × Uniform => (observationMixing es.1 i).downWeight t) :=
      (measurable_obs_downWeight i t).comp measurable_fst
    have hu : Measurable (fun es : ℝ × Uniform => (observationMixing es.1 i).upWeight t / scale j) :=
      ((measurable_obs_upWeight i t).comp measurable_fst).div_const _
    apply Measurable.ite _ measurable_const (Measurable.ite _ measurable_const
      (Measurable.ite _ measurable_const measurable_const))
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) hd
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hd.add (hu.mul_const _))
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hd.add hu)

private noncomputable def referenceWeight (ρ : ℝ) : ℝ := ρ / (ρ + ρ⁻¹)

private theorem referenceWeight_bounds {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ referenceWeight ρ ∧ referenceWeight ρ ≤ 1 := by
  unfold referenceWeight
  have h : 0 < ρ + ρ⁻¹ := by positivity
  exact ⟨div_nonneg hρ.le h.le, (div_le_one h).2 (le_add_of_nonneg_right (inv_pos.mpr hρ).le)⟩

private noncomputable def observationPrice (ρ : ℝ) (x z : Prices) (θ : Fin 3 → Uniform) (i : Fin 3) :
    Prices :=
  if i = 0 then z
  else if (θ i : ℝ) < referenceWeight ρ then (x.1,z.2) else (z.1,x.2)

private theorem observationPrice_mem (ρ : ℝ) (x z : Prices) (θ : Fin 3 → Uniform) (i : Fin 3) :
    observationPrice ρ x z θ i ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices) := by
  unfold observationPrice
  split
  · exact mem_insert _ _
  · split
    · exact mem_insert_of_mem _ (mem_insert _ _)
    · exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))

private noncomputable def observationCoefficient (est ρ : ℝ) (x : Prices) : ℝ :=
  2000 * (ρ + ρ⁻¹)^2 / ((x.2 - x.1) * est)

private def startObservation : ObservationState := fun _ => initial

private noncomputable def observationHistoryStep (est : ℝ) (ω : ObservationSeed)
    (s : ObservationState × ℕ) (q : Prices × Bool) : ObservationState × ℕ :=
  let i := observationSlot s.2
  (Function.update s.1 i (select (observationMixing est i) (ω.2 s.2) q.2 (s.1 i)), s.2 + 1)

private noncomputable def replayObservation (est : ℝ) (ω : ObservationSeed) (h : ObservationHistory) :
    ObservationState :=
  (h.foldl (observationHistoryStep est ω) (startObservation,0)).1

private theorem observation_fold_length (est : ℝ) (ω : ObservationSeed)
    (s : ObservationState × ℕ) (h : ObservationHistory) :
    (h.foldl (observationHistoryStep est ω) s).2 = s.2 + h.length := by
  induction h generalizing s with
  | nil => simp
  | cons q h ih => rw [List.foldl_cons, ih]; simp [observationHistoryStep]; omega

private theorem replayObservation_append (est : ℝ) (ω : ObservationSeed) (h : ObservationHistory)
    (q : Prices × Bool) :
    let i := observationSlot h.length
    replayObservation est ω (h ++ [q]) = Function.update (replayObservation est ω h) i
      (select (observationMixing est i) (ω.2 h.length) q.2 (replayObservation est ω h i)) := by
  simp [replayObservation, List.foldl_append, observationHistoryStep, observation_fold_length]

@[fun_prop]
private theorem measurable_replayObservation (h : ObservationHistory) :
    Measurable (fun ew : ℝ × ObservationSeed => replayObservation ew.1 ew.2 h) := by
  induction h using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton h q ih =>
    have heq : (fun ew : ℝ × ObservationSeed => replayObservation ew.1 ew.2 (h ++ [q])) =
      fun ew => Function.update (replayObservation ew.1 ew.2 h) (observationSlot h.length)
        (select (observationMixing ew.1 (observationSlot h.length)) (ew.2.2 h.length) q.2
          (replayObservation ew.1 ew.2 h (observationSlot h.length))) := by
      funext ew
      exact replayObservation_append ew.1 ew.2 h q
    rw [heq]
    apply measurable_pi_lambda
    intro i
    by_cases hslot : i = observationSlot h.length
    · subst i
      simp only [Function.update_self]
      have h₁ : Measurable (fun ew : ℝ × ObservationSeed => ew.2.2 h.length) :=
        (measurable_pi_apply h.length).comp (measurable_snd.comp measurable_snd)
      have h₂ : Measurable (fun ew : ℝ × ObservationSeed =>
          replayObservation ew.1 ew.2 h (observationSlot h.length)) :=
        (measurable_pi_apply (observationSlot h.length)).comp ih
      exact (measurable_obs_select (observationSlot h.length) q.2).comp
        ((measurable_fst.prodMk h₁).prodMk h₂)
    · simp only [Function.update_of_ne hslot]
      exact (measurable_pi_apply i).comp ih

private def observationStep (s : ObservationState) (y : Prices) (coef : ℝ) : Prices ⊕ ℝ :=
  if ∀ i, (s i).isLeft = true then
    .inr (if ∀ i, s i = .inl true then coef else 0)
  else .inl y

private instance : MeasurableSingletonClass ObservationState := inferInstance

@[fun_prop]
private theorem measurable_observationStep :
    Measurable (fun a : ObservationState × (Prices × ℝ) =>
      observationStep a.1 a.2.1 a.2.2) := by
  refine measurable_from_prod_countable_right ?_
  intro s
  unfold observationStep
  dsimp only
  by_cases hs : ∀ i, (s i).isLeft = true
  · by_cases ht : ∀ i, s i = .inl true
    · simp only [if_pos hs, if_pos ht]
      exact measurable_inr.comp (measurable_snd : Measurable (Prod.snd : Prices × ℝ → ℝ))
    · simp only [if_pos hs, if_neg ht]
      exact measurable_const
  · simp only [if_neg hs]
    exact measurable_inl.comp (measurable_fst : Measurable (Prod.fst : Prices × ℝ → Prices))

/-- The four numeric inputs suffice to implement the observation uniformly in the unknown law. -/
private noncomputable def observationAction (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    (h : ObservationHistory) : Prices ⊕ ℝ :=
  observationStep (replayObservation est ω h) (observationPrice ρ x z ω.1 (observationSlot h.length))
    (observationCoefficient est ρ x)

private abbrev ObservationArgs := (ℝ × ℝ) × (Prices × Prices) × ObservationSeed

private theorem measurable_observationAction (h : ObservationHistory) :
    Measurable (fun args : ObservationArgs =>
      observationAction args.1.1 args.1.2 args.2.1.1 args.2.1.2 args.2.2 h) := by
  let i := observationSlot h.length
  have hest : Measurable (fun args : ObservationArgs => args.1.1) :=
    measurable_fst.comp measurable_fst
  have hρ : Measurable (fun args : ObservationArgs => args.1.2) :=
    measurable_snd.comp measurable_fst
  have hx : Measurable (fun args : ObservationArgs => args.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hz : Measurable (fun args : ObservationArgs => args.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hω : Measurable (fun args : ObservationArgs => args.2.2) :=
    measurable_snd.comp measurable_snd
  have hS : Measurable (fun args : ObservationArgs => replayObservation args.1.1 args.2.2 h) := by
    simpa only [Function.comp_def] using ((measurable_replayObservation h).comp (hest.prodMk hω))
  have hP : Measurable (fun args : ObservationArgs =>
      observationPrice args.1.2 args.2.1.1 args.2.1.2 args.2.2.1 i) := by
    by_cases hi : i = 0
    · simp only [observationPrice, if_pos hi]
      exact hz
    · simp only [observationPrice, if_neg hi]
      have hθ : Measurable (fun args : ObservationArgs => (args.2.2.1 i : ℝ)) :=
        measurable_subtype_coe.comp ((measurable_pi_apply i).comp (measurable_fst.comp hω))
      apply Measurable.ite
        (measurableSet_lt hθ (hρ.div (hρ.add hρ.inv)))
      · exact (measurable_fst.comp hx).prodMk (measurable_snd.comp hz)
      · exact (measurable_fst.comp hz).prodMk (measurable_snd.comp hx)
  have hC : Measurable (fun args : ObservationArgs =>
      observationCoefficient args.1.1 args.1.2 args.2.1.1) :=
    (((hρ.add hρ.inv).pow_const 2).const_mul 2000).div
      (((measurable_snd.comp hx).sub (measurable_fst.comp hx)).mul hest)
  unfold observationAction
  simpa only [Function.comp_def] using
    (measurable_observationStep.comp (hS.prodMk (hP.prodMk hC)))

private noncomputable def observationProc (est ρ : ℝ) (x z : Prices) : Proc Prices ℝ ObservationSeed where
  step ω h := observationAction est ρ x z ω h
  measurable_step h := by
    have hh : Measurable (fun ω : ObservationSeed => (est,ω)) :=
      measurable_const.prodMk measurable_id
    have hS : Measurable (fun ω : ObservationSeed => replayObservation est ω h) :=
      (measurable_replayObservation h).comp hh
    let i := observationSlot h.length
    have hP : Measurable (fun ω : ObservationSeed => observationPrice ρ x z ω.1 i) := by
      by_cases hi : i = 0
      · simp only [observationPrice, if_pos hi]
        exact measurable_const
      · simp only [observationPrice, if_neg hi]
        have hθ : Measurable (fun ω : ObservationSeed => (ω.1 i : ℝ)) :=
          measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst)
        exact Measurable.ite (measurableSet_lt hθ measurable_const) measurable_const measurable_const
    exact measurable_observationStep.comp (hS.prodMk (hP.prodMk measurable_const))

private theorem observation_queries_first (est ρ : ℝ) (x z : Prices) :
    (observationProc est ρ x z).QueriesFirst := by
  intro ω
  simp [observationProc, observationAction, replayObservation, startObservation, initial, observationStep]

private theorem observation_queries (est ρ : ℝ) (x z : Prices) :
    (observationProc est ρ x z).QueriesIn {z,(x.1,z.2),(z.1,x.2)} := by
  intro ω h y hy
  change observationAction est ρ x z ω h = .inl y at hy
  unfold observationAction observationStep at hy
  split at hy
  · split at hy <;> contradiction
  · cases hy
    exact observationPrice_mem _ _ _ _ _

private theorem observation_outputs (est ρ L : ℝ) (x z : Prices)
    (h₀ : 0 ≤ observationCoefficient est ρ x) (hL : observationCoefficient est ρ x ≤ L) :
    (observationProc est ρ x z).OutputsIn (Set.Icc 0 L) := by
  intro ω h a ha
  change observationAction est ρ x z ω h = .inr a at ha
  unfold observationAction observationStep at ha
  split at ha
  · split at ha
    · cases ha
      exact ⟨h₀,hL⟩
    · cases ha
      exact ⟨le_rfl,h₀.trans hL⟩
  · contradiction

end BilateralProfitRegular.Factory
end BundlePart014


section BundlePart015


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option maxHeartbeats 900000

private abbrev ObservationSample := (Fin 3 → Uniform) × (Fin 3 → Inputs)
private abbrev ObservationPath := ObservationSeed × Stream

private def splitSlots (x : Inputs) (i : Fin 3) (n : ℕ) : Input := x (slotTime i n)

@[fun_prop]
private theorem measurable_splitSlots : Measurable splitSlots := by
  unfold splitSlots
  fun_prop

private noncomputable def observationLaw : Measure ObservationSample :=
  selectorLaw.prod (Measure.infinitePi fun _ => streamLaw)

private instance : IsProbabilityMeasure observationLaw := by unfold observationLaw; infer_instance

private def observationSample (x : ObservationPath) : ObservationSample :=
  (x.1.1, splitSlots (pairAt (x.1.2, x.2)))

@[fun_prop]
private theorem measurable_observationSample : Measurable observationSample := by
  unfold observationSample
  fun_prop

private theorem splitSlots_law :
    streamLaw.map splitSlots = Measure.infinitePi (fun _ : Fin 3 => streamLaw) := by
  let e := fun j : Fin 3 × ℕ => slotTime j.1 j.2
  have he : Measurable (fun x : Inputs => fun j => x (e j)) := by fun_prop
  have hsplit : splitSlots = (MeasurableEquiv.curry (Fin 3) ℕ Input) ∘
      (fun x : Inputs => fun j => x (e j)) := by rfl
  unfold streamLaw
  rw [hsplit, ← Measure.map_map (by fun_prop) he,
    Measure.map_infinitePi_infinitePi_of_inj slotTime_injective]
  exact Measure.infinitePi_map_curry (fun (_ : Fin 3) (_ : ℕ) => inputLaw)

private theorem observationSample_law :
    (Proc.law observationSeedLaw).map observationSample = observationLaw := by
  let e : ObservationPath ≃ᵐ ((Fin 3 → Uniform) × (Stream × Stream)) := MeasurableEquiv.prodAssoc
  have he := (measurePreserving_prodAssoc selectorLaw Proc.coinLaw Proc.coinLaw).map_eq
  have hcomp : observationSample =
      (Prod.map id (splitSlots ∘ pairAt)) ∘ e := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) e.measurable, Proc.law,
    observationSeedLaw, show ⇑e = _ from rfl, he, ← Measure.map_prod_map,
    Measure.map_id, ← Measure.map_map measurable_splitSlots measurable_pairAt]
  change (selectorLaw.prod (((Proc.law Proc.coinLaw).map pairAt).map splitSlots)) = _
  rw [paired_law]
  change selectorLaw.prod (streamLaw.map splitSlots) = _
  rw [splitSlots_law, observationLaw]
  all_goals fun_prop

private noncomputable def observationBias (prob : Prices → ℝ) (ρ : ℝ) (x z : Prices)
    (θ : Fin 3 → Uniform) (i : Fin 3) : ℝ := prob (observationPrice ρ x z θ i)

private noncomputable def observationTrace (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (a : ObservationSample) : ObservationState :=
  fun i => run (observationMixing est i) (observationBias prob ρ x z a.1 i)
    (slotCount n i) (a.2 i)

private theorem observationTrace_step (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    let a := observationSample (ω,U)
    let S := observationTrace est ρ x z prob n a
    let i := observationSlot n
    let y := observationPrice ρ x z ω.1 i
    observationTrace est ρ x z prob (n+1) a =
      Function.update S i (select (observationMixing est i) (ω.2 n)
        (decide ((U n : ℝ) < prob y)) (S i)) := by
  dsimp only
  funext j
  rw [observationTrace, slotCount_succ]
  by_cases hj : j = observationSlot n
  · subst j
    simp only [if_true, Function.update_self, run_succ, update]
    simp only [observationSample, splitSlots, pairAt, slotTime_slotCount,
      observationBias, observationTrace]
  · simp only [Ne.symm hj, if_false, add_zero, Function.update_of_ne hj, observationTrace]

private theorem observationTrace_absorbed (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream)
    (hf : ∀ i, (observationTrace est ρ x z prob n (observationSample (ω,U)) i).isLeft = true) :
    observationTrace est ρ x z prob (n+1) (observationSample (ω,U)) =
      observationTrace est ρ x z prob n (observationSample (ω,U)) := by
  rw [observationTrace_step]
  funext i
  by_cases hi : i = observationSlot n
  · subst i
    have h := hf (observationSlot n)
    cases hs : observationTrace est ρ x z prob n (observationSample (ω,U)) (observationSlot n) with
    | inl d => simp [select]
    | inr jk => simp [hs] at h
  · exact Function.update_of_ne hi _ _

private theorem observation_trace_eq_replay (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    let h := (observationProc est ρ x z).hist prob ω U n
    let S := observationTrace est ρ x z prob n (observationSample (ω,U))
    replayObservation est ω h = S ∧ ((¬ ∀ i, (S i).isLeft = true) → h.length = n) := by
  induction n with
  | zero =>
    constructor
    · funext i
      simp [observationTrace, run_zero, Proc.hist, replayObservation, startObservation]
    · simp [Proc.hist]
  | succ n ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨ih,hlen⟩
    let h := (observationProc est ρ x z).hist prob ω U n
    let S := observationTrace est ρ x z prob n (observationSample (ω,U))
    let i := observationSlot n
    let y := observationPrice ρ x z ω.1 i
    by_cases hdone : ∀ j, (S j).isLeft = true
    · have hs : (observationProc est ρ x z).step ω h =
          .inr (if ∀ j, S j = .inl true then observationCoefficient est ρ x else 0) := by
        change observationStep (replayObservation est ω h) _ _ = _
        rw [ih, observationStep, if_pos hdone]
      rw [Proc.hist, show (observationProc est ρ x z).step ω h = _ from hs]
      rw [observationTrace_absorbed est ρ x z prob n ω U hdone]
      exact ⟨ih, fun hh => (hh hdone).elim⟩
    · have hn : h.length = n := hlen hdone
      have hs : (observationProc est ρ x z).step ω h = .inl y := by
        change observationStep (replayObservation est ω h)
          (observationPrice ρ x z ω.1 (observationSlot h.length)) _ = _
        rw [ih, hn, observationStep, if_neg hdone]
      rw [Proc.hist, show (observationProc est ρ x z).step ω h = _ from hs]
      refine ⟨?_, fun _ => ?_⟩
      · rw [replayObservation_append, hn, ih, observationTrace_step]
      · simp [List.length_append, show ((observationProc est ρ x z).hist prob ω U n).length = n from hn]

private theorem observation_stopped_iff (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    (observationProc est ρ x z).stopped prob ω U n ↔
      ∀ i, (observationTrace est ρ x z prob n (observationSample (ω,U)) i).isLeft = true := by
  unfold Proc.stopped
  change (observationStep (replayObservation est ω ((observationProc est ρ x z).hist prob ω U n))
    _ _).isRight = true ↔ _
  rw [(observation_trace_eq_replay est ρ x z prob n ω U).1]
  unfold observationStep
  split <;> simp_all

private theorem slot_stop_exists (m : Mixing) (p : ℝ) (x : Inputs)
    (hx : totalRounds m p x ≠ ⊤) :
    ∃ (n : ℕ) (d : Bool), run m p n x = .inl d ∧ totalRounds m p x = n := by
  have hstop : ∃ n d, run m p n x = .inl d := by
    by_contra h
    exact hx ((never_finishes_iff m p x).mp h)
  let ω : Stream := fun n => (x n).1
  let U : Stream := fun n => (x n).2
  have he : pairAt (ω,U) = x := by funext n; exact Prod.eta _
  have hs : ∃ n, (procedure m).stopped (fun _ => p) ω U n := by
    rcases hstop with ⟨n,d,hd⟩
    exact ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,he ▸ hd⟩⟩
  have hrun := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hs)
  rw [he] at hrun
  rcases hrun with ⟨d,hd⟩
  refine ⟨_,d,hd,?_⟩
  have hRounds := rounds_eq_sum m p ω U
  rw [rounds_eq_find m p ω U hs, he] at hRounds
  simpa [totalRounds] using hRounds.symm

private theorem observation_rounds_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (ω : ObservationSeed) (U : Stream) :
    let a := observationSample (ω,U)
    ((observationProc est ρ x z).rounds prob ω U : ENNReal) ≤
      3 * ∑ i, totalRounds (observationMixing est i) (observationBias prob ρ x z a.1 i) (a.2 i) := by
  dsimp only
  let a := observationSample (ω,U)
  let total := fun i : Fin 3 => totalRounds (observationMixing est i)
    (observationBias prob ρ x z a.1 i) (a.2 i)
  by_cases h : ∃ i, total i = ⊤
  · rcases h with ⟨i,hi⟩
    have hsum : ∑ j, total j = ⊤ :=
      top_unique (hi ▸ Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i))
    change _ ≤ 3 * ∑ j, total j
    simp [hsum]
  · have h' (i : Fin 3) : total i ≠ ⊤ := fun hi => h ⟨i,hi⟩
    choose n d hd htotal using fun i : Fin 3 => slot_stop_exists (observationMixing est i)
      (observationBias prob ρ x z a.1 i) (a.2 i) (h' i)
    let N := ∑ i, n i
    have hni (i : Fin 3) : n i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hstop : (observationProc est ρ x z).stopped prob ω U (3*N) := by
      rw [observation_stopped_iff]
      intro i
      rw [observationTrace, slotCount_cycle, run_absorbed _ _ _ (hd i) (hni i)]
      rfl
    have hle : (observationProc est ρ x z).rounds prob ω U ≤ (3*N : ℕ) :=
      iInf_le_of_le (3*N) (iInf_le _ hstop)
    have hh := ENat.toENNReal_mono hle
    change _ ≤ 3 * ∑ j, total j
    simp only [show ∀ i, total i = n i from htotal]
    push_cast at hh ⊢
    simpa [N] using hh

end BilateralProfitRegular.Factory
end BundlePart015


section BundlePart016


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private theorem measurable_observationSlotFunction {α : Type} [MeasurableSpace α]
    (prob : Prices → ℝ) (ρ : ℝ) (x z : Prices) (i : Fin 3)
    (f : ℝ → Inputs → α) (hf : ∀ p, Measurable (f p)) :
    Measurable (fun s : ObservationSample => f (observationBias prob ρ x z s.1 i) (s.2 i)) := by
  have hx : Measurable (fun s : ObservationSample => s.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hi : i = 0
  · simpa only [observationBias, observationPrice, if_pos hi, Function.comp_def] using
      ((hf (prob z)).comp hx)
  · have heq : (fun s : ObservationSample =>
        f (observationBias prob ρ x z s.1 i) (s.2 i)) =
      fun s : ObservationSample =>
        if (s.1 i : ℝ) < referenceWeight ρ then f (prob (x.1,z.2)) (s.2 i)
        else f (prob (z.1,x.2)) (s.2 i) := by
      funext s
      unfold observationBias observationPrice
      rw [if_neg hi]
      split <;> rfl
    rw [heq]
    have hθ : Measurable (fun s : ObservationSample => (s.1 i : ℝ)) :=
      measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst)
    exact Measurable.ite (measurableSet_lt hθ measurable_const)
      ((hf _).comp hx) ((hf _).comp hx)

private noncomputable def observationSlotRounds (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) (s : ObservationSample) : ENNReal :=
  totalRounds (observationMixing est i) (observationBias prob ρ x z s.1 i) (s.2 i)

private theorem measurable_observationSlotRounds (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) : Measurable (observationSlotRounds est ρ x z prob i) :=
  measurable_observationSlotFunction prob ρ x z i _ (measurable_totalRounds _)

private theorem observation_slot_lintegral_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) (N : ENNReal)
    (hN : ∀ θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N) :
    (∫⁻ s, observationSlotRounds est ρ x z prob i s ∂observationLaw) ≤ N := by
  unfold observationLaw
  rw [lintegral_prod _ (measurable_observationSlotRounds est ρ x z prob i).aemeasurable]
  have he (θ : Fin 3 → Uniform) :
      (∫⁻ v, observationSlotRounds est ρ x z prob i (θ,v)
        ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) =
      ∫⁻ s, totalRounds (observationMixing est i) (observationBias prob ρ x z θ i) s ∂streamLaw := by
    change (∫⁻ v : Fin 3 → Inputs, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) (v i) ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) = _
    rw [← lintegral_map (measurable_totalRounds _ _) (measurable_pi_apply _),
      Measure.infinitePi_map_eval]
  simp_rw [he]
  exact (lintegral_mono hN).trans_eq (by simp)

private theorem observation_expRounds_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (N : Fin 3 → ENNReal)
    (hN : ∀ i θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N i) :
    (observationProc est ρ x z).expRounds prob observationSeedLaw ≤ 3 * ∑ i, N i := by
  unfold Proc.expRounds
  calc
    _ ≤ ∫⁻ s, (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i
        (observationSample s) ∂(Proc.law observationSeedLaw) :=
      lintegral_mono fun s => observation_rounds_le est ρ x z prob s.1 s.2
    _ = ∫⁻ s, (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i s ∂observationLaw := by
      have hm : Measurable (fun s => (3 : ENNReal) *
          ∑ i, observationSlotRounds est ρ x z prob i s) :=
        measurable_const.mul (Finset.measurable_fun_sum _ fun i _ =>
          measurable_observationSlotRounds est ρ x z prob i)
      rw [← lintegral_map hm measurable_observationSample, observationSample_law]
    _ = 3 * ∑ i, ∫⁻ s, observationSlotRounds est ρ x z prob i s ∂observationLaw := by
      rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ fun i _ =>
        measurable_observationSlotRounds est ρ x z prob i)]
      rw [lintegral_finsetSum _ (fun i _ => measurable_observationSlotRounds est ρ x z prob i)]
    _ ≤ _ := by
      gcongr with i _
      exact observation_slot_lintegral_le est ρ x z prob i (N i) (hN i)

private theorem observation_out_measured_none (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (N : Fin 3 → ENNReal) (hfin : ∀ i, N i ≠ ⊤)
    (hN : ∀ i θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N i) :
    Proc.law observationSeedLaw {s | (observationProc est ρ x z).out prob s.1 s.2 = none} = 0 := by
  have hfact (i : Fin 3) : ∀ᵐ s ∂observationLaw, observationSlotRounds est ρ x z prob i s < ⊤ := by
    exact ae_lt_top (measurable_observationSlotRounds est ρ x z prob i)
      (ne_top_of_le_ne_top (hfin i) (observation_slot_lintegral_le est ρ x z prob i _ (hN i)))
  have htop : ∀ᵐ s ∂(Proc.law observationSeedLaw), ∀ i,
      observationSlotRounds est ρ x z prob i (observationSample s) < ⊤ := by
    apply ae_all_iff.2
    intro i
    have hm := measurable_observationSlotRounds est ρ x z prob i
    have hfi := hfact i
    simpa only [observationSample_law] using
      (ae_map_iff measurable_observationSample.aemeasurable
        (measurableSet_lt hm measurable_const)).mp (by rw [observationSample_law]; exact hfi)
  have hn : ∀ᵐ s ∂(Proc.law observationSeedLaw),
      (observationProc est ρ x z).out prob s.1 s.2 ≠ none := by
    filter_upwards [htop] with s hs
    have hbound := observation_rounds_le est ρ x z prob s.1 s.2
    have hfin' : (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i (observationSample s) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr (fun i _ => (hs i).ne))
    have hrs : ((observationProc est ρ x z).rounds prob s.1 s.2 : ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin' hbound
    have hstop : ∃ n, (observationProc est ρ x z).stopped prob s.1 s.2 n := by
      by_contra h
      apply hrs
      have hr : (observationProc est ρ x z).rounds prob s.1 s.2 = ⊤ := by
        unfold Proc.rounds
        simp [not_exists.mp h]
      simp [hr]
    rw [Proc.out, dif_pos hstop]
    have he := Nat.find_spec hstop
    unfold Proc.stopped at he
    cases hh : (observationProc est ρ x z).step s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop)) with
    | inl y =>
      exact (Bool.noConfusion (he.symm.trans (congrArg Sum.isRight hh)))
    | inr b => simp
  simpa only [ae_iff, not_not] using hn

private def observationSuccess (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ) :
    Set ObservationSample :=
  {s | ∀ i, s.2 i ∈ success (observationMixing est i) (observationBias prob ρ x z s.1 i)}

private noncomputable def slotSuccessIndicator (m : Mixing) (p : ℝ) (s : Inputs) : ℝ :=
  (success m p).indicator (fun _ => 1) s

private theorem measurable_slotSuccessIndicator (m : Mixing) (p : ℝ) :
    Measurable (slotSuccessIndicator m p) := measurable_const.indicator (measurable_success m p)

private theorem slotSuccessIndicator_integral (m : Mixing) (p : ℝ) :
    (∫ s, slotSuccessIndicator m p s ∂streamLaw) = (streamLaw (success m p)).toReal := by
  simp [slotSuccessIndicator, integral_indicator (measurable_success m p), Measure.real]

private theorem observationSuccessIndicator_eq (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (s : ObservationSample) :
    (observationSuccess est ρ x z prob).indicator (fun _ => (1 : ℝ)) s =
      ∏ i, slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z s.1 i) (s.2 i) := by
  by_cases h : s ∈ observationSuccess est ρ x z prob
  · rw [Set.indicator_of_mem h]
    symm
    exact Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (h i) _)
  · have hn : ∃ i, s.2 i ∉ success (observationMixing est i)
        (observationBias prob ρ x z s.1 i) := by
      by_contra! h'
      exact h h'
    rcases hn with ⟨i,hi⟩
    rw [Set.indicator_of_notMem h, Finset.prod_eq_zero (Finset.mem_univ i)
      (show slotSuccessIndicator _ _ _ = 0 from Set.indicator_of_notMem hi _)]

private theorem measurable_observationSuccess (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ) :
    MeasurableSet (observationSuccess est ρ x z prob) := by
  have hm (i : Fin 3) : Measurable (fun s : ObservationSample =>
      slotSuccessIndicator (observationMixing est i)
        (observationBias prob ρ x z s.1 i) (s.2 i)) :=
    measurable_observationSlotFunction prob ρ x z i _ (measurable_slotSuccessIndicator _)
  have he : observationSuccess est ρ x z prob =
      {s | (∏ i, slotSuccessIndicator (observationMixing est i)
        (observationBias prob ρ x z s.1 i) (s.2 i)) = 1} := by
    ext s
    rw [mem_setOf_eq, ← observationSuccessIndicator_eq]
    by_cases h : s ∈ observationSuccess est ρ x z prob <;> simp [h]
  rw [he]
  exact (Finset.measurable_fun_prod _ (fun i _ => hm i)) (measurableSet_singleton _)

private theorem observation_out_getD (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (s : ObservationPath) :
    ((observationProc est ρ x z).out prob s.1 s.2).getD 0 =
      (observationSuccess est ρ x z prob).indicator
        (fun _ => observationCoefficient est ρ x) (observationSample s) := by
  let a := observationSample s
  let m := fun i => observationMixing est i
  let p := fun i => observationBias prob ρ x z a.1 i
  let A := observationSuccess est ρ x z prob
  by_cases hs : a ∈ A
  · have hex (i : Fin 3) : ∃ n, run (m i) (p i) n (a.2 i) = .inl true := hs i
    choose n hn using hex
    let N := ∑ i, n i
    have hni (i : Fin 3) : n i ≤ N :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hstop : ∃ k, (observationProc est ρ x z).stopped prob s.1 s.2 k := by
      refine ⟨3*N, (observation_stopped_iff est ρ x z prob _ _ _).mpr ?_⟩
      intro i
      rw [observationTrace, slotCount_cycle, run_absorbed _ _ _ (hn i) (hni i)]
      rfl
    rw [Proc.out, dif_pos hstop, Set.indicator_of_mem hs]
    change ((observationStep (replayObservation est s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop))) _ _).getRight?).getD 0 = _
    rw [(observation_trace_eq_replay est ρ x z prob _ _ _).1, observationStep,
      if_pos ((observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop))]
    have htrue (i : Fin 3) :
        observationTrace est ρ x z prob (Nat.find hstop) a i = .inl true := by
      let k := slotCount (Nat.find hstop) i
      have hdone := (observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop) i
      change (run (m i) (p i) k (a.2 i)).isLeft = true at hdone
      change run (m i) (p i) k (a.2 i) = _
      cases heq : run (m i) (p i) k (a.2 i) with
      | inl d =>
        have he₁ := run_absorbed _ _ _ heq (le_max_left k (n i))
        have he₂ := run_absorbed _ _ _ (hn i) (le_max_right k (n i))
        rw [he₁] at he₂
        exact he₂
      | inr jk => simp [heq] at hdone
    rw [if_pos (show _ from htrue)]
    rfl
  · rw [Set.indicator_of_notMem hs, Proc.out]
    split
    · rename_i hstop
      change ((observationStep (replayObservation est s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop))) _ _).getRight?).getD 0 = _
      rw [(observation_trace_eq_replay est ρ x z prob _ _ _).1, observationStep,
        if_pos ((observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop))]
      have hfalse : ¬ ∀ i, observationTrace est ρ x z prob (Nat.find hstop) a i = .inl true := by
        intro ht
        apply hs
        intro i
        exact ⟨slotCount (Nat.find hstop) i, ht i⟩
      rw [if_neg (show _ from hfalse)]
      rfl
    · rfl

end BilateralProfitRegular.Factory
end BundlePart016


section BundlePart017


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private theorem integral_uniform_choice {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (v w : ℝ) :
    (∫ θ : Uniform, if (θ : ℝ) < r then v else w) = r * v + (1-r) * w := by
  have heq : (fun θ : Uniform => if (θ : ℝ) < r then v else w) =
      fun θ : Uniform => (if (θ : ℝ) < r then v-w else 0) + w := by
    funext θ
    split <;> simp_all
  have hI : Integrable (fun θ : Uniform => if (θ : ℝ) < r then v-w else 0) volume := by
    change Integrable (({θ : Uniform | (θ : ℝ) < r} : Set Uniform).indicator (fun _ => v-w)) volume
    exact (integrable_const _).indicator (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [heq, integral_add hI (integrable_const w), integral_indicator_lt hr hr']
  simp
  ring

private theorem observation_mean_from_slots (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (f : Fin 3 → Uniform → ℝ) (hf : ∀ i u, 0 ≤ f i u)
    (hmean : ∀ θ i, streamLaw
      (success (observationMixing est i) (observationBias prob ρ x z θ i)) = ENNReal.ofReal (f i (θ i))) :
    (∫ s, ((observationProc est ρ x z).out prob s.1 s.2).getD 0 ∂(Proc.law observationSeedLaw)) =
      observationCoefficient est ρ x * ∏ i, ∫ θ : Uniform, f i θ := by
  let A := observationSuccess est ρ x z prob
  let c := observationCoefficient est ρ x
  have hA : MeasurableSet A := measurable_observationSuccess est ρ x z prob
  let I := A.indicator (fun _ => (1 : ℝ))
  have hI : Integrable I observationLaw := (integrable_const _).indicator hA
  have hIm : Measurable I := measurable_const.indicator hA
  have heq : (fun s : ObservationPath => ((observationProc est ρ x z).out prob s.1 s.2).getD 0) =
      fun s => c * I (observationSample s) := by
    funext s
    rw [observation_out_getD]
    change A.indicator (fun _ => c) (observationSample s) = _
    by_cases hs : observationSample s ∈ A <;> simp [I, hs]
  rw [heq, integral_const_mul,
    ← integral_map measurable_observationSample.aemeasurable hIm.aestronglyMeasurable,
    observationSample_law]
  congr 1
  unfold observationLaw at hI ⊢
  rw [integral_prod I hI]
  have hcond (θ : Fin 3 → Uniform) :
      (∫ v, I (θ,v) ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) = ∏ i, f i (θ i) := by
    have he : (fun v => I (θ,v)) = fun v =>
        ∏ i, slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z θ i) (v i) := by
      funext v
      exact observationSuccessIndicator_eq est ρ x z prob (θ,v)
    rw [he, Measure.infinitePi_eq_pi]
    rw [integral_fintype_prod_eq_prod
      (fun i => slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z θ i))]
    simp_rw [slotSuccessIndicator_integral, hmean θ, ENNReal.toReal_ofReal (hf _ _)]
  simp_rw [hcond]
  rw [selectorLaw, Measure.infinitePi_eq_pi, integral_fintype_prod_eq_prod f]

private theorem observation_slot_spec (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (he : 0 < est) (he' : est ≤ 1)
    (hp : ∀ y ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices),
      est / 10 ≤ prob y ∧ prob y ≤ 10 * est ∧ prob y ≤ 1) (θ : Fin 3 → Uniform) (i : Fin 3) :
    (∫⁻ s, totalRounds (observationMixing est i) (observationBias prob ρ x z θ i) s ∂streamLaw) ≤
      ENNReal.ofReal (3000 / est) ∧
    streamLaw (success (observationMixing est i) (observationBias prob ρ x z θ i)) =
      ENNReal.ofReal (if i = 0 then prob z / (20*est)
        else est / (20 * observationBias prob ρ x z θ i)) := by
  let y := observationPrice ρ x z θ i
  let p := prob y
  have hy := hp y (observationPrice_mem ρ x z θ i)
  have hp₀ : 0 < p := (by positivity : 0 < est/10).trans_le hy.1
  have hest : positiveEstimate est = est := by simp [positiveEstimate, he]
  by_cases hi : i = 0
  · have hyp : p = prob z := by simp [p, y, observationPrice, hi]
    let c := 1 / (20 * positiveEstimate est)
    have hc : 0 < c := by dsimp [c]; positivity [positiveEstimate_pos est]
    have hce : c = 1 / (20 * est) := by unfold c; rw [hest]
    have hcp : c * p ≤ 1/2 := by
      rw [hce]
      have he₁ : 0 < 20 * est := by positivity
      rw [one_div, inv_mul_eq_div]
      apply (div_le_iff₀ he₁).mpr
      linarith [hy.2.1]
    have hb : 0 < mix p (linearMixing c hc).upWeight := by rw [linear_up]; positivity
    have hab : 2 * mix p (linearMixing c hc).downWeight ≤ mix p (linearMixing c hc).upWeight := by
      rw [linear_down, linear_up]
      rw [show 2 * (c*p/(1+c)) = (2*(c*p))/(1+c) by ring]
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 1+c)).2
      linarith
    have hmean := stream_success (linearMixing c hc) hp₀.le hy.2.2 hb hab
    have hdur := lintegral_rounds_le (linearMixing c hc) hp₀.le hy.2.2 hb hab
    rw [linear_down, linear_up] at hmean
    rw [linear_up] at hdur
    simp only [if_pos hi, observationMixing]
    change _ ≤ _ ∧ _ = ENNReal.ofReal (prob z / (20*est))
    refine ⟨hdur.trans (ENNReal.ofReal_le_ofReal ?_), hmean.trans ?_⟩
    · calc
        282 / (1 / (1 + c)) = 282 * (1 + c) := by simp
        _ ≤ 3000 / est := by
          apply (le_div_iff₀ he).mpr
          rw [hce]
          have hh : (1 / (20 * est)) * est = 1 / 20 := by field_simp
          rw [mul_assoc, add_mul, hh, one_mul]
          linarith
    · congr 1
      rw [← hyp, hce]
      field_simp
  · let m := positiveEstimate est / 20
    have hm : 0 < m := div_pos (positiveEstimate_pos _) (by norm_num)
    have hme : m = est / 20 := by unfold m; rw [hest]
    have hmp : 2 * m ≤ p := by rw [hme]; linarith [hy.1]
    have hb : 0 < mix p (reciprocalMixing m hm).upWeight := by rw [reciprocal_up]; positivity
    have hab : 2 * mix p (reciprocalMixing m hm).downWeight ≤ mix p (reciprocalMixing m hm).upWeight := by
      rw [reciprocal_down, reciprocal_up]
      rw [show 2 * (m/(1+m)) = (2*m)/(1+m) by ring]
      exact (div_le_div_iff_of_pos_right (by positivity : 0 < 1+m)).2 hmp
    have hmean := stream_success (reciprocalMixing m hm) hp₀.le hy.2.2 hb hab
    have hdur := lintegral_rounds_le (reciprocalMixing m hm) hp₀.le hy.2.2 hb hab
    rw [reciprocal_down, reciprocal_up] at hmean
    rw [reciprocal_up] at hdur
    simp only [if_neg hi, observationMixing]
    change _ ≤ _ ∧ _ = ENNReal.ofReal (est / (20*p))
    refine ⟨hdur.trans (ENNReal.ofReal_le_ofReal ?_), hmean.trans ?_⟩
    · calc
        282 / (p/(1+m)) = (282 * (1+m))/p := by field_simp
        _ ≤ 300 / p := (div_le_div_iff_of_pos_right hp₀).2 (by rw [hme]; linarith)
        _ ≤ 3000 / est := by
          apply (div_le_div_iff₀ hp₀ he).2
          linarith [hy.1]
    · congr 1
      rw [hme]
      field_simp [hm.ne', hp₀.ne']

private theorem observation_law_spec (E : Environment) (hE : RegularUnit E)
    (δ : ℝ) (hδ : 0 < δ) (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (hρ : 0 < ρ)
    (x z : Prices) (hx : x ∈ c.region) (hz : z ∈ c.region) :
    (observationProc c.est ρ x z).expRounds (P E) observationSeedLaw ≤ ENNReal.ofReal (27000 / δ) ∧
    Proc.law observationSeedLaw {s | (observationProc c.est ρ x z).out (P E) s.1 s.2 = none} = 0 ∧
    (∫ s, ((observationProc c.est ρ x z).out (P E) s.1 s.2).getD 0 ∂(Proc.law observationSeedLaw)) =
      1 / auxProfit E (ρ * balance E z) x := by
  rcases hc with ⟨hK, hcompact, hconv, hw, haux, hcross, he, he', hwidth⟩
  have hc' : c.Valid E δ := ⟨hK,hcompact,hconv,hw,haux,hcross,he,he',hwidth⟩
  have he₀ := hδ.trans_le he
  have hp : ∀ y ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices),
      c.est / 10 ≤ P E y ∧ P E y ≤ 10 * c.est ∧ P E y ≤ 1 := by
    intro y hy
    have hy' : y ∈ ({x,z,(x.1,z.2),(z.1,x.2)} : Set Prices) := mem_insert_of_mem _ hy
    have hb := (hcross x hx z hz).2.2 y hy'
    exact ⟨hb.1,hb.2,((onUnit_facts E hE.1).1 y).2⟩
  let N : Fin 3 → ENNReal := fun _ => ENNReal.ofReal (3000 / c.est)
  have hb i θ := (observation_slot_spec c.est ρ x z (P E) he₀ he' hp θ i).1
  have hcost := observation_expRounds_le c.est ρ x z (P E) N hb
  have hcost' : 3 * ∑ i, N i ≤ ENNReal.ofReal (27000 / δ) := by
    simp only [N, Fin.sum_univ_three]
    have hp₀ : 0 ≤ 3000 / c.est := by positivity
    have hthree : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_num
    rw [← ENNReal.ofReal_add hp₀ hp₀, ← ENNReal.ofReal_add (add_nonneg hp₀ hp₀) hp₀,
      hthree, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (3 : ℝ) * (3000 / c.est + 3000 / c.est + 3000 / c.est) = 27000 / c.est by ring]
    exact div_le_div_of_nonneg_left (by norm_num) hδ he
  refine ⟨hcost.trans hcost', observation_out_measured_none _ _ _ _ _ N (fun _ => ENNReal.ofReal_ne_top) hb, ?_⟩
  let f := fun i (θ : Uniform) =>
    if i = (0 : Fin 3) then P E z / (20*c.est)
    else if (θ : ℝ) < referenceWeight ρ then c.est / (20*P E (x.1,z.2))
      else c.est / (20*P E (z.1,x.2))
  have hpos₁ : 0 < P E (x.1,z.2) := lt_of_lt_of_le (by positivity) (hp _ (by simp)).1
  have hpos₂ : 0 < P E (z.1,x.2) := lt_of_lt_of_le (by positivity) (hp _ (by simp)).1
  have hfn i θ : 0 ≤ f i θ := by
    unfold f
    split
    · have := ((onUnit_facts E hE.1).1 z).1
      positivity
    · split <;> positivity
  have hfm θ i := (observation_slot_spec c.est ρ x z (P E) he₀ he' hp θ i).2
  have hfm' θ i : streamLaw
      (success (observationMixing c.est i) (observationBias (P E) ρ x z θ i)) =
      ENNReal.ofReal (f i (θ i)) := by
    rw [hfm]
    by_cases hi : i=0
    · simp [f,hi]
    · unfold f observationBias observationPrice
      simp only [if_neg hi]
      split <;> rfl
  rw [observation_mean_from_slots c.est ρ x z (P E) f hfn hfm', Fin.prod_univ_three]
  have hm0 : (∫ θ : Uniform, f 0 θ) = P E z / (20*c.est) := by simp [f]
  have wm := referenceWeight_bounds hρ
  have hm (i : Fin 3) (hi : i ≠ 0) :
      (∫ θ : Uniform, f i θ) = observationReciprocalMean E c ρ x z := by
    simp only [f, if_neg hi]
    exact integral_uniform_choice wm.1 wm.2 _ _
  rw [hm0, hm 1 (by decide), hm 2 (by decide)]
  change observationScale c ρ x * (_ * _ * _) = _
  rw [show P E z / (20*c.est) * observationReciprocalMean E c ρ x z *
      observationReciprocalMean E c ρ x z =
      P E z / (20*c.est) * (observationReciprocalMean E c ρ x z)^2 by ring, ← mul_assoc]
  exact observation_mean_identity E hE δ hδ c hc' ρ hρ x z hx hz

end BilateralProfitRegular.Factory
end BundlePart017


section BundlePart018


namespace BilateralProfitRegular.Proc

open Classical MeasureTheory
open scoped ENNReal BigOperators

variable {Q α Ω : Type} [MeasurableSpace Q] [MeasurableSpace α] [MeasurableSpace Ω]

private theorem hist_eq_of_stopped (F : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval)
    {n m : ℕ} (h : F.stopped prob ω U n) (hnm : n ≤ m) :
    F.hist prob ω U m = F.hist prob ω U n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [hist, ih]
    unfold stopped at h
    cases hs : F.step ω (F.hist prob ω U n) with
    | inl y => simp [hs] at h
    | inr b => rfl

private theorem query_eq_none_iff_stopped (F : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω)
    (U : ℕ → unitInterval) (n : ℕ) :
    F.query prob ω U n = none ↔ F.stopped prob ω U n := by
  unfold query stopped
  cases F.step ω (F.hist prob ω U n) <;> simp

private theorem count_queries (F : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω) (U : ℕ → unitInterval) :
    (∑' n : ℕ, if F.query prob ω U n = none then (0 : ENNReal) else 1) =
      (F.rounds prob ω U : ENNReal) := by
  by_cases h : ∃ n, F.stopped prob ω U n
  · let k := Nat.find h
    have hk : F.stopped prob ω U k := Nat.find_spec h
    have hrounds : F.rounds prob ω U = (k : ℕ∞) := by
      unfold rounds
      apply le_antisymm
      · exact iInf_le_of_le k (iInf_le _ hk)
      · refine le_iInf (fun n => le_iInf (fun hn => ?_))
        exact_mod_cast Nat.find_min' h hn
    have hx (n : ℕ) : F.query prob ω U n = none ↔ k ≤ n := by
      rw [query_eq_none_iff_stopped]
      refine ⟨Nat.find_min' h, fun hn => ?_⟩
      unfold stopped at ⊢
      rw [hist_eq_of_stopped F prob ω U hk hn]
      exact hk
    rw [hrounds]
    have he : (fun n => if F.query prob ω U n = none then (0 : ENNReal) else 1) =
        (Finset.range k : Set ℕ).indicator (fun _ => 1) := by
      ext n
      by_cases hn : k ≤ n
      · simp [Set.indicator, (hx n).2 hn, Nat.not_lt.mpr hn]
      · simp [Set.indicator, show F.query prob ω U n ≠ none from fun hq => hn ((hx n).1 hq),
          Nat.lt_of_not_ge hn]
    rw [he, tsum_eq_sum (s := Finset.range k)]
    · calc
        _ = ∑ j ∈ Finset.range k, (1 : ENNReal) :=
          Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem hj _)
        _ = _ := by simp
    · exact fun j hj => Set.indicator_of_notMem hj _
  · have he : (fun n => if F.query prob ω U n = none then (0 : ENNReal) else 1) = fun _ => 1 := by
      funext n
      have hn : ¬ F.stopped prob ω U n := not_exists.mp h n
      simp [query_eq_none_iff_stopped, hn]
    unfold rounds
    simp [he, not_exists.mp h, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

/-- A uniform cost bound for every query extends to the expected total cost of a
procedure with a random duration. -/
private theorem expCost_le_mul_expRounds (F : Proc Q α Ω) (prob : Q → ℝ) (Pω : Measure Ω)
    (g : Q → ℝ) (B : ENNReal) (hB : B ≠ ⊤)
    (h : ∀ ω hs q, F.step ω hs = Sum.inl q → ENNReal.ofReal (g q) ≤ B) :
    F.expCost prob Pω g ≤ B * F.expRounds prob Pω := by
  unfold expCost expRounds
  calc
    _ ≤ ∫⁻ x, B * (F.rounds prob x.1 x.2 : ENNReal) ∂(law Pω) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← count_queries, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro n
      unfold query
      cases he : F.step x.1 (F.hist prob x.1 x.2 n) with
      | inl q => simpa using h x.1 _ q he
      | inr b => simp
    _ = _ := lintegral_const_mul' _ _ hB

end BilateralProfitRegular.Proc
end BundlePart018


section BundlePart019



namespace BilateralProfitRegular.Factory

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem observation_expected_regret (E : Environment) (hE : RegularUnit E)
    (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (hmax : muStar E < 6*δ)
    (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (z : Prices) (hz : z ∈ c.region)
    (hρ : CalibValid E η δ c z ρ) (x : Prices) (hx : x ∈ c.region) :
    let r := auxProfit E (ρ * balance E z)
    let L := fun x => 1 / r x
    (observationProc c.est ρ x z).expCost (P E) observationSeedLaw (fun y => muStar E - mu E y) ≤
      ENNReal.ofReal (216000 * (muStar E - r z) / δ) +
        ENNReal.ofReal (3888000 * δ) * ENNReal.ofReal (L x - sInf (L '' c.region)) := by
  dsimp only
  let r := auxProfit E (ρ * balance E z)
  let L := fun x => 1 / r x
  let g := muStar E - r z
  let l := L x - sInf (L '' c.region)
  let B := 8*g + 144*δ^2*l
  let F := observationProc c.est ρ x z
  have hδ : 0 < δ := hη.trans hηδ
  have hcp := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ z hz
  have hg : 0 ≤ g := sub_nonneg.mpr (hcp.2.1.trans hcp.2.2)
  have hL : BddBelow (L '' c.region) := by
    refine ⟨0,?_⟩
    rintro _ ⟨a,ha,rfl⟩
    have hlam := mul_pos hρ.1 (balance_pos E hE.1 (hc.1 hz))
    exact (one_div_pos.mpr (auxProfit_pos E hE.1 hlam (hc.1 ha))).le
  have hl : 0 ≤ l := sub_nonneg.mpr (csInf_le hL (mem_image_of_mem L hx))
  have hcost (ω : ObservationSeed) (h : ObservationHistory) (y : Prices) :
      F.step ω h = Sum.inl y → ENNReal.ofReal (muStar E - mu E y) ≤ ENNReal.ofReal B := by
    intro hy
    have hm := observation_queries c.est ρ x z ω h y hy
    exact ENNReal.ofReal_le_ofReal (observation_query_gap E hE c η δ hη hηδ hmax hc z hz ρ hρ x hx y hm).2
  have hrounds := (observation_law_spec E hE δ hδ c hc ρ hρ.1 x z hx hz).1
  calc
    _ ≤ ENNReal.ofReal B * F.expRounds (P E) observationSeedLaw :=
      Proc.expCost_le_mul_expRounds F (P E) observationSeedLaw _ _ ENNReal.ofReal_ne_top hcost
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (27000/δ) := by gcongr
    _ = ENNReal.ofReal (216000 * g / δ) + ENNReal.ofReal (3888000*δ) * ENNReal.ofReal l := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ B by unfold B; positivity),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3888000*δ),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 216000*g/δ) (by positivity)]
      congr 1
      unfold B
      field_simp [hδ.ne']
      ring

end BilateralProfitRegular.Factory
end BundlePart019


section BundlePart020



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

set_option maxHeartbeats 900000

private theorem measurable_update_with_bias (m : Mixing) :
    Measurable (fun a : State × (ℝ × Input) => update m a.2.1 a.1 a.2.2) := by
  refine measurable_from_prod_countable_right ?_
  intro s
  have he : (fun a : ℝ × Input => update m a.1 s a.2) = fun a : ℝ × Input =>
      if (a.2.2 : ℝ) < a.1 then select m a.2.1 true s else select m a.2.1 false s := by
    funext a
    by_cases ha : (a.2.2 : ℝ) < a.1 <;> simp [update, ha]
  rw [he]
  have hU : Measurable (fun a : ℝ × Input => (a.2.2 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hu : Measurable (fun a : ℝ × Input => a.2.1) := measurable_fst.comp measurable_snd
  exact Measurable.ite (measurableSet_lt hU measurable_fst)
    ((measurable_select m true s).comp hu) ((measurable_select m false s).comp hu)

private theorem measurable_run_with_bias (m : Mixing) (n : ℕ) :
    Measurable (fun a : ℝ × Inputs => run m a.1 n a.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [run_succ]
    exact (measurable_update_with_bias m).comp
      (ih.prodMk (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)))

private theorem measurable_price_with_query (ρ : ℝ) (z : Prices) (i : Fin 3) :
    Measurable (fun a : Prices × (Fin 3 → Uniform) => observationPrice ρ a.1 z a.2 i) := by
  by_cases hi : i = 0
  · simp only [observationPrice, if_pos hi]
    exact measurable_const
  · simp only [observationPrice, if_neg hi]
    have hθ : Measurable (fun a : Prices × (Fin 3 → Uniform) => (a.2 i : ℝ)) :=
      measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd)
    exact Measurable.ite (measurableSet_lt hθ measurable_const)
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)
      (measurable_const.prodMk (measurable_snd.comp measurable_fst))

private theorem measurable_slot_run_with_query (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob) (i : Fin 3) (n : ℕ) :
    Measurable (fun a : Prices × ObservationSample => run (observationMixing est i)
      (observationBias prob ρ a.1 z a.2.1 i) n (a.2.2 i)) := by
  have hθ : Measurable (fun a : Prices × ObservationSample => (a.1,a.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hb : Measurable (fun a : Prices × ObservationSample => observationBias prob ρ a.1 z a.2.1 i) :=
    hp.comp ((measurable_price_with_query ρ z i).comp hθ)
  have hs : Measurable (fun a : Prices × ObservationSample => a.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact (measurable_run_with_bias (observationMixing est i) n).comp (hb.prodMk hs)

private theorem measurable_success_with_query (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob) :
    MeasurableSet {a : Prices × ObservationSample | a.2 ∈ observationSuccess est ρ a.1 z prob} := by
  have hset : {a : Prices × ObservationSample | a.2 ∈ observationSuccess est ρ a.1 z prob} =
      ⋂ i : Fin 3, ⋃ n : ℕ, {a : Prices × ObservationSample |
        run (observationMixing est i) (observationBias prob ρ a.1 z a.2.1 i) n (a.2.2 i) = .inl true} := by
    ext a
    simp [observationSuccess, success]
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_slot_run_with_query est ρ z hp i n)
    (measurableSet_singleton (Sum.inl true : State))

private noncomputable def observationValue (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ)
    (a : Prices × ObservationPath) : ℝ :=
  ((observationProc est ρ a.1 z).out prob a.2.1 a.2.2).getD 0

private theorem measurable_observationValue (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob) : Measurable (observationValue est ρ z prob) := by
  have hmap : Measurable (fun a : Prices × ObservationPath => (a.1, observationSample a.2)) :=
    measurable_fst.prodMk (measurable_observationSample.comp measurable_snd)
  have hm := (measurable_success_with_query est ρ z hp).preimage hmap
  have hcoeff : Measurable (observationCoefficient est ρ) :=
    measurable_const.div ((measurable_snd.sub measurable_fst).mul_const est)
  have he : observationValue est ρ z prob =
      ((fun a : Prices × ObservationPath => (a.1, observationSample a.2)) ⁻¹'
        {a : Prices × ObservationSample | a.2 ∈ observationSuccess est ρ a.1 z prob}).indicator
        (fun a => observationCoefficient est ρ a.1) := by
    funext a
    unfold observationValue
    rw [observation_out_getD]
    rfl
  rw [he]
  exact (hcoeff.comp measurable_fst).indicator hm

private theorem measurable_tradeProbability (E : Environment) (hE : OnUnit E) : Measurable (P E) :=
  (BilateralProfitMHR.positive_density_profit_facts E hE).2.1

private theorem measurable_expectedProfit (E : Environment) (hE : OnUnit E) : Measurable (mu E) := by
  change Measurable (fun y : Prices => (y.2-y.1) * P E y)
  exact (measurable_snd.sub measurable_fst).mul (measurable_tradeProbability E hE)

private instance : IsProbabilityMeasure (Proc.law observationSeedLaw) := by
  unfold Proc.law
  infer_instance

private noncomputable def observationKernel (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ) :
    Kernel Prices ℝ :=
  (Kernel.id ×ₖ Kernel.const Prices (Proc.law observationSeedLaw)).map
    (observationValue est ρ z prob)

private theorem observationKernel_markov (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ)
    (hp : Measurable prob) : IsMarkovKernel (observationKernel est ρ z prob) := by
  unfold observationKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_observationValue est ρ z hp)

private theorem observationKernel_apply (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) (x : Prices) :
    observationKernel est ρ z prob x =
      (Proc.law observationSeedLaw).map (fun s => observationValue est ρ z prob (x,s)) := by
  unfold observationKernel
  rw [Kernel.map_apply _ (measurable_observationValue est ρ z hp)]
  ext s hs
  have hm : Measurable (fun s : ObservationPath => observationValue est ρ z prob (x,s)) :=
    (measurable_observationValue est ρ z hp).comp measurable_prodMk_left
  rw [Measure.map_apply (measurable_observationValue est ρ z hp) hs,
    Kernel.id_prod_apply' _ _ ((measurable_observationValue est ρ z hp) hs),
    Kernel.const_apply, Measure.map_apply hm hs]
  rfl

private noncomputable def observationEnv (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ) : ObsEnv Prices :=
  fun _ => (observationKernel est ρ z prob).comap Prod.snd measurable_snd

private theorem observationEnv_markov (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (τ : ℕ) : IsMarkovKernel (observationEnv est ρ z prob τ) := by
  letI := observationKernel_markov est ρ z prob hp
  unfold observationEnv
  infer_instance

private theorem observationEnv_apply (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) {τ : ℕ} (h : Fin τ → Prices × ℝ) (x : Prices) :
    observationEnv est ρ z prob τ (h,x) =
      (Proc.law observationSeedLaw).map (fun s => observationValue est ρ z prob (x,s)) :=
  observationKernel_apply est ρ z hp x

private theorem observationValue_bounded (E : Environment) (hE : RegularUnit E) (η δ : ℝ)
    (hη : 0 < η) (hηδ : η < δ) (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (z : Prices)
    (hz : z ∈ c.region) (hρ : CalibValid E η δ c z ρ) (x : Prices) (hx : x ∈ c.region)
    (s : ObservationPath) :
    observationValue c.est ρ z (P E) (x,s) ∈ Icc 0 (81000/δ) := by
  have hB : 0 ≤ 81000 / δ := by have := hη.trans hηδ; positivity
  unfold observationValue
  rw [observation_out_getD]
  by_cases hs : observationSample s ∈ observationSuccess c.est ρ x z (P E)
  · rw [Set.indicator_of_mem hs]
    exact observationScale_bounds E hE c η δ hη hηδ hc z hz ρ hρ x hx
  · rw [Set.indicator_of_notMem hs]
    exact ⟨le_rfl,hB⟩

private theorem observationEnv_contract (E : Environment) (hE : RegularUnit E) (η δ : ℝ)
    (hη : 0 < η) (hηδ : η < δ) (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (z : Prices)
    (hz : z ∈ c.region) (hρ : CalibValid E η δ c z ρ) :
    let ν := observationEnv c.est ρ z (P E)
    let L := fun x => 1 / auxProfit E (ρ * balance E z) x
    ν.MeanOn L c.region ∧ ν.ValuesIn c.region (Icc 0 (81000/δ)) := by
  dsimp only
  let ν := observationEnv c.est ρ z (P E)
  have hP := measurable_tradeProbability E hE.1
  have hm (x : Prices) : Measurable (fun s => observationValue c.est ρ z (P E) (x,s)) :=
    (measurable_observationValue c.est ρ z hP).comp measurable_prodMk_left
  refine ⟨⟨observationEnv_markov c.est ρ z hP,?_⟩,?_⟩
  · intro τ history x hx
    rw [observationEnv_apply _ _ _ hP]
    refine ⟨?_,?_⟩
    · apply (integrable_map_measure aestronglyMeasurable_id (hm x).aemeasurable).2
      apply Integrable.of_bound (hm x).aestronglyMeasurable (81000/δ)
      refine Filter.Eventually.of_forall (fun s => ?_)
      have hs := observationValue_bounded E hE η δ hη hηδ c hc ρ z hz hρ x hx s
      simpa [Real.norm_eq_abs, abs_of_nonneg hs.1] using hs.2
    · rw [integral_map (f := fun y : ℝ => y) (hm x).aemeasurable (measurable_id.aestronglyMeasurable)]
      exact (observation_law_spec E hE δ (hη.trans hηδ) c hc ρ hρ.1 x z hx hz).2.2
  · intro τ history x hx
    rw [observationEnv_apply _ _ _ hP, Measure.map_apply (hm x) measurableSet_Icc.compl]
    have he : (fun s => observationValue c.est ρ z (P E) (x,s)) ⁻¹' (Icc 0 (81000/δ))ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      exact fun s hs => hs (observationValue_bounded E hE η δ hη hηδ c hc ρ z hz hρ x hx s)
    rw [he, measure_empty]

end BilateralProfitRegular.Factory
end BundlePart020


section BundlePart021



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

/-- The total nonnegative cost incurred by one observation on its supplied tape. -/
private noncomputable def observationPathCost (est ρ : ℝ) (z : Prices) (prob g : Prices → ℝ)
    (a : Prices × ObservationPath) : ENNReal :=
  ∑' n, (((observationProc est ρ a.1 z).query prob a.2.1 a.2.2 n).map
    (fun y => ENNReal.ofReal (g y))).getD 0

private theorem measurable_observationPathCost (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) :
    Measurable (observationPathCost est ρ z prob g) := by
  unfold observationPathCost
  apply Measurable.tsum
  intro n
  let S := fun a : Prices × ObservationPath =>
    observationTrace est ρ a.1 z prob n (observationSample a.2)
  let y := fun a : Prices × ObservationPath =>
    observationPrice ρ a.1 z a.2.1.1 (observationSlot n)
  have hmS (i : Fin 3) : Measurable (fun a => S a i) := by
    have hm : Measurable (fun a : Prices × ObservationPath => (a.1, observationSample a.2)) :=
      measurable_fst.prodMk (measurable_observationSample.comp measurable_snd)
    exact (measurable_slot_run_with_query est ρ z hp i (slotCount n i)).comp hm
  have hmY : Measurable y := by
    have hθ : Measurable (fun a : Prices × ObservationPath => a.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_snd)
    exact (measurable_price_with_query ρ z (observationSlot n)).comp (measurable_fst.prodMk hθ)
  have hmD : MeasurableSet {a | ∀ i, (S a i).isLeft = true} := by
    have he : {a | ∀ i, (S a i).isLeft = true} = ⋂ i : Fin 3,
        {a | (S a i).isLeft = true} := by ext a; simp
    rw [he]
    exact MeasurableSet.iInter fun i =>
      (((measurable_of_countable Sum.isLeft).comp (hmS i)) (measurableSet_singleton true))
  have he : (fun a : Prices × ObservationPath =>
      (((observationProc est ρ a.1 z).query prob a.2.1 a.2.2 n).map
        (fun y => ENNReal.ofReal (g y))).getD 0) =
    fun a : Prices × ObservationPath =>
      if ∀ i, (S a i).isLeft = true then 0 else ENNReal.ofReal (g (y a)) := by
    funext a
    let h := (observationProc est ρ a.1 z).hist prob a.2.1 a.2.2 n
    have hr := observation_trace_eq_replay est ρ a.1 z prob n a.2.1 a.2.2
    have hs : replayObservation est a.2.1 h = S a := hr.1
    have hl : (¬ ∀ i, (S a i).isLeft = true) → h.length = n := hr.2
    unfold Proc.query
    change ((observationStep (replayObservation est a.2.1 h)
      (observationPrice ρ a.1 z a.2.1.1 (observationSlot h.length))
      (observationCoefficient est ρ a.1)).getLeft?.map (fun y => ENNReal.ofReal (g y))).getD 0 = _
    rw [hs, observationStep]
    by_cases hd : ∀ i, (S a i).isLeft = true
    · simp only [if_pos hd, Sum.getLeft?, Option.map_none, Option.getD_none]
    · rw [hl hd]
      simp only [if_neg hd, Sum.getLeft?, Option.map_some, Option.getD_some]
      rfl
  rw [he]
  exact Measurable.ite hmD measurable_const (ENNReal.measurable_ofReal.comp (hg.comp hmY))

private theorem measurable_observationExpectedCost (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) :
    Measurable (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g) := by
  exact (measurable_observationPathCost est ρ z hp hg).lintegral_prod_right'

variable {Ω : Type} [MeasurableSpace Ω]

/-- Nested integration over fresh independent tapes, one per adaptive observation. Each tape
supplies both the returned observation and the physical query cost of that same call. -/
private noncomputable def observationGo (A : BanditAlg Prices Ω)
    (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ) (cst : Prices × ObservationPath → ENNReal)
    (term : (τ : ℕ) → (Fin τ → Prices × ℝ) → ENNReal) :
    (k τ : ℕ) → Ω → (Fin τ → Prices × ℝ) → ENNReal
  | 0, τ, _, h => term τ h
  | k+1, τ, ω, h =>
    let x := A.query τ ω h
    ∫⁻ s, cst (x,s) +
      observationGo A est ρ z prob cst term k (τ+1) ω
        (Fin.snoc (α := fun _ => Prices × ℝ) h (x, observationValue est ρ z prob (x,s)))
        ∂(Proc.law observationSeedLaw)

private theorem observationGo_eq_go (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob)
    {pathCost : Prices × ObservationPath → ENNReal} (hc : Measurable pathCost)
    {term : (τ : ℕ) → (Fin τ → Prices × ℝ) → ENNReal} (ht : ∀ τ, Measurable (term τ))
    (k τ : ℕ) (ω : Ω) (h : Fin τ → Prices × ℝ) :
    observationGo A est ρ z prob pathCost term k τ ω h =
      A.go (observationEnv est ρ z prob)
        (fun x => ∫⁻ s, pathCost (x,s) ∂(Proc.law observationSeedLaw)) term k τ ω h := by
  let ν := observationEnv est ρ z prob
  let c := fun x => ∫⁻ s, pathCost (x,s) ∂(Proc.law observationSeedLaw)
  have hcm : Measurable c := hc.lintegral_prod_right'
  have hν := observationEnv_markov est ρ z hp
  induction k generalizing τ with
  | zero => rfl
  | succ k ih =>
    let x := A.query τ ω h
    let F := fun y => A.go ν c term k (τ+1) ω
      (Fin.snoc (α := fun _ => Prices × ℝ) h (x,y))
    have hsnoc : Measurable (fun y : ℝ =>
        (ω, Fin.snoc (α := fun _ => Prices × ℝ) h (x,y))) :=
      measurable_const.prodMk (BanditAlg.measurable_snoc_pair.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    have hF : Measurable F := (A.measurable_go ν hν hcm ht k (τ+1)).comp hsnoc
    have hm : Measurable (fun s => observationValue est ρ z prob (x,s)) :=
      (measurable_observationValue est ρ z hp).comp measurable_prodMk_left
    simp only [observationGo, BanditAlg.go, ih]
    change (∫⁻ s, pathCost (x,s) + F (observationValue est ρ z prob (x,s))
        ∂(Proc.law observationSeedLaw)) = c x + ∫⁻ y, F y ∂(ν τ (h,x))
    have hc' : Measurable (fun s : ObservationPath => pathCost (x,s)) :=
      hc.comp measurable_prodMk_left
    rw [lintegral_add_left hc', observationEnv_apply _ _ _ hp, lintegral_map hF hm]

private theorem observation_trajectory_exp (A : BanditAlg Prices Ω) (Pω : Measure Ω)
    (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob) (n : ℕ)
    {f : (Fin n → Prices × ℝ) → ENNReal} (hf : Measurable f) :
    (∫⁻ ω, observationGo A est ρ z prob (fun _ => 0)
      (fun τ h => if hn : τ = n then f (fun i => h (Fin.cast hn.symm i)) else 0)
      n 0 ω Fin.elim0 ∂Pω) =
      A.trajExp (observationEnv est ρ z prob) Pω n f := by
  unfold BanditAlg.trajExp
  have ht (τ : ℕ) : Measurable (fun h : Fin τ → Prices × ℝ =>
      if hn : τ = n then f (fun i => h (Fin.cast hn.symm i)) else 0) := by
    split <;> rename_i h
    · subst τ
      simpa only [Fin.cast_eq_self] using hf
    · exact measurable_const
  apply lintegral_congr
  intro ω
  have he := observationGo_eq_go A est ρ z hp (pathCost := fun _ => 0)
    (measurable_const) ht n 0 ω Fin.elim0
  simpa only [lintegral_zero, Pi.zero_def] using he

private theorem go_cost_affine_bound (A : BanditAlg Prices Ω) (ν : ObsEnv Prices)
    (hν : ∀ τ, IsMarkovKernel (ν τ)) (K : Set Prices) (hK : A.QueriesIn K)
    (c d : Prices → ENNReal) (a b : ENNReal) (hb : b ≠ ⊤)
    (hlocal : ∀ x ∈ K, c x ≤ a + b*d x) (k τ : ℕ) (ω : Ω) (h : Fin τ → Prices × ℝ) :
    A.go ν c (fun _ _ => 0) k τ ω h ≤
      k*a + b*A.go ν d (fun _ _ => 0) k τ ω h := by
  induction k generalizing τ with
  | zero => simp [BanditAlg.go]
  | succ k ih =>
    let x := A.query τ ω h
    let H := fun y => Fin.snoc (α := fun _ => Prices × ℝ) h (x,y)
    let μ := ν τ (h,x)
    haveI := hν τ
    let G := fun y => A.go ν d (fun _ _ => 0) k (τ+1) ω (H y)
    have hstep : c x ≤ a + b*d x := hlocal x (hK τ ω h)
    have hs :
        (∫⁻ y, A.go ν c (fun _ _ => 0) k (τ+1) ω (H y) ∂μ) ≤
          (k : ENNReal)*a + b * ∫⁻ y, G y ∂μ := by
      calc
        _ ≤ ∫⁻ y, (k : ENNReal)*a + b*G y ∂μ := lintegral_mono fun y => ih _ (H y)
        _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ hb, lintegral_const]
          have hm : μ univ = 1 := measure_univ
          rw [hm, mul_one]
    rw [BanditAlg.go, BanditAlg.go]
    change c x + (∫⁻ y, A.go ν c (fun _ _ => 0) k (τ+1) ω (H y) ∂μ) ≤
      (↑(k+1) : ENNReal)*a + b*(d x + ∫⁻ y, G y ∂μ)
    apply (add_le_add hstep hs).trans
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, mul_add]
    exact le_of_eq (by ac_rfl)

/-- The expected trading regret of one complete virtual run, evaluated on fresh tapes. -/
private theorem observation_run_cost (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (E : Environment) (hE : RegularUnit E) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (hmax : muStar E < 6*δ) (c : Candidate) (hc : c.Valid E δ) (hK : A.QueriesIn c.region)
    (ρ : ℝ) (z : Prices) (hz : z ∈ c.region) (hρ : CalibValid E η δ c z ρ) (n : ℕ) :
    let L := fun x => 1 / auxProfit E (ρ * balance E z) x
    (∫⁻ ω, observationGo A c.est ρ z (P E)
        (observationPathCost c.est ρ z (P E) (fun y => muStar E - mu E y))
        (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) ≤
      n * ENNReal.ofReal (216000 * (muStar E - auxProfit E (ρ * balance E z) z) / δ) +
        ENNReal.ofReal (3888000*δ) *
        A.regret (observationEnv c.est ρ z (P E)) Pω n L c.region := by
  dsimp only
  let ν := observationEnv c.est ρ z (P E)
  let g := fun y => muStar E - mu E y
  let L := fun x => 1 / auxProfit E (ρ * balance E z) x
  let a := ENNReal.ofReal (216000 * (muStar E - auxProfit E (ρ * balance E z) z) / δ)
  let b := ENNReal.ofReal (3888000*δ)
  let cst := fun x => (observationProc c.est ρ x z).expCost (P E) observationSeedLaw g
  let gap := fun x => ENNReal.ofReal (L x - sInf (L '' c.region))
  have hP := measurable_tradeProbability E hE.1
  have hg : Measurable g := measurable_const.sub (measurable_expectedProfit E hE.1)
  have hpath := measurable_observationPathCost c.est ρ z hP hg
  have hν := observationEnv_markov c.est ρ z hP
  have hb : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlocal : ∀ x ∈ c.region, cst x ≤ a+b*gap x :=
    fun x hx => observation_expected_regret E hE η δ hη hηδ hmax c hc ρ z hz hρ x hx
  have he (ω : Ω) :
      observationGo A c.est ρ z (P E) (observationPathCost c.est ρ z (P E) g)
          (fun _ _ => 0) n 0 ω Fin.elim0 =
        A.go ν cst (fun _ _ => 0) n 0 ω Fin.elim0 :=
    observationGo_eq_go A c.est ρ z hP hpath (fun _ => measurable_const) _ _ _ _
  calc
    _ = ∫⁻ ω, A.go ν cst (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω := lintegral_congr he
    _ ≤ ∫⁻ ω, (n : ENNReal)*a + b*A.go ν gap (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω :=
      lintegral_mono fun ω => go_cost_affine_bound A ν hν c.region hK cst gap a b hb
        hlocal n 0 ω Fin.elim0
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ hb, lintegral_const,
        measure_univ, mul_one]
      rfl

end BilateralProfitRegular.Factory
end BundlePart021


section BundlePart022


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- The real indicator for a trade bit with bias `p`. -/
private noncomputable def hit (p : ℝ) (u : Uniform) : ℝ := if (u : ℝ) < p then 1 else 0

@[fun_prop]
private theorem measurable_hit (p : ℝ) : Measurable (hit p) :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
    measurable_const measurable_const

private theorem hit_nonneg (p : ℝ) (u : Uniform) : 0 ≤ hit p u := by unfold hit; split <;> norm_num

private theorem hit_le_one (p : ℝ) (u : Uniform) : hit p u ≤ 1 := by unfold hit; split <;> norm_num

private theorem bernoulli_mgf_le {p lam : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hlam : |lam| ≤ 1) :
    (∫ u : Uniform, Real.exp (lam * (hit p u - p))) ≤ Real.exp (p * lam^2) := by
  let a := Real.exp (lam * (1-p))
  let b := Real.exp (lam * (0-p))
  have heq : (fun u : Uniform => Real.exp (lam * (hit p u - p))) =
      fun u : Uniform => (if (u : ℝ) < p then a-b else 0) + b := by
    funext u
    by_cases h : (u : ℝ) < p <;> simp [hit, h, a,b]
  have hi : Integrable (fun u : Uniform => if (u : ℝ) < p then a-b else 0) volume := by
    change Integrable (({u : Uniform | (u : ℝ) < p} : Set Uniform).indicator (fun _ => a-b)) volume
    exact (integrable_const _).indicator (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [heq]
  have hAdd := integral_add hi (integrable_const b)
  rw [hAdd, integral_indicator_lt hp hp', integral_const, probReal_univ, one_smul]
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hlam)).2
  calc
    _ = Real.exp (-lam*p) * (1+p*(Real.exp lam-1)) := by
      dsimp [a,b]
      rw [show lam*(1-p) = -lam*p + lam by ring, Real.exp_add]
      simp only [zero_sub]
      rw [show lam * -p = -lam*p by ring]
      ring
    _ ≤ Real.exp (-lam*p) * Real.exp (p * (lam+lam^2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      calc
        _ ≤ 1 + p * (lam + lam^2) := by
          nlinarith [mul_nonneg hp (show 0 ≤ lam^2 - (Real.exp lam - 1 - lam) by linarith)]
        _ ≤ _ := by linarith only [Real.add_one_le_exp (p * (lam + lam^2))]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Number of trades in a block indexed by distinct coordinates of the uniform stream. -/
private noncomputable def hitCount {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) (U : Stream) : ℝ :=
  ∑ i, hit p (U (coord i))

@[fun_prop]
private theorem measurable_hitCount {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) :
    Measurable (hitCount p coord) := by
  unfold hitCount
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_hit p).comp (measurable_pi_apply _)

private theorem hitCount_bounds {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) (U : Stream) :
    0 ≤ hitCount p coord U ∧ hitCount p coord U ≤ n := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => hit_nonneg _ _
  · calc
      _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun _ _ => hit_le_one _ _
      _ = _ := by simp

private theorem hitCount_mgf_le {n : ℕ} {p lam : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hlam : |lam| ≤ 1)
    (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    (∫ U, Real.exp (lam * (hitCount p coord U - n*p)) ∂Proc.coinLaw) ≤
      Real.exp (n*p*lam^2) := by
  have hi : iIndepFun (fun i (U : Stream) => U (coord i)) Proc.coinLaw :=
    (iIndepFun_infinitePi (X := fun (_ : ℕ) (u : Uniform) => u) (by fun_prop)).precomp hc
  let f := fun u : Uniform => Real.exp (lam * (hit p u - p))
  have hfm : Measurable f := Real.measurable_exp.comp ((measurable_hit p).sub_const p |>.const_mul lam)
  have heq : (fun U : Stream => Real.exp (lam * (hitCount p coord U - n*p))) =
      fun U => ∏ i, f (U (coord i)) := by
    funext U
    change _ = ∏ i, Real.exp (lam * (hit p (U (coord i)) - p))
    rw [← Real.exp_sum]
    congr 1
    simp only [hitCount, mul_sub, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [heq, hi.integral_fun_prod_comp
    (fun i => (measurable_pi_apply (coord i)).aemeasurable)
    (fun _ => hfm.aestronglyMeasurable)]
  have hiaval (i : Fin n) :
      (∫ U, f (U (coord i)) ∂Proc.coinLaw) = ∫ u, f u ∂(volume : Measure Uniform) := by
    rw [← integral_map (measurable_pi_apply (coord i)).aemeasurable hfm.aestronglyMeasurable]
    exact congrArg (fun μ => ∫ u, f u ∂μ) (Measure.infinitePi_map_eval _ _)
  simp_rw [hiaval]
  calc
    _ ≤ ∏ _ : Fin n, Real.exp (p*lam^2) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => Real.exp_nonneg _)
        (fun _ _ => bernoulli_mgf_le hp hp' hlam)
    _ = _ := by simp [Real.exp_nat_mul, mul_assoc]

private theorem hitCount_tail_one_side {n : ℕ} {p ε s : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hs : s = 1 ∨ s = -1)
    (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    Proc.coinLaw {U | ε * n * p ≤ s * (hitCount p coord U - n*p)} ≤
      ENNReal.ofReal (Real.exp (-(n*p*ε^2/4))) := by
  let lam := s * ε / 2
  let Z := fun U : Stream => Real.exp (lam * (hitCount p coord U - n*p))
  let t := Real.exp (n*p*ε^2/2)
  have ht : 0 < t := Real.exp_pos _
  have hlam : |lam| ≤ 1 := by rcases hs with rfl | rfl <;>
    simp [lam, abs_div, abs_of_nonneg hε] <;> linarith
  have hZ : Measurable Z :=
    Real.measurable_exp.comp ((measurable_hitCount p coord).sub_const _ |>.const_mul lam)
  have hZint : Integrable Z Proc.coinLaw := by
    apply Integrable.of_bound hZ.aestronglyMeasurable (Real.exp (|lam| * n))
    refine Filter.Eventually.of_forall fun U => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have hcount := hitCount_bounds p coord U
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hn' : (n : ℝ) * p ≤ n := by nlinarith
    have hb : |hitCount p coord U - n*p| ≤ n := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    exact (le_abs_self _).trans (by rw [abs_mul]; gcongr)
  have hmgf := hitCount_mgf_le hp hp' hlam coord hc
  have hlamsq : lam^2 = ε^2/4 := by rcases hs with rfl | rfl <;> dsimp [lam] <;> ring
  have hset : {U | ε * n * p ≤ s * (hitCount p coord U - n*p)} ⊆
      {U | ENNReal.ofReal t ≤ ENNReal.ofReal (Z U)} := by
    intro U hU
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hU (show 0 ≤ ε/2 by positivity)
    dsimp [lam]
    nlinarith
  calc
    _ ≤ Proc.coinLaw {U | ENNReal.ofReal t ≤ ENNReal.ofReal (Z U)} := measure_mono hset
    _ ≤ (∫⁻ U, ENNReal.ofReal (Z U) ∂Proc.coinLaw) / ENNReal.ofReal t :=
      meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hZ).aemeasurable
        (by simpa using ht) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (n*p*lam^2)) / ENNReal.ofReal t := by
      rw [← ofReal_integral_eq_lintegral_ofReal hZint (Filter.Eventually.of_forall (fun U => Real.exp_nonneg _))]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmgf) _
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos ht, hlamsq]
      dsimp [t]
      rw [← Real.exp_sub]
      congr 2
      ring

private theorem hitCount_relative_tail {n : ℕ} {p ε : ℝ} (hn : 0 < n) (hp : 0 < p) (hp' : p ≤ 1)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    Proc.coinLaw {U | ε < |(hitCount p coord U / n) / p - 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(n*p*ε^2/4))) := by
  let A : Set Stream := {U | ε * n * p ≤ (1 : ℝ) * (hitCount p coord U - n*p)}
  let B : Set Stream := {U | ε * n * p ≤ (-1 : ℝ) * (hitCount p coord U - n*p)}
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hset : {U | ε < |(hitCount p coord U / n) / p - 1|} ⊆ A ∪ B := by
    intro U hU
    change ε < |(hitCount p coord U / n) / p - 1| at hU
    have den : 0 < (n : ℝ)*p := mul_pos hn' hp
    rw [div_div, show hitCount p coord U / ((n : ℝ)*p) - 1 =
      (hitCount p coord U - n*p) / (n*p) by field_simp, abs_div, abs_of_pos den,
      lt_div_iff₀ den] at hU
    rcases lt_abs.mp hU with h | h
    · left
      change ε * n * p ≤ (1 : ℝ) * (hitCount p coord U - n*p)
      nlinarith
    · right
      change ε * n * p ≤ (-1 : ℝ) * (hitCount p coord U - n*p)
      nlinarith
  calc
    _ ≤ Proc.coinLaw (A ∪ B) := measure_mono hset
    _ ≤ Proc.coinLaw A + Proc.coinLaw B := measure_union_le _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (hitCount_tail_one_side hp.le hp' hε hε' (.inl rfl) coord hc)
        (hitCount_tail_one_side hp.le hp' hε hε' (.inr rfl) coord hc)

end BilateralProfitRegular.Factory
end BundlePart022


section BundlePart023




namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 600000

private abbrev CalibrationPrices := ℝ × ℝ
private abbrev CalibrationHistory := List (CalibrationPrices × Bool)

private noncomputable def calibrationSamples (T : ℕ) (η δ est : ℝ) : ℕ :=
  ⌈1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est)⌉₊

private noncomputable def historyFrequency (n j : ℕ) (h : CalibrationHistory) : ℝ :=
  (∑ i : Fin n, if (h[j+i.val]?.getD ((0,0),false)).2 then (1 : ℝ) else 0) / n

private noncomputable def calibrationValue (off f₁ f₂ : ℝ) : ℝ :=
  Real.exp (off - (1 / 2) * Real.log (f₁ / f₂))

private noncomputable def calibrationStep (n : ℕ) (off : ℝ) (y₁ y₂ : CalibrationPrices)
    (h : CalibrationHistory) : CalibrationPrices ⊕ ℝ :=
  if h.length < n then .inl y₁
  else if h.length < 2*n then .inl y₂
  else .inr (calibrationValue off (historyFrequency n 0 h) (historyFrequency n n h))

private noncomputable def calibrationProc (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices) :
    Proc CalibrationPrices ℝ Unit where
  step _ h := calibrationStep (calibrationSamples T η δ est) off (z.1,w.2) (w.1,z.2) h
  measurable_step _ := measurable_const

private theorem calibration_queries (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices) :
    (calibrationProc T η δ est off w z).QueriesIn {(z.1,w.2),(w.1,z.2)} := by
  intro ω h y hy
  change calibrationStep _ _ _ _ h = Sum.inl y at hy
  unfold calibrationStep at hy
  split at hy
  · cases hy
    exact mem_insert _ _
  · split at hy
    · cases hy
      exact mem_insert_of_mem _ (mem_singleton _)
    · contradiction

private theorem measurable_calibrationValue :
    Measurable (fun a : ℝ × ℝ × ℝ => calibrationValue a.1 a.2.1 a.2.2) := by
  unfold calibrationValue
  fun_prop

private theorem measurable_calibrationStep (h : CalibrationHistory) :
    Measurable (fun a : ℕ × ℝ × CalibrationPrices × CalibrationPrices =>
      calibrationStep a.1 a.2.1 a.2.2.1 a.2.2.2 h) := by
  refine measurable_from_prod_countable_right ?_
  intro n
  unfold calibrationStep
  dsimp only
  by_cases hn : h.length < n
  · simp only [if_pos hn]
    exact measurable_inl.comp (measurable_fst.comp measurable_snd)
  · by_cases hn' : h.length < 2*n
    · simp only [if_neg hn, if_pos hn']
      exact measurable_inl.comp (measurable_snd.comp measurable_snd)
    · simp only [if_neg hn, if_neg hn']
      exact measurable_inr.comp (measurable_calibrationValue.comp
        (measurable_fst.prodMk (measurable_const : Measurable
          (fun _ : ℝ × CalibrationPrices × CalibrationPrices =>
            (historyFrequency n 0 h, historyFrequency n n h)))))

private theorem measurable_calibration (T : ℕ) (η : ℝ) (h : CalibrationHistory) :
    Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (calibrationProc T η a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2).step () h) := by
  have hn : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      calibrationSamples T η a.1 a.2.1) := by
    unfold calibrationSamples
    apply Nat.measurable_ceil.comp
    fun_prop
  have hoff : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      a.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hy₁ : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (a.2.2.2.2.1,a.2.2.2.1.2)) := by fun_prop
  have hy₂ : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (a.2.2.2.1.1,a.2.2.2.2.2)) := by fun_prop
  exact (measurable_calibrationStep h).comp (hn.prodMk (hoff.prodMk (hy₁.prodMk hy₂)))

private noncomputable def calibrationHistory (n k : ℕ) (y₁ y₂ : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) : CalibrationHistory :=
  List.ofFn fun i : Fin k =>
    let y := if i.val < n then y₁ else y₂
    (y, decide ((U i.val : ℝ) < prob y))

private theorem calibration_history (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) (k : ℕ) :
    let n := calibrationSamples T η δ est
    (calibrationProc T η δ est off w z).hist prob () U k =
      calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U := by
  let n := calibrationSamples T η δ est
  let F := calibrationProc T η δ est off w z
  let y₁ := (z.1,w.2)
  let y₂ := (w.1,z.2)
  have hfstep (hh : CalibrationHistory) : F.step () hh = calibrationStep n off y₁ y₂ hh := rfl
  change F.hist prob () U k = calibrationHistory n (min k (2*n)) y₁ y₂ prob U
  induction k with
  | zero => simp [calibrationHistory, Proc.hist]
  | succ k ih =>
    rw [Proc.hist, ih, hfstep]
    have hh : (calibrationHistory n (min k (2*n)) y₁ y₂ prob U).length = min k (2*n) := by
      simp [calibrationHistory]
    by_cases hk : k < 2*n
    · have hk' : min (k+1) (2*n) = k+1 := min_eq_left (by omega)
      have hh' : min k (2*n) = k := min_eq_left hk.le
      rw [hk', hh']
      rw [hh'] at hh
      unfold calibrationStep
      simp only [hh, if_pos hk]
      by_cases hkn : k < n
      · simp only [if_pos hkn, calibrationHistory]
        rw [List.ofFn_succ_last]
        simp only [Fin.val_castSucc, Fin.val_last, hkn, if_true]
      · simp only [if_neg hkn, calibrationHistory]
        rw [List.ofFn_succ_last]
        simp only [Fin.val_castSucc, Fin.val_last, hkn, if_false]
    · have h₁ : min k (2*n) = 2*n := min_eq_right (Nat.le_of_not_gt hk)
      have h₂ : min (k+1) (2*n) = 2*n := min_eq_right (by omega)
      rw [h₁] at hh
      rw [h₁,h₂]
      unfold calibrationStep
      simp only [hh, if_neg (show ¬ (2*n < n) by omega), lt_irrefl, if_false]

private theorem calibration_stopped (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) (k : ℕ) :
    (calibrationProc T η δ est off w z).stopped prob () U k ↔
      2 * calibrationSamples T η δ est ≤ k := by
  let n := calibrationSamples T η δ est
  unfold Proc.stopped
  rw [calibration_history]
  change (calibrationStep n off (z.1,w.2) (w.1,z.2)
    (calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U)).isRight = true ↔ 2*n ≤ k
  have hlen : (calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U).length =
      min k (2*n) := by simp [calibrationHistory]
  unfold calibrationStep
  simp only [hlen]
  split
  · have : ¬ 2*n ≤ k := by omega
    simp [this]
  · split
    · have : ¬ 2*n ≤ k := by omega
      simp [this]
    · have : 2*n ≤ k := by omega
      simp [this]

private theorem calibration_out (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) :
    let n := calibrationSamples T η δ est
    let p₁ := prob (z.1,w.2)
    let p₂ := prob (w.1,z.2)
    (calibrationProc T η δ est off w z).out prob () U =
      some (calibrationValue off
        (hitCount p₁ (fun i : Fin n => i.val) U / n)
        (hitCount p₂ (fun i : Fin n => n+i.val) U / n)) := by
  dsimp only
  let n := calibrationSamples T η δ est
  let F := calibrationProc T η δ est off w z
  let y₁ := (z.1,w.2)
  let y₂ := (w.1,z.2)
  have hs := calibration_stopped T η δ est off w z prob U
  have he : ∃ k, F.stopped prob () U k := ⟨2*n, (hs _).2 le_rfl⟩
  have hfind : Nat.find he = 2*n :=
    le_antisymm (Nat.find_min' he ((hs _).2 le_rfl)) ((hs _).1 (Nat.find_spec he))
  change F.out prob () U = _
  rw [Proc.out, dif_pos he, hfind, calibration_history]
  change (F.step () (calibrationHistory n (min (2*n) (2*n)) y₁ y₂ prob U)).getRight? = _
  rw [min_self]
  have hstep (h : CalibrationHistory) : F.step () h = calibrationStep n off y₁ y₂ h := rfl
  rw [hstep]
  have hlen : (calibrationHistory n (2*n) y₁ y₂ prob U).length = 2*n := by simp [calibrationHistory]
  unfold calibrationStep
  simp only [hlen, if_neg (show ¬ (2*n < n) by omega), lt_irrefl, if_false, Sum.getRight?]
  have hf (j : ℕ) (hj : j = 0 ∨ j = n) :
      historyFrequency n j (calibrationHistory n (2*n) y₁ y₂ prob U)
        = hitCount (prob (if j = 0 then y₁ else y₂)) (fun i : Fin n => j+i.val) U / n := by
    unfold historyFrequency hitCount
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    have hji : j + i.val < (calibrationHistory n (2*n) y₁ y₂ prob U).length := by
      rw [hlen]
      rcases hj with rfl | rfl <;> omega
    rw [List.getElem?_eq_getElem hji, Option.getD_some]
    simp only [calibrationHistory, List.getElem_ofFn, hit]
    rcases hj with rfl | rfl
    · simp [hi]
    · have hn : ¬ n + i.val < n := by omega
      have hn' : n ≠ 0 := by omega
      simp [hn, hn']
  rw [hf 0 (.inl rfl)]
  by_cases hn : n = 0
  · simp [hn, show calibrationSamples T η δ est = 0 from hn, historyFrequency, hitCount]
  · rw [hf n (.inr rfl)]
    simp only [hn, if_false, if_true, zero_add]
    rfl

end BilateralProfitRegular.Factory
end BundlePart023


section BundlePart024


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 900000

private theorem calibration_T_ge_two (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1)
    (hT : gridK η ≤ T) : 2 ≤ T := by
  have hK : 1 < gridK η := by
    by_contra! hK
    have hd : 1 < 1/η := (lt_div_iff₀ hη).2 (by linarith)
    exact (not_le_of_gt hd) (le_trans (Nat.le_ceil (1/η)) (by exact_mod_cast hK))
  omega

private theorem calibration_samples_pos (T : ℕ) (hT : 2 ≤ T) (η δ est : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < est) : 0 < calibrationSamples T η δ est := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 < Real.log (2 * (T : ℝ)) := Real.log_pos (by linarith)
  have hceil := Nat.le_ceil (1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est))
  have hpos : (0 : ℝ) < calibrationSamples T η δ est :=
    (by positivity : 0 < 1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est)).trans_le hceil
  exact_mod_cast hpos

private theorem calibration_samples_le (T : ℕ) (hT : 2 ≤ T) (η δ est : ℝ)
    (hη : 0 < η) (hη' : η < 1) (hδ : 0 < δ) (he : δ ≤ est) :
    2 * (calibrationSamples T η δ est : ℝ) ≤ 5000000000 * Real.log T / η := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := by linarith
  have hlog : 0 < Real.log (2 * (T : ℝ)) := Real.log_pos (by linarith)
  have hlogT : (1/2 : ℝ) ≤ Real.log T := (by
    linarith [Real.log_two_gt_d9] : (1/2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hTr)
  have hlog' : Real.log (2 * (T : ℝ)) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hTr]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1000000000 * δ *
    Real.log (2 * (T : ℝ)) / (η * est) by have := hδ.trans_le he; positivity)
  have hfrac : 1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est) ≤
      2000000000 * Real.log T / η := by
    apply (div_le_div_iff₀ (mul_pos hη (hδ.trans_le he)) hη).mpr
    have hmain : δ * Real.log (2 * (T : ℝ)) ≤ est * (2 * Real.log T) :=
      mul_le_mul he hlog' hlog.le (hδ.trans_le he).le
    nlinarith [mul_le_mul_of_nonneg_right hmain hη.le]
  have hone : (1 / 2 : ℝ) ≤ Real.log T / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hceil' : (calibrationSamples T η δ est : ℝ) <
      1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est) + 1 := hceil
  apply le_trans (show 2 * (calibrationSamples T η δ est : ℝ) ≤
      2 * (2000000000 * Real.log T / η + 1) by linarith)
  rw [show (5000000000 : ℝ) * Real.log T / η = 5000000000 * (Real.log T / η) by ring]
  rw [show (2000000000 : ℝ) * Real.log T / η = 2000000000 * (Real.log T / η) by ring]
  linarith

private theorem log_ratio_close {f p ε : ℝ} (hp : 0 < p) (hε : ε ≤ 1/2)
    (h : |f/p-1| ≤ ε) : 0 < f ∧ |Real.log (f/p)| ≤ 2*ε := by
  have hfp : 0 < f/p := by linarith [(abs_le.mp h).1]
  have hf : 0 < f := (div_pos_iff.mp hfp).resolve_right (fun hneg => (not_lt_of_gt hp) hneg.2) |>.1
  let t := f/p - 1
  have ht : |t| ≤ ε := h
  have hlt : |-t| < 1 := by rw [abs_neg]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le hlt 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, zero_add, pow_one, abs_neg] at hb
  have he : 1 - -t = f/p := by unfold t; ring
  rw [he] at hb
  refine ⟨hf, hb.trans ?_⟩
  have hden : 0 < 1 - |t| := by linarith
  apply (div_le_iff₀ hden).mpr
  have hε₀ : 0 ≤ ε := (abs_nonneg t).trans ht
  have hden' : (1/2 : ℝ) ≤ 1 - |t| := by linarith
  have hmul := mul_le_mul_of_nonneg_left hden' (by positivity : 0 ≤ 2*ε)
  linarith

private theorem calibration_valid_of_relative (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (δ η : ℝ) (hc : c.Valid E δ) (z : CalibrationPrices)
    (hz : z ∈ c.region) (ε : ℝ) (hε : ε ≤ 1/2)
    (hε' : 2*ε ≤ 1/1000 * Real.sqrt (η/δ))
    (f₁ f₂ : ℝ)
    (hp₁ : 0 < P E (z.1,c.root.2)) (hp₂ : 0 < P E (c.root.1,z.2))
    (h₁ : |f₁ / P E (z.1,c.root.2) - 1| ≤ ε)
    (h₂ : |f₂ / P E (c.root.1,z.2) - 1| ≤ ε) :
    CalibValid E η δ c z (calibrationValue c.offset f₁ f₂) := by
  let p₁ := P E (z.1,c.root.2)
  let p₂ := P E (c.root.1,z.2)
  have hz' := hc.1 hz
  have hw' := hc.1 hc.2.2.2.1
  have bz := balance_pos E hE.1 hz'
  have bw := balance_pos E hE.1 hw'
  rcases log_ratio_close hp₁ hε h₁ with ⟨hf₁,hl₁⟩
  rcases log_ratio_close hp₂ hε h₂ with ⟨hf₂,hl₂⟩
  let ρ := calibrationValue c.offset f₁ f₂
  have hρ : 0 < ρ := Real.exp_pos _
  refine ⟨hρ,?_⟩
  have hEq := eq_47 E hE z c.root hz' hw'
  change |Real.log (ρ * balance E z / c.param E)| ≤ _
  have hlog : Real.log (ρ * balance E z / c.param E) =
      (1/2) * (Real.log (f₂/p₂) - Real.log (f₁/p₁)) := by
    rw [Candidate.param, Real.log_div (mul_pos hρ bz).ne' (mul_pos (Real.exp_pos _) bw).ne',
      Real.log_mul hρ.ne' bz.ne', Real.log_mul (Real.exp_pos _).ne' bw.ne', Real.log_exp]
    have hdiff : Real.log (balance E z) - Real.log (balance E c.root) =
        (1/2) * Real.log (p₁/p₂) := by
      rw [← Real.log_div bz.ne' bw.ne']
      exact hEq
    change Real.log (Real.exp (c.offset-(1/2)*Real.log (f₁/f₂))) +
      Real.log (balance E z) - (c.offset + Real.log (balance E c.root)) = _
    rw [Real.log_exp, Real.log_div hf₁.ne' hf₂.ne', Real.log_div hf₂.ne' hp₂.ne',
      Real.log_div hf₁.ne' hp₁.ne']
    rw [Real.log_div hp₁.ne' hp₂.ne'] at hdiff
    linarith
  rw [hlog, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2) * (|Real.log (f₂/p₂)| + |Real.log (f₁/p₁)|) :=
      mul_le_mul_of_nonneg_left (by simpa using abs_sub_le (Real.log (f₂/p₂)) 0 (Real.log (f₁/p₁))) (by norm_num)
    _ ≤ 2*ε := by linarith
    _ ≤ _ := hε'

private theorem calibration_tail_exp {T : ℕ} (hT : 2 ≤ T) {η δ est p : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < est) (hp : est / 10 ≤ p) :
    Real.exp (-((calibrationSamples T η δ est : ℝ)*p*(Real.sqrt (η/δ)/2000)^2/4)) ≤
      1 / (4 * (T : ℝ)) := by
  let n := calibrationSamples T η δ est
  let L := Real.log (2 * (T : ℝ))
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT₀ : 0 < (T : ℝ) := by linarith
  have hL : 0 ≤ L := (Real.log_pos (by linarith : 1 < 2 * (T : ℝ))).le
  have hn := Nat.le_ceil (1000000000 * δ * L / (η * est))
  change _ ≤ (n : ℝ) at hn
  have hmul := (div_le_iff₀ (mul_pos hη he)).1 hn
  have hmul' : (n : ℝ)*η*est ≤ (n : ℝ)*η*(10*p) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hbound : (100000000 : ℝ) * δ * L ≤ (n : ℝ)*η*p := by nlinarith
  have heps : (Real.sqrt (η/δ) / 2000)^2 = (η/δ)/4000000 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hbig : 2 * L ≤ (n : ℝ)*p*(Real.sqrt (η/δ)/2000)^2/4 := by
    rw [heps]
    have hr : (n : ℝ) * p * (η / δ / 4000000) / 4 =
        ((n : ℝ)*η*p) / (16000000*δ) := by ring
    rw [hr]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16000000*δ)).2
    nlinarith [mul_nonneg hδ.le hL]
  calc
    _ ≤ Real.exp (-(2 * L)) := Real.exp_le_exp.mpr (by exact neg_le_neg hbig)
    _ = 1 / (2 * (T : ℝ))^2 := by
      rw [Real.exp_neg, show 2*L = L+L by ring, Real.exp_add, show Real.exp L = 2*(T : ℝ)
        from Real.exp_log (by positivity), one_div, pow_two]
    _ ≤ _ := by
      gcongr
      nlinarith [mul_nonneg (show 0 ≤ (T : ℝ) by positivity)
        (show 0 ≤ (T : ℝ) - 1 by linarith)]

private theorem calibration_failure_le (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1) (hT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region) :
    Proc.law (Measure.dirac ()) {s | ¬ ∃ r,
      (calibrationProc T η δ c.est c.offset c.root z).out (P E) s.1 s.2 = some r ∧
        CalibValid E η δ c z r} ≤ ENNReal.ofReal (1 / (T : ℝ)) := by
  let F := calibrationProc T η δ c.est c.offset c.root z
  let n := calibrationSamples T η δ c.est
  let p₁ := P E (z.1,c.root.2)
  let p₂ := P E (c.root.1,z.2)
  let ε := Real.sqrt (η/δ) / 2000
  have hδ := hη.trans hηδ
  have he := hδ.trans_le hc.2.2.2.2.2.2.1
  have hT' := calibration_T_ge_two T η hη hη' hT
  have hn : 0 < n := calibration_samples_pos T hT' η δ c.est hη hδ he
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    have hS : Real.sqrt (η/δ) ≤ 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num, by norm_num; exact (div_le_one hδ).2 hηδ.le⟩
    unfold ε
    linarith
  have hε' : 2*ε ≤ (1/1000)*Real.sqrt (η/δ) := by unfold ε; ring_nf; rfl
  have cross := hc.2.2.2.2.2.1 z hz c.root hc.2.2.2.1
  have hp₁ : c.est/10 ≤ p₁ := (cross.2.2 _ (by simp)).1
  have hp₂ : c.est/10 ≤ p₂ := (cross.2.2 _ (by simp)).1
  have hp₁' : 0 < p₁ := (by positivity : 0 < c.est/10).trans_le hp₁
  have hp₂' : 0 < p₂ := (by positivity : 0 < c.est/10).trans_le hp₂
  let coord₁ := fun i : Fin n => i.val
  let coord₂ := fun i : Fin n => n+i.val
  have hcoord₁ : Function.Injective coord₁ := fun i j h => Fin.ext h
  have hcoord₂ : Function.Injective coord₂ := fun i j h => Fin.ext (Nat.add_left_cancel h)
  let A := {U : Stream | ε < |(hitCount p₁ coord₁ U / n) / p₁ - 1|}
  let B := {U : Stream | ε < |(hitCount p₂ coord₂ U / n) / p₂ - 1|}
  have hA : MeasurableSet A := by
    unfold A
    exact measurableSet_lt measurable_const
      (((measurable_hitCount p₁ coord₁).div_const _).div_const _ |>.sub_const _ |>.abs)
  have hB : MeasurableSet B := by
    unfold B
    exact measurableSet_lt measurable_const
      (((measurable_hitCount p₂ coord₂).div_const _).div_const _ |>.sub_const _ |>.abs)
  have hbound (p : ℝ) (hpl : c.est / 10 ≤ p) (hpu : p ≤ 1)
      (coord : Fin n → ℕ) (hj : Function.Injective coord) :
      Proc.coinLaw {U | ε < |(hitCount p coord U / n) / p - 1|} ≤
        2 * ENNReal.ofReal (1 / (4*(T : ℝ))) := by
    have hp : 0 < p := (by positivity : 0 < c.est/10).trans_le hpl
    apply (hitCount_relative_tail hn hp hpu hε (by linarith) coord hj).trans
    gcongr
    exact calibration_tail_exp hT' hη hδ he hpl
  have hset : {s | ¬ ∃ r, F.out (P E) s.1 s.2 = some r ∧ CalibValid E η δ c z r} ⊆
      Prod.snd ⁻¹' (A ∪ B) := by
    rintro ⟨⟨⟩,U⟩ hU
    by_contra hbad
    have h_A : U ∉ A := fun h => hbad (.inl h)
    have h_B : U ∉ B := fun h => hbad (.inr h)
    have h₁ : |(hitCount p₁ coord₁ U / n) / p₁ - 1| ≤ ε := le_of_not_gt h_A
    have h₂ : |(hitCount p₂ coord₂ U / n) / p₂ - 1| ≤ ε := le_of_not_gt h_B
    exact hU ⟨_,calibration_out T η δ c.est c.offset c.root z (P E) U,
      calibration_valid_of_relative E hE c δ η hc z hz ε hεhalf hε' _ _ hp₁' hp₂' h₁ h₂⟩
  change Proc.law (Measure.dirac ()) {s | ¬ ∃ r, F.out (P E) s.1 s.2 = some r ∧
    CalibValid E η δ c z r} ≤ _
  calc
    _ ≤ Proc.law (Measure.dirac ()) (Prod.snd ⁻¹' (A ∪ B)) := measure_mono hset
    _ = Proc.coinLaw (A ∪ B) := by
      rw [Proc.law, ← Measure.map_apply measurable_snd (hA.union hB), Measure.map_snd_prod]
      simp
    _ ≤ _ := by
      have ht : 0 ≤ 1 / (4 * (T : ℝ)) := by positivity
      calc
        _ ≤ Proc.coinLaw A + Proc.coinLaw B := measure_union_le _ _
        _ ≤ _ + _ := add_le_add
          (hbound p₁ hp₁ ((onUnit_facts E hE.1).1 _).2 coord₁ hcoord₁)
          (hbound p₂ hp₂ ((onUnit_facts E hE.1).1 _).2 coord₂ hcoord₂)
        _ = _ := by
          have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
          rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end BilateralProfitRegular.Factory
end BundlePart024


section BundlePart025



namespace BilateralProfitRegular

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

namespace Factory

private theorem calibration_cost_le (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1)
    (hT : gridK η ≤ T) (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region) :
    (calibrationProc T η δ c.est c.offset c.root z).QueriesIn triT ∧
    (calibrationProc T η δ c.est c.offset c.root z).expCost (P E) (Measure.dirac ())
        (fun y => muStar E - mu E y) ≤ ENNReal.ofReal (5000000000 * Real.log T / η) := by
  let F := calibrationProc T η δ c.est c.offset c.root z
  let n := calibrationSamples T η δ c.est
  have cross := hc.2.2.2.2.2.1 z hz c.root hc.2.2.2.1
  have hF : F.QueriesIn triT := by
    intro ω h y hy
    have hy' := calibration_queries T η δ c.est c.offset c.root z ω h y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy'
    rcases hy' with rfl | rfl
    · exact cross.1
    · exact cross.2.1
  refine ⟨hF,?_⟩
  have hn : (2 * (n : ℝ)) ≤ 5000000000 * Real.log T / η :=
    calibration_samples_le T (calibration_T_ge_two T η hη hη' hT) η δ c.est hη hη'
      (hη.trans hηδ) hc.2.2.2.2.2.2.1
  have hcost (y : CalibrationPrices) (hy : y ∈ triT) :
      ENNReal.ofReal (muStar E - mu E y) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hμ := (onUnit_facts E hE.1).2.2.2.1.2
    have hg : 0 ≤ mu E y := by
      rw [mu_formula]
      exact mul_nonneg (sub_nonneg.mpr hy.2.1) ((onUnit_facts E hE.1).1 y).1
    linarith
  have hpoint (s : Unit × Stream) :
      (∑' k, ((F.query (P E) s.1 s.2 k).map
        (fun q => ENNReal.ofReal (muStar E - mu E q))).getD 0) ≤ (2*n : ℕ) := by
    rcases s with ⟨⟨⟩,U⟩
    rw [tsum_eq_sum (s := Finset.range (2*n))]
    · calc
        _ ≤ ∑ k ∈ Finset.range (2*n), (1 : ENNReal) := by
          apply Finset.sum_le_sum
          intro k _
          unfold Proc.query
          cases he : F.step () (F.hist (P E) () U k) with
          | inl y => exact hcost y (hF _ _ _ he)
          | inr r => simp
        _ = _ := by simp
    · intro k hk
      have hnk : 2*n ≤ k := Nat.le_of_not_gt (by simpa using hk)
      have hd := (calibration_stopped T η δ c.est c.offset c.root z (P E) U k).mpr hnk
      change (F.step () (F.hist (P E) () U k)).isRight = true at hd
      unfold Proc.query
      cases he : F.step () (F.hist (P E) () U k) with
      | inl y => simp [he] at hd
      | inr r => simp
  change F.expCost (P E) (Measure.dirac ()) _ ≤ _
  unfold Proc.expCost
  calc
    _ ≤ ∫⁻ _s, ((2*n : ℕ) : ENNReal) ∂(Proc.law (Measure.dirac ())) := lintegral_mono hpoint
    _ = ((2*n : ℕ) : ENNReal) := by
      haveI : IsProbabilityMeasure (Proc.law (Measure.dirac ())) := by unfold Proc.law; infer_instance
      simp
    _ ≤ _ := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn)

end Factory

end BilateralProfitRegular
end BundlePart025


section BundlePart026





namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

/-- Replace an invalid posted price by the feasible price `(0,0)`. -/
private noncomputable def mainClampPrice (x : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if x ∈ triT then x else (0,0)

private theorem mainClampPrice_eq {x : ℝ × ℝ} (hx : x ∈ triT) : mainClampPrice x = x := by
  classical
  exact if_pos hx

private theorem mainClampPrice_outside {x : ℝ × ℝ} (hx : x ∉ triT) : mainClampPrice x = (0,0) := by
  classical
  exact if_neg hx

private theorem mainClampPrice_legal (x : ℝ × ℝ) : mainClampPrice x ∈ triT := by
  classical
  by_cases hx : x ∈ triT
  · rwa [mainClampPrice_eq hx]
  · rw [mainClampPrice_outside hx]
    norm_num [triT]

@[fun_prop]
private theorem measurable_mainClampPrice : Measurable mainClampPrice := by
  classical
  exact measurable_id.ite measurableSet_mainTri measurable_const

/-- The phase invariant obtained directly from a valid initializer output. -/
private theorem mainPhaseTimeline_from_init {E : Environment} {T : ℕ} {δ : ℝ} {cs : List Candidate}
    (hE : RegularUnit E) (hT : 2 ≤ T) (hInit : InitGuarantee E (mainEta T) δ cs)
    (H : ℕ → MainPhaseReport cs.length) (j : ℕ)
    (hClean : MainPhaseClean E (mainEta T) δ cs H j) :
    let s := mainPhaseTimeline (mainEta T) δ cs H j
    s.1.Nonempty ∧ (∀ i ∈ s.1, s.2 i ∈ (cs.get i).region) ∧
      ∀ i ∈ s.1, ∀ ρ' : ℝ, CalibValid E (mainEta T) δ (cs.get i) (s.2 i) ρ' →
        muStar E - auxProfit E (ρ' * balance E (s.2 i)) (s.2 i) ≤ 65 * (mainEta T + acc δ j) := by
  obtain ⟨hηδ, hδopt, hoptδ, hValid, hNear⟩ := hInit
  obtain ⟨istar, hi⟩ := List.exists_mem_iff_get.mp hNear
  have h := mainPhaseTimeline_guarantee hE (mainEta_pos hT) (mainEta_lt_one hT)
    hηδ hδopt hoptδ (fun i => hValid _ (List.get_mem cs i)) istar hi H j hClean
  exact ⟨⟨istar, h.1⟩, h.2⟩

end BilateralProfitRegular
end BundlePart026


section BundlePart027




namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade

private theorem isOpen_mainIntT : IsOpen intT :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

/-- The success event of refinement is measurable on the array of completed trajectories. -/
private theorem measurableSet_refineGood {M n : ℕ} {E : Environment} {lam δ ε : ℝ}
    {K : Set (ℝ × ℝ)} (hE : RegularUnit E) (hlam : 0 < lam) (hK : IsCompact K) (hsub : K ⊆ intT) :
    MeasurableSet {hs : MainRefineTrajs M n | RefineGood E lam δ ε K hs} := by
  classical
  have hInv : ContinuousOn (fun x => 1 / auxProfit E lam x) K :=
    ((lemma_6_2 E hE lam hlam).1.continuousOn isOpen_mainIntT).mono hsub
  have hCont : ContinuousOn (auxProfit E lam) K := by
    have hh := hInv.inv₀ (fun x hx => div_ne_zero one_ne_zero (auxProfit_pos E hE.1 hlam (hsub hx)).ne')
    change ContinuousOn (fun x => (1 / auxProfit E lam x)⁻¹) K at hh
    have he : (fun x => (1 / auxProfit E lam x)⁻¹) = auxProfit E lam := by
      funext x
      simp only [one_div, inv_inv]
    rwa [he] at hh
  let profit : (ℝ × ℝ) → ℝ := K.piecewise (auxProfit E lam) (fun _ => 0)
  have hProfit : Measurable profit :=
    hCont.measurable_piecewise continuousOn_const hK.measurableSet
  let lower : Set ℝ := ⋂ x : K, Ici (auxProfit E lam x - ε)
  have hlower : IsClosed lower := isClosed_iInter fun _ => isClosed_Ici
  have hLow (r : ℝ) : r ∈ lower ↔ ∀ x ∈ K, auxProfit E lam x - ε ≤ r := by
    simp only [lower, mem_iInter, mem_Ici, Subtype.forall]
  let est (hs : MainRefineTrajs M n) (m : Fin M) := rhatOf δ (avgObs (hs m))
  let query (hs : MainRefineTrajs M n) (m : Fin M) := avgQuery (hs m)
  have hEq :
      {hs : MainRefineTrajs M n | RefineGood E lam δ ε K hs} =
      {hs | ∀ m, (∀ m', avgObs (hs m) ≤ avgObs (hs m')) →
        query hs m ∈ K ∧ est hs m ∈ lower ∧ est hs m ≤ profit (query hs m) + ε} := by
    ext hs
    simp only [mem_ofPred_eq]
    constructor
    · intro h m hm
      obtain ⟨hK', hl, hr⟩ := h m hm
      refine ⟨hK', (hLow _).mpr hl, ?_⟩
      change est hs m ≤ K.piecewise (auxProfit E lam) (fun _ => 0) (query hs m) + ε
      rw [Set.piecewise_eq_of_mem K (auxProfit E lam) (fun _ => (0 : ℝ)) hK']
      exact hr
    · intro h m hm
      obtain ⟨hK', hl, hr⟩ := h m hm
      refine ⟨hK', (hLow _).mp hl, ?_⟩
      change est hs m ≤ K.piecewise (auxProfit E lam) (fun _ => 0) (query hs m) + ε at hr
      rwa [Set.piecewise_eq_of_mem K (auxProfit E lam) (fun _ => (0 : ℝ)) hK'] at hr
  rw [hEq]
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro m
  have he : Measurable (fun hs => est hs m) :=
    (measurable_mainRhat δ).comp (measurable_mainAvgObs.comp (measurable_pi_apply m))
  have hq : Measurable (fun hs => query hs m) := measurable_mainAvgQuery.comp (measurable_pi_apply m)
  have hcmp : Measurable (fun hs : MainRefineTrajs M n => ∀ m', avgObs (hs m) ≤ avgObs (hs m')) :=
    Measurable.forall fun m' => measurableSet_setOfPred.mp (measurableSet_le
      (measurable_mainAvgObs.comp (measurable_pi_apply m))
      (measurable_mainAvgObs.comp (measurable_pi_apply m')))
  apply hcmp.imp
  exact (measurableSet_setOfPred.mp (hq hK.measurableSet)).and
    ((measurableSet_setOfPred.mp (he hlower.measurableSet)).and
      (measurableSet_setOfPred.mp
        (measurableSet_le he ((hProfit.comp hq).add measurable_const))))

end BilateralProfitRegular
end BundlePart027


section BundlePart028


noncomputable section

namespace BilateralProfitRegular

open MeasureTheory
open scoped ENNReal

/-- The next action or final result after a chronological one-bit history. -/
private abbrev Program (α : Type) := List Bool → α ⊕ (ℝ × ℝ)

namespace Program

variable {α β Ω Ξ : Type}

private def after (p : Program α) (b : Bool) : Program α := fun h => p (b :: h)

private def pure (a : α) : Program α := fun _ => .inl a

private def bind (p : Program α) (k : α → Program β) : Program β
  | [] => (p []).elim (fun a => k a []) Sum.inr
  | b :: h => (p []).elim (fun a => k a (b :: h)) (fun _ => bind (p.after b) k h)

private theorem bind_eq_of_stop {p : Program α} {a : α} (ha : p [] = .inl a)
    (k : α → Program β) : p.bind k = k a := by
  funext h
  cases h <;> simp [bind, ha]

private theorem after_bind_of_ask {p : Program α} {x : ℝ × ℝ} (hx : p [] = .inr x)
    (k : α → Program β) (b : Bool) :
    (p.bind k).after b = (p.after b).bind k := by
  funext h
  simp [after, bind, hx]

private def value (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (p : Program α) : ℕ → (ℕ → α → ℝ≥0∞) → ℝ≥0∞
  | 0, finish => (p []).elim (finish 0) (fun _ => 0)
  | n+1, finish => (p []).elim (finish (n+1)) fun x =>
      gap x + (ENNReal.ofReal (prob x) * (p.after true).value prob gap n finish +
        ENNReal.ofReal (1 - prob x) * (p.after false).value prob gap n finish)

@[simp]
private theorem value_pure (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (a : α) (n : ℕ) (finish : ℕ → α → ℝ≥0∞) :
    (pure a).value prob gap n finish = finish n a := by
  cases n <;> rfl

private theorem value_bind (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (p : Program α) (k : α → Program β) (n : ℕ) (finish : ℕ → β → ℝ≥0∞) :
    (p.bind k).value prob gap n finish =
      p.value prob gap n (fun m a => (k a).value prob gap m finish) := by
  induction n generalizing p with
  | zero =>
    cases h : p [] with
    | inl a => rw [bind_eq_of_stop h]; simp [value, h]
    | inr x => simp [value, bind, h]
  | succ n ih =>
    cases h : p [] with
    | inl a => rw [bind_eq_of_stop h]; simp [value, h]
    | inr x =>
      have hb : p.bind k [] = .inr x := by simp [bind, h]
      simp only [value, hb, h, Sum.elim_inr, after_bind_of_ask h, ih]

private def Legal (S : Set (ℝ × ℝ)) (p : Program α) : Prop :=
  ∀ h x, p h = .inr x → x ∈ S

private theorem legal_bind {S : Set (ℝ × ℝ)} {p : Program α} {k : α → Program β}
    (hp : Legal S p) (hk : ∀ a, Legal S (k a)) : Legal S (p.bind k) := by
  intro h
  induction h generalizing p with
  | nil =>
    intro x hx
    cases h0 : p [] with
    | inl a => exact hk a [] x (by simpa [bind, h0] using hx)
    | inr y => exact hp [] x (by simpa [bind, h0] using hx)
  | cons b h ih =>
    intro x hx
    cases h0 : p [] with
    | inl a => exact hk a (b :: h) x (by simpa [bind, h0] using hx)
    | inr y =>
      apply ih (p := p.after b) (fun l z hz => hp (b :: l) z hz) x
      simpa [bind, h0] using hx

private def mapQuery (f : (ℝ × ℝ) → (ℝ × ℝ)) (p : Program α) : Program α :=
  fun h => (p h).map id f

private theorem mapQuery_eq {f : (ℝ × ℝ) → (ℝ × ℝ)} {S : Set (ℝ × ℝ)} {p : Program α}
    (hp : Legal S p) (hf : ∀ x ∈ S, f x = x) : p.mapQuery f = p := by
  funext h
  cases he : p h with
  | inl a => simp [mapQuery, he]
  | inr x => simp [mapQuery, he, hf _ (hp h x he)]

private theorem legal_mapQuery {f : (ℝ × ℝ) → (ℝ × ℝ)} {S : Set (ℝ × ℝ)} (p : Program α)
    (hf : ∀ x, f x ∈ S) : Legal S (p.mapQuery f) := by
  intro h x hx
  cases he : p h with
  | inl a => simp [mapQuery, he] at hx
  | inr y =>
    have heq : f y = x := by simpa [mapQuery, he] using hx
    exact heq ▸ hf y

private theorem value_mono (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞) (p : Program α)
    (n : ℕ) {f g : ℕ → α → ℝ≥0∞} (hfg : ∀ m ≤ n, ∀ a, f m a ≤ g m a) :
    p.value prob gap n f ≤ p.value prob gap n g := by
  induction n generalizing p with
  | zero =>
    cases h : p [] with
    | inl a => simpa [value, h] using hfg 0 le_rfl a
    | inr x => simp [value, h]
  | succ n ih =>
    cases h : p [] with
    | inl a => simpa [value, h] using hfg (n + 1) le_rfl a
    | inr x =>
      simp only [value, h, Sum.elim_inr]
      exact add_le_add le_rfl (add_le_add
        (mul_le_mul' le_rfl (ih _ (fun m hm => hfg m (hm.trans (Nat.le_succ n)))))
        (mul_le_mul' le_rfl (ih _ (fun m hm => hfg m (hm.trans (Nat.le_succ n))))))

private theorem value_le_time {prob : (ℝ × ℝ) → ℝ} {gap : (ℝ × ℝ) → ℝ≥0∞}
    {S : Set (ℝ × ℝ)} {p : Program α} (hp : Legal S p)
    (hprob : ∀ x, 0 ≤ prob x ∧ prob x ≤ 1) (B : ℝ≥0∞) (hgap : ∀ x ∈ S, gap x ≤ B)
    (n : ℕ) {finish : ℕ → α → ℝ≥0∞} (hf : ∀ m ≤ n, ∀ a, finish m a ≤ (m : ℝ≥0∞) * B) :
    p.value prob gap n finish ≤ (n : ℝ≥0∞) * B := by
  induction n generalizing p with
  | zero =>
    cases h : p [] with
    | inl a => simpa [value, h] using hf 0 le_rfl a
    | inr x => simp [value, h]
  | succ n ih =>
    cases h : p [] with
    | inl a => simpa [value, h] using hf (n+1) le_rfl a
    | inr x =>
      have hsum : ENNReal.ofReal (prob x) + ENNReal.ofReal (1 - prob x) = 1 := by
        rw [← ENNReal.ofReal_add (hprob x).1 (sub_nonneg.mpr (hprob x).2)]
        simp
      simp only [value, h, Sum.elim_inr]
      have hadd (b : Bool) : (p.after b).value prob gap n finish ≤ (n : ℝ≥0∞) * B :=
        ih (fun h' y hy => hp (b :: h') y hy) (fun m hm => hf m (hm.trans (Nat.le_succ n)))
      calc
        _ ≤ B + (ENNReal.ofReal (prob x) * ((n : ℝ≥0∞) * B) +
            ENNReal.ofReal (1 - prob x) * ((n : ℝ≥0∞) * B)) :=
          add_le_add (hgap x (hp [] x h)) (add_le_add
            (mul_le_mul' le_rfl (hadd true)) (mul_le_mul' le_rfl (hadd false)))
        _ = _ := by rw [← add_mul, hsum, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm]

section Measurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω] [MeasurableSpace Ξ]

private def MeasurableFamily (p : Ω → Program α) : Prop :=
  ∀ h, Measurable (fun ω => p ω h)

private theorem measurableFamily_after {p : Ω → Program α} (hp : MeasurableFamily p) (b : Bool) :
    MeasurableFamily (fun ω => (p ω).after b) := fun h => hp (b :: h)

private theorem measurableFamily_pure {a : Ω → α} (ha : Measurable a) :
    MeasurableFamily (fun ω => pure (a ω)) := fun _ => measurable_inl.comp ha

private theorem measurableFamily_mapQuery {f : (ℝ × ℝ) → (ℝ × ℝ)} (hf : Measurable f)
    {p : Ω → Program α} (hp : MeasurableFamily p) :
    MeasurableFamily (fun ω => (p ω).mapQuery f) :=
  fun h => (measurable_id.sumMap hf).comp (hp h)

private theorem measurable_sum_prod_elim {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    {left : Ω × α → Z} {right : Ω × Y → Z} (hl : Measurable left) (hr : Measurable right) :
    Measurable (fun x : Ω × (α ⊕ Y) =>
      x.2.elim (fun a => left (x.1, a)) (fun y => right (x.1, y))) := by
  let e := MeasurableEquiv.prodSumDistrib Ω α Y
  convert (hl.sumElim hr).comp e.measurable using 1
  ext ⟨ω, x⟩
  cases x <;> rfl

private theorem measurableFamily_bind {p : Ω → Program α} {k : Ω × α → Program β}
    (hp : MeasurableFamily p) (hk : MeasurableFamily k) :
    MeasurableFamily (fun ω => (p ω).bind (fun a => k (ω, a))) := by
  intro h
  induction h generalizing p with
  | nil =>
    have hleft : Measurable (fun x : Ω × α => k x []) := hk []
    have hright : Measurable (fun x : Ω × (ℝ × ℝ) => (Sum.inr x.2 : β ⊕ (ℝ × ℝ))) :=
      measurable_inr.comp measurable_snd
    have hsum : Measurable (fun x : Ω × (α ⊕ (ℝ × ℝ)) =>
        x.2.elim (fun a => k (x.1, a) []) (fun y => Sum.inr y)) := by
      exact measurable_sum_prod_elim hleft hright
    exact hsum.comp (measurable_id.prodMk (hp []))
  | cons b h ih =>
    have hleft : Measurable (fun x : Ω × α => k x (b :: h)) := hk _
    have hright : Measurable (fun x : Ω × (ℝ × ℝ) =>
        ((p x.1).after b).bind (fun a => k (x.1, a)) h) :=
      (ih (measurableFamily_after hp b)).comp measurable_fst
    have hsum : Measurable (fun x : Ω × (α ⊕ (ℝ × ℝ)) =>
        x.2.elim (fun a => k (x.1, a) (b :: h))
          (fun _ => ((p x.1).after b).bind (fun a => k (x.1, a)) h)) := by
      exact measurable_sum_prod_elim hleft hright
    exact hsum.comp (measurable_id.prodMk (hp []))

private theorem measurable_value {prob : (ℝ × ℝ) → ℝ} {gap : (ℝ × ℝ) → ℝ≥0∞}
    (hprob : Measurable prob) (hgap : Measurable gap) {p : Ω → Program α}
    (hp : MeasurableFamily p) (n : ℕ) {finish : ℕ → Ω × α → ℝ≥0∞}
    (hf : ∀ n, Measurable (finish n)) :
    Measurable (fun ω => (p ω).value prob gap n (fun m a => finish m (ω, a))) := by
  induction n generalizing p with
  | zero =>
    have hsum := measurable_sum_prod_elim (hf 0)
      (measurable_const : Measurable (fun _ : Ω × (ℝ × ℝ) => (0 : ℝ≥0∞)))
    exact hsum.comp (measurable_id.prodMk (hp []))
  | succ n ih =>
    have htrue := ih (measurableFamily_after hp true)
    have hfalse := ih (measurableFamily_after hp false)
    have hright : Measurable (fun x : Ω × (ℝ × ℝ) =>
        gap x.2 + (ENNReal.ofReal (prob x.2) *
          ((p x.1).after true).value prob gap n (fun m a => finish m (x.1, a)) +
          ENNReal.ofReal (1 - prob x.2) *
          ((p x.1).after false).value prob gap n (fun m a => finish m (x.1, a)))) :=
      (hgap.comp measurable_snd).add
        (((hprob.comp measurable_snd).ennreal_ofReal.mul (htrue.comp measurable_fst)).add
          ((measurable_const.sub (hprob.comp measurable_snd)).ennreal_ofReal.mul
            (hfalse.comp measurable_fst)))
    exact (measurable_sum_prod_elim (hf (n+1)) hright).comp (measurable_id.prodMk (hp []))

omit [MeasurableSpace α] in
private theorem lintegral_value (P : Measure Ξ) [IsProbabilityMeasure P]
    (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ℝ≥0∞) (p : Program α) (n : ℕ)
    (finish : ℕ → α → Ξ → ℝ≥0∞) (hf : ∀ m a, Measurable (finish m a)) :
    (∫⁻ ζ, p.value prob gap n (fun m a => finish m a ζ) ∂P) =
      p.value prob gap n (fun m a => ∫⁻ ζ, finish m a ζ ∂P) := by
  have hmeas (r : Program α) (m : ℕ) :
      Measurable fun ζ => r.value prob gap m (fun k a => finish k a ζ) := by
    induction m generalizing r with
    | zero =>
      cases hr : r [] with
      | inl a => simpa [value, hr] using hf 0 a
      | inr x => simp [value, hr]
    | succ m ih =>
      cases hr : r [] with
      | inl a => simpa [value, hr] using hf (m+1) a
      | inr x =>
        simp only [value, hr, Sum.elim_inr]
        exact measurable_const.add ((measurable_const.mul (ih _)).add
          (measurable_const.mul (ih _)))
  induction n generalizing p with
  | zero => cases h : p [] <;> simp [value, h]
  | succ n ih =>
    cases h : p [] with
    | inl a => simp [value, h]
    | inr x =>
      simp only [value, h, Sum.elim_inr]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_add_left (f := fun ζ => ENNReal.ofReal (prob x) *
          (p.after true).value prob gap n (fun m a => finish m a ζ))
          (measurable_const.mul (hmeas _ _)),
        lintegral_const_mul _ (hmeas _ _), lintegral_const_mul _ (hmeas _ _), ih, ih]

private theorem expected_bind (P : Measure Ω) (Q : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {prob : (ℝ × ℝ) → ℝ} {gap : (ℝ × ℝ) → ℝ≥0∞}
    (hprob : Measurable prob) (hgap : Measurable gap)
    {p : Ω → Program α} {k : α × Ξ → Program β}
    (hp : MeasurableFamily p) (hk : MeasurableFamily k)
    (n : ℕ) {finish : ℕ → β → ℝ≥0∞} (hf : ∀ n, Measurable (finish n)) :
    (∫⁻ s, ((p s.1).bind fun a => k (a, s.2)).value prob gap n finish ∂(P.prod Q)) =
      ∫⁻ ω, (p ω).value prob gap n
        (fun m a => ∫⁻ ζ, (k (a, ζ)).value prob gap m finish ∂Q) ∂P := by
  have hp' : MeasurableFamily (fun s : Ω × Ξ => p s.1) :=
    fun h => (hp h).comp measurable_fst
  have hk' : MeasurableFamily (fun s : (Ω × Ξ) × α => k (s.2, s.1.2)) :=
    fun h => (hk h).comp (measurable_snd.prodMk measurable_fst.snd)
  have hb := measurable_value hprob hgap (measurableFamily_bind hp' hk') n
    (finish := fun m z => finish m z.2) (fun m => (hf m).comp measurable_snd)
  rw [lintegral_prod _ hb.aemeasurable]
  refine lintegral_congr fun ω => ?_
  simp only [value_bind]
  apply lintegral_value
  intro m a
  exact measurable_value hprob hgap
    (fun h => (hk h).comp (measurable_const.prodMk measurable_id)) m
    (finish := fun m z => finish m z.2) (fun m => (hf m).comp measurable_snd)

end Measurable

end Program
end BilateralProfitRegular
end
end BundlePart028


section BundlePart029



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory

private def erasePrices (bits : List Bool) : ObservationHistory := bits.map (fun b => ((0,0),b))

private theorem replayObservation_erasePrices (est : ℝ) (ω : ObservationSeed) (h : ObservationHistory) :
    replayObservation est ω (erasePrices (h.map Prod.snd)) = replayObservation est ω h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h q ih =>
    have hs : erasePrices ((h ++ [q]).map Prod.snd) = erasePrices (h.map Prod.snd) ++ [((0,0),q.2)] := by
      simp [erasePrices]
    have hl : (erasePrices (h.map Prod.snd)).length = h.length := by simp [erasePrices]
    rw [hs, replayObservation_append, replayObservation_append, ih, hl]

private theorem observationAction_erasePrices (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    (h : ObservationHistory) :
    observationAction est ρ x z ω (erasePrices (h.map Prod.snd)) = observationAction est ρ x z ω h := by
  unfold observationAction
  rw [replayObservation_erasePrices]
  simp only [erasePrices, List.length_map]

private theorem historyFrequency_erasePrices (n j : ℕ) (h : ObservationHistory) :
    historyFrequency n j (erasePrices (h.map Prod.snd)) = historyFrequency n j h := by
  unfold historyFrequency erasePrices
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [List.getElem?_map]
  cases hi : h[j+i.val]? with
  | none => rfl
  | some q => rfl

private theorem calibrationStep_erasePrices (n : ℕ) (off : ℝ) (y₁ y₂ : Prices)
    (h : CalibrationHistory) :
    calibrationStep n off y₁ y₂ (erasePrices (h.map Prod.snd)) = calibrationStep n off y₁ y₂ h := by
  simp only [calibrationStep, historyFrequency_erasePrices]
  simp only [erasePrices, List.length_map]

private theorem measurable_sum_swap {α β : Type} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Sum.swap : α ⊕ β → β ⊕ α) :=
  measurable_inr.sumElim measurable_inl

/-- Loss observation as a decision tree on the chronological trade bits. -/
private noncomputable def observationProgram (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed) :
    List Bool → ℝ ⊕ Prices :=
  fun bits => (observationAction est ρ x z ω (erasePrices bits)).swap

private theorem observationProgram_replay (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    (h : ObservationHistory) :
    observationProgram est ρ x z ω (h.map Prod.snd) = ((observationProc est ρ x z).step ω h).swap := by
  unfold observationProgram
  rw [observationAction_erasePrices]
  rfl

private theorem measurable_observationProgram (bits : List Bool) :
    Measurable (fun a : ObservationArgs =>
      observationProgram a.1.1 a.1.2 a.2.1.1 a.2.1.2 a.2.2 bits) :=
  (measurable_sum_swap).comp (measurable_observationAction (erasePrices bits))

/-- Calibration as a deterministic decision tree on the chronological trade bits. -/
private noncomputable def calibrationProgram (T : ℕ) (η δ est off : ℝ) (w z : Prices) :
    List Bool → ℝ ⊕ Prices :=
  fun bits => ((calibrationProc T η δ est off w z).step () (erasePrices bits)).swap

private theorem calibrationProgram_replay (T : ℕ) (η δ est off : ℝ) (w z : Prices) (h : CalibrationHistory) :
    calibrationProgram T η δ est off w z (h.map Prod.snd) =
      ((calibrationProc T η δ est off w z).step () h).swap := by
  unfold calibrationProgram
  change (calibrationStep _ _ _ _ (erasePrices (h.map Prod.snd))).swap =
    (calibrationStep _ _ _ _ h).swap
  rw [calibrationStep_erasePrices]

private theorem measurable_calibrationProgram (T : ℕ) (η : ℝ) (bits : List Bool) :
    Measurable (fun a : ℝ × ℝ × ℝ × Prices × Prices =>
      calibrationProgram T η a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 bits) :=
  (measurable_sum_swap).comp (measurable_calibration T η (erasePrices bits))

end BilateralProfitRegular.Factory
end BundlePart029


section BundlePart030


set_option autoImplicit false

/-- A finite decision tree whose internal nodes query one coordinate and branch on its bit. -/
private inductive ProbeTree (I R : Type) where
  | leaf (value : R) : ProbeTree I R
  | node (index : I) (no yes : ProbeTree I R) : ProbeTree I R

namespace ProbeTree

private def eval {I R : Type} : ProbeTree I R → (I → Bool) → List I × R
  | leaf r, _ => ([], r)
  | node i no yes, bits =>
      let next := if bits i then eval yes bits else eval no bits
      (i :: next.1, next.2)

private def ValidSeen {I R : Type} [DecidableEq I] (seen : Finset I) : ProbeTree I R → Prop
  | leaf _ => True
  | node i no yes => i ∉ seen ∧ ValidSeen (insert i seen) no ∧ ValidSeen (insert i seen) yes

private def fillBits {I : Type} [DecidableEq I] (read : List I) (acc bits : I → Bool) : I → Bool :=
  fun i => if i ∈ read then bits i else acc i

private theorem fillBits_nil {I : Type} [DecidableEq I] (acc bits : I → Bool) :
    fillBits [] acc bits = acc := by
  funext i
  simp [fillBits]

private theorem fillBits_cons {I : Type} [DecidableEq I] (i : I) (read : List I) (acc bits : I → Bool) :
    fillBits (i :: read) acc bits = fillBits read (Function.update acc i (bits i)) bits := by
  funext j
  by_cases hj : j ∈ read <;> by_cases hji : j = i <;> simp [fillBits, hj, hji]

private def readBlock {I R : Type} [DecidableEq I] :
    List I → (I → Bool) → ((I → Bool) → ProbeTree I R) → ProbeTree I R
  | [], acc, cont => cont acc
  | i :: rest, acc, cont =>
      node i (readBlock rest (Function.update acc i false) cont)
        (readBlock rest (Function.update acc i true) cont)

private theorem readBlock_eval {I R : Type} [DecidableEq I] (read : List I) (acc bits : I → Bool)
    (cont : (I → Bool) → ProbeTree I R) :
    eval (readBlock read acc cont) bits =
      let next := eval (cont (fillBits read acc bits)) bits
      (read ++ next.1, next.2) := by
  induction read generalizing acc with
  | nil => simp [readBlock, fillBits_nil]
  | cons i rest ih =>
    rw [readBlock, eval]
    have hfill := fillBits_cons i rest acc bits
    cases hb : bits i <;>
      simp only [hb] at hfill ⊢ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, ih, hfill, List.cons_append]

private theorem readBlock_valid {I R : Type} [DecidableEq I] (seen : Finset I) (read : List I)
    (acc : I → Bool) (cont : (I → Bool) → ProbeTree I R)
    (hn : read.Nodup) (hfresh : ∀ i ∈ read, i ∉ seen)
    (hc : ∀ acc', ValidSeen (seen ∪ read.toFinset) (cont acc')) :
    ValidSeen seen (readBlock read acc cont) := by
  induction read generalizing seen acc with
  | nil => simpa [readBlock] using hc acc
  | cons i rest ih =>
    obtain ⟨hi, hn⟩ := List.nodup_cons.mp hn
    have hifresh := hfresh i (by simp)
    have hrestfresh : ∀ j ∈ rest, j ∉ insert i seen := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun he => hi (he ▸ hj), hfresh j (List.mem_cons_of_mem i hj)⟩
    have hset : insert i seen ∪ rest.toFinset = seen ∪ (i :: rest).toFinset := by
      ext j
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    have hcont : ∀ acc', ValidSeen (insert i seen ∪ rest.toFinset) (cont acc') := by
      intro acc'
      rw [hset]
      exact hc acc'
    exact ⟨hifresh, ih _ _ hn hrestfresh hcont, ih _ _ hn hrestfresh hcont⟩

end ProbeTree
end BundlePart030


section BundlePart031


noncomputable section

namespace ProbeTree

open MeasureTheory Set
open scoped ENNReal

section Split
variable {I V : Type} [DecidableEq I] [MeasurableSpace V]

private def joinCoordinate (i : I) (d : V × ({j : I // j ≠ i} → V)) (j : I) : V :=
  if h : j = i then d.1 else d.2 ⟨j, h⟩

private theorem measurable_joinCoordinate (i : I) : Measurable (joinCoordinate (V := V) i) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · simpa [joinCoordinate, h] using
      (measurable_fst : Measurable (Prod.fst : V × ({j : I // j ≠ i} → V) → V))
  · simpa [joinCoordinate, h, Function.comp_def] using
      ((measurable_pi_apply (⟨j,h⟩ : {j : I // j ≠ i})).comp measurable_snd :
        Measurable (fun w : V × ({j : I // j ≠ i} → V) => w.2 ⟨j,h⟩))

private theorem measurePreserving_joinCoordinate (D : Measure V) [IsProbabilityMeasure D] (i : I) :
    MeasurePreserving (joinCoordinate i)
      (D.prod (Measure.infinitePi (fun _ : {j : I // j ≠ i} => D)))
      (Measure.infinitePi fun _ : I => D) := by
  refine ⟨measurable_joinCoordinate i, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  let A := if i ∈ s then t i else Set.univ
  let S := s.subtype (fun j => j ≠ i)
  let B := (↑S : Set {j : I // j ≠ i}).pi (fun j => t j)
  have heq : joinCoordinate i ⁻¹' (↑s : Set I).pi t = A ×ˢ B := by
    ext w
    simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, B]
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · by_cases hi : i ∈ s
        · simpa [A, hi, joinCoordinate] using H i hi
        · simp [A, hi]
      · intro j hj
        have hj' : (j : I) ∈ s := Finset.mem_subtype.mp hj
        simpa [joinCoordinate, j.property] using H j hj'
    · rintro ⟨hi, hr⟩ j hj
      by_cases he : j = i
      · subst j
        simpa [A, hj, joinCoordinate] using hi
      · have hj' : (⟨j, he⟩ : {j : I // j ≠ i}) ∈ S := Finset.mem_subtype.mpr hj
        simpa [joinCoordinate, he] using hr ⟨j, he⟩ hj'
  have hA : D A = ∏ j ∈ s.filter (fun j => j = i), D (t j) := by
    by_cases hi : i ∈ s <;> simp [A, Finset.filter_eq', hi]
  have hB : (Measure.infinitePi fun _ : {j : I // j ≠ i} => D) B =
      ∏ j ∈ s.filter (fun j => j ≠ i), D (t j) := by
    change (Measure.infinitePi fun _ : {j : I // j ≠ i} => D)
      ((↑S : Set {j : I // j ≠ i}).pi (fun j => t j)) = _
    rw [Measure.infinitePi_pi (s := S) (t := fun j => t j) _ (fun j _ => ht j)]
    exact Finset.prod_subtype_eq_prod_filter (s := s) (fun j => D (t j))
  rw [Measure.map_apply (measurable_joinCoordinate i) (MeasurableSet.pi s.countable_toSet (fun j _ => ht j)),
    heq, Measure.prod_prod, hA, hB]
  exact Finset.prod_filter_mul_prod_filter_not s (fun j => j = i) (fun j => D (t j))

private theorem lintegral_branch_pi (D : Measure V) [IsProbabilityMeasure D] (i : I)
    (e : Set V) (he : MeasurableSet e) (f0 f1 : (I → V) → ℝ≥0∞)
    (h0 : Measurable f0) (h1 : Measurable f1)
    (hind0 : ∀ (x y : I → V), (∀ j, j ≠ i → x j = y j) → f0 x = f0 y)
    (hind1 : ∀ (x y : I → V), (∀ j, j ≠ i → x j = y j) → f1 x = f1 y)
    [DecidablePred fun v : V => v ∈ e] :
    (∫⁻ x, if x i ∈ e then f1 x else f0 x ∂(Measure.infinitePi fun _ : I => D)) =
      D e * (∫⁻ x, f1 x ∂(Measure.infinitePi fun _ : I => D)) +
        D eᶜ * (∫⁻ x, f0 x ∂(Measure.infinitePi fun _ : I => D)) := by
  classical
  obtain ⟨w⟩ : Nonempty V := nonempty_of_isProbabilityMeasure D
  let rest : Measure ({j : I // j ≠ i} → V) := Measure.infinitePi fun _ => D
  let g0 : ({j : I // j ≠ i} → V) → ℝ≥0∞ := fun z => f0 (joinCoordinate i (w,z))
  let g1 : ({j : I // j ≠ i} → V) → ℝ≥0∞ := fun z => f1 (joinCoordinate i (w,z))
  have hcomp0 (x : V) (u : {j : I // j ≠ i} → V) :
      f0 (joinCoordinate i (x,u)) = g0 u :=
    hind0 _ _ (by intro j hj; simp [joinCoordinate,hj])
  have hcomp1 (x : V) (u : {j : I // j ≠ i} → V) :
      f1 (joinCoordinate i (x,u)) = g1 u :=
    hind1 _ _ (by intro j hj; simp [joinCoordinate,hj])
  have hfg (f : (I → V) → ℝ≥0∞) (hf : Measurable f)
      (g : ({j : I // j ≠ i} → V) → ℝ≥0∞)
      (h : ∀ x u, f (joinCoordinate i (x,u)) = g u) :
      (∫⁻ x, f x ∂(Measure.infinitePi fun _ : I => D)) = ∫⁻ u, g u ∂rest := by
    rw [← (measurePreserving_joinCoordinate D i).lintegral_comp hf]
    rw [lintegral_prod (fun z => f (joinCoordinate i z))
      (hf.comp (measurable_joinCoordinate i)).aemeasurable]
    simp only [h, lintegral_const, measure_univ, mul_one, rest]
  have hsel : Measurable (fun x : I → V => if x i ∈ e then f1 x else f0 x) :=
    Measurable.ite (he.preimage (measurable_pi_apply i)) h1 h0
  rw [hfg _ h1 g1 hcomp1,hfg _ h0 g0 hcomp0,
    ← (measurePreserving_joinCoordinate D i).lintegral_comp hsel]
  rw [lintegral_prod (fun z => if joinCoordinate i z i ∈ e then f1 (joinCoordinate i z)
      else f0 (joinCoordinate i z)) (hsel.comp (measurable_joinCoordinate i)).aemeasurable]
  have hinner (x : V) : (∫⁻ u, (if x ∈ e then g1 u else g0 u) ∂rest) =
      if x ∈ e then (∫⁻ u, g1 u ∂rest) else (∫⁻ u, g0 u ∂rest) := by
    split_ifs <;> rfl
  have htranslate (x : V) (u : {j : I // j ≠ i} → V) :
      (if joinCoordinate i (x,u) i ∈ e then f1 (joinCoordinate i (x,u))
        else f0 (joinCoordinate i (x,u))) =
      (if x ∈ e then g1 u else g0 u) := by
    rw [hcomp0,hcomp1]
    simp [joinCoordinate]
  simp only [htranslate]
  change (∫⁻ x, (∫⁻ u, (if x ∈ e then g1 u else g0 u) ∂rest) ∂D) = _
  simp only [hinner]
  have hs (A B : ℝ≥0∞) : (fun x => if x ∈ e then A else B) =
        (fun x => e.indicator (fun _ => A) x + eᶜ.indicator (fun _ => B) x) := by
    funext x
    by_cases hx : x ∈ e <;> simp [hx]
  rw [hs, lintegral_add_left (measurable_const.indicator he),
    lintegral_indicator_const he, lintegral_indicator_const he.compl]
  ac_rfl

end Split

section Tree
variable {I R V : Type} [DecidableEq I]

/-- Expected cost of probing until a leaf, with a continuation of the remaining horizon. -/
private def value (q : I → ℝ) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) :
    ℕ → ProbeTree I R → ℝ≥0∞
  | n, leaf r => finish n r
  | 0, node _ _ _ => 0
  | n+1, node i no yes =>
      g i + (ENNReal.ofReal (q i) * value q g finish n yes +
        ENNReal.ofReal (1-q i) * value q g finish n no)

/-- Cost before continuation for a fixed tape of bits, stopping at the physical horizon. -/
private def tapeCost (bits : I → Bool) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) :
    ℕ → ProbeTree I R → ℝ≥0∞
  | n, leaf r => finish n r
  | 0, node _ _ _ => 0
  | n+1, node i no yes =>
      g i + if bits i then tapeCost bits g finish n yes else tapeCost bits g finish n no

private theorem tapeCost_congr (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    {seen : Finset I} {tree : ProbeTree I R} (hvalid : ValidSeen seen tree)
    {bits b' : I → Bool} (h : ∀ j, j ∉ seen → bits j = b' j) (n : ℕ) :
    tapeCost bits g finish n tree = tapeCost b' g finish n tree := by
  induction tree generalizing n seen with
  | leaf r => simp [tapeCost]
  | node i no yes ih0 ih1 =>
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨hi,hno,hyes⟩ := hvalid
      simp only [tapeCost, h i hi]
      congr 1
      split <;> first
        | apply ih1 hyes (fun j hj => h j (fun hmem => hj (Finset.mem_insert_of_mem hmem)))
        | apply ih0 hno (fun j hj => h j (fun hmem => hj (Finset.mem_insert_of_mem hmem)))

omit [DecidableEq I] in
private theorem tapeCost_eval (bits : I → Bool) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    (n : ℕ) (tree : ProbeTree I R) (h : (tree.eval bits).1.length ≤ n) :
    tapeCost bits g finish n tree =
      ((tree.eval bits).1.map g).sum + finish (n - (tree.eval bits).1.length) (tree.eval bits).2 := by
  induction tree generalizing n with
  | leaf r => simp [tapeCost, eval]
  | node i no yes ih0 ih1 =>
    cases hi : bits i <;> simp [eval,hi] at h ⊢
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      simp [tapeCost,hi,ih0 n (by omega),Nat.succ_sub_succ_eq_sub, add_assoc]
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      simp [tapeCost,hi,ih1 n (by omega),Nat.succ_sub_succ_eq_sub, add_assoc]

omit [DecidableEq I] in
private theorem tapeCost_le_full (bits : I → Bool) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    (n : ℕ) (tree : ProbeTree I R) :
    tapeCost bits g finish n tree ≤
      ((tree.eval bits).1.map g).sum + finish (n - (tree.eval bits).1.length) (tree.eval bits).2 := by
  induction tree generalizing n with
  | leaf r => simp [tapeCost, eval]
  | node i no yes ih0 ih1 =>
    cases n with
    | zero => exact bot_le
    | succ n =>
      cases hb : bits i
      · simpa [tapeCost, eval, hb, Nat.succ_sub_succ_eq_sub, add_assoc] using
          add_le_add_right (ih0 n) (g i)
      · simpa [tapeCost, eval, hb, Nat.succ_sub_succ_eq_sub, add_assoc] using
          add_le_add_right (ih1 n) (g i)

end Tree

section Integral
variable {I R V : Type} [DecidableEq I] [MeasurableSpace V]

private def bitsFromSets (e : I → Set V) (w : I → V) : I → Bool :=
  fun i => by classical exact decide (w i ∈ e i)

omit [DecidableEq I] in
private theorem measurable_tapeCost (e : I → Set V) (he : ∀ i, MeasurableSet (e i))
    (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) (n : ℕ) (tree : ProbeTree I R) :
    Measurable (fun w : I → V =>
      tapeCost (bitsFromSets e w) g finish n tree) := by
  classical
  induction tree generalizing n with
  | leaf r => simp only [tapeCost]; exact measurable_const
  | node i no yes ih0 ih1 =>
    cases n with
    | zero => exact measurable_const
    | succ n =>
      simp only [tapeCost, bitsFromSets, decide_eq_true_eq]
      exact measurable_const.add
        (Measurable.ite ((he i).preimage (measurable_pi_apply i)) (ih1 n) (ih0 n))

private theorem value_eq_lintegral (D : Measure V) [IsProbabilityMeasure D]
    (e : I → Set V) (he : ∀ i, MeasurableSet (e i))
    (q : I → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (hmass : ∀ i, D (e i) = ENNReal.ofReal (q i))
    (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    {seen : Finset I} (n : ℕ) (tree : ProbeTree I R) (hvalid : ValidSeen seen tree) :
    value q g finish n tree =
      ∫⁻ w, tapeCost (bitsFromSets e w) g finish n tree
        ∂(Measure.infinitePi fun _ : I => D) := by
  classical
  induction tree generalizing n seen with
    | leaf r => simp [value,tapeCost]
    | node i no yes ih0 ih1 =>
      cases n with
      | zero => simp [value,tapeCost]
      | succ n =>
        obtain ⟨hi,hno,hyes⟩ := hvalid
        simp only [value, tapeCost, bitsFromSets, decide_eq_true_eq]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        rw [lintegral_branch_pi D i (e i) (he i) _ _
          (measurable_tapeCost e he g finish n no)
          (measurable_tapeCost e he g finish n yes)]
        · have hc : D (e i)ᶜ = ENNReal.ofReal (1-q i) := by
            rw [measure_compl (he i) (measure_ne_top D _), measure_univ, hmass]
            rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (hq i).1]
          rw [hc, hmass, ← ih1 n hyes, ← ih0 n hno]
        · intro x y h
          apply tapeCost_congr g finish hno
          intro j hj
          simp only [bitsFromSets, h j (fun hij => hj (by simp [hij]))]
        · intro x y h
          apply tapeCost_congr g finish hyes
          intro j hj
          simp only [bitsFromSets, h j (fun hij => hj (by simp [hij]))]

end Integral
end ProbeTree
end
end BundlePart031


section BundlePart032



namespace BilateralProfitRegular.Proc

open MeasureTheory
open scoped Classical ENNReal

variable {Q α Ω : Type} [MeasurableSpace Q] [MeasurableSpace α] [MeasurableSpace Ω]

/-- Expected cost of a procedure stopped at the physical horizon, with a prescribed
continuation value for each output and remaining horizon. -/
private noncomputable def prefixValue (pr : Proc Q α Ω) (prob : Q → ℝ) (gap : Q → ℝ)
    (finish : ℕ → α → ℝ≥0∞) (ω : Ω) : ℕ → List (Q × Bool) → ℝ≥0∞
  | 0, h => match pr.step ω h with
    | .inl _ => 0
    | .inr a => finish 0 a
  | n + 1, h => match pr.step ω h with
    | .inl q => ENNReal.ofReal (gap q) +
        (ENNReal.ofReal (prob q) * prefixValue pr prob gap finish ω n (h ++ [(q, true)]) +
          ENNReal.ofReal (1 - prob q) * prefixValue pr prob gap finish ω n (h ++ [(q, false)]))
    | .inr a => finish (n + 1) a

/-- Cost on a fixed uniform tape. A coordinate is consumed precisely when a query is made. -/
private noncomputable def prefixTapeCost (pr : Proc Q α Ω) (prob : Q → ℝ) (gap : Q → ℝ)
    (finish : ℕ → α → ℝ≥0∞) (ω : Ω) (U : ℕ → unitInterval) :
    ℕ → ℕ → List (Q × Bool) → ℝ≥0∞
  | 0, _, h => match pr.step ω h with
    | .inl _ => 0
    | .inr a => finish 0 a
  | n + 1, k, h => match pr.step ω h with
    | .inl q => ENNReal.ofReal (gap q) + prefixTapeCost pr prob gap finish ω U n (k + 1)
        (h ++ [(q, decide ((U k : ℝ) < prob q))])
    | .inr a => finish (n + 1) a

private theorem prefixTapeCost_tail_congr (pr : Proc Q α Ω) (prob : Q → ℝ) (gap : Q → ℝ)
    (finish : ℕ → α → ℝ≥0∞) (ω : Ω) (U U' : ℕ → unitInterval) (n k : ℕ)
    (h : List (Q × Bool)) (hu : ∀ j, k ≤ j → U j = U' j) :
    pr.prefixTapeCost prob gap finish ω U n k h =
      pr.prefixTapeCost prob gap finish ω U' n k h := by
  induction n generalizing k h with
  | zero => simp [prefixTapeCost]
  | succ n ih =>
    cases hs : pr.step ω h with
    | inl q =>
      simp only [prefixTapeCost, hs, hu k le_rfl]
      rw [ih _ _ (fun j hj => hu j ((Nat.le_succ k).trans hj))]
    | inr a => simp [prefixTapeCost, hs]

private theorem measurable_prefixTapeCost_fixed_seed (pr : Proc Q α Ω) (prob : Q → ℝ)
    (gap : Q → ℝ) (finish : ℕ → α → ℝ≥0∞) (ω : Ω)
    (n k : ℕ) (h : List (Q × Bool)) :
    Measurable (fun U : ℕ → unitInterval => pr.prefixTapeCost prob gap finish ω U n k h) := by
  induction n generalizing k h with
  | zero => simp only [prefixTapeCost]; exact measurable_const
  | succ n ih =>
    cases hs : pr.step ω h with
    | inr a => simp only [prefixTapeCost, hs]; exact measurable_const
    | inl q =>
      simp only [prefixTapeCost, hs]
      have hm : Measurable (fun U : ℕ → unitInterval => (U k : ℝ)) :=
        measurable_subtype_coe.comp (measurable_pi_apply (X := fun _ : ℕ => unitInterval) k)
      have hc := measurableSet_lt hm
        (measurable_const (a := prob q))
      have he (U : ℕ → unitInterval) :
          pr.prefixTapeCost prob gap finish ω U n (k + 1)
              (h ++ [(q, decide ((U k : ℝ) < prob q))]) =
            if (U k : ℝ) < prob q then
              pr.prefixTapeCost prob gap finish ω U n (k + 1) (h ++ [(q, true)])
            else pr.prefixTapeCost prob gap finish ω U n (k + 1) (h ++ [(q, false)]) := by
        by_cases hb : (U k : ℝ) < prob q <;> simp [hb]
      simp_rw [he]
      exact measurable_const.add (Measurable.ite hc (ih _ _) (ih _ _))

private theorem prefixValue_eq_lintegral_tape (pr : Proc Q α Ω) (prob : Q → ℝ)
    (hp : ∀ q, prob q ∈ Set.Icc (0 : ℝ) 1) (gap : Q → ℝ)
    (finish : ℕ → α → ℝ≥0∞) (ω : Ω) (n k : ℕ) (h : List (Q × Bool)) :
    pr.prefixValue prob gap finish ω n h =
      ∫⁻ U, pr.prefixTapeCost prob gap finish ω U n k h ∂coinLaw := by
  have : IsProbabilityMeasure coinLaw := by unfold coinLaw; infer_instance
  induction n generalizing k h with
  | zero => simp [prefixValue, prefixTapeCost]
  | succ n ih =>
    cases hs : pr.step ω h with
    | inr a => simp [prefixValue, prefixTapeCost, hs]
    | inl q =>
      simp only [prefixValue, prefixTapeCost, hs]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      let p : unitInterval := ⟨prob q, hp q⟩
      let F (b : Bool) (U : ℕ → unitInterval) :=
        pr.prefixTapeCost prob gap finish ω U n (k + 1) (h ++ [(q, b)])
      have hF (b : Bool) : Measurable (F b) :=
        pr.measurable_prefixTapeCost_fixed_seed prob gap finish ω n (k + 1) _
      have he (U : ℕ → unitInterval) :
          pr.prefixTapeCost prob gap finish ω U n (k + 1)
              (h ++ [(q, decide ((U k : ℝ) < prob q))]) =
            if U k ∈ Set.Iio p then F true U else F false U := by
        change F (decide ((U k : ℝ) < prob q)) U = if (U k : ℝ) < prob q then _ else _
        by_cases hb : (U k : ℝ) < prob q <;> simp [hb]
      simp_rw [he]
      have hInd (b : Bool) (U V : ℕ → unitInterval)
          (hUV : ∀ j, j ≠ k → U j = V j) : F b U = F b V :=
        pr.prefixTapeCost_tail_congr prob gap finish ω U V n (k + 1) _
          (fun j hj => hUV j (by omega))
      unfold coinLaw
      rw [ProbeTree.lintegral_branch_pi _ k _ measurableSet_Iio _ _
        (hF false) (hF true) (hInd false) (hInd true)]
      have hm : (volume : Measure unitInterval) (Set.Iio p) = ENNReal.ofReal (prob q) :=
        unitInterval.volume_Iio p
      have hmc : (volume : Measure unitInterval) (Set.Iio p)ᶜ =
          ENNReal.ofReal (1 - prob q) := by
        rw [measure_compl measurableSet_Iio (measure_ne_top _ _), measure_univ, hm,
          ENNReal.ofReal_sub _ (hp q).1, ENNReal.ofReal_one]
      rw [hm, hmc]
      rw [ih (k + 1) (h ++ [(q, true)]), ih (k + 1) (h ++ [(q, false)])]
      rfl

private theorem hist_eq_after_stop (pr : Proc Q α Ω) (prob : Q → ℝ)
    (ω : Ω) (U : ℕ → unitInterval) {k n : ℕ} {a : α}
    (hn : k ≤ n) (hk : pr.step ω (pr.hist prob ω U k) = Sum.inr a) :
    pr.hist prob ω U n = pr.hist prob ω U k := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [hist, ih, hk]

private theorem out_eq_some_of_step_right (pr : Proc Q α Ω) (prob : Q → ℝ) (ω : Ω)
    (U : ℕ → unitInterval) (k : ℕ) (a : α)
    (hk : pr.step ω (pr.hist prob ω U k) = Sum.inr a) : pr.out prob ω U = some a := by
  have hstop : ∃ n, pr.stopped prob ω U n := ⟨k, by simp [stopped, hk]⟩
  let j := Nat.find hstop
  have hfind : pr.stopped prob ω U j := Nat.find_spec hstop
  have hle : j ≤ k := Nat.find_min' hstop (by simp [stopped, hk])
  rw [out, dif_pos hstop]
  change (pr.step ω (pr.hist prob ω U j)).getRight? = some a
  cases hf : pr.step ω (pr.hist prob ω U j) with
  | inl q =>
    have hfalse : (pr.step ω (pr.hist prob ω U j)).isRight = true := hfind
    rw [hf] at hfalse
    cases hfalse
  | inr b =>
    have hhist := hist_eq_after_stop pr prob ω U hle hf
    rw [← hhist, hk] at hf
    rw [← Sum.inr.inj hf]
    rfl

set_option maxHeartbeats 600000 in
private theorem prefixTapeCost_le_expCost_integrand (pr : Proc Q α Ω) (prob : Q → ℝ)
    (gap : Q → ℝ) (finish : ℕ → α → ℝ≥0∞) (envelope : α → ℝ≥0∞)
    (hfinish : ∀ n a, finish n a ≤ envelope a)
    (ω : Ω) (U : ℕ → unitInterval) (n : ℕ) :
    pr.prefixTapeCost prob gap finish ω U n 0 [] ≤
      (∑' j, ((pr.query prob ω U j).map fun q => ENNReal.ofReal (gap q)).getD 0) +
      ((pr.out prob ω U).map envelope).getD 0 := by
  let G (j : ℕ) := ((pr.query prob ω U j).map fun q => ENNReal.ofReal (gap q)).getD 0
  let D := ((pr.out prob ω U).map envelope).getD 0
  have hb (n k : ℕ) :
      pr.prefixTapeCost prob gap finish ω U n k (pr.hist prob ω U k) ≤
        (∑ i : Fin n, G (k + (i : ℕ))) + D := by
    induction n generalizing k with
    | zero =>
      cases hs : pr.step ω (pr.hist prob ω U k) with
      | inl q => simp [prefixTapeCost, hs]
      | inr a =>
        simpa [prefixTapeCost, hs, D, pr.out_eq_some_of_step_right prob ω U k a hs] using
          hfinish 0 a
    | succ n ih =>
      cases hs : pr.step ω (pr.hist prob ω U k) with
      | inr a =>
        have he : D = envelope a := by
          simp [D, pr.out_eq_some_of_step_right prob ω U k a hs]
        rw [prefixTapeCost, hs, he]
        exact (hfinish (n + 1) a).trans (le_add_of_nonneg_left bot_le)
      | inl q =>
        have hnext : pr.hist prob ω U (k + 1) = pr.hist prob ω U k ++
            [(q, decide ((U k : ℝ) < prob q))] := by rw [hist, hs]
        have hG : G k = ENNReal.ofReal (gap q) := by simp [G, query, hs]
        simp only [prefixTapeCost, hs]
        rw [← hnext, Fin.sum_univ_succ]
        simp only [Fin.val_zero, add_zero, Fin.val_succ, hG, add_assoc]
        have he : (∑ i : Fin n, G (k + ((i : ℕ) + 1))) =
            ∑ i : Fin n, G ((k + 1) + (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          omega
        rw [he]
        exact add_le_add_right (ih (k + 1)) _
  have hi := hb n 0
  simp only [hist, zero_add] at hi
  refine hi.trans (add_le_add_left ?_ _)
  rw [Fin.sum_univ_eq_sum_range G]
  exact ENNReal.sum_le_tsum _

/-- Bounded-horizon composition, charged by the full procedure cost and an output-only
envelope. Joint tape measurability is explicit because separate measurability at fixed
histories does not establish measurability along random price histories. -/
private theorem prefixExpected_le (pr : Proc Q α Ω) (prob : Q → ℝ)
    (hp : ∀ q, prob q ∈ Set.Icc (0 : ℝ) 1) (P : Measure Ω) [IsProbabilityMeasure P]
    (gap : Q → ℝ) (finish : ℕ → α → ℝ≥0∞) (envelope : α → ℝ≥0∞)
    (hfinish : ∀ n a, finish n a ≤ envelope a) (n : ℕ)
    (hTape : AEMeasurable (fun x : Ω × (ℕ → unitInterval) =>
      pr.prefixTapeCost prob gap finish x.1 x.2 n 0 []) (law P))
    (hEnvelope : AEMeasurable (fun x : Ω × (ℕ → unitInterval) =>
      ((pr.out prob x.1 x.2).map envelope).getD 0) (law P)) :
    (∫⁻ ω, pr.prefixValue prob gap finish ω n [] ∂P) ≤
      pr.expCost prob P gap +
        ∫⁻ x, ((pr.out prob x.1 x.2).map envelope).getD 0 ∂(law P) := by
  have : IsProbabilityMeasure coinLaw := by unfold coinLaw; infer_instance
  simp_rw [pr.prefixValue_eq_lintegral_tape prob hp gap finish _ n 0 []]
  rw [← lintegral_prod _ hTape]
  refine (lintegral_mono fun (x : Ω × (ℕ → unitInterval)) =>
    pr.prefixTapeCost_le_expCost_integrand prob gap finish envelope hfinish x.1 x.2 n).trans_eq ?_
  exact lintegral_add_right' _ hEnvelope

end BilateralProfitRegular.Proc
end BundlePart032


section BundlePart033



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private theorem measurable_observationStateAt (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) (k : ℕ) (i : Fin 3) :
    Measurable (fun a : Prices × ObservationPath =>
      observationTrace est ρ a.1 z prob k (observationSample a.2) i) := by
  have hm : Measurable (fun a : Prices × ObservationPath => (a.1, observationSample a.2)) :=
    measurable_fst.prodMk (measurable_observationSample.comp measurable_snd)
  exact (measurable_slot_run_with_query est ρ z hp i (slotCount k i)).comp hm

private theorem measurable_observationDoneAt (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) (k : ℕ) :
    MeasurableSet {a : Prices × ObservationPath |
      ∀ i, (observationTrace est ρ a.1 z prob k (observationSample a.2) i).isLeft = true} := by
  have he : {a : Prices × ObservationPath |
      ∀ i, (observationTrace est ρ a.1 z prob k (observationSample a.2) i).isLeft = true} =
      ⋂ i : Fin 3, {a : Prices × ObservationPath |
        (observationTrace est ρ a.1 z prob k (observationSample a.2) i).isLeft = true} := by
    ext a; simp
  rw [he]
  exact MeasurableSet.iInter (fun i => ((measurable_of_countable Sum.isLeft).comp
    (measurable_observationStateAt est ρ z hp k i)) (measurableSet_singleton true))

private theorem measurable_observationTrueAt (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) (k : ℕ) :
    MeasurableSet {a : Prices × ObservationPath |
      ∀ i, observationTrace est ρ a.1 z prob k (observationSample a.2) i = .inl true} := by
  have he : {a : Prices × ObservationPath |
      ∀ i, observationTrace est ρ a.1 z prob k (observationSample a.2) i = .inl true} =
      ⋂ i : Fin 3, {a : Prices × ObservationPath |
        observationTrace est ρ a.1 z prob k (observationSample a.2) i = .inl true} := by
    ext a; simp
  rw [he]
  exact MeasurableSet.iInter (fun i => (measurable_observationStateAt est ρ z hp k i)
    (measurableSet_singleton (Sum.inl true : State)))

private theorem measurable_observationPrefixTape (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (finish : ℕ → ℝ → ENNReal)
    (hf : ∀ n, Measurable (finish n)) (n k : ℕ) :
    Measurable (fun a : Prices × ObservationPath =>
      let F := observationProc est ρ a.1 z
      F.prefixTapeCost prob g finish a.2.1 a.2.2 n k (F.hist prob a.2.1 a.2.2 k)) := by
  let done (j : ℕ) (a : Prices × ObservationPath) :=
    ∀ i, (observationTrace est ρ a.1 z prob j (observationSample a.2) i).isLeft = true
  let ans (j : ℕ) (a : Prices × ObservationPath) :=
    if ∀ i, observationTrace est ρ a.1 z prob j (observationSample a.2) i = .inl true then
      observationCoefficient est ρ a.1 else 0
  let y (j : ℕ) (a : Prices × ObservationPath) :=
    observationPrice ρ a.1 z a.2.1.1 (observationSlot j)
  let F (a : Prices × ObservationPath) := observationProc est ρ a.1 z
  let h (j : ℕ) (a : Prices × ObservationPath) := (F a).hist prob a.2.1 a.2.2 j
  have mDone (j : ℕ) : MeasurableSet {a | done j a} := measurable_observationDoneAt est ρ z hp j
  have mAns (j : ℕ) : Measurable (ans j) := Measurable.ite
    (measurable_observationTrueAt est ρ z hp j)
    (measurable_const.div
      (((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)).mul_const est))
    measurable_const
  have mPrice (j : ℕ) : Measurable (y j) :=
    (measurable_price_with_query ρ z (observationSlot j)).comp
      (measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hAct (j : ℕ) (a : Prices × ObservationPath) :
      (F a).step a.2.1 (h j a) = if done j a then .inr (ans j a) else .inl (y j a) := by
    have hr := observation_trace_eq_replay est ρ a.1 z prob j a.2.1 a.2.2
    have he : replayObservation est a.2.1 (h j a) =
        observationTrace est ρ a.1 z prob j (observationSample a.2) := hr.1
    change observationStep (replayObservation est a.2.1 (h j a))
      (observationPrice ρ a.1 z a.2.1.1 (observationSlot (h j a).length))
      (observationCoefficient est ρ a.1) = _
    rw [he, observationStep]
    by_cases hd : done j a
    · have hd' : ∀ i, (observationTrace est ρ a.1 z prob j (observationSample a.2) i).isLeft = true := hd
      simp only [if_pos hd, if_pos hd']
      rfl
    · rw [hr.2 hd]
  induction n generalizing k with
  | zero =>
    have he : (fun a : Prices × ObservationPath =>
          (F a).prefixTapeCost prob g finish a.2.1 a.2.2 0 k (h k a)) =
        fun a : Prices × ObservationPath =>
          if done k a then finish 0 (ans k a) else 0 := by
      funext a
      rw [Proc.prefixTapeCost, hAct]
      by_cases hd : done k a
      · simp only [if_pos hd]
      · simp only [if_neg hd]
    change Measurable (fun a => (F a).prefixTapeCost prob g finish a.2.1 a.2.2 0 k (h k a))
    rw [he]
    exact Measurable.ite (mDone k) ((hf 0).comp (mAns k)) measurable_const
  | succ n ih =>
    have he : (fun a : Prices × ObservationPath =>
          (F a).prefixTapeCost prob g finish a.2.1 a.2.2 (n+1) k (h k a)) =
        fun a : Prices × ObservationPath =>
          if done k a then finish (n+1) (ans k a)
          else ENNReal.ofReal (g (y k a)) +
            (F a).prefixTapeCost prob g finish a.2.1 a.2.2 n (k+1) (h (k+1) a) := by
      funext a
      rw [Proc.prefixTapeCost, hAct]
      by_cases hd : done k a
      · simp only [if_pos hd]
      · simp only [if_neg hd]
        have hNext : h (k+1) a = h k a ++ [(y k a, decide ((a.2.2 k : ℝ) < prob (y k a)))] := by
          change (F a).hist prob a.2.1 a.2.2 (k+1) = _
          rw [Proc.hist, show (F a).step a.2.1 ((F a).hist prob a.2.1 a.2.2 k) = _ from hAct k a,
            if_neg hd]
        rw [hNext]
    change Measurable (fun a => (F a).prefixTapeCost prob g finish a.2.1 a.2.2 (n+1) k (h k a))
    rw [he]
    exact Measurable.ite (mDone k) ((hf (n+1)).comp (mAns k))
      ((ENNReal.measurable_ofReal.comp (hg.comp (mPrice k))).add (ih (k+1)))

private theorem measurable_observationEnvelope (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ}
    (hp : Measurable prob) (envelope : ℝ → ENNReal) (he : Measurable envelope) :
    Measurable (fun a : Prices × ObservationPath =>
      (((observationProc est ρ a.1 z).out prob a.2.1 a.2.2).map envelope).getD 0) := by
  let A := {a : Prices × ObservationPath |
    ∃ k, (observationProc est ρ a.1 z).stopped prob a.2.1 a.2.2 k}
  have hA : MeasurableSet A := by
    have heq : A = ⋃ k : ℕ, {a : Prices × ObservationPath |
      ∀ i, (observationTrace est ρ a.1 z prob k (observationSample a.2) i).isLeft = true} := by
      ext a
      simp [A, observation_stopped_iff]
    rw [heq]
    exact MeasurableSet.iUnion (measurable_observationDoneAt est ρ z hp)
  have heq : (fun a : Prices × ObservationPath =>
      (((observationProc est ρ a.1 z).out prob a.2.1 a.2.2).map envelope).getD 0) =
      fun a => if a ∈ A then envelope (observationValue est ρ z prob a) else 0 := by
    funext a
    by_cases hA : a ∈ A
    · rw [if_pos hA]
      rcases hA with ⟨k,hk⟩
      let F := observationProc est ρ a.1 z
      change (F.step a.2.1 (F.hist prob a.2.1 a.2.2 k)).isRight = true at hk
      cases hstep : F.step a.2.1 (F.hist prob a.2.1 a.2.2 k) with
      | inl y => rw [hstep] at hk; cases hk
      | inr d =>
        have hOut := F.out_eq_some_of_step_right prob a.2.1 a.2.2 k d hstep
        change ((F.out prob a.2.1 a.2.2).map envelope).getD 0 =
          envelope ((F.out prob a.2.1 a.2.2).getD 0)
        rw [hOut]
        rfl
    · simp only [if_neg hA]
      unfold Proc.out
      rw [dif_neg (show ¬∃ k, _ from hA)]
      rfl
  rw [heq]
  exact Measurable.ite hA (he.comp (measurable_observationValue est ρ z hp)) measurable_const

private theorem observation_prefix_expected_le (est ρ : ℝ) (z x : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (hprob : ∀ q, prob q ∈ Icc 0 1)
    (finish : ℕ → ℝ → ENNReal) (hf : ∀ n, Measurable (finish n)) (envelope : ℝ → ENNReal)
    (he : Measurable envelope) (hle : ∀ n a, finish n a ≤ envelope a) (n : ℕ) :
    (∫⁻ ω, (observationProc est ρ x z).prefixValue prob g finish ω n [] ∂observationSeedLaw) ≤
      (observationProc est ρ x z).expCost prob observationSeedLaw g +
        ∫⁻ y, envelope y ∂observationKernel est ρ z prob x := by
  let F := observationProc est ρ x z
  have mp : Measurable (fun a : ObservationPath => (x,a)) := measurable_prodMk_left
  have hTape : Measurable (fun a : ObservationPath => F.prefixTapeCost prob g finish a.1 a.2 n 0 []) := by
    simpa only [Function.comp_def, Proc.hist] using
      ((measurable_observationPrefixTape est ρ z hp hg finish hf n 0).comp mp)
  have hEnvelope : Measurable (fun a : ObservationPath =>
      ((F.out prob a.1 a.2).map envelope).getD 0) := by
    simpa only [Function.comp_def] using
      ((measurable_observationEnvelope est ρ z hp envelope he).comp mp)
  have hInt :
      (∫⁻ a : ObservationPath, ((F.out prob a.1 a.2).map envelope).getD 0
        ∂(Proc.law observationSeedLaw)) ≤
      ∫⁻ y, envelope y ∂observationKernel est ρ z prob x := by
    have hm : Measurable (fun a => observationValue est ρ z prob (x,a)) :=
      (measurable_observationValue est ρ z hp).comp mp
    rw [observationKernel_apply est ρ z hp x, lintegral_map he hm]
    apply lintegral_mono
    intro a
    change ((F.out prob a.1 a.2).map envelope).getD 0 ≤ envelope ((F.out prob a.1 a.2).getD 0)
    cases F.out prob a.1 a.2 <;> simp
  exact (F.prefixExpected_le prob hprob observationSeedLaw g finish envelope hle n
    hTape.aemeasurable hEnvelope.aemeasurable).trans (add_le_add le_rfl hInt)

end BilateralProfitRegular.Factory
end BundlePart033


section BundlePart034


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private abbrev RunHistory (τ : ℕ) := Fin τ → Prices × ℝ

private noncomputable def runTapeLaw (k : ℕ) : Measure (Fin k → ObservationPath) :=
  Measure.pi (fun _ => Proc.law observationSeedLaw)

private instance runTapeLaw_probability (k : ℕ) : IsProbabilityMeasure (runTapeLaw k) := by
  unfold runTapeLaw
  infer_instance

private theorem runTape_cons_preserving (k : ℕ) :
    MeasurePreserving
      (fun s : ObservationPath × (Fin k → ObservationPath) => Fin.cons s.1 s.2)
      ((Proc.law observationSeedLaw).prod (runTapeLaw k)) (runTapeLaw (k+1)) := by
  let μ := Proc.law observationSeedLaw
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (0 : Fin (k+1))).symm
  have hh : (fun s : ObservationPath × (Fin k → ObservationPath) => Fin.cons s.1 s.2) =
      ⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ObservationPath) 0).symm) := by
    funext s i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [hh]
  exact he

variable {Ω : Type} [MeasurableSpace Ω]

/-- Execute a complete virtual run on a finite list of independent observation tapes.
The result combines the physical query costs with a terminal payoff on the trajectory. -/
private noncomputable def observationTapeRun (A : BanditAlg Prices Ω)
    (est ρ : ℝ) (z : Prices) (prob : Prices → ℝ)
    (cst : Prices × ObservationPath → ENNReal) (term : (τ : ℕ) → RunHistory τ → ENNReal) :
    (k τ : ℕ) → Ω → RunHistory τ → (Fin k → ObservationPath) → ENNReal
  | 0, τ, _, h, _ => term τ h
  | k+1, τ, ω, h, tapes =>
    let x := A.query τ ω h
    let s := tapes 0
    cst (x,s) +
      observationTapeRun A est ρ z prob cst term k (τ+1) ω
        (Fin.snoc (α := fun _ => Prices × ℝ) h (x, observationValue est ρ z prob (x,s)))
        (fun i => tapes i.succ)

private theorem measurable_observationTapeRun (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob)
    {cst : Prices × ObservationPath → ENNReal} (hc : Measurable cst)
    {term : (τ : ℕ) → RunHistory τ → ENNReal} (ht : ∀ τ, Measurable (term τ))
    (k τ : ℕ) : Measurable (fun a : (Ω × RunHistory τ) × (Fin k → ObservationPath) =>
      observationTapeRun A est ρ z prob cst term k τ a.1.1 a.1.2 a.2) := by
  induction k generalizing τ with
  | zero => exact (ht τ).comp (measurable_snd.comp measurable_fst)
  | succ k ih =>
    let W := (Ω × RunHistory τ) × (Fin (k+1) → ObservationPath)
    let getX := fun a : W => A.query τ a.1.1 a.1.2
    let getS := fun a : W => a.2 0
    have hx : Measurable getX := (A.measurable_query τ).comp measurable_fst
    have hs : Measurable getS := (measurable_pi_apply 0).comp measurable_snd
    have hY : Measurable (fun a : W => observationValue est ρ z prob (getX a,getS a)) :=
      (measurable_observationValue est ρ z hp).comp (hx.prodMk hs)
    have hH : Measurable (fun a : W =>
        Fin.snoc (α := fun _ => Prices × ℝ) a.1.2
          (getX a, observationValue est ρ z prob (getX a,getS a))) :=
      BanditAlg.measurable_snoc_pair.comp ((measurable_snd.comp measurable_fst).prodMk (hx.prodMk hY))
    have hω : Measurable (fun a : W => a.1.1) := measurable_fst.comp measurable_fst
    have htail : Measurable (fun a : W => fun i : Fin k => a.2 i.succ) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
    simp only [observationTapeRun]
    change Measurable (fun a : W =>
      cst (getX a,getS a) + observationTapeRun A est ρ z prob cst term k (τ+1) a.1.1
        (Fin.snoc (α := fun _ => Prices × ℝ) a.1.2
          (getX a, observationValue est ρ z prob (getX a,getS a))) (fun i => a.2 i.succ))
    exact (hc.comp (hx.prodMk hs)).add ((ih (τ+1)).comp ((hω.prodMk hH).prodMk htail))

private theorem observationTapeRun_eq_go (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob)
    {cst : Prices × ObservationPath → ENNReal} (hc : Measurable cst)
    {term : (τ : ℕ) → RunHistory τ → ENNReal} (ht : ∀ τ, Measurable (term τ))
    (k τ : ℕ) (ω : Ω) (h : RunHistory τ) :
    (∫⁻ tapes, observationTapeRun A est ρ z prob cst term k τ ω h tapes ∂runTapeLaw k) =
      observationGo A est ρ z prob cst term k τ ω h := by
  induction k generalizing τ with
  | zero => simp [observationTapeRun, observationGo]
  | succ k ih =>
    let μ := Proc.law observationSeedLaw
    let x := A.query τ ω h
    let F := observationTapeRun A est ρ z prob cst term (k+1) τ ω h
    have hPair : Measurable (fun t : Fin (k+1) → ObservationPath => ((ω,h),t)) :=
      measurable_prodMk_left
    have hF : Measurable F := by
      simpa only [Function.comp_def] using
        ((measurable_observationTapeRun A est ρ z hp hc ht (k+1) τ).comp hPair)
    let jt := fun s : ObservationPath × (Fin k → ObservationPath) =>
      Fin.cons (α := fun _ => ObservationPath) s.1 s.2
    have hs : MeasurePreserving jt (μ.prod (runTapeLaw k)) (runTapeLaw (k+1)) :=
      runTape_cons_preserving k
    change (∫⁻ tapes, F tapes ∂runTapeLaw (k+1)) = _
    have hm : Measurable (fun s => F (jt s)) := hF.comp hs.measurable
    rw [← hs.lintegral_comp hF, lintegral_prod _ hm.aemeasurable]
    unfold observationGo
    apply lintegral_congr
    intro s
    let H := Fin.snoc (α := fun _ => Prices × ℝ) h (x, observationValue est ρ z prob (x,s))
    have heq : (fun tapes : Fin k → ObservationPath => F (jt (s,tapes))) =
        fun tapes => cst (x,s) + observationTapeRun A est ρ z prob cst term k (τ+1) ω H tapes := by
      funext tapes
      simp only [F, jt, observationTapeRun, Fin.cons_zero, Fin.cons_succ, H, x]
    rw [heq, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, ih]

end BilateralProfitRegular.Factory
end BundlePart034


section BundlePart035


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option maxHeartbeats 800000

private noncomputable def copyTerminal (n τ : ℕ) (h : RunHistory τ) : RunHistory n :=
  if hn : τ = n then fun i => h (Fin.cast hn.symm i) else fun _ => ((0,0),0)

private theorem measurable_copyTerminal (n τ : ℕ) : Measurable (copyTerminal n τ) := by
  unfold copyTerminal
  split <;> rename_i hn
  · subst τ
    simp only [Fin.cast_eq_self]
    exact measurable_id
  · exact measurable_const

variable {Ω : Type} [MeasurableSpace Ω]

/-- Completed output trajectory of one optimizer copy on its own independent observation tapes. -/
private noncomputable def copyTapeResult (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (prob : Prices → ℝ) (n : ℕ) :
    (k τ : ℕ) → Ω → RunHistory τ → (Fin k → ObservationPath) → RunHistory n
  | 0, τ, _, h, _ => copyTerminal n τ h
  | k+1, τ, ω, h, tapes =>
    let x := A.query τ ω h
    let obs := observationValue est ρ z prob (x,tapes 0)
    copyTapeResult A est ρ z prob n k (τ+1) ω
      (Fin.snoc (α := fun _ => Prices × ℝ) h (x,obs)) (fun i => tapes i.succ)

private theorem measurable_copyTapeResult (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob) (n k τ : ℕ) :
    Measurable (fun a : (Ω × RunHistory τ) × (Fin k → ObservationPath) =>
      copyTapeResult A est ρ z prob n k τ a.1.1 a.1.2 a.2) := by
  induction k generalizing τ with
  | zero => exact (measurable_copyTerminal n τ).comp (measurable_snd.comp measurable_fst)
  | succ k ih =>
    let W := (Ω × RunHistory τ) × (Fin (k+1) → ObservationPath)
    let X := fun a : W => A.query τ a.1.1 a.1.2
    let S := fun a : W => a.2 0
    have hX : Measurable X := (A.measurable_query τ).comp measurable_fst
    have hS : Measurable S := (measurable_pi_apply 0).comp measurable_snd
    have hY : Measurable (fun a : W => observationValue est ρ z prob (X a,S a)) :=
      (measurable_observationValue est ρ z hp).comp (hX.prodMk hS)
    have hH : Measurable (fun a : W => Fin.snoc (α := fun _ => Prices × ℝ) a.1.2
        (X a, observationValue est ρ z prob (X a,S a))) :=
      BanditAlg.measurable_snoc_pair.comp ((measurable_snd.comp measurable_fst).prodMk
        (hX.prodMk hY))
    have hω : Measurable (fun a : W => a.1.1) := measurable_fst.comp measurable_fst
    have ht : Measurable (fun a : W => fun i : Fin k => a.2 i.succ) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
    simp only [copyTapeResult]
    exact (ih (τ+1)).comp ((hω.prodMk hH).prodMk ht)

private noncomputable def completedCopy (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (prob : Prices → ℝ) (n : ℕ) (a : Ω × (Fin n → ObservationPath)) : RunHistory n :=
  copyTapeResult A est ρ z prob n n 0 a.1 Fin.elim0 a.2

private theorem measurable_completedCopy (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob : Prices → ℝ} (hp : Measurable prob) (n : ℕ) :
    Measurable (completedCopy A est ρ z prob n) :=
  (measurable_copyTapeResult A est ρ z hp n n 0).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

private theorem tapeRun_eq_copyPayoff (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (prob : Prices → ℝ) (n : ℕ) (f : RunHistory n → ENNReal) (k τ : ℕ)
    (ω : Ω) (h : RunHistory τ) (tapes : Fin k → ObservationPath) (hkn : τ+k=n) :
    observationTapeRun A est ρ z prob (fun _ => 0)
      (fun τ h => if hn : τ=n then f (fun i => h (Fin.cast hn.symm i)) else 0) k τ ω h tapes =
      f (copyTapeResult A est ρ z prob n k τ ω h tapes) := by
  induction k generalizing τ with
  | zero =>
    have ht : τ=n := by omega
    subst τ
    simp [observationTapeRun, copyTapeResult, copyTerminal]
  | succ k ih =>
    rw [observationTapeRun, copyTapeResult, zero_add]
    exact ih _ _ _ (by omega)

private theorem completedCopy_lintegral_eq_trajExp (A : BanditAlg Prices Ω) (Pω : Measure Ω)
    [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (n : ℕ) {f : RunHistory n → ENNReal} (hf : Measurable f) :
    (∫⁻ a, f (completedCopy A est ρ z prob n a) ∂(Pω.prod (runTapeLaw n))) =
      A.trajExp (observationEnv est ρ z prob) Pω n f := by
  have hfm : Measurable (fun a => f (completedCopy A est ρ z prob n a)) :=
    hf.comp (measurable_completedCopy A est ρ z hp n)
  let term := fun τ (h : RunHistory τ) =>
    if hn : τ=n then f (fun i => h (Fin.cast hn.symm i)) else 0
  have ht (τ : ℕ) : Measurable (term τ) := by
    unfold term
    split <;> rename_i hn
    · subst τ
      simpa only [Fin.cast_eq_self] using hf
    · exact measurable_const
  rw [lintegral_prod _ hfm.aemeasurable, ← observation_trajectory_exp A Pω est ρ z hp n hf]
  apply lintegral_congr
  intro ω
  change _ = observationGo A est ρ z prob (fun _ => 0) term n 0 ω Fin.elim0
  rw [← observationTapeRun_eq_go A est ρ z hp measurable_const ht]
  apply lintegral_congr
  intro tapes
  exact (tapeRun_eq_copyPayoff A est ρ z prob n f n 0 ω Fin.elim0 tapes (by simp)).symm

private theorem program_finCons_preserving {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (k : ℕ) :
    MeasurePreserving (fun s : D × (Fin k → D) => Fin.cons s.1 s.2)
      (μ.prod (Measure.pi (fun _ => μ))) (Measure.pi (fun _ : Fin (k+1) => μ)) := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (0 : Fin (k+1))).symm
  have hh : (fun s : D × (Fin k → D) => Fin.cons s.1 s.2) =
      ⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => D) 0).symm) := by
    funext s i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [hh]
  exact he

/-- Product measure of independent optimizer seeds and independent arrays of observation tapes. -/
private noncomputable def batchTapeLaw (Pω : Measure Ω) (n m : ℕ) :
    Measure (Fin m → Ω × (Fin n → ObservationPath)) :=
  Measure.pi (fun _ => Pω.prod (runTapeLaw n))

private instance batchTapeLaw_probability (Pω : Measure Ω) [IsProbabilityMeasure Pω] (n m : ℕ) :
    IsProbabilityMeasure (batchTapeLaw Pω n m) := by unfold batchTapeLaw; infer_instance

private theorem measurable_finCons {D : Type} [MeasurableSpace D] (m : ℕ) :
    Measurable (fun p : D × (Fin m → D) => Fin.cons (α := fun _ => D) p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

private theorem completedBatch_lintegral_eq_multiExp (A : BanditAlg Prices Ω) (Pω : Measure Ω)
    [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (n m : ℕ) {f : (Fin m → RunHistory n) → ENNReal} (hf : Measurable f) :
    (∫⁻ a, f (fun i => completedCopy A est ρ z prob n (a i)) ∂batchTapeLaw Pω n m) =
      A.multiExp (observationEnv est ρ z prob) Pω n m f := by
  let R := completedCopy A est ρ z prob n
  have hR : Measurable R := measurable_completedCopy A est ρ z hp n
  have hRall (k : ℕ) : Measurable (fun a : Fin k → Ω × (Fin n → ObservationPath) => fun i => R (a i)) :=
    measurable_pi_lambda _ (fun i => hR.comp (measurable_pi_apply i))
  let μ := Pω.prod (runTapeLaw n)
  induction m with
  | zero =>
    have he : (fun a : Fin 0 → Ω × (Fin n → ObservationPath) => f (fun i => R (a i))) =
        fun _ => f Fin.elim0 := by funext a; congr 1; exact Subsingleton.elim _ _
    rw [show (fun a : Fin 0 → Ω × (Fin n → ObservationPath) => f (fun i => R (a i))) = _ from he]
    simp [BanditAlg.multiExp]
  | succ m ih =>
    let J := fun t : RunHistory n => A.multiExp (observationEnv est ρ z prob) Pω n m
      (fun ts => f (Fin.cons (α := fun _ => RunHistory n) t ts))
    have hJ : Measurable J := by
      have heq : J = fun t => ∫⁻ a, f (Fin.cons t (fun i => R (a i))) ∂batchTapeLaw Pω n m := by
        funext t
        symm
        exact ih ((hf.comp (measurable_finCons m)).comp measurable_prodMk_left)
      rw [heq]
      have hm : Measurable (fun s : RunHistory n × (Fin m → Ω × (Fin n → ObservationPath)) =>
          f (Fin.cons s.1 (fun i => R (s.2 i)))) :=
        ((hf.comp (measurable_finCons m)).comp (measurable_fst.prodMk ((hRall m).comp measurable_snd)))
      exact hm.lintegral_prod_right'
    let H := fun a : Fin (m+1) → Ω × (Fin n → ObservationPath) => f (fun i => R (a i))
    have hH : Measurable H := hf.comp (hRall (m+1))
    let jt := fun s : (Ω × (Fin n → ObservationPath)) × (Fin m → Ω × (Fin n → ObservationPath)) =>
      Fin.cons (α := fun _ => Ω × (Fin n → ObservationPath)) s.1 s.2
    have hpres : MeasurePreserving jt (μ.prod (batchTapeLaw Pω n m)) (batchTapeLaw Pω n (m+1)) :=
      program_finCons_preserving μ m
    have hm : Measurable (fun s => H (jt s)) := hH.comp hpres.measurable
    change (∫⁻ a, H a ∂batchTapeLaw Pω n (m+1)) = A.trajExp _ Pω n J
    rw [← completedCopy_lintegral_eq_trajExp A Pω est ρ z hp n hJ, ← hpres.lintegral_comp hH,
      lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro a
    change (∫⁻ ts, H (jt (a,ts)) ∂batchTapeLaw Pω n m) = J (R a)
    have he : (fun ts : Fin m → Ω × (Fin n → ObservationPath) => H (jt (a,ts))) =
        fun ts => f (Fin.cons (R a) (fun i => R (ts i))) := by
      funext ts
      unfold H jt
      congr
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [he]
    exact ih ((hf.comp (measurable_finCons m)).comp measurable_prodMk_left)

end BilateralProfitRegular.Factory
end BundlePart035


section BundlePart036


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

private theorem banditGo_cost_terminal (A : BanditAlg Prices Ω) (ν : ObsEnv Prices)
    (hν : ∀ τ, IsMarkovKernel (ν τ)) {c : Prices → ENNReal} (hc : Measurable c)
    (term : (τ : ℕ) → RunHistory τ → ENNReal) (k τ : ℕ) (ω : Ω) (h : RunHistory τ) :
    A.go ν c term k τ ω h =
      A.go ν c (fun _ _ => 0) k τ ω h + A.go ν 0 term k τ ω h := by
  induction k generalizing τ with
  | zero => simp [BanditAlg.go]
  | succ k ih =>
    let x := A.query τ ω h
    let H := fun y => Fin.snoc (α := fun _ => Prices × ℝ) h (x,y)
    let μ := ν τ (h,x)
    let C := fun y => A.go ν c (fun _ _ => 0) k (τ+1) ω (H y)
    let F := fun y => A.go ν 0 term k (τ+1) ω (H y)
    have hm : Measurable (fun y => (ω,H y)) :=
      measurable_const.prodMk (BanditAlg.measurable_snoc_pair.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    have hC : Measurable C :=
      (A.measurable_go ν hν hc (fun _ => measurable_const) k (τ+1)).comp hm
    simp only [BanditAlg.go, Pi.zero_apply, zero_add]
    change c x + (∫⁻ y, A.go ν c term k (τ+1) ω (H y) ∂μ) =
      c x + (∫⁻ y, C y ∂μ) + ∫⁻ y, F y ∂μ
    have he (y : ℝ) : A.go ν c term k (τ+1) ω (H y) = C y + F y := ih _ _
    simp_rw [he]
    rw [lintegral_add_left hC, add_assoc]

private theorem measurable_multiExp_family {D : Type} [MeasurableSpace D]
    (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (n m : ℕ) {f : D × (Fin m → RunHistory n) → ENNReal} (hf : Measurable f) :
    Measurable (fun d => A.multiExp (observationEnv est ρ z prob) Pω n m (fun hs => f (d,hs))) := by
  let R := completedCopy A est ρ z prob n
  have hr : Measurable (fun a : Fin m → Ω × (Fin n → ObservationPath) => fun i => R (a i)) :=
    measurable_pi_lambda _ (fun i => (measurable_completedCopy A est ρ z hp n).comp (measurable_pi_apply i))
  have h := hf.comp (measurable_fst.prodMk (hr.comp measurable_snd))
  have hpoint (d : D) :
      A.multiExp (observationEnv est ρ z prob) Pω n m (fun hs => f (d,hs)) =
      ∫⁻ a, f (d,fun i => R (a i)) ∂batchTapeLaw Pω n m :=
    (completedBatch_lintegral_eq_multiExp A Pω est ρ z hp n m (hf.comp measurable_prodMk_left)).symm
  have heq : (fun d => A.multiExp (observationEnv est ρ z prob) Pω n m (fun hs => f (d,hs))) =
      fun d => ∫⁻ a, f (d,fun i => R (a i)) ∂batchTapeLaw Pω n m := funext hpoint
  rw [heq]
  haveI : IsProbabilityMeasure (batchTapeLaw Pω n m) := by unfold batchTapeLaw; infer_instance
  exact h.lintegral_prod_right'

end BilateralProfitRegular.Factory
end BundlePart036


section BundlePart037





namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

set_option maxHeartbeats 900000

private theorem observationProgram_value_eq_prefix (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    (prob g : Prices → ℝ) (finish : ℕ → ℝ → ENNReal) (n : ℕ) (h : ObservationHistory) :
    Program.value prob (fun q => ENNReal.ofReal (g q))
      (fun bs => observationProgram est ρ x z ω (h.map Prod.snd ++ bs)) n finish =
        (observationProc est ρ x z).prefixValue prob g finish ω n h := by
  let Z := observationProgram est ρ x z ω
  have follow (h : ObservationHistory) (y : Prices) (b : Bool) :
      Program.after (fun bs => Z (h.map Prod.snd ++ bs)) b =
        fun bs => Z ((h ++ [(y,b)]).map Prod.snd ++ bs) := by
    funext bs
    simp [Program.after, List.map_append, List.append_assoc]
  induction n generalizing h with
  | zero =>
    rw [Program.value, Proc.prefixValue, List.append_nil, observationProgram_replay]
    cases (observationProc est ρ x z).step ω h <;> rfl
  | succ n ih =>
    rw [Program.value, Proc.prefixValue, List.append_nil, observationProgram_replay]
    cases hs : (observationProc est ρ x z).step ω h with
    | inl y =>
      simp only [Sum.swap, Sum.elim_inl, Sum.elim_inr]
      rw [follow h y true, follow h y false, ih, ih]
    | inr r => rfl

private theorem observationProgram_expected_le (est ρ : ℝ) (x z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (hprob : ∀ y, prob y ∈ Icc 0 1)
    (finish : ℕ → ℝ → ENNReal) (hf : ∀ n, Measurable (finish n)) (envelope : ℝ → ENNReal)
    (he : Measurable envelope) (hle : ∀ n a, finish n a ≤ envelope a) (n : ℕ) :
    (∫⁻ ω, Program.value prob (fun y => ENNReal.ofReal (g y))
      (observationProgram est ρ x z ω) n finish ∂observationSeedLaw) ≤
      (observationProc est ρ x z).expCost prob observationSeedLaw g +
        ∫⁻ y, envelope y ∂observationKernel est ρ z prob x := by
  have hval (ω : ObservationSeed) :
      Program.value prob (fun y => ENNReal.ofReal (g y)) (observationProgram est ρ x z ω) n finish =
      (observationProc est ρ x z).prefixValue prob g finish ω n [] :=
    observationProgram_value_eq_prefix est ρ x z ω prob g finish n []
  simp_rw [hval]
  exact observation_prefix_expected_le est ρ z x hp hg hprob finish hf envelope he hle n

variable {Ω : Type} [MeasurableSpace Ω]

/-- One optimizer copy drives a fresh observation decision tree at each virtual step. -/
private noncomputable def copyProgram (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices) (n : ℕ)
    (ω : Ω) : (k τ : ℕ) → RunHistory τ → (Fin k → ObservationSeed) → Program (RunHistory n)
  | 0, τ, h, _ => Program.pure (copyTerminal n τ h)
  | k+1, τ, h, seeds =>
    let x := A.query τ ω h
    Program.bind (observationProgram est ρ x z (seeds 0)) (fun y =>
      copyProgram A est ρ z n ω k (τ+1)
        (Fin.snoc (α := fun _ => Prices × ℝ) h (x,y)) (fun i => seeds i.succ))

/-- Compose independent optimizer copies and retain the complete array of trajectories. -/
private noncomputable def batchProgram (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices) (n : ℕ) :
    (m : ℕ) → (Fin m → Ω × (Fin n → ObservationSeed)) → Program (Fin m → RunHistory n)
  | 0, _ => Program.pure Fin.elim0
  | m+1, seeds =>
    let s := seeds 0
    Program.bind (copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2) (fun h =>
      Program.bind (batchProgram A est ρ z n m (fun i => seeds i.succ)) (fun hs =>
        Program.pure (Fin.cons h hs)))

private theorem measurable_copyProgram {D : Type} [MeasurableSpace D] (A : BanditAlg Prices Ω)
    (n k τ : ℕ) (est ρ : D → ℝ) (z : D → Prices) (ω : D → Ω)
    (h : D → RunHistory τ) (seeds : D → Fin k → ObservationSeed)
    (he : Measurable est) (hr : Measurable ρ) (hz : Measurable z) (hω : Measurable ω)
    (hh : Measurable h) (hs : Measurable seeds) :
    Program.MeasurableFamily (fun d => copyProgram A (est d) (ρ d) (z d) n (ω d) k τ
      (h d) (seeds d)) := by
  induction k generalizing D τ with
  | zero =>
    exact Program.measurableFamily_pure ((measurable_copyTerminal n τ).comp hh)
  | succ k ih =>
    let X := fun d => A.query τ (ω d) (h d)
    have hX : Measurable X := (A.measurable_query τ).comp (hω.prodMk hh)
    have h0 : Measurable (fun d => seeds d 0) := (measurable_pi_apply 0).comp hs
    have hm : Measurable (fun d : D => (((est d,ρ d),(X d,z d),seeds d 0) : ObservationArgs)) :=
      (he.prodMk hr).prodMk ((hX.prodMk hz).prodMk h0)
    have hp : Program.MeasurableFamily
        (fun d => observationProgram (est d) (ρ d) (X d) (z d) (seeds d 0)) := by
      intro bs
      simpa only [Function.comp_def] using (measurable_observationProgram bs).comp hm
    let H := fun p : D × ℝ => Fin.snoc (α := fun _ => Prices × ℝ) (h p.1) (X p.1,p.2)
    have hH : Measurable H := BanditAlg.measurable_snoc_pair.comp
      ((hh.comp measurable_fst).prodMk ((hX.comp measurable_fst).prodMk measurable_snd))
    let T := fun p : D × ℝ => fun i : Fin k => seeds p.1 i.succ
    have hT : Measurable T := measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply i.succ).comp (hs.comp measurable_fst))
    have hk : Program.MeasurableFamily (fun p : D × ℝ =>
        copyProgram A (est p.1) (ρ p.1) (z p.1) n (ω p.1) k (τ+1) (H p) (T p)) :=
      ih (τ+1) _ _ _ _ _ _ (he.comp measurable_fst) (hr.comp measurable_fst)
        (hz.comp measurable_fst) (hω.comp measurable_fst) hH hT
    exact Program.measurableFamily_bind hp hk

private theorem measurable_batchProgram {D : Type} [MeasurableSpace D] (A : BanditAlg Prices Ω)
    (est ρ : D → ℝ) (z : D → Prices) (n m : ℕ)
    (seeds : D → Fin m → Ω × (Fin n → ObservationSeed))
    (he : Measurable est) (hr : Measurable ρ) (hz : Measurable z) (hs : Measurable seeds) :
    Program.MeasurableFamily (fun d => batchProgram A (est d) (ρ d) (z d) n m (seeds d)) := by
  induction m generalizing D with
  | zero => exact Program.measurableFamily_pure measurable_const
  | succ m ih =>
    let s₀ := fun d => seeds d 0
    have hs₀ : Measurable s₀ := (measurable_pi_apply 0).comp hs
    have hp : Program.MeasurableFamily (fun d => copyProgram A (est d) (ρ d) (z d) n
        (s₀ d).1 n 0 Fin.elim0 (s₀ d).2) :=
      measurable_copyProgram A n n 0 _ _ _ _ _ _ he hr hz (measurable_fst.comp hs₀)
        measurable_const (measurable_snd.comp hs₀)
    let tail := fun p : D × RunHistory n => fun i : Fin m => seeds p.1 i.succ
    have hTail : Measurable tail := measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply i.succ).comp (hs.comp measurable_fst))
    have ht : Program.MeasurableFamily (fun p : D × RunHistory n =>
        batchProgram A (est p.1) (ρ p.1) (z p.1) n m (tail p)) :=
      ih _ _ _ _ (he.comp measurable_fst) (hr.comp measurable_fst) (hz.comp measurable_fst) hTail
    have hc : Program.MeasurableFamily (fun p : (D × RunHistory n) × (Fin m → RunHistory n) =>
        Program.pure (Fin.cons (α := fun _ => RunHistory n) p.1.2 p.2)) :=
      Program.measurableFamily_pure ((measurable_finCons m).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact Program.measurableFamily_bind hp (Program.measurableFamily_bind ht hc)

private theorem observationProgram_legal (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    {S : Set Prices} (hS : ({z,(x.1,z.2),(z.1,x.2)} : Set Prices) ⊆ S) :
    Program.Legal S (observationProgram est ρ x z ω) := by
  intro bits y hy
  change ((observationProc est ρ x z).step ω (erasePrices bits)).swap = .inr y at hy
  cases h : (observationProc est ρ x z).step ω (erasePrices bits) with
  | inr v => simp [h, Sum.swap] at hy
  | inl q =>
    have hyq : q = y := by simpa [h, Sum.swap] using hy
    rw [← hyq]
    exact hS (observation_queries est ρ x z ω (erasePrices bits) q h)

private theorem legal_batchProgram (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n m : ℕ) (seeds : Fin m → Ω × (Fin n → ObservationSeed))
    {K S : Set Prices} (hA : A.QueriesIn K)
    (hS : ∀ x ∈ K, ∀ s, Program.Legal S (observationProgram est ρ x z s)) :
    Program.Legal S (batchProgram A est ρ z n m seeds) := by
  have hCopy (ω : Ω) (k τ : ℕ) (h : RunHistory τ) (s : Fin k → ObservationSeed) :
      Program.Legal S (copyProgram A est ρ z n ω k τ h s) := by
    induction k generalizing τ with
    | zero =>
      intro bs y hy
      simp [copyProgram, Program.pure] at hy
    | succ k ih =>
      unfold copyProgram
      exact Program.legal_bind (hS _ (hA _ _ _) _)
        (fun y => ih _ _ _)
  induction m with
  | zero =>
    intro bs y hy
    simp [batchProgram, Program.pure] at hy
  | succ m ih =>
    unfold batchProgram
    refine Program.legal_bind (hCopy _ _ _ _ _) (fun h =>
      Program.legal_bind (ih _) fun h' => ?_)
    intro bs y hy
    simp [Program.pure] at hy

private theorem batchProgram_legal (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n m : ℕ) (seeds : Fin m → Ω × (Fin n → ObservationSeed))
    {K S : Set Prices} (hA : A.QueriesIn K)
    (hS : ∀ x ∈ K, ({z,(x.1,z.2),(z.1,x.2)} : Set Prices) ⊆ S) :
    Program.Legal S (batchProgram A est ρ z n m seeds) :=
  legal_batchProgram A est ρ z n m seeds hA
    (fun x hx s => observationProgram_legal est ρ x z s (hS x hx))

private theorem batchProgram_mapQuery_eq (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n m : ℕ) (seeds : Fin m → Ω × (Fin n → ObservationSeed))
    {K S : Set Prices} (hA : A.QueriesIn K)
    (hS : ∀ x ∈ K, ({z,(x.1,z.2),(z.1,x.2)} : Set Prices) ⊆ S)
    {f : Prices → Prices} (hf : ∀ x ∈ S, f x = x) :
    Program.mapQuery f (batchProgram A est ρ z n m seeds) = batchProgram A est ρ z n m seeds :=
  Program.mapQuery_eq (batchProgram_legal A est ρ z n m seeds hA hS) hf

private noncomputable def copyProgramSeedLaw (Pω : Measure Ω) (n : ℕ) :
    Measure (Ω × (Fin n → ObservationSeed)) :=
  Pω.prod (Measure.pi (fun _ => observationSeedLaw))

private instance copyProgramSeedLaw_markov (Pω : Measure Ω) [IsProbabilityMeasure Pω] (n : ℕ) :
    IsProbabilityMeasure (copyProgramSeedLaw Pω n) := by
  unfold copyProgramSeedLaw
  infer_instance

private noncomputable def batchProgramSeedLaw (Pω : Measure Ω) (n m : ℕ) :
    Measure (Fin m → Ω × (Fin n → ObservationSeed)) :=
  Measure.pi (fun _ => copyProgramSeedLaw Pω n)

end BilateralProfitRegular.Factory
end BundlePart037


section BundlePart038


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

set_option maxHeartbeats 1000000

variable {Ω : Type} [MeasurableSpace Ω]

private theorem measurable_runTerminalPayoff {n : ℕ} {f : RunHistory n → ENNReal} (hf : Measurable f)
    (τ : ℕ) : Measurable (fun h : RunHistory τ =>
      if hn : τ = n then f (fun i => h (Fin.cast hn.symm i)) else 0) := by
  split <;> rename_i h
  · subst τ
    simpa only [Fin.cast_eq_self] using hf
  · exact measurable_const

private theorem copyProgram_prefix_go_le (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    {prob g : Prices → ℝ} (hp : Measurable prob) (hg : Measurable g)
    (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n : ℕ) (ω : Ω) (finish : ℕ → RunHistory n → ENNReal) (hf : ∀ r, Measurable (finish r))
    (env : RunHistory n → ENNReal) (he : Measurable env) (hle : ∀ r h, finish r h ≤ env h)
    (k τ : ℕ) (h : RunHistory τ) (hkn : τ+k=n) (N : ℕ) :
    (∫⁻ seeds, Program.value prob (fun y => ENNReal.ofReal (g y))
      (copyProgram A est ρ z n ω k τ h seeds) N finish
      ∂(Measure.pi fun _ : Fin k => observationSeedLaw)) ≤
      A.go (observationEnv est ρ z prob)
        (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
        (fun τ hx => if hτ : τ=n then env (fun i => hx (Fin.cast hτ.symm i)) else 0)
        k τ ω h := by
  let ν := observationEnv est ρ z prob
  let c := fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g
  let term := fun τ (hx : RunHistory τ) => if hτ : τ=n then env (fun i => hx (Fin.cast hτ.symm i)) else 0
  let G := fun y => ENNReal.ofReal (g y)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hg
  have hmC : Measurable c := measurable_observationExpectedCost est ρ z hp hg
  have hν := observationEnv_markov est ρ z hp
  have hterm (τ : ℕ) : Measurable (term τ) := measurable_runTerminalPayoff he τ
  induction k generalizing τ N with
  | zero =>
    have ht : τ=n := by omega
    subst τ
    simpa [copyProgram, copyTerminal, BanditAlg.go] using hle N h
  | succ k ih =>
    let x := A.query τ ω h
    let H := fun y => Fin.snoc (α := fun _ => Prices × ℝ) h (x,y)
    let p := fun s : ObservationSeed => observationProgram est ρ x z s
    let q := fun s : ℝ × (Fin k → ObservationSeed) =>
      copyProgram A est ρ z n ω k (τ+1) (H s.1) s.2
    have hP : Program.MeasurableFamily p := by
      intro bs
      have hm : Measurable (fun s : ObservationSeed => (((est,ρ),(x,z),s) : ObservationArgs)) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      simpa only [Function.comp_def] using (measurable_observationProgram bs).comp hm
    have hH : Measurable H := BanditAlg.measurable_snoc_pair.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hQ : Program.MeasurableFamily q :=
      measurable_copyProgram A n k (τ+1) _ _ _ _ _ _ measurable_const measurable_const
        measurable_const measurable_const (hH.comp measurable_fst) measurable_snd
    let Q := Measure.pi (fun _ : Fin k => observationSeedLaw)
    let W := fun seed => Program.value prob G (copyProgram A est ρ z n ω (k+1) τ h seed) N finish
    have hW : Measurable W := Program.measurable_value hp hG
      (measurable_copyProgram A n (k+1) τ _ _ _ _ _ _ measurable_const measurable_const
        measurable_const measurable_const measurable_const measurable_id) N
      (finish := fun r a => finish r a.2) (fun r => (hf r).comp measurable_snd)
    let J := fun r y => ∫⁻ ζ, Program.value prob G (q (y,ζ)) r finish ∂Q
    have hJ (r : ℕ) : Measurable (J r) := by
      have hm := Program.measurable_value hp hG hQ r
        (finish := fun m a => finish m a.2) (fun m => (hf m).comp measurable_snd)
      exact hm.lintegral_prod_right'
    let B := fun y => A.go ν c term k (τ+1) ω (H y)
    have hB : Measurable B :=
      (A.measurable_go ν hν hmC hterm k (τ+1)).comp (measurable_const.prodMk hH)
    have hJB (r : ℕ) (y : ℝ) : J r y ≤ B y :=
      ih (τ+1) (H y) (by omega) r
    have hπ : (∫⁻ seeds, W seeds ∂(Measure.pi fun _ : Fin (k+1) => observationSeedLaw)) =
        ∫⁻ s : ObservationSeed × (Fin k → ObservationSeed),
          Program.value prob G (Program.bind (p s.1) (fun y => q (y,s.2))) N finish
          ∂(observationSeedLaw.prod Q) := by
      have heq := (program_finCons_preserving observationSeedLaw k).lintegral_comp hW
      simpa only [W, copyProgram, Fin.cons_zero, Fin.cons_succ, p, q, H, x] using heq.symm
    change (∫⁻ seeds, W seeds ∂(Measure.pi fun _ : Fin (k+1) => observationSeedLaw)) ≤ _
    rw [hπ, Program.expected_bind observationSeedLaw Q hp hG hP hQ N hf]
    have hpre := observationProgram_expected_le est ρ x z hp hg hprob J hJ B hB hJB N
    change _ ≤ A.go ν c term (k+1) τ ω h
    rw [BanditAlg.go]
    exact hpre

private theorem copyProgram_prefix_le (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ} (hp : Measurable prob) (hg : Measurable g)
    (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n N : ℕ) (finish : ℕ → RunHistory n → ENNReal) (hf : ∀ r, Measurable (finish r))
    (env : RunHistory n → ENNReal) (he : Measurable env) (hle : ∀ r h, finish r h ≤ env h) :
    (∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y))
      (copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2) N finish ∂copyProgramSeedLaw Pω n) ≤
      (∫⁻ ω, A.go (observationEnv est ρ z prob)
        (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
        (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) +
      A.trajExp (observationEnv est ρ z prob) Pω n env := by
  let ν := observationEnv est ρ z prob
  let c := fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g
  let term := fun τ (hx : RunHistory τ) => if hτ : τ=n then env (fun i => hx (Fin.cast hτ.symm i)) else 0
  have hP : Program.MeasurableFamily (fun s : Ω × (Fin n → ObservationSeed) =>
      copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2) :=
    measurable_copyProgram A n n 0 _ _ _ _ _ _ measurable_const measurable_const
      measurable_const measurable_fst measurable_const measurable_snd
  have hV : Measurable (fun s : Ω × (Fin n → ObservationSeed) =>
      Program.value prob (fun y => ENNReal.ofReal (g y))
        (copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2) N finish) :=
    Program.measurable_value hp (ENNReal.measurable_ofReal.comp hg) hP N
    (finish := fun m a => finish m a.2) (fun m => (hf m).comp measurable_snd)
  have hc := measurable_observationExpectedCost est ρ z hp hg
  have hν := observationEnv_markov est ρ z hp
  unfold copyProgramSeedLaw
  rw [lintegral_prod _ hV.aemeasurable]
  calc
    _ ≤ ∫⁻ ω, A.go ν c term n 0 ω Fin.elim0 ∂Pω := lintegral_mono (fun ω =>
      copyProgram_prefix_go_le A est ρ z hp hg hprob n ω finish hf env he hle n 0 Fin.elim0 (by simp) N)
    _ = _ := by
      have hsplit (ω : Ω) : A.go ν c term n 0 ω Fin.elim0 =
          A.go ν c (fun _ _ => 0) n 0 ω Fin.elim0 + A.go ν 0 term n 0 ω Fin.elim0 :=
        banditGo_cost_terminal A ν hν hc term n 0 ω Fin.elim0
      simp_rw [hsplit]
      have hC : Measurable (fun ω => A.go ν c (fun _ _ => 0) n 0 ω Fin.elim0) :=
        (A.measurable_go ν hν hc (fun _ => measurable_const) n 0).comp
          (measurable_id.prodMk measurable_const)
      rw [lintegral_add_left hC]
      rfl

private theorem trajExp_add_const (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (n : ℕ) {f : RunHistory n → ENNReal} (hf : Measurable f) (d : ENNReal) :
    A.trajExp (observationEnv est ρ z prob) Pω n (fun h => d + f h) =
      d + A.trajExp (observationEnv est ρ z prob) Pω n f := by
  have hm : Measurable (fun h => d + f h) := measurable_const.add hf
  rw [← completedCopy_lintegral_eq_trajExp A Pω est ρ z hp n hm,
    ← completedCopy_lintegral_eq_trajExp A Pω est ρ z hp n hf]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

private theorem batchProgram_prefix_le (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ} (hp : Measurable prob) (hg : Measurable g)
    (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n m N : ℕ) (finish : ℕ → (Fin m → RunHistory n) → ENNReal)
    (hf : ∀ r, Measurable (finish r)) (env : (Fin m → RunHistory n) → ENNReal)
    (he : Measurable env) (hle : ∀ r h, finish r h ≤ env h) :
    (∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N finish
        ∂batchProgramSeedLaw Pω n m) ≤
      (m : ENNReal) * (∫⁻ ω, A.go (observationEnv est ρ z prob)
          (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
          (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) +
      A.multiExp (observationEnv est ρ z prob) Pω n m env := by
  let ν := observationEnv est ρ z prob
  let G := fun y => ENNReal.ofReal (g y)
  let D := Ω × (Fin n → ObservationSeed)
  let μ := copyProgramSeedLaw Pω n
  let C := ∫⁻ ω, A.go ν (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
    (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hg
  induction m generalizing N with
  | zero =>
    have : IsProbabilityMeasure (batchProgramSeedLaw Pω n 0) := by unfold batchProgramSeedLaw; infer_instance
    simpa [batchProgram,BanditAlg.multiExp] using hle N Fin.elim0
  | succ m ih =>
    let Q := batchProgramSeedLaw Pω n m
    have : IsProbabilityMeasure Q := by unfold Q batchProgramSeedLaw; infer_instance
    let p := fun s : D => copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2
    let q := fun a : RunHistory n × (Fin m → D) =>
      Program.bind (batchProgram A est ρ z n m a.2) (fun h =>
        Program.pure (Fin.cons (α := fun _ => RunHistory n) a.1 h))
    have hP : Program.MeasurableFamily p :=
      measurable_copyProgram A n n 0 _ _ _ _ _ _ measurable_const measurable_const
        measurable_const measurable_fst measurable_const measurable_snd
    have ht : Program.MeasurableFamily (fun a : RunHistory n × (Fin m → D) =>
        batchProgram A est ρ z n m a.2) :=
      measurable_batchProgram A _ _ _ n m _ measurable_const measurable_const measurable_const measurable_snd
    have hc : Program.MeasurableFamily (fun a : (RunHistory n × (Fin m → D)) × (Fin m → RunHistory n) =>
        Program.pure (Fin.cons (α := fun _ => RunHistory n) a.1.1 a.2)) :=
      Program.measurableFamily_pure ((measurable_finCons m).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    have hQ : Program.MeasurableFamily q := Program.measurableFamily_bind ht hc
    let W := fun s => Program.value prob G (batchProgram A est ρ z n (m+1) s) N finish
    have hW : Measurable W := Program.measurable_value hp hG
      (measurable_batchProgram A _ _ _ n (m+1) _ measurable_const measurable_const measurable_const measurable_id)
      N (finish := fun r a => finish r a.2) (fun r => (hf r).comp measurable_snd)
    have hpi : (∫⁻ s, W s ∂batchProgramSeedLaw Pω n (m+1)) =
        ∫⁻ s : D × (Fin m → D), Program.value prob G (Program.bind (p s.1) (fun a => q (a,s.2))) N finish
          ∂(μ.prod Q) := by
      have hm := (program_finCons_preserving μ m).lintegral_comp hW
      simpa only [W, batchProgram, p, q, Fin.cons_zero, Fin.cons_succ, batchProgramSeedLaw, Q, μ]
        using hm.symm
    let J := fun r y => ∫⁻ ζ, Program.value prob G (q (y,ζ)) r finish ∂Q
    have hJ (r : ℕ) : Measurable (J r) :=
      (Program.measurable_value hp hG hQ r
        (finish := fun m a => finish m a.2) (fun m => (hf m).comp measurable_snd)).lintegral_prod_right'
    let V := fun h : RunHistory n => A.multiExp ν Pω n m (fun hs => env (Fin.cons h hs))
    have hV : Measurable V :=
      measurable_multiExp_family A Pω est ρ z hp n m (he.comp (measurable_finCons m))
    let B := fun h => (m : ENNReal)*C + V h
    have hB : Measurable B := measurable_const.add hV
    have hjb (r : ℕ) (y : RunHistory n) : J r y ≤ B y := by
      let finish' := fun r h => finish r (Fin.cons (α := fun _ => RunHistory n) y h)
      let env' := fun h => env (Fin.cons (α := fun _ => RunHistory n) y h)
      have hc : Measurable (fun h : Fin m → RunHistory n =>
          Fin.cons (α := fun _ => RunHistory n) y h) :=
        (measurable_finCons m).comp (measurable_const.prodMk measurable_id)
      have hr := ih r finish' (fun t => (hf t).comp hc) env' (he.comp hc) (fun t h => hle t _)
      unfold J q
      simp only [Program.value_bind, Program.value_pure]
      exact hr
    change (∫⁻ s, W s ∂batchProgramSeedLaw Pω n (m+1)) ≤ _
    rw [hpi, Program.expected_bind μ Q hp hG hP hQ N hf]
    have hfirst := copyProgram_prefix_le A Pω est ρ z hp hg hprob n N J hJ B hB hjb
    calc
      _ ≤ C + A.trajExp ν Pω n B := hfirst
      _ = _ := by
        unfold B
        rw [trajExp_add_const A Pω est ρ z hp n hV]
        change C + ((m : ENNReal) * C + A.trajExp ν Pω n V) =
          ((m+1 : ℕ) : ENNReal)*C + A.trajExp ν Pω n V
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        ac_rfl

private theorem multiExp_good_envelope_le (A : BanditAlg Prices Ω) (Pω : Measure Ω)
    [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob : Prices → ℝ} (hp : Measurable prob)
    (n m T : ℕ) (hT : 0 < T) (R : ENNReal) (good : Set (Fin m → RunHistory n))
    (hgood : MeasurableSet good)
    (hbad : A.multiExp (observationEnv est ρ z prob) Pω n m
      (goodᶜ.indicator (fun _ => (1 : ENNReal))) ≤ ENNReal.ofReal (1 / (T : ℝ))) :
    A.multiExp (observationEnv est ρ z prob) Pω n m
      (fun hs => R + (T : ENNReal) * goodᶜ.indicator (fun _ => (1 : ENNReal)) hs) ≤ R + 1 := by
  let f := goodᶜ.indicator (fun _ => (1 : ENNReal))
  let ν := observationEnv est ρ z prob
  let μ := batchTapeLaw Pω n m
  let X := fun (a : Fin m → Ω × (Fin n → ObservationPath)) i =>
    completedCopy A est ρ z prob n (a i)
  have hf : Measurable f := measurable_const.indicator hgood.compl
  have henv : Measurable (fun hs => R + (T : ENNReal) * f hs) :=
    measurable_const.add (measurable_const.mul hf)
  have : IsProbabilityMeasure μ := by unfold μ batchTapeLaw; infer_instance
  have htfin : (T : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top T
  have hprod : (T : ENNReal) * ENNReal.ofReal (1 / (T : ℝ)) = 1 := by
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    rw [← ENNReal.ofReal_natCast T, ← ENNReal.ofReal_mul ht.le]
    rw [one_div, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one]
  calc
    _ = ∫⁻ a, R + (T : ENNReal) * f (X a) ∂μ :=
      (completedBatch_lintegral_eq_multiExp A Pω est ρ z hp n m henv).symm
    _ = R + (T : ENNReal) * A.multiExp ν Pω n m f := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ htfin]
      rw [completedBatch_lintegral_eq_multiExp A Pω est ρ z hp n m hf]
    _ ≤ R + 1 := add_le_add le_rfl (hprod ▸ mul_le_mul' le_rfl hbad)

end BilateralProfitRegular.Factory
end BundlePart038


section BundlePart039



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

namespace Program

variable {α β : Type}

/-- A program can only return a result after this many physical queries. -/
private def MinQueries (k : ℕ) (p : Program α) : Prop :=
  ∀ h : List Bool, h.length < k → ∃ x, p h = Sum.inr x

private theorem minQueries_after {k : ℕ} {p : Program α} (hp : MinQueries k p) (b : Bool) :
    MinQueries (k-1) (p.after b) := by
  intro h hh
  exact hp (b :: h) (by simpa only [List.length_cons] using (show h.length+1 < k by omega))

private theorem minQueries_bind {k l : ℕ} {p : Program α} {q : α → Program β}
    (hp : MinQueries k p) (hq : ∀ a, MinQueries l (q a)) : MinQueries (k+l) (p.bind q) := by
  intro h
  induction h generalizing k p with
  | nil =>
    intro hl
    cases he : p [] with
    | inl a =>
      have hk : k = 0 := by
        by_contra hn
        obtain ⟨x,hx⟩ := hp [] (by simpa using Nat.pos_of_ne_zero hn)
        simp [he] at hx
      obtain ⟨x,hx⟩ := hq a [] (by simpa [hk] using hl)
      exact ⟨x, by simp [bind, he, hx]⟩
    | inr x => exact ⟨x, by simp [bind, he]⟩
  | cons b h ih =>
    intro hl
    cases he : p [] with
    | inl a =>
      have hk : k = 0 := by
        by_contra hn
        obtain ⟨x,hx⟩ := hp [] (by simpa using Nat.pos_of_ne_zero hn)
        simp [he] at hx
      obtain ⟨x,hx⟩ := hq a (b::h) (by simpa [hk] using hl)
      exact ⟨x, by simp [bind, he, hx]⟩
    | inr x =>
      obtain ⟨y,hy⟩ := ih (minQueries_after hp b) (by simp only [List.length_cons] at hl; omega)
      exact ⟨y, by simp [bind, he, hy]⟩

/-- Only remaining horizons attainable after the mandatory queries enter the payoff. -/
private theorem value_mono_minQueries {p : Program α} {k : ℕ} (hp : MinQueries k p)
    (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ENNReal) (N : ℕ)
    {f g : ℕ → α → ENNReal} (hfg : ∀ r, r+k ≤ N → ∀ a, f r a ≤ g r a) :
    p.value prob gap N f ≤ p.value prob gap N g := by
  induction N generalizing k p with
  | zero =>
    cases he : p [] with
    | inl a =>
      have hk : k = 0 := by
        by_contra hn
        obtain ⟨x,hx⟩ := hp [] (by simpa using Nat.pos_of_ne_zero hn)
        simp [he] at hx
      simpa [value, he] using hfg 0 (by simp [hk]) a
    | inr x => simp [value, he]
  | succ N ih =>
    cases he : p [] with
    | inl a =>
      have hk : k = 0 := by
        by_contra hn
        obtain ⟨x,hx⟩ := hp [] (by simpa using Nat.pos_of_ne_zero hn)
        simp [he] at hx
      simpa [value, he] using hfg (N+1) (by simp [hk]) a
    | inr x =>
      simp only [value, he, Sum.elim_inr]
      have h (b : Bool) : (p.after b).value prob gap N f ≤ (p.after b).value prob gap N g :=
        ih (minQueries_after hp b) (fun r hr => hfg r (by omega))
      exact add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl (h true))
        (mul_le_mul' le_rfl (h false)))

private theorem value_eq_minQueries {p : Program α} {k : ℕ} (hp : MinQueries k p)
    (prob : (ℝ × ℝ) → ℝ) (gap : (ℝ × ℝ) → ENNReal) (N : ℕ)
    {f g : ℕ → α → ENNReal} (hfg : ∀ r, r+k ≤ N → ∀ a, f r a = g r a) :
    p.value prob gap N f = p.value prob gap N g :=
  le_antisymm (value_mono_minQueries hp prob gap N (fun r hr a => (hfg r hr a).le))
    (value_mono_minQueries hp prob gap N (fun r hr a => (hfg r hr a).ge))

end Program

namespace Factory

variable {Ω : Type} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000

private theorem observationProgram_minQueries (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed) :
    Program.MinQueries 1 (observationProgram est ρ x z ω) := by
  intro h hh
  have he : h = [] := List.length_eq_zero_iff.mp (by omega)
  subst h
  have h0 := observation_queries_first est ρ x z ω
  rw [show observationProgram est ρ x z ω [] =
    ((observationProc est ρ x z).step ω []).swap from observationProgram_replay est ρ x z ω []]
  cases hstep : (observationProc est ρ x z).step ω [] with
  | inl y => exact ⟨y,rfl⟩
  | inr y => simp [hstep] at h0

private theorem copyProgram_minQueries (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n : ℕ) (ω : Ω) (k τ : ℕ) (h : RunHistory τ) (s : Fin k → ObservationSeed) :
    Program.MinQueries k (copyProgram A est ρ z n ω k τ h s) := by
  induction k generalizing τ with
  | zero => intro h hh; omega
  | succ k ih =>
    simpa only [copyProgram, Nat.add_comm 1 k] using
      Program.minQueries_bind (observationProgram_minQueries est ρ (A.query τ ω h) z (s 0))
        (q := fun y => copyProgram A est ρ z n ω k (τ+1)
          (Fin.snoc (α := fun _ => Prices × ℝ) h (A.query τ ω h,y)) (fun i => s i.succ))
        (fun y => ih _ _ _)

private theorem batchProgram_minQueries (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n m : ℕ) (s : Fin m → Ω × (Fin n → ObservationSeed)) :
    Program.MinQueries (m*n) (batchProgram A est ρ z n m s) := by
  induction m with
  | zero => intro h hh; simp at hh
  | succ m ih =>
    unfold batchProgram
    rw [Nat.succ_mul, Nat.add_comm (m*n) n]
    apply Program.minQueries_bind (copyProgram_minQueries A est ρ z n (s 0).1 n 0 Fin.elim0 (s 0).2)
    intro y
    rw [← Nat.add_zero (m*n)]
    exact Program.minQueries_bind (ih (fun i => s i.succ)) (fun _ => by intro h hh; omega)

private theorem batchProgram_zero_horizon (A : BanditAlg Prices Ω) (est ρ : ℝ) (z : Prices)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (s : Fin m → Ω × (Fin n → ObservationSeed))
    (prob : Prices → ℝ) (gap : Prices → ENNReal) (finish : ℕ → (Fin m → RunHistory n) → ENNReal) :
    Program.value prob gap (batchProgram A est ρ z n m s) 0 finish = 0 := by
  obtain ⟨x,hx⟩ := batchProgram_minQueries A est ρ z n m s []
    (by simpa using Nat.mul_pos hm hn)
  simp [Program.value, hx]

/-- If the horizon is contained in the first `b` copy budgets and there
are more copies to run, the capped batch pays at most `b` complete-copy costs. -/
private theorem batchProgram_prefix_le_blocks (A : BanditAlg Prices Ω)
    (Pω : Measure Ω) [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (C : ENNReal)
    (hC : (∫⁻ ω, A.go (observationEnv est ρ z prob)
      (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
      (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) ≤ C)
    (b m N : ℕ) (hbm : b < m) (hN : N ≤ b*n)
    (finish : ℕ → (Fin m → RunHistory n) → ENNReal) (hf : ∀ r, Measurable (finish r)) :
    (∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N finish
        ∂batchProgramSeedLaw Pω n m) ≤ (b : ENNReal) * C := by
  let ν := observationEnv est ρ z prob
  let G := fun y => ENNReal.ofReal (g y)
  let D := Ω × (Fin n → ObservationSeed)
  let μ := copyProgramSeedLaw Pω n
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hg
  induction b generalizing m N with
  | zero =>
    have he : N = 0 := by simpa using hN
    subst N
    simp_rw [batchProgram_zero_horizon A est ρ z n m hn hbm]
    simp
  | succ b ih =>
    cases m with
    | zero => omega
    | succ m =>
      let Q := batchProgramSeedLaw Pω n m
      have : IsProbabilityMeasure Q := by unfold Q batchProgramSeedLaw; infer_instance
      let p := fun s : D => copyProgram A est ρ z n s.1 n 0 Fin.elim0 s.2
      let q := fun a : RunHistory n × (Fin m → D) =>
        Program.bind (batchProgram A est ρ z n m a.2) (fun h =>
          Program.pure (Fin.cons (α := fun _ => RunHistory n) a.1 h))
      have hP : Program.MeasurableFamily p :=
        measurable_copyProgram A n n 0 _ _ _ _ _ _ measurable_const measurable_const
          measurable_const measurable_fst measurable_const measurable_snd
      have ht : Program.MeasurableFamily (fun a : RunHistory n × (Fin m → D) =>
          batchProgram A est ρ z n m a.2) :=
        measurable_batchProgram A _ _ _ n m _ measurable_const measurable_const measurable_const measurable_snd
      have hc : Program.MeasurableFamily (fun a : (RunHistory n × (Fin m → D)) × (Fin m → RunHistory n) =>
          Program.pure (Fin.cons (α := fun _ => RunHistory n) a.1.1 a.2)) :=
        Program.measurableFamily_pure ((measurable_finCons m).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      have hQ : Program.MeasurableFamily q := Program.measurableFamily_bind ht hc
      let W := fun s => Program.value prob G (batchProgram A est ρ z n (m+1) s) N finish
      have hW : Measurable W := Program.measurable_value hp hG
        (measurable_batchProgram A _ _ _ n (m+1) _ measurable_const measurable_const measurable_const measurable_id)
        N (finish := fun r a => finish r a.2) (fun r => (hf r).comp measurable_snd)
      have hpi : (∫⁻ s, W s ∂batchProgramSeedLaw Pω n (m+1)) =
          ∫⁻ s : D × (Fin m → D), Program.value prob G (Program.bind (p s.1) (fun a => q (a,s.2))) N finish
            ∂(μ.prod Q) := by
        have hm := (program_finCons_preserving μ m).lintegral_comp hW
        simpa only [W, batchProgram, p, q, Fin.cons_zero, Fin.cons_succ, batchProgramSeedLaw, Q, μ]
          using hm.symm
      let J := fun r y => ∫⁻ ζ, Program.value prob G (q (y,ζ)) r finish ∂Q
      have hJ (r : ℕ) : Measurable (J r) :=
        (Program.measurable_value hp hG hQ r
          (finish := fun m a => finish m a.2) (fun m => (hf m).comp measurable_snd)).lintegral_prod_right'
      let J' := fun r y => J (min r (N-n)) y
      have hjb (r : ℕ) (y : RunHistory n) : J' r y ≤ (b : ENNReal)*C := by
        let finish' := fun r h => finish r (Fin.cons (α := fun _ => RunHistory n) y h)
        have hc : Measurable (fun h : Fin m → RunHistory n =>
            Fin.cons (α := fun _ => RunHistory n) y h) :=
          (measurable_finCons m).comp (measurable_const.prodMk measurable_id)
        have hb : min r (N-n) ≤ b*n := by
          rw [Nat.succ_mul] at hN
          omega
        have hr := ih m (min r (N-n)) (by omega) hb finish' (fun t => (hf t).comp hc)
        unfold J' J q
        simp only [Program.value_bind, Program.value_pure]
        exact hr
      change (∫⁻ s, W s ∂batchProgramSeedLaw Pω n (m+1)) ≤ _
      rw [hpi, Program.expected_bind μ Q hp hG hP hQ N hf]
      have hclip (s : D) : Program.value prob G (p s) N J = Program.value prob G (p s) N J' :=
        Program.value_eq_minQueries (copyProgram_minQueries A est ρ z n s.1 n 0 Fin.elim0 s.2)
          prob G N (fun r hr y => by simp [J', Nat.min_eq_left (show r ≤ N-n by omega)])
      change (∫⁻ s, Program.value prob G (p s) N J ∂μ) ≤ _
      simp_rw [hclip]
      have hfirst := copyProgram_prefix_le A Pω est ρ z hp hg hprob n N J'
        (fun r => hJ (min r (N-n))) (fun _ => (b : ENNReal)*C) measurable_const hjb
      have hconst : A.trajExp ν Pω n (fun _ => (b : ENNReal)*C) = (b : ENNReal)*C := by
        rw [← completedCopy_lintegral_eq_trajExp A Pω est ρ z hp n
          (measurable_const : Measurable (fun _ : RunHistory n => (b : ENNReal)*C))]
        simp
      refine hfirst.trans ?_
      rw [hconst, Nat.cast_succ, add_mul, one_mul]
      exact (add_le_add hC le_rfl).trans_eq (add_comm _ _)

/-- A copy is charged only if at least one query of it can be played.
The terminal envelope is charged only if the complete batch can fit. -/
private theorem batchProgram_prefix_le_started (A : BanditAlg Prices Ω)
    (Pω : Measure Ω) [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (m N : ℕ) (C : ENNReal)
    (hC : (∫⁻ ω, A.go (observationEnv est ρ z prob)
      (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
      (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) ≤ C)
    (finish : ℕ → (Fin m → RunHistory n) → ENNReal) (hf : ∀ r, Measurable (finish r))
    (env : (Fin m → RunHistory n) → ENNReal) (he : Measurable env)
    (hle : ∀ r ≤ N-m*n, ∀ h, finish r h ≤ env h) :
    (∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N finish
        ∂batchProgramSeedLaw Pω n m) ≤
      ((min m (N ⌈/⌉ n) : ℕ) : ENNReal) * C +
        if m*n ≤ N then A.multiExp (observationEnv est ρ z prob) Pω n m env else 0 := by
  let b := N ⌈/⌉ n
  have hb : N ≤ b*n := by
    rw [Nat.mul_comm]
    exact (ceilDiv_le_iff_le_mul hn).mp (le_refl b)
  by_cases hdone : m*n ≤ N
  · have hmb : m ≤ b := Nat.le_of_mul_le_mul_right (hdone.trans hb) hn
    let finish' := fun r hs => finish (min r (N-m*n)) hs
    rw [if_pos hdone, min_eq_left hmb]
    calc
      _ ≤ ∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y))
          (batchProgram A est ρ z n m s) N finish' ∂batchProgramSeedLaw Pω n m :=
        lintegral_mono (fun s => Program.value_mono_minQueries (batchProgram_minQueries A est ρ z n m s)
          prob (fun y => ENNReal.ofReal (g y)) N (fun r hr hs => by
            simp [finish', Nat.min_eq_left (show r ≤ N-m*n by omega)]))
      _ ≤ _ := (batchProgram_prefix_le A Pω est ρ z hp hg hprob n m N finish'
        (fun r => hf (min r (N-m*n))) env he (fun r hs => hle _ (min_le_right _ _) hs)).trans
          (add_le_add (mul_le_mul' le_rfl hC) le_rfl)
  · rw [if_neg hdone, add_zero]
    by_cases hbm : b < m
    · rw [min_eq_right hbm.le]
      exact batchProgram_prefix_le_blocks A Pω est ρ z hp hg hprob n hn C hC b m N hbm hb finish hf
    · have hmb : m ≤ b := by omega
      rw [min_eq_left hmb]
      have hv (s : Fin m → Ω × (Fin n → ObservationSeed)) :
          Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N finish =
            Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N
              (fun _ _ => 0) :=
        Program.value_eq_minQueries (batchProgram_minQueries A est ρ z n m s) prob
          (fun y => ENNReal.ofReal (g y)) N (fun r hr _ => (hdone (by omega)).elim)
      simp_rw [hv]
      have heq : A.multiExp (observationEnv est ρ z prob) Pω n m (fun _ => 0) = 0 := by
        rw [← completedBatch_lintegral_eq_multiExp A Pω est ρ z hp n m
          (measurable_const : Measurable (fun _ : Fin m → RunHistory n => (0 : ENNReal)))]
        simp
      have hbase := batchProgram_prefix_le A Pω est ρ z hp hg hprob n m N (fun _ _ => 0)
        (fun _ => measurable_const) (fun _ => 0) measurable_const (fun _ _ => le_rfl)
      rw [heq, add_zero] at hbase
      exact hbase.trans (mul_le_mul' le_rfl hC)

private theorem batchProgram_prefix_le_started_good (A : BanditAlg Prices Ω)
    (Pω : Measure Ω) [IsProbabilityMeasure Pω] (est ρ : ℝ) (z : Prices) {prob g : Prices → ℝ}
    (hp : Measurable prob) (hg : Measurable g) (hprob : ∀ y, prob y ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (m N T : ℕ) (hNT : N ≤ T) (hT : 0 < T) (C : ENNReal)
    (hC : (∫⁻ ω, A.go (observationEnv est ρ z prob)
      (fun x => (observationProc est ρ x z).expCost prob observationSeedLaw g)
      (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) ≤ C)
    (finish : ℕ → (Fin m → RunHistory n) → ENNReal) (hf : ∀ r, Measurable (finish r))
    (R : ENNReal) (good : Set (Fin m → RunHistory n)) (hgood : MeasurableSet good)
    (hbad : A.multiExp (observationEnv est ρ z prob) Pω n m
      (goodᶜ.indicator (fun _ => (1 : ENNReal))) ≤ ENNReal.ofReal (1 / (T : ℝ)))
    (hfinish : ∀ r ≤ N-m*n, ∀ hs, finish r hs ≤ (r : ENNReal))
    (hfinishGood : ∀ r ≤ N-m*n, ∀ hs ∈ good, finish r hs ≤ R) :
    (∫⁻ s, Program.value prob (fun y => ENNReal.ofReal (g y)) (batchProgram A est ρ z n m s) N finish
        ∂batchProgramSeedLaw Pω n m) ≤
      ((min m (N ⌈/⌉ n) : ℕ) : ENNReal) * C + if m*n ≤ N then R + 1 else 0 := by
  let env := fun hs => R + (T : ENNReal) * goodᶜ.indicator (fun _ => (1 : ENNReal)) hs
  have he : Measurable env := measurable_const.add
    (measurable_const.mul (measurable_const.indicator hgood.compl))
  have hle (r : ℕ) (hr : r ≤ N-m*n) (hs : Fin m → RunHistory n) : finish r hs ≤ env hs := by
    by_cases hm : hs ∈ good
    · have hb : hs ∉ goodᶜ := by simpa using hm
      simpa [env, Set.indicator_of_notMem hb] using hfinishGood r hr hs hm
    · have hb : hs ∈ goodᶜ := hm
      have ht : (r : ENNReal) ≤ (T : ENNReal) := by
        exact_mod_cast hr.trans ((Nat.sub_le _ _).trans hNT)
      simp only [env, Set.indicator_of_mem hb, mul_one]
      exact (hfinish r hr hs).trans (ht.trans le_add_self)
  refine (batchProgram_prefix_le_started A Pω est ρ z hp hg hprob n hn m N C hC
    finish hf env he hle).trans (add_le_add le_rfl ?_)
  split_ifs
  · exact multiExp_good_envelope_le A Pω est ρ z hp n m T hT R good hgood hbad
  · exact le_rfl

end Factory
end BilateralProfitRegular
end
end BundlePart039


section BundlePart040



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private def regretGap (E : Environment) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (muStar E - mu E x)

private theorem measurable_P (E : Environment) (hE : OnUnit E) : Measurable (P E) :=
  (BilateralProfitMHR.positive_density_profit_facts E hE).2.1

private theorem measurable_regretGap (E : Environment) (hE : OnUnit E) : Measurable (regretGap E) :=
  (measurable_const.sub ((measurable_snd.sub measurable_fst).mul (measurable_P E hE))).ennreal_ofReal

private theorem regretGap_le (E : Environment) (hE : OnUnit E) (x : ℝ × ℝ) (hx : x ∈ triT) :
    regretGap E x ≤ ENNReal.ofReal (muStar E) := by
  apply ENNReal.ofReal_le_ofReal
  have hmu := mul_nonneg (sub_nonneg.mpr hx.2.1) ((onUnit_facts E hE).1 x).1
  change muStar E - (x.2 - x.1) * P E x ≤ muStar E
  linarith

private theorem triT_mem_unitSq {x : ℝ × ℝ} (hx : x ∈ triT) : x ∈ BilateralProfitMHR.unitSq :=
  ⟨⟨hx.1, hx.2.1.trans hx.2.2⟩, ⟨hx.1.trans hx.2.1, hx.2.2⟩⟩

private theorem zero_mem_triT : ((0, 0) : ℝ × ℝ) ∈ triT := by norm_num [triT]

private structure RandomProgram (I A : Type) [MeasurableSpace I] [MeasurableSpace A] where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : Measure Seed
  probability : IsProbabilityMeasure law
  run : I × Seed → Program A
  measurable_run : Program.MeasurableFamily run
  legal : ∀ s, Program.Legal triT (run s)

namespace RandomProgram

variable {I A B J : Type} [MeasurableSpace I] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace J]

private instance (p : RandomProgram I A) : MeasurableSpace p.Seed := p.seedSpace

private instance (p : RandomProgram I A) : IsProbabilityMeasure p.law := p.probability

private def expected (p : RandomProgram I A) (E : Environment) (i : I) (n : ℕ)
    (finish : ℕ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (p.run (i, ω)).value (P E) (regretGap E) n finish ∂p.law

private def pure (f : I → A) (hf : Measurable f) : RandomProgram I A where
  Seed := Unit
  seedSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance
  run s := Program.pure (f s.1)
  measurable_run := Program.measurableFamily_pure (hf.comp measurable_fst)
  legal := by simp [Program.Legal, Program.pure]

@[simp]
private theorem expected_pure (f : I → A) (hf : Measurable f) (E : Environment)
    (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    (pure f hf).expected E i n finish = finish n (f i) := by
  change (∫⁻ (_ : Unit), (Program.pure (f i)).value (P E) (regretGap E) n finish
    ∂Measure.dirac ()) = finish n (f i)
  rw [Program.value_pure, lintegral_const]
  simp

private def compInput (p : RandomProgram I A) (f : J → I) (hf : Measurable f) : RandomProgram J A where
  Seed := p.Seed
  seedSpace := p.seedSpace
  law := p.law
  probability := p.probability
  run s := p.run (f s.1, s.2)
  measurable_run h := (p.measurable_run h).comp ((hf.comp measurable_fst).prodMk measurable_snd)
  legal s := p.legal (f s.1, s.2)

@[simp]
private theorem expected_compInput (p : RandomProgram I A) (f : J → I) (hf : Measurable f)
    (E : Environment) (i : J) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    (p.compInput f hf).expected E i n finish = p.expected E (f i) n finish := rfl

private def bind (p : RandomProgram I A) (k : RandomProgram (I × A) B) : RandomProgram I B where
  Seed := p.Seed × k.Seed
  seedSpace := inferInstance
  law := p.law.prod k.law
  probability := inferInstance
  run s := (p.run (s.1, s.2.1)).bind (fun a => k.run ((s.1, a), s.2.2))
  measurable_run := Program.measurableFamily_bind
    (fun h => (p.measurable_run h).comp (measurable_fst.prodMk measurable_snd.fst))
    (fun h => (k.measurable_run h).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd.snd))
  legal s := Program.legal_bind (p.legal _) (fun a => k.legal ((s.1, a), s.2.2))

private theorem expected_bind (p : RandomProgram I A) (k : RandomProgram (I × A) B)
    (E : Environment) (hE : OnUnit E) (i : I) (n : ℕ) {finish : ℕ → B → ℝ≥0∞}
    (hf : ∀ n, Measurable (finish n)) :
    (p.bind k).expected E i n finish =
      p.expected E i n (fun m a => k.expected E (i, a) m finish) := by
  apply Program.expected_bind p.law k.law (measurable_P E hE) (measurable_regretGap E hE)
    (fun h => (p.measurable_run h).comp (measurable_const.prodMk measurable_id))
    (fun h => (k.measurable_run h).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) n hf

private theorem measurable_expected (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    (n : ℕ) {finish : ℕ → A → ℝ≥0∞} (hf : ∀ m, Measurable (finish m)) :
    Measurable (fun i => p.expected E i n finish) :=
  (Program.measurable_value (measurable_P E hE) (measurable_regretGap E hE)
    p.measurable_run n (finish := fun m x => finish m x.2)
    (fun m => (hf m).comp measurable_snd)).lintegral_prod_right

private theorem expected_le_time (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    (i : I) (n : ℕ) (B : ℝ≥0∞) (hB : ENNReal.ofReal (muStar E) ≤ B)
    {finish : ℕ → A → ℝ≥0∞} (hf : ∀ m ≤ n, ∀ a, finish m a ≤ (m : ℝ≥0∞) * B) :
    p.expected E i n finish ≤ (n : ℝ≥0∞) * B := by
  calc
    _ ≤ ∫⁻ (_ : p.Seed), (n : ℝ≥0∞) * B ∂p.law :=
      lintegral_mono fun s => Program.value_le_time (p.legal _) (onUnit_facts E hE).1 B
        (fun x hx => (regretGap_le E hE x hx).trans hB) n hf
    _ = _ := by simp

private def Bound (p : RandomProgram I A) (E : Environment) (T : ℕ)
    (pre : I → Prop) (good : I → A → Prop) (cost : ℝ≥0∞) : Prop :=
  ∀ i, pre i → ∀ n ≤ T, ∀ (finish : ℕ → A → ℝ≥0∞),
    (∀ m, Measurable (finish m)) →
    (∀ m ≤ n, ∀ a, finish m a ≤ (m : ℝ≥0∞)) →
    ∀ R : ℝ≥0∞, (∀ m ≤ n, ∀ a, good i a → finish m a ≤ R) →
    p.expected E i n finish ≤ cost + R

private theorem bound_of_postprocess (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    (T : ℕ) {pre : I → Prop} {good : I → A → Prop} {post : I → B → Prop} {cost : ℝ≥0∞}
    (f : I × A → B) (hf : Measurable f) (hp : p.Bound E T pre good cost)
    (hpost : ∀ i a, pre i → good i a → post i (f (i, a))) :
    (p.bind (pure f hf)).Bound E T pre post cost := by
  intro i hi n hn finish hmeas htime R hR
  rw [expected_bind p _ E hE i n hmeas]
  simp_rw [expected_pure]
  exact hp i hi n hn _ (fun m => (hmeas m).comp (hf.comp
    ((measurable_const (a := i)).prodMk measurable_id))) (fun m hm a => htime m hm _)
    R (fun m hm a ha => hR m hm _ (hpost i a hi ha))

open scoped Classical in
private def when (p : RandomProgram I I) (s : Set I) (hs : MeasurableSet s) : RandomProgram I I where
  Seed := p.Seed
  seedSpace := p.seedSpace
  law := p.law
  probability := p.probability
  run x h := if x.1 ∈ s then p.run x h else .inl x.1
  measurable_run h := (p.measurable_run h).ite (hs.preimage measurable_fst)
    (Program.measurableFamily_pure measurable_fst h)
  legal x h y hy := by
    split at hy
    · exact p.legal x h y hy
    · cases hy

private theorem bound_when (p : RandomProgram I I) (s : Set I) (hs : MeasurableSet s)
    (E : Environment) (T : ℕ) {pre : I → Prop} {good : I → I → Prop} {cost : ℝ≥0∞}
    (hp : p.Bound E T (fun i => pre i ∧ i ∈ s) good cost)
    (hskip : ∀ i, pre i → i ∉ s → good i i) :
    (p.when s hs).Bound E T pre good cost := by
  classical
  intro i hi n hn finish hf htime R hR
  by_cases he : i ∈ s
  · have hrun (ω : p.Seed) : (p.when s hs).run (i, ω) = p.run (i, ω) := by
      funext h
      simp [when, he]
    change (∫⁻ ω : p.Seed, ((p.when s hs).run (i, ω)).value (P E) (regretGap E) n finish
      ∂p.law) ≤ _
    simp_rw [hrun]
    exact hp i ⟨hi, he⟩ n hn finish hf htime R hR
  · have h := hR n le_rfl i (hskip i hi he)
    have hrun (ω : p.Seed) : (p.when s hs).run (i, ω) = Program.pure i := by
      funext h
      simp [when, he, Program.pure]
    change (∫⁻ ω : p.Seed, ((p.when s hs).run (i, ω)).value (P E) (regretGap E) n finish
      ∂p.law) ≤ _
    simp_rw [hrun, Program.value_pure]
    simpa using h.trans (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ cost from bot_le))

private theorem bound_bind (p : RandomProgram I A) (k : RandomProgram (I × A) B)
    (E : Environment) (hE : OnUnit E) (T : ℕ)
    {pre : I → Prop} {good₁ : I → A → Prop} {good₂ : I × A → B → Prop}
    {post : I → B → Prop} {c₁ c₂ : ℝ≥0∞}
    (hp : p.Bound E T pre good₁ c₁)
    (hk : k.Bound E T (fun x => pre x.1 ∧ good₁ x.1 x.2) good₂ c₂)
    (hgood : ∀ i, pre i → ∀ a, good₁ i a → ∀ b, good₂ (i, a) b → post i b) :
    (p.bind k).Bound E T pre post (c₁ + c₂) := by
  intro i hi n hn finish hf htime R hR
  rw [expected_bind p k E hE i n hf, add_assoc]
  refine hp i hi n hn _ (fun m => (measurable_expected k E hE m hf).comp
    (measurable_const.prodMk measurable_id)) ?_ (c₂ + R) ?_
  · intro m hm a
    have hmu := (onUnit_facts E hE).2.2.2.1.2
    simpa using (expected_le_time k E hE (i, a) m 1
      (by simpa using ENNReal.ofReal_le_ofReal hmu)
      (fun r hr b => by simpa using htime r (hr.trans hm) b))
  · intro m hm a ha
    exact hk (i, a) ⟨hi, ha⟩ m (hm.trans hn) finish hf
      (fun r hr => htime r (hr.trans hm)) R (fun r hr b hb => hR r (hr.trans hm) b (hgood i hi a ha b hb))

end RandomProgram
end BilateralProfitRegular
end
end BundlePart040


section BundlePart041


noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

namespace Program

variable {A : Type}

private theorem value_gap_mono {prob : (ℝ × ℝ) → ℝ} {g g' : (ℝ × ℝ) → ℝ≥0∞}
    {S : Set (ℝ × ℝ)} {p : Program A} (hp : p.Legal S)
    (hgap : ∀ x ∈ S, g x ≤ g' x) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    p.value prob g n finish ≤ p.value prob g' n finish := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases hx : p [] with
    | inl a => simp [value, hx]
    | inr x =>
      simp only [value, hx, Sum.elim_inr]
      have hb (b : Bool) : (p.after b).value prob g n finish ≤
          (p.after b).value prob g' n finish :=
        ih (fun h y hy => hp (b :: h) y hy)
      exact add_le_add (hgap x (hp [] x hx))
        (add_le_add (mul_le_mul' le_rfl (hb true)) (mul_le_mul' le_rfl (hb false)))

private theorem value_le_add_baseline {prob : (ℝ × ℝ) → ℝ} {g g' : (ℝ × ℝ) → ℝ≥0∞}
    {S : Set (ℝ × ℝ)} {p : Program A} (hp : p.Legal S)
    (hprob : ∀ x, 0 ≤ prob x ∧ prob x ≤ 1) (b : ℝ≥0∞)
    (hgap : ∀ x ∈ S, g x ≤ b + g' x) (n : ℕ) {f f' : ℕ → A → ℝ≥0∞}
    (hf : ∀ m ≤ n, ∀ a, f m a ≤ (m : ℝ≥0∞) * b + f' m a) :
    p.value prob g n f ≤ (n : ℝ≥0∞) * b + p.value prob g' n f' := by
  induction n generalizing p with
  | zero =>
    cases hx : p [] with
    | inl a => simpa [value, hx] using hf 0 le_rfl a
    | inr x => simp [value, hx]
  | succ n ih =>
    cases hx : p [] with
    | inl a => simpa only [value, hx, Sum.elim_inl] using hf (n+1) le_rfl a
    | inr x =>
      let q := ENNReal.ofReal (prob x)
      let qb := ENNReal.ofReal (1 - prob x)
      let byes := (p.after true).value prob g' n f'
      let bno := (p.after false).value prob g' n f'
      let base := (n : ℝ≥0∞) * b
      have hsum : q + qb = 1 := by
        dsimp only [q, qb]
        rw [← ENNReal.ofReal_add (hprob x).1 (sub_nonneg.mpr (hprob x).2)]
        simp
      have hb (bit : Bool) : (p.after bit).value prob g n f ≤
          base + (p.after bit).value prob g' n f' :=
        ih (fun h y hy => hp (bit :: h) y hy) (fun m hm => hf m (hm.trans (Nat.le_succ n)))
      change (p []).elim (f (n + 1)) (fun y => g y +
        (ENNReal.ofReal (prob y) * (p.after true).value prob g n f +
        ENNReal.ofReal (1 - prob y) * (p.after false).value prob g n f)) ≤
        ((n + 1 : ℕ) : ℝ≥0∞) * b + (p []).elim (f' (n+1)) (fun y => g' y +
        (ENNReal.ofReal (prob y) * byes + ENNReal.ofReal (1 - prob y) * bno))
      rw [hx, Sum.elim_inr, Sum.elim_inr]
      calc
        _ ≤ (b + g' x) + (q * (base + byes) + qb * (base + bno)) :=
          add_le_add (hgap x (hp [] x hx))
            (add_le_add (mul_le_mul' le_rfl (hb true)) (mul_le_mul' le_rfl (hb false)))
        _ = (b + (q + qb) * base) + (g' x + (q * byes + qb * bno)) := by
          rw [mul_add, mul_add, add_mul]
          ac_rfl
        _ = _ := by rw [hsum, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm base b]

end Program

namespace RandomProgram

variable {I A B J : Type} [MeasurableSpace I] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace J]

private def expectedCost (p : RandomProgram I A) (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞)
    (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (p.run (i, ω)).value (P E) g n finish ∂p.law

@[simp]
private theorem expectedCost_regretGap (p : RandomProgram I A) (E : Environment)
    (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    p.expectedCost E (regretGap E) i n finish = p.expected E i n finish := rfl

private theorem expectedCost_mono (p : RandomProgram I A) (E : Environment)
    {g g' : (ℝ × ℝ) → ℝ≥0∞} (hg : ∀ x ∈ triT, g x ≤ g' x)
    (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    p.expectedCost E g i n finish ≤ p.expectedCost E g' i n finish :=
  lintegral_mono fun ω => Program.value_gap_mono (p.legal (i, ω)) hg n finish

private theorem expectedCost_finish_mono (p : RandomProgram I A) (E : Environment)
    (g : (ℝ × ℝ) → ℝ≥0∞) (i : I) (n : ℕ) {f f' : ℕ → A → ℝ≥0∞}
    (hf : ∀ m ≤ n, ∀ a, f m a ≤ f' m a) :
    p.expectedCost E g i n f ≤ p.expectedCost E g i n f' :=
  lintegral_mono fun ω => Program.value_mono (P E) g (p.run (i, ω)) n hf

@[simp]
private theorem expectedCost_pure (f : I → A) (hf : Measurable f) (E : Environment)
    (g : (ℝ × ℝ) → ℝ≥0∞) (i : I) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    (pure f hf).expectedCost E g i n finish = finish n (f i) := by
  change (∫⁻ (_ : Unit), (Program.pure (f i)).value (P E) g n finish
    ∂Measure.dirac ()) = finish n (f i)
  simp

@[simp]
private theorem expectedCost_compInput (p : RandomProgram I A) (f : J → I) (hf : Measurable f)
    (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞) (i : J) (n : ℕ) (finish : ℕ → A → ℝ≥0∞) :
    (p.compInput f hf).expectedCost E g i n finish = p.expectedCost E g (f i) n finish := rfl

private theorem expectedCost_when_of_mem (p : RandomProgram I I) (s : Set I) (hs : MeasurableSet s)
    (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞) {i : I} (hi : i ∈ s)
    (n : ℕ) (finish : ℕ → I → ℝ≥0∞) :
    (p.when s hs).expectedCost E g i n finish = p.expectedCost E g i n finish := by
  apply lintegral_congr
  intro ω
  have hr : (p.when s hs).run (i, ω) = p.run (i, ω) := by
    funext h
    simp [when, hi]
  rw [hr]

private theorem expectedCost_when_of_not_mem (p : RandomProgram I I) (s : Set I) (hs : MeasurableSet s)
    (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞) {i : I} (hi : i ∉ s)
    (n : ℕ) (finish : ℕ → I → ℝ≥0∞) :
    (p.when s hs).expectedCost E g i n finish = finish n i := by
  have hr (ω : p.Seed) : (p.when s hs).run (i, ω) = Program.pure i := by
    funext h
    simp [when, hi, Program.pure]
  change (∫⁻ ω : p.Seed, ((p.when s hs).run (i, ω)).value (P E) g n finish ∂p.law) = _
  simp_rw [hr, Program.value_pure, lintegral_const, measure_univ, mul_one]

private theorem expectedCost_bind (p : RandomProgram I A) (k : RandomProgram (I × A) B)
    (E : Environment) (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g)
    (i : I) (n : ℕ) {finish : ℕ → B → ℝ≥0∞} (hf : ∀ n, Measurable (finish n)) :
    (p.bind k).expectedCost E g i n finish =
      p.expectedCost E g i n (fun m a => k.expectedCost E g (i, a) m finish) := by
  apply Program.expected_bind p.law k.law (measurable_P E hE) hg
    (fun h => (p.measurable_run h).comp (measurable_const.prodMk measurable_id))
    (fun h => (k.measurable_run h).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) n hf

private theorem measurable_expectedCost (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g)
    (n : ℕ) {finish : ℕ → A → ℝ≥0∞} (hf : ∀ m, Measurable (finish m)) :
    Measurable (fun i => p.expectedCost E g i n finish) :=
  (Program.measurable_value (measurable_P E hE) hg p.measurable_run n
    (finish := fun m x => finish m x.2) (fun m => (hf m).comp measurable_snd)).lintegral_prod_right

private theorem expectedCost_le_time (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    (g : (ℝ × ℝ) → ℝ≥0∞) (i : I) (n : ℕ) (B : ℝ≥0∞)
    (hgap : ∀ x ∈ triT, g x ≤ B) {finish : ℕ → A → ℝ≥0∞}
    (hf : ∀ m ≤ n, ∀ a, finish m a ≤ (m : ℝ≥0∞) * B) :
    p.expectedCost E g i n finish ≤ (n : ℝ≥0∞) * B := by
  calc
    _ ≤ ∫⁻ (_ : p.Seed), (n : ℝ≥0∞) * B ∂p.law :=
      lintegral_mono fun s => Program.value_le_time (p.legal _) (onUnit_facts E hE).1 B hgap n hf
    _ = _ := by simp

private theorem expectedCost_le_add_baseline (p : RandomProgram I A) (E : Environment) (hE : OnUnit E)
    {g g' : (ℝ × ℝ) → ℝ≥0∞} (i : I) (n : ℕ) (b : ℝ≥0∞)
    (hgap : ∀ x ∈ triT, g x ≤ b + g' x) {f f' : ℕ → A → ℝ≥0∞}
    (hf : ∀ m ≤ n, ∀ a, f m a ≤ (m : ℝ≥0∞) * b + f' m a) :
    p.expectedCost E g i n f ≤ (n : ℝ≥0∞) * b + p.expectedCost E g' i n f' := by
  calc
    _ ≤ ∫⁻ ω : p.Seed, (n : ℝ≥0∞) * b + (p.run (i, ω)).value (P E) g' n f' ∂p.law :=
      lintegral_mono fun ω =>
        Program.value_le_add_baseline (p.legal _) (onUnit_facts E hE).1 b hgap n hf
    _ = _ := by rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]; rfl

private theorem expectedCost_le_add_baseline_tsub (p : RandomProgram I A) (E : Environment)
    (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞) (i : I) (n : ℕ) (b : ℝ≥0∞)
    (finish : ℕ → A → ℝ≥0∞) :
    p.expectedCost E g i n finish ≤ (n : ℝ≥0∞) * b +
      p.expectedCost E (fun x => g x - b) i n (fun m a => finish m a - (m : ℝ≥0∞) * b) :=
  expectedCost_le_add_baseline p E hE i n b
    (fun _ _ => le_add_tsub) (fun _ _ _ => le_add_tsub)

end RandomProgram

end BilateralProfitRegular
end
end BundlePart041


section BundlePart042


namespace BilateralProfitRegular.Factory

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

set_option maxHeartbeats 1000000

private theorem observation_expected_excess_cost (E : Environment) (hE : RegularUnit E)
    (η δ ε : ℝ) (hη : 0 < η) (hηδ : η < δ) (hε : 0 ≤ ε) (hmax : muStar E < 6*δ)
    (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (z : Prices) (hz : z ∈ c.region)
    (hρ : CalibValid E η δ c z ρ)
    (hgap : muStar E - auxProfit E (ρ * balance E z) z ≤ 65 * (η + ε))
    (x : Prices) (hx : x ∈ c.region) :
    let L := fun x => 1 / auxProfit E (ρ * balance E z) x
    (observationProc c.est ρ x z).expCost (P E) observationSeedLaw (fun y => muStar E - mu E y - 520*η) ≤
      ENNReal.ofReal (14040000*ε/δ) + ENNReal.ofReal (3888000*δ) *
        ENNReal.ofReal (L x - sInf (L '' c.region)) := by
  dsimp only
  let L := fun x => 1 / auxProfit E (ρ * balance E z) x
  let ℓ := L x - sInf (L '' c.region)
  let B := 520*ε + 144*δ^2*ℓ
  let F := observationProc c.est ρ x z
  have hδ : 0 < δ := hη.trans hηδ
  have hL : BddBelow (L '' c.region) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a,ha,rfl⟩
    have hlam := mul_pos hρ.1 (balance_pos E hE.1 (hc.1 hz))
    exact (one_div_pos.mpr (auxProfit_pos E hE.1 hlam (hc.1 ha))).le
  have hℓ : 0 ≤ ℓ := sub_nonneg.mpr (csInf_le hL (mem_image_of_mem L hx))
  have hcost (ω : ObservationSeed) (h : ObservationHistory) (y : Prices)
      (hy : F.step ω h = Sum.inl y) :
      ENNReal.ofReal (muStar E - mu E y - 520*η) ≤ ENNReal.ofReal B := by
    have hm := observation_queries c.est ρ x z ω h y hy
    have hquery := (observation_query_gap E hE c η δ hη hηδ hmax hc z hz ρ hρ x hx y hm).2
    change muStar E - mu E y ≤ 8*(muStar E - auxProfit E (ρ * balance E z) z) + 144*δ^2*ℓ at hquery
    apply ENNReal.ofReal_le_ofReal
    change muStar E - mu E y - 520*η ≤ 520*ε + 144*δ^2*ℓ
    linarith only [hquery, hgap]
  have hrounds := (observation_law_spec E hE δ hδ c hc ρ hρ.1 x z hx hz).1
  calc
    _ ≤ ENNReal.ofReal B * F.expRounds (P E) observationSeedLaw :=
      Proc.expCost_le_mul_expRounds F (P E) observationSeedLaw _ _ ENNReal.ofReal_ne_top hcost
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (27000/δ) := mul_le_mul' le_rfl hrounds
    _ = ENNReal.ofReal (14040000*ε/δ) + ENNReal.ofReal (3888000*δ) * ENNReal.ofReal ℓ := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ B by unfold B; positivity),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3888000*δ),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 14040000*ε/δ) (by positivity)]
      congr 1
      unfold B
      field_simp [hδ.ne']
      ring

/-- Complete-copy cost after subtracting the per-round baseline before truncation at zero. -/
private theorem observation_run_excess_cost {Ω : Type} [MeasurableSpace Ω]
    (A : BanditAlg Prices Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (E : Environment) (hE : RegularUnit E) (η δ ε : ℝ)
    (hη : 0 < η) (hηδ : η < δ) (hε : 0 ≤ ε) (hmax : muStar E < 6*δ)
    (c : Candidate) (hc : c.Valid E δ) (hK : A.QueriesIn c.region)
    (ρ : ℝ) (z : Prices) (hz : z ∈ c.region) (hρ : CalibValid E η δ c z ρ)
    (hgap : muStar E - auxProfit E (ρ * balance E z) z ≤ 65 * (η + ε)) (n : ℕ) :
    let ν := observationEnv c.est ρ z (P E)
    let L := fun x => 1 / auxProfit E (ρ * balance E z) x
    (∫⁻ ω, A.go ν
        (fun x => (observationProc c.est ρ x z).expCost (P E) observationSeedLaw
          (fun y => muStar E - mu E y - 520*η)) (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω) ≤
      n * ENNReal.ofReal (14040000*ε/δ) + ENNReal.ofReal (3888000*δ) *
        A.regret ν Pω n L c.region := by
  dsimp only
  let ν := observationEnv c.est ρ z (P E)
  let L := fun x => 1 / auxProfit E (ρ * balance E z) x
  let g := fun y => muStar E - mu E y - 520*η
  let a := ENNReal.ofReal (14040000*ε/δ)
  let b := ENNReal.ofReal (3888000*δ)
  let cst := fun x => (observationProc c.est ρ x z).expCost (P E) observationSeedLaw g
  let d := fun x => ENNReal.ofReal (L x - sInf (L '' c.region))
  have hν := observationEnv_markov c.est ρ z (measurable_tradeProbability E hE.1)
  have hb : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlocal (x : Prices) (hx : x ∈ c.region) : cst x ≤ a + b*d x :=
    observation_expected_excess_cost E hE η δ ε hη hηδ hε hmax c hc ρ z hz hρ hgap x hx
  calc
    _ ≤ ∫⁻ ω, (n : ENNReal)*a + b*A.go ν d (fun _ _ => 0) n 0 ω Fin.elim0 ∂Pω :=
      lintegral_mono (fun ω => go_cost_affine_bound A ν hν c.region hK cst d a b hb
        hlocal n 0 ω Fin.elim0)
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ hb, lintegral_const,
        measure_univ, mul_one]
      rfl

end BilateralProfitRegular.Factory
end BundlePart042


section BundlePart043


namespace BilateralProfitRegular

/-- The common regret scale before replacing `log (2T)` by a multiple of `log T`. -/
private noncomputable def mainBudget (T : ℕ) : ℝ :=
  (T : ℝ) ^ ((3 : ℝ) / 5) * mainLog T ^ 5

private theorem mainEta_mul_T {T : ℕ} (hT : 2 ≤ T) :
    (T : ℝ) * mainEta T = (T : ℝ) ^ ((3 : ℝ) / 5) := by
  have hpos : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold mainEta
  calc
    (T : ℝ) * (T : ℝ) ^ (-(2 : ℝ) / 5) =
        (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ (-(2 : ℝ) / 5) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring

private theorem main_inverse_rate {T : ℕ} (hT : 2 ≤ T) :
    (1 / mainEta T) * Real.sqrt (1 / mainEta T) = (T : ℝ) ^ ((3 : ℝ) / 5) := by
  have hpos : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [mainEta_inv hT, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
  congr 1
  ring

private theorem mainBudget_le_final {T : ℕ} (hT : 2 ≤ T) :
    mainBudget T ≤ 32 * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^5 := by
  unfold mainBudget
  have hp := pow_le_pow_left₀ (zero_le_one.trans (mainLog_ge_one hT)) (mainLog_le_two_log hT) 5
  refine (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Nat.cast_nonneg T) _)).trans_eq ?_
  ring

end BilateralProfitRegular
end BundlePart043


section BundlePart044


namespace BilateralProfitRegular

noncomputable section

/-- Include the first phase whose single-copy observation count exceeds the horizon. -/
private def startedPhaseCount (C₀ : ℝ) (T : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, T < phaseLen C₀ T j then Nat.find h + 1 else 1

private def startedRunMax (C₀ : ℝ) (T : ℕ) : ℕ :=
  max (phaseLen C₀ T 0) (4 * T)

private def startedRunFactor (C₀ : ℝ) : ℝ := 48 * C₀ + 5

private theorem started_phaseLen_pos {C₀ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀) :
    0 < phaseLen C₀ T j := by
  have hL : 0 < mainLog T := zero_lt_one.trans_le (mainLog_ge_one hT)
  exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.ceil_pos.mpr (mul_pos hC₀ (pow_pos hL _)))

private theorem started_phaseLen_succ (C₀ : ℝ) (T j : ℕ) :
    phaseLen C₀ T (j + 1) = 4 * phaseLen C₀ T j := by
  simp only [phaseLen, pow_succ]
  ring

private theorem started_phase_witness {C₀ : ℝ} {T : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀) :
    T < phaseLen C₀ T ⌈mainLog T⌉₊ := by
  let j := ⌈mainLog T⌉₊
  have hLog : 1 ≤ Real.log 4 := by
    simpa [mainLog, show (2 : ℝ) * 2 = 4 by norm_num] using mainLog_ge_one (T := 2) le_rfl
  have hc : mainLog T ≤ (j : ℝ) := Nat.le_ceil _
  have hj : (j : ℝ) ≤ (j : ℝ) * Real.log 4 := le_mul_of_one_le_right (by positivity) hLog
  have hpow : (2 : ℝ) * T ≤ (4 : ℝ) ^ j := by
    have h := Real.exp_le_exp.mpr (hc.trans hj)
    rwa [mainLog, Real.exp_log (by positivity), Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
  have h0 : (1 : ℕ) ≤ ⌈C₀ * mainLog T ^ 4⌉₊ := by
    simpa [phaseLen, mainLog] using started_phaseLen_pos (j := 0) hT hC₀
  have hf : 4 ^ j ≤ phaseLen C₀ T j := by
    change 4 ^ j ≤ 4 ^ j * ⌈C₀ * mainLog T ^ 4⌉₊
    exact Nat.le_mul_of_pos_right _ h0
  have hTreal : (0 : ℝ) < T := by positivity
  exact (Nat.cast_lt.mp (show (T : ℝ) < ((4 : ℕ) ^ j : ℕ) by
    push_cast
    linarith only [hTreal, hpow])).trans_le hf

private theorem startedPhaseCount_spec {C₀ : ℝ} {T : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀) :
    0 < startedPhaseCount C₀ T ∧
    T < phaseLen C₀ T (startedPhaseCount C₀ T - 1) ∧
    (∀ j, j + 1 < startedPhaseCount C₀ T → phaseLen C₀ T j ≤ T) ∧
    (startedPhaseCount C₀ T : ℝ) ≤ 3 * mainLog T := by
  classical
  have hw := started_phase_witness hT hC₀
  have h : ∃ j, T < phaseLen C₀ T j := ⟨_, hw⟩
  unfold startedPhaseCount
  rw [dif_pos h]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using Nat.find_spec h
  · intro j hj
    exact le_of_not_gt (Nat.find_min h (by omega))
  · have hJ : (Nat.find h : ℝ) ≤ (⌈mainLog T⌉₊ : ℝ) := Nat.cast_le.mpr (Nat.find_min' h hw)
    have hl := mainLog_ge_one hT
    have hc := Nat.ceil_lt_add_one (zero_le_one.trans hl)
    push_cast
    linarith only [hJ, hl, hc]

private theorem startedPhaseCount_eq_one {C₀ : ℝ} {T : ℕ} (h : T < phaseLen C₀ T 0) :
    startedPhaseCount C₀ T = 1 := by
  classical
  have hw : ∃ j, T < phaseLen C₀ T j := ⟨0, h⟩
  rw [startedPhaseCount, dif_pos hw, Nat.eq_zero_of_le_zero (Nat.find_min' hw h)]

private theorem started_phase_previous_le {C₀ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hj : j < startedPhaseCount C₀ T) :
    j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T := by
  rcases j with _ | j
  · exact Or.inl rfl
  · exact Or.inr ((startedPhaseCount_spec hT hC₀).2.2.1 j hj)

private theorem started_phase_bounds {C₀ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hj : j < startedPhaseCount C₀ T) :
    1 ≤ phaseLen C₀ T j ∧ phaseLen C₀ T j ≤ startedRunMax C₀ T := by
  refine ⟨started_phaseLen_pos hT hC₀, ?_⟩
  cases j with
  | zero => exact le_max_left _ _
  | succ j =>
      have hprev := (startedPhaseCount_spec hT hC₀).2.2.1 j hj
      rw [started_phaseLen_succ]
      exact (Nat.mul_le_mul_left _ hprev).trans (le_max_right _ _)

private theorem startedRunMax_bound {C₀ : ℝ} {T : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀) :
    (startedRunMax C₀ T : ℝ) ≤ startedRunFactor C₀ * T := by
  have hL := mainLog_ge_one hT
  have hl : 0 ≤ mainLog T := zero_le_one.trans hL
  have hbase : 0 < 2 * (T : ℝ) := by positivity
  have hx := Real.pow_div_factorial_le_exp (mainLog T) hl 4
  rw [mainLog, Real.exp_log hbase] at hx
  norm_num at hx
  have hpow : mainLog T ^ 4 ≤ 48 * (T : ℝ) := by
    change Real.log (2 * T)^4 ≤ 48 * (T : ℝ)
    linarith only [hx]
  have hceil : (⌈C₀ * mainLog T ^ 4⌉₊ : ℝ) < C₀ * mainLog T ^ 4 + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hC₀.le (by positivity))
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hC := mul_le_mul_of_nonneg_left hpow hC₀.le
  have hT0 : (0 : ℝ) ≤ T := by positivity
  unfold startedRunMax startedRunFactor
  rw [Nat.cast_max]
  refine max_le ?_ ?_
  · simp only [phaseLen, pow_zero, one_mul]
    change (⌈C₀ * mainLog T ^ 4⌉₊ : ℝ) ≤ _
    linarith only [hceil, hC, hT1, hT0]
  · push_cast
    nlinarith only [hT0, mul_nonneg hC₀.le hT0]

/-- The maximum number of copies of length `n` that can start in the remaining rounds. -/
private def startedCopies (M r n : ℕ) : ℕ :=
  min M ⌈(r : ℝ) / n⌉₊

private theorem startedCopies_le (M r n : ℕ) : startedCopies M r n ≤ M :=
  min_le_left _ _

private theorem le_startedCopies_of_start {M r n s : ℕ} (hn : 0 < n) (hM : s ≤ M)
    (hr : 0 < s → (s - 1) * n < r) : s ≤ startedCopies M r n := by
  cases s with
  | zero => exact Nat.zero_le _
  | succ s =>
      apply le_min hM
      apply Nat.lt_ceil.mpr
      apply (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
      exact_mod_cast (show s * n < r from hr (Nat.succ_pos _))

private theorem startedCopies_mul_le {M r n B : ℕ} (hn : 0 < n) (hB : n ≤ B) :
    startedCopies M r n * n ≤ r + B := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ (r : ℝ) / n by positivity)
  have hcap : (startedCopies M r n : ℝ) ≤ (⌈(r : ℝ) / n⌉₊ : ℝ) :=
    Nat.cast_le.mpr (min_le_right _ _)
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbound := mul_lt_mul_of_pos_right (hcap.trans_lt h) hnp
  rw [add_mul, one_mul, div_mul_cancel₀ _ hnp.ne'] at hbound
  exact (by exact_mod_cast hbound.le : startedCopies M r n * n ≤ r + n).trans
    (Nat.add_le_add_left hB _)

private theorem started_sqrt_split {s k a b : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (s*a) + Real.sqrt (k*b) ≤ Real.sqrt ((s+k)*(a+b)) := by
  let f : Fin 2 → ℝ := ![s, k]
  let g : Fin 2 → ℝ := ![a, b]
  have hf (i : Fin 2) : 0 ≤ f i := by fin_cases i <;> assumption
  have hg (i : Fin 2) : 0 ≤ g i := by fin_cases i <;> assumption
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg
  simpa [f, g, Fin.sum_univ_two, Real.sqrt_mul hs, Real.sqrt_mul hk,
    Real.sqrt_mul (add_nonneg hs hk)] using h

private theorem started_sqrt_square_mul {s n : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (s * (s * n)) = s * Real.sqrt n := by
  rw [← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs]

/-- A completed group spends at least its prescribed number of observations.
The continuation may also skip unused scheduled copies. -/
private theorem started_potential_step {K s k r r' n B : ℕ} (hK : s + k ≤ K)
    (hr : r' + s * n ≤ r) :
    (s : ℝ) * Real.sqrt n + Real.sqrt ((k : ℝ) * ((r' : ℝ) + B)) ≤
      Real.sqrt ((K : ℝ) * ((r : ℝ) + B)) := by
  have hs : 0 ≤ (s : ℝ) := by positivity
  have hk : 0 ≤ (k : ℝ) := by positivity
  rw [← started_sqrt_square_mul hs]
  refine (started_sqrt_split hs hk (by positivity) (by positivity)).trans ?_
  apply Real.sqrt_le_sqrt
  have hK' : (s : ℝ) + k ≤ K := by exact_mod_cast hK
  have hr' : (r' : ℝ) + (s : ℝ) * n ≤ r := by exact_mod_cast hr
  exact mul_le_mul hK' (by linarith only [hr']) (by positivity) (by positivity)

/-- The unfinished final group contributes its started copies and has no continuation. -/
private theorem started_potential_last {K s r n B : ℕ} (hs : s ≤ K) (hr : s * n ≤ r + B) :
    (s : ℝ) * Real.sqrt n ≤ Real.sqrt ((K : ℝ) * ((r : ℝ) + B)) := by
  rw [← started_sqrt_square_mul (Nat.cast_nonneg s)]
  exact Real.sqrt_le_sqrt (mul_le_mul (by exact_mod_cast hs) (by exact_mod_cast hr)
    (by positivity) (by positivity))

private theorem started_potential_split {K s r n B : ℕ} (hs : s ≤ K) (hr : s * n ≤ r) :
    (s : ℝ) * Real.sqrt n + Real.sqrt (((K-s : ℕ) : ℝ) * (((r-s*n : ℕ) : ℝ) + B)) ≤
      Real.sqrt ((K : ℝ) * ((r : ℝ) + B)) :=
  started_potential_step (by omega) (by omega)

private theorem started_phaseLen_mul_acc_div {C₀ δ : ℝ} {T j : ℕ} (hδ : 0 < δ) :
    (phaseLen C₀ T j : ℝ) * acc δ j / δ =
      Real.sqrt (phaseLen C₀ T j : ℝ) * Real.sqrt (phaseLen C₀ T 0 : ℝ) := by
  let n₀ := (phaseLen C₀ T 0 : ℝ)
  have h₀ : 0 ≤ n₀ := by positivity
  have hN : (phaseLen C₀ T j : ℝ) = (4 : ℝ)^j * n₀ := by
    simp [n₀, phaseLen]
  have hP : (4 : ℝ)^j = ((2 : ℝ)^j)^2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hH : (4 : ℝ)^j * ((1 / 2 : ℝ)^j) = (2 : ℝ)^j := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((4 : ℝ)^j * n₀) * (1 / 2 : ℝ)^j := by
      rw [hN, acc]
      field_simp
    _ = (2 : ℝ)^j * n₀ := by rw [← hH]; ring
    _ = _ := by
      rw [hN, hP, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), mul_assoc,
        Real.mul_self_sqrt h₀]

private theorem started_copy_acc_bound {C₀ δ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hδ : 0 < δ) :
    (phaseLen C₀ T j : ℝ) * acc δ j / δ ≤
      Real.sqrt (C₀ + 1) * (Real.sqrt (phaseLen C₀ T j : ℝ) * mainLog T ^ 2) := by
  have hL := mainLog_ge_one hT
  have hL₄ : 1 ≤ mainLog T ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hL 4
  have hn : (phaseLen C₀ T 0 : ℝ) ≤ (C₀ + 1) * mainLog T ^ 4 := by
    change ( (4 ^ (0 : ℕ) * ⌈C₀ * mainLog T ^ 4⌉₊ : ℕ) : ℝ) ≤ _
    simp only [pow_zero, one_mul]
    have h := Nat.ceil_lt_add_one (show 0 ≤ C₀ * mainLog T ^ 4 by positivity)
    linarith only [h, hL₄]
  have hs : Real.sqrt (phaseLen C₀ T 0 : ℝ) ≤ Real.sqrt (C₀ + 1) * mainLog T^2 := by
    apply (Real.sqrt_le_sqrt hn).trans_eq
    rw [Real.sqrt_mul (by linarith : 0 ≤ C₀ + 1), show mainLog T^4 = (mainLog T^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  rw [started_phaseLen_mul_acc_div hδ]
  calc
    _ ≤ Real.sqrt (phaseLen C₀ T j : ℝ) * (Real.sqrt (C₀ + 1) * mainLog T^2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private theorem started_copy_log_bound {C₀ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hj : j < startedPhaseCount C₀ T) :
    Real.log (2 * (phaseLen C₀ T j : ℝ)) ≤
      (1 + Real.log (startedRunFactor C₀)) * mainLog T := by
  have hn : (0 : ℝ) < phaseLen C₀ T j := Nat.cast_pos.mpr (started_phaseLen_pos hT hC₀)
  have hD : 1 ≤ startedRunFactor C₀ := by unfold startedRunFactor; linarith
  have hlogD : 0 ≤ Real.log (startedRunFactor C₀) := Real.log_nonneg hD
  have hL : 1 ≤ mainLog T := mainLog_ge_one hT
  have hnT : (phaseLen C₀ T j : ℝ) ≤ startedRunFactor C₀ * (T : ℝ) :=
    (Nat.cast_le.mpr (started_phase_bounds hT hC₀ hj).2).trans (startedRunMax_bound hT hC₀)
  have hpT : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    Real.log (2 * (phaseLen C₀ T j : ℝ)) ≤ Real.log (startedRunFactor C₀ * (2 * (T : ℝ))) :=
      Real.log_le_log (by positivity) (by nlinarith only [hnT])
    _ = Real.log (startedRunFactor C₀) + mainLog T := by
      rw [Real.log_mul (by linarith : startedRunFactor C₀ ≠ 0) (by positivity), mainLog]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hL hlogD
      nlinarith only [h]

private theorem started_copy_log_sq_bound {C₀ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hj : j < startedPhaseCount C₀ T) :
    Real.sqrt (phaseLen C₀ T j : ℝ) * Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2 ≤
      (1 + Real.log (startedRunFactor C₀)) ^ 2 *
        (Real.sqrt (phaseLen C₀ T j : ℝ) * mainLog T ^ 2) := by
  have hn : (1 : ℝ) ≤ phaseLen C₀ T j := by
    exact_mod_cast (show 1 ≤ phaseLen C₀ T j from started_phaseLen_pos hT hC₀)
  have hlog : 0 ≤ Real.log (2 * (phaseLen C₀ T j : ℝ)) :=
    Real.log_nonneg (by linarith only [hn])
  have hs := pow_le_pow_left₀ hlog (started_copy_log_bound hT hC₀ hj) 2
  calc
    _ ≤ Real.sqrt (phaseLen C₀ T j : ℝ) * ((1 + Real.log (startedRunFactor C₀)) * mainLog T) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private theorem started_copy_bound {C₀ δ : ℝ} {T j : ℕ} (hT : 2 ≤ T) (hC₀ : 0 < C₀)
    (hδ : 0 < δ) (hj : j < startedPhaseCount C₀ T) :
    (phaseLen C₀ T j : ℝ) * acc δ j / δ +
        Real.sqrt (phaseLen C₀ T j : ℝ) * Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2 ≤
      (Real.sqrt (C₀ + 1) + (1 + Real.log (startedRunFactor C₀)) ^ 2) *
        (Real.sqrt (phaseLen C₀ T j : ℝ) * mainLog T ^ 2) := by
  rw [add_mul]
  exact add_le_add (started_copy_acc_bound hT hC₀ hδ) (started_copy_log_sq_bound hT hC₀ hj)

/-- The common regret rate for the actual started copies. -/
private def startedRate (T : ℕ) : ℝ := (T : ℝ)^((3 : ℝ)/5) * mainLog T ^ ((7 : ℝ) / 2)

private theorem pow_log_le_started {T k : ℕ} (hT : 2 ≤ T) (hk : k ≤ 3) :
    mainLog T ^ k ≤ mainLog T ^ ((7 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  have h : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  exact Real.rpow_le_rpow_of_exponent_le (mainLog_ge_one hT) (by linarith only [h])

private theorem one_le_startedRate {T : ℕ} (hT : 2 ≤ T) : 1 ≤ startedRate T := by
  have hI := mainEta_inv_ge_one hT
  have hS := Real.one_le_sqrt.mpr hI
  have hLog := pow_log_le_started (k := 0) hT (by decide)
  simp only [pow_zero] at hLog
  rw [startedRate, ← main_inverse_rate hT]
  calc
    (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

private theorem started_eta_rate {T : ℕ} (hT : 2 ≤ T) : (T : ℝ) * mainEta T ≤ startedRate T := by
  have hL := pow_log_le_started (k := 0) hT (by decide)
  simp only [pow_zero] at hL
  rw [mainEta_mul_T hT, startedRate]
  exact le_mul_of_one_le_right (Real.rpow_nonneg (Nat.cast_nonneg T) _) hL

private theorem started_init_rate {T : ℕ} (hT : 2 ≤ T) :
    (gridK (mainEta T) : ℝ) * Real.log (T : ℝ)^2 ≤ 2 * startedRate T := by
  let I := 1 / mainEta T
  let L := mainLog T
  have hI : 1 ≤ I := mainEta_inv_ge_one hT
  have hI0 : 0 ≤ I := zero_le_one.trans hI
  have hs : 1 ≤ Real.sqrt I := Real.one_le_sqrt.mpr hI
  have hK : (gridK (mainEta T) : ℝ) ≤ 2 * I := by
    have h := Nat.ceil_lt_add_one hI0
    change (gridK (mainEta T) : ℝ) < I + 1 at h
    linarith only [h, hI]
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hlog : Real.log (T : ℝ) ≤ L :=
    Real.log_le_log (by linarith only [ht]) (by linarith only [ht])
  have hlog0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg ht
  have hL := pow_log_le_started (k := 2) hT (by decide)
  have hIS : I ≤ I * Real.sqrt I := le_mul_of_one_le_right hI0 hs
  calc
    _ ≤ (2 * I) * L^2 :=
      mul_le_mul hK (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)
    _ ≤ (2 * (I * Real.sqrt I)) * L^((7 : ℝ)/2) := by gcongr
    _ = 2 * startedRate T := by
      rw [startedRate, ← main_inverse_rate hT]
      change (2 * (I * Real.sqrt I)) * L^((7 : ℝ)/2) = 2 * (I * Real.sqrt I * L^((7 : ℝ)/2))
      ring

private theorem started_budget_bounds {C₀ Ccount δ : ℝ} {T N : ℕ}
    (hT : 2 ≤ T) (hC₀ : 0 < C₀) (hCount : 0 ≤ Ccount) (hδ₁ : δ ≤ 1)
    (hN : (N : ℝ) ≤ Ccount * Real.sqrt (δ / mainEta T) * mainLog T) :
    let J := startedPhaseCount C₀ T
    let M := numCopies C₀ T
    (N : ℝ) * J * (mainLog T / mainEta T) ≤ (3 * Ccount) * startedRate T ∧
    Real.sqrt (((N * J * M : ℕ) : ℝ) * ((T + startedRunMax C₀ T : ℕ) : ℝ)) * mainLog T^2 ≤
      Real.sqrt (3 * Ccount * (C₀ + 1) * (1 + startedRunFactor C₀)) * startedRate T ∧
    2 * (N : ℝ) * J ≤ (6 * Ccount) * startedRate T := by
  let I := 1 / mainEta T
  let L := mainLog T
  let s := Real.sqrt I
  let J := startedPhaseCount C₀ T
  let M := numCopies C₀ T
  let A := C₀ + 1
  let D := startedRunFactor C₀
  let B := startedRunMax C₀ T
  let Q := 3 * Ccount * A * (1 + D)
  have hL : 0 ≤ L := zero_le_one.trans (mainLog_ge_one hT)
  have hI : 1 ≤ I := mainEta_inv_ge_one hT
  have hI0 : 0 ≤ I := zero_le_one.trans hI
  have hs : 0 ≤ s := Real.sqrt_nonneg I
  have hp : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hD : 0 ≤ D := by dsimp [D, startedRunFactor]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hδ : δ / mainEta T ≤ I := div_le_div_of_nonneg_right hδ₁ (mainEta_pos hT).le
  have hN' : (N : ℝ) ≤ Ccount * s * L :=
    hN.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ) hCount) hL)
  have hJ : (J : ℝ) ≤ 3 * L := (startedPhaseCount_spec hT hC₀).2.2.2
  have hM : (M : ℝ) ≤ A * L := (main_numCopies_bound hT hC₀).2
  have hNJ : (N : ℝ) * J ≤ (3 * Ccount) * s * L^2 := by
    calc
      _ ≤ (Ccount * s * L) * (3 * L) :=
        mul_le_mul hN' hJ (Nat.cast_nonneg J) (by positivity)
      _ = _ := by ring
  have hBudget : I * s * L ^ ((7 : ℝ)/2) = startedRate T := by
    unfold startedRate
    rw [← main_inverse_rate hT]
  have hRunRate : Real.sqrt (s * T * L^3) * L^2 = startedRate T := by
    have ht : Real.sqrt (s * T) = (T : ℝ)^((3 : ℝ)/5) := by
      dsimp [s, I]
      rw [mainEta_inv hT]
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hp.le]
      conv_lhs => arg 1; arg 2; rw [← Real.rpow_one (T : ℝ)]
      rw [← Real.rpow_add hp, ← Real.rpow_mul hp.le]
      congr 1
      ring
    have hLr : Real.sqrt (L^3) * L^2 = L^((7 : ℝ)/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL, ← Real.rpow_natCast,
        ← Real.rpow_add (zero_lt_one.trans_le (mainLog_ge_one hT))]
      congr 1
      norm_num
    rw [Real.sqrt_mul (mul_nonneg hs hp.le), mul_assoc, ht, hLr]
    rfl
  change (N : ℝ) * J * (L / mainEta T) ≤ (3 * Ccount) * startedRate T ∧
    Real.sqrt (((N * J * M : ℕ) : ℝ) * ((T + B : ℕ) : ℝ)) * L^2 ≤
      Real.sqrt Q * startedRate T ∧
    2 * (N : ℝ) * J ≤ (6 * Ccount) * startedRate T
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_mul_one_div, ← hBudget]
    calc
      _ ≤ ((3 * Ccount) * s * L^2) * (L * I) := by gcongr
      _ = (3 * Ccount) * (I * s) * L^3 := by ring
      _ ≤ (3 * Ccount) * (I * s) * L^((7 : ℝ)/2) := by
        gcongr
        exact pow_log_le_started hT (by decide)
      _ = _ := by ring
  · push_cast
    have hCopies : (N : ℝ) * J * M ≤ (3 * Ccount * A) * s * L^3 := by
      calc
        _ ≤ ((3 * Ccount) * s * L^2) * (A * L) :=
          mul_le_mul hNJ hM (Nat.cast_nonneg M) (by positivity)
        _ = _ := by ring
    have hRounds : (T : ℝ) + B ≤ (1 + D) * T := by
      have h : (B : ℝ) ≤ D * T := startedRunMax_bound hT hC₀
      linarith only [h]
    have hR : (N : ℝ) * J * M * ((T : ℝ) + B) ≤ Q * (s * T * L^3) := by
      calc
        _ ≤ ((3 * Ccount * A) * s * L^3) * ((1 + D) * T) :=
          mul_le_mul hCopies hRounds (by positivity) (by positivity)
        _ = _ := by dsimp [Q]; ring
    calc
      _ ≤ Real.sqrt (Q * (s * T * L^3)) * L^2 :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hR) (sq_nonneg _)
      _ = _ := by rw [Real.sqrt_mul hQ, mul_assoc, hRunRate]
  · have hIS : s ≤ I * s := le_mul_of_one_le_left hs hI
    have hL' := pow_log_le_started (k := 2) hT (by decide)
    rw [← hBudget]
    calc
      _ = 2 * ((N : ℝ) * J) := by ring
      _ ≤ 2 * ((3 * Ccount) * s * L^2) := by gcongr
      _ = (6 * Ccount) * (s * L^2) := by ring
      _ ≤ (6 * Ccount) * ((I * s) * L^((7 : ℝ)/2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hIS hL' (sq_nonneg _) (mul_nonneg hI0 hs)) (by positivity)

end

end BilateralProfitRegular
end BundlePart044


section BundlePart045








noncomputable section

namespace BilateralProfitRegular

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

set_option maxHeartbeats 1000000

private def startedObservationRange : ℝ := 81000

private theorem startedObservationRange_pos : 0 < startedObservationRange := by
  norm_num [startedObservationRange]

private def startedC₂ : ℝ := mainOptimizerConstant startedObservationRange startedObservationRange_pos

private theorem startedC₂_pos : 0 < startedC₂ := mainOptimizerConstant_pos startedObservationRange_pos

private def startedC₀ : ℝ :=
  Classical.choose (lemma_6_6.1 startedObservationRange startedC₂ startedObservationRange_pos startedC₂_pos)

private theorem startedC₀_pos : 0 < startedC₀ :=
  (Classical.choose_spec
    (lemma_6_6.1 startedObservationRange startedC₂ startedObservationRange_pos startedC₂_pos)).1

private abbrev StartedPhase (T : ℕ) := Fin (startedPhaseCount startedC₀ T)

private abbrev StartedBatchHist (T : ℕ) (j : ℕ) :=
  Fin (numCopies startedC₀ T) → Factory.RunHistory (phaseLen startedC₀ T j)

private theorem startedCopies_pos {T : ℕ} (hT : 2 ≤ T) : 0 < numCopies startedC₀ T :=
  (main_numCopies_bound hT startedC₀_pos).1

private def startedCopyCostConstant : ℝ :=
  14040000 * Real.sqrt (startedC₀ + 1) +
    3888000 * startedC₂ * (1 + Real.log (startedRunFactor startedC₀)) ^ 2

private theorem startedCopyCostConstant_nonneg : 0 ≤ startedCopyCostConstant := by
  unfold startedCopyCostConstant
  have := startedC₂_pos
  positivity

private def startedBatchOptimizer {T : ℕ} (δ : ℝ) (c : Candidate) (j : StartedPhase T) :=
  mainOptimizerChoice startedObservationRange_pos δ c.region (phaseLen startedC₀ T j)

private theorem startedOptimizer_contract {T : ℕ} {δ : ℝ} {c : Candidate} (j : StartedPhase T)
    (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T) (hηδ : mainEta T < δ)
    (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6 * δ) (hc : c.Valid E δ)
    {z : ℝ × ℝ} (hz : z ∈ c.region) {ρ : ℝ} (hCal : CalibValid E (mainEta T) δ c z ρ) :
    let n := phaseLen startedC₀ T j
    let A := startedBatchOptimizer δ c j
    let L := fun x => 1 / auxProfit E (ρ * balance E z) x
    A.alg.QueriesIn c.region ∧
      ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn L c.region →
        ν.ValuesIn c.region (Icc 0 (startedObservationRange / δ)) →
        A.alg.regret ν A.seedLaw n L c.region ≤
          ENNReal.ofReal (startedC₂ / δ * Real.sqrt n * Real.log (2 * n) ^ 2) := by
  let A := startedBatchOptimizer δ c j
  have hfeas : MainOptimizerFeasible δ c.region (phaseLen startedC₀ T j) :=
    ⟨(mainEta_pos hT).trans hηδ, ⟨c.root, hc.2.2.2.1⟩,
      hc.2.1, hc.2.2.1, hc.1, started_phaseLen_pos hT startedC₀_pos⟩
  obtain ⟨hlam, hsafe⟩ := mainCalib_safe_auxProfit hE (mainEta_pos hT) hηδ hδopt hoptδ hc hz hCal
  exact ⟨(A.guarantee hfeas).1, (A.guarantee hfeas).2 E hE _ hlam hsafe⟩

/-- The independent optimizer copies run serially at the manuscript phase length. -/
private def startedBatch {T : ℕ} {δ : ℝ} {cs : List Candidate} (j : StartedPhase T)
    (i : Fin cs.length) : RandomProgram ((ℝ × ℝ) × ℝ) (StartedBatchHist T j) :=
  let c := cs.get i
  let n := phaseLen startedC₀ T j
  let m := numCopies startedC₀ T
  let A := startedBatchOptimizer δ c j
  let Seed := Fin m → A.Seed × (Fin n → Factory.ObservationSeed)
  let Input := ((ℝ × ℝ) × ℝ) × Seed
  { Seed := Seed
    seedSpace := inferInstance
    law := Factory.batchProgramSeedLaw A.seedLaw n m
    probability := by
      unfold Factory.batchProgramSeedLaw Factory.copyProgramSeedLaw
      infer_instance
    run s := (Factory.batchProgram A.alg c.est s.1.2 s.1.1 n m s.2).mapQuery mainClampPrice
    measurable_run := Program.measurableFamily_mapQuery measurable_mainClampPrice
      (Factory.measurable_batchProgram A.alg (fun _ : Input => c.est) (fun p => p.1.2) (fun p => p.1.1) n m
        Prod.snd measurable_const measurable_fst.snd measurable_fst.fst measurable_snd)
    legal s := Program.legal_mapQuery _ mainClampPrice_legal }

private theorem Program.minQueries_mapQuery {α : Type} {p : Program α} {k : ℕ}
    (hp : p.MinQueries k) (f : (ℝ × ℝ) → (ℝ × ℝ)) : (p.mapQuery f).MinQueries k := by
  intro h hh
  obtain ⟨x,hx⟩ := hp h hh
  exact ⟨f x, by simp [Program.mapQuery, hx]⟩

private theorem startedBatch_minQueries {T : ℕ} {δ : ℝ} {cs : List Candidate} (j : StartedPhase T)
    (i : Fin cs.length) (x : (ℝ × ℝ) × ℝ) (s : (startedBatch (δ := δ) j i).Seed) :
    ((startedBatch (δ := δ) j i).run (x,s)).MinQueries
      (numCopies startedC₀ T * phaseLen startedC₀ T j) := by
  let c := cs.get i
  let A := startedBatchOptimizer δ c j
  exact Program.minQueries_mapQuery
    (Factory.batchProgram_minQueries A.alg c.est x.2 x.1 _ _ s) mainClampPrice

private theorem startedBatch_failure {T : ℕ} {δ : ℝ} {cs : List Candidate} (j : StartedPhase T)
    (i : Fin cs.length) (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T)
    (hInit : InitGuarantee E (mainEta T) δ cs) (z : ℝ × ℝ) (hz : z ∈ (cs.get i).region)
    (ρ : ℝ) (hCal : CalibValid E (mainEta T) δ (cs.get i) z ρ) :
    let c := cs.get i
    let n := phaseLen startedC₀ T j
    let A := startedBatchOptimizer δ c j
    let ν := Factory.observationEnv c.est ρ z (P E)
    A.alg.multiExp ν A.seedLaw n (numCopies startedC₀ T)
      (fun hs => if RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs then 0 else 1) ≤
      ENNReal.ofReal (1 / (T : ℝ)) := by
  let c := cs.get i
  let A := startedBatchOptimizer δ c j
  let ν := Factory.observationEnv c.est ρ z (P E)
  have hc := hInit.2.2.2.1 c (List.get_mem cs i)
  obtain ⟨hlam, _⟩ := mainCalib_safe_auxProfit hE (mainEta_pos hT) hInit.1
    hInit.2.1 hInit.2.2.1 hc hz hCal
  have hj := started_phase_previous_le hT startedC₀_pos j.isLt
  have hEnv := Factory.observationEnv_contract E hE (mainEta T) δ (mainEta_pos hT)
    hInit.1 c hc ρ z hz hCal
  have hA := startedOptimizer_contract j E hE hT hInit.1 hInit.2.1 hInit.2.2.1 hc hz hCal
  have h := (Classical.choose_spec
    (lemma_6_6.1 startedObservationRange startedC₂ startedObservationRange_pos startedC₂_pos)).2
  exact h T (mainEta T) (mainEta_pos hT) (mainEta_lt_one hT) (mainEta_grid_le_T hT)
    E hE δ c hInit.1 hInit.2.1 hInit.2.2.1 hc (ρ * balance E z) hlam hCal.2 j hj
    A.Seed A.seedSpace A.seedLaw A.seedProbability A.alg hA.1 hA.2 ν hEnv.1 hEnv.2

private theorem startedBatch_copy_cost {T : ℕ} {δ : ℝ} {c : Candidate}
    (j : StartedPhase T) (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T)
    (hηδ : mainEta T < δ) (hδopt : δ ≤ muStar E) (hoptδ : muStar E < 6*δ)
    (hc : c.Valid E δ) (z : ℝ × ℝ) (hz : z ∈ c.region)
    (ρ : ℝ) (hCal : CalibValid E (mainEta T) δ c z ρ)
    (hgap : muStar E - auxProfit E (ρ * balance E z) z ≤ 65 * (mainEta T + acc δ j)) :
    let A := startedBatchOptimizer δ c j
    let n := phaseLen startedC₀ T j
    let ν := Factory.observationEnv c.est ρ z (P E)
    (∫⁻ ω, A.alg.go ν
      (fun x => (Factory.observationProc c.est ρ x z).expCost (P E) Factory.observationSeedLaw
        (fun y => muStar E - mu E y - 520 * mainEta T)) (fun _ _ => 0) n 0 ω Fin.elim0 ∂A.seedLaw) ≤
      ENNReal.ofReal (startedCopyCostConstant * Real.sqrt (n : ℝ) * mainLog T ^ 2) := by
  dsimp only
  let A := startedBatchOptimizer δ c j
  let n := phaseLen startedC₀ T j
  let ν := Factory.observationEnv c.est ρ z (P E)
  let L := fun x => 1 / auxProfit E (ρ * balance E z) x
  let ε := acc δ j
  let u := Real.sqrt (n : ℝ) * mainLog T ^ 2
  let a := 14040000 * Real.sqrt (startedC₀ + 1)
  let b := 3888000 * startedC₂ * (1 + Real.log (startedRunFactor startedC₀)) ^ 2
  have hη := mainEta_pos hT
  have hδ := hη.trans hηδ
  have hε : 0 ≤ ε := by unfold ε acc; positivity
  have hA := startedOptimizer_contract j E hE hT hηδ hδopt hoptδ hc hz hCal
  have hEnv := Factory.observationEnv_contract E hE (mainEta T) δ hη hηδ c hc ρ z hz hCal
  have hReg := hA.2 ν hEnv.1 hEnv.2
  have hraw := Factory.observation_run_excess_cost A.alg A.seedLaw E hE (mainEta T) δ ε hη
    hηδ hε hoptδ c hc hA.1 ρ z hz hCal hgap n
  have h1 : (n : ENNReal) * ENNReal.ofReal (14040000 * ε / δ) ≤ ENNReal.ofReal (a*u) := by
    rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (n : ℝ) * (14040000 * ε / δ) = 14040000 * ((n : ℝ) * ε / δ) := by ring
      _ ≤ 14040000 * (Real.sqrt (startedC₀ + 1) * u) :=
        mul_le_mul_of_nonneg_left (started_copy_acc_bound hT startedC₀_pos (j := j) hδ) (by norm_num)
      _ = _ := by unfold a; ring
  have h2 : ENNReal.ofReal (3888000 * δ) * A.alg.regret ν A.seedLaw n L c.region ≤
      ENNReal.ofReal (b*u) := by
    refine (mul_le_mul' le_rfl hReg).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3888000 * δ)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (3888000 * δ) * (startedC₂ / δ * Real.sqrt (n : ℝ) * Real.log (2 * n) ^ 2) =
          (3888000 * startedC₂) * (Real.sqrt (n : ℝ) * Real.log (2 * n) ^ 2) := by
        field_simp [hδ.ne']
      _ ≤ (3888000 * startedC₂) * ((1 + Real.log (startedRunFactor startedC₀))^2 * u) :=
        mul_le_mul_of_nonneg_left (started_copy_log_sq_bound hT startedC₀_pos j.isLt) (by
          have := startedC₂_pos
          positivity)
      _ = _ := by unfold b; ring
  refine hraw.trans ((add_le_add h1 h2).trans_eq ?_)
  have hb : 0 ≤ b := by
    unfold b
    have := startedC₂_pos
    positivity
  rw [← ENNReal.ofReal_add (by unfold a u; positivity) (by unfold u; positivity)]
  congr 1
  unfold a b u startedCopyCostConstant
  ring

/-- On a clean input, the shifted physical regret charges only started copies
and a continuation is available only when the whole batch can finish. -/
private theorem startedBatch_expected_le {T : ℕ} {δ : ℝ} {cs : List Candidate}
    (j : StartedPhase T) (i : Fin cs.length) (E : Environment) (hE : RegularUnit E)
    (hT : 2 ≤ T) (hInit : InitGuarantee E (mainEta T) δ cs)
    (z : ℝ × ℝ) (hz : z ∈ (cs.get i).region)
    (ρ : ℝ) (hCal : CalibValid E (mainEta T) δ (cs.get i) z ρ)
    (hgap : muStar E - auxProfit E (ρ * balance E z) z ≤ 65 * (mainEta T + acc δ j))
    (N : ℕ) (hNT : N ≤ T) (finish : ℕ → StartedBatchHist T j → ENNReal)
    (hFinish : ∀ r, Measurable (finish r))
    (htime : ∀ r ≤ N, ∀ hs, finish r hs ≤ (r : ENNReal)) (R : ENNReal)
    (hGood : ∀ r ≤ N - numCopies startedC₀ T * phaseLen startedC₀ T j, ∀ hs,
      RefineGood E (ρ * balance E z) δ (acc δ j) (cs.get i).region hs → finish r hs ≤ R) :
    let n := phaseLen startedC₀ T j
    let m := numCopies startedC₀ T
    (startedBatch (δ := δ) j i).expectedCost E
        (fun y => ENNReal.ofReal (muStar E - mu E y - 520 * mainEta T)) (z,ρ) N finish ≤
      ((min m (N ⌈/⌉ n) : ℕ) : ENNReal) *
        ENNReal.ofReal (startedCopyCostConstant * Real.sqrt (n : ℝ) * mainLog T ^ 2) +
      if m*n ≤ N then R + 1 else 0 := by
  dsimp only
  let c := cs.get i
  let n := phaseLen startedC₀ T j
  let m := numCopies startedC₀ T
  let A := startedBatchOptimizer δ c j
  let ν := Factory.observationEnv c.est ρ z (P E)
  let g := fun y => muStar E - mu E y - 520 * mainEta T
  let good : Set (StartedBatchHist T j) :=
    {hs | RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs}
  have hc : c.Valid E δ := hInit.2.2.2.1 c (List.get_mem cs i)
  have hη := mainEta_pos hT
  have hQ : A.alg.QueriesIn c.region :=
    (startedOptimizer_contract j E hE hT hInit.1 hInit.2.1 hInit.2.2.1 hc hz hCal).1
  have hlam := (mainCalib_safe_auxProfit hE hη hInit.1 hInit.2.1 hInit.2.2.1 hc hz hCal).1
  have hMeasGood : MeasurableSet good := measurableSet_refineGood hE hlam hc.2.1 hc.1
  have hbad : A.alg.multiExp ν A.seedLaw n m
      (goodᶜ.indicator (fun _ => (1 : ENNReal))) ≤ ENNReal.ofReal (1 / (T : ℝ)) := by
    have heq : goodᶜ.indicator (fun _ => (1 : ENNReal)) =
        fun hs => if RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs then 0 else 1 := by
      funext hs
      by_cases h : hs ∈ good
      · simp [Set.indicator_of_notMem (show hs ∉ goodᶜ by simpa using h),
          show RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs from h]
      · simp [Set.indicator_of_mem (show hs ∈ goodᶜ from h),
          show ¬ RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs from h]
    rw [heq]
    exact startedBatch_failure j i E hE hT hInit z hz ρ hCal
  have hS (x : ℝ × ℝ) (hx : x ∈ c.region) :
      ({z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)) ⊆ triT := by
    have hcross := hc.2.2.2.2.2.1 x hx z hz
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · have hi := hc.1 hz
      exact ⟨hi.1.le, hi.2.1.le, hi.2.2.le⟩
    · exact hcross.1
    · exact hcross.2.1
  have hclamp (s : Fin m → A.Seed × (Fin n → Factory.ObservationSeed)) :
      Program.mapQuery mainClampPrice (Factory.batchProgram A.alg c.est ρ z n m s) =
        Factory.batchProgram A.alg c.est ρ z n m s :=
    Factory.batchProgram_mapQuery_eq A.alg c.est ρ z n m s hQ hS
      (fun _ hx => mainClampPrice_eq hx)
  have hp := measurable_P E hE.1
  have hg : Measurable g :=
    (measurable_const.sub (Factory.measurable_expectedProfit E hE.1)).sub_const _
  have hCost := startedBatch_copy_cost j E hE hT hInit.1 hInit.2.1 hInit.2.2.1 hc z hz ρ hCal hgap
  change (∫⁻ s, Program.value (P E) (fun y => ENNReal.ofReal (g y))
      (Program.mapQuery mainClampPrice (Factory.batchProgram A.alg c.est ρ z n m s)) N finish
        ∂Factory.batchProgramSeedLaw A.seedLaw n m) ≤ _
  simp_rw [hclamp]
  exact Factory.batchProgram_prefix_le_started_good A.alg A.seedLaw c.est ρ z hp hg
    (onUnit_facts E hE.1).1 n (started_phaseLen_pos hT startedC₀_pos) m N T hNT (by omega)
    _ hCost finish hFinish R good hMeasGood hbad
    (fun r hr => htime r (hr.trans (Nat.sub_le _ _))) hGood

end BilateralProfitRegular
end
end BundlePart045


section BundlePart046


namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

private abbrev MainScheduleHistory (N : ℕ) := ℕ → MainPhaseReport N

/-- The unwritten slots are immaterial until their phase and index are processed. -/
private def mainEmptyScheduleHistory (N : ℕ) : MainScheduleHistory N :=
  fun _ _ => (1, (0, 0), 0)

/-- Update one candidate's report, leaving all other reports unchanged. -/
private def mainWriteReport {N : ℕ} (H : MainScheduleHistory N) (j : ℕ) (i : Fin N)
    (R : MainRefinementEntry) : MainScheduleHistory N :=
  Function.update H j (Function.update (H j) i R)

@[simp]
private theorem mainWriteReport_here {N : ℕ} (H : MainScheduleHistory N) (j : ℕ) (i : Fin N)
    (R : MainRefinementEntry) : mainWriteReport H j i R j i = R := by
  simp [mainWriteReport]

private theorem mainWriteReport_other_phase {N : ℕ} (H : MainScheduleHistory N) {j k : ℕ} (i : Fin N)
    (R : MainRefinementEntry) (hk : k ≠ j) : mainWriteReport H j i R k = H k := by
  simp [mainWriteReport, Function.update_of_ne hk]

private theorem mainWriteReport_other_index {N : ℕ} (H : MainScheduleHistory N) (j : ℕ) {i l : Fin N}
    (R : MainRefinementEntry) (hl : l ≠ i) : mainWriteReport H j i R j l = H j l := by
  simp [mainWriteReport, Function.update_of_ne hl]

private theorem measurable_mainWriteReport {N : ℕ} (j : ℕ) (i : Fin N) :
    Measurable (fun p : MainScheduleHistory N × MainRefinementEntry => mainWriteReport p.1 j i p.2) := by
  have hi0 : Measurable (fun p : MainPhaseReport N × MainRefinementEntry =>
      Function.update p.1 i p.2) := measurable_update'
  have hj0 : Measurable (fun p : MainScheduleHistory N × MainPhaseReport N =>
      Function.update p.1 j p.2) := measurable_update'
  have hm : Measurable (fun p : MainScheduleHistory N × MainRefinementEntry => (p.1 j, p.2)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
  have hi : Measurable (fun p : MainScheduleHistory N × MainRefinementEntry =>
      Function.update (p.1 j) i p.2) := hi0.comp hm
  exact hj0.comp (measurable_fst.prodMk hi)

/-- The part of a clean phase report associated with one active candidate. -/
private def MainPhaseEntryClean (E : Environment) (η δ : ℝ) (j : ℕ) (c : Candidate)
    (z : ℝ × ℝ) (R : MainRefinementEntry) : Prop :=
  CalibValid E η δ c z R.1 ∧ R.2.1 ∈ c.region ∧
    (∀ x ∈ c.region, auxProfit E (R.1 * balance E z) x - acc δ j ≤ R.2.2) ∧
    R.2.2 ≤ auxProfit E (R.1 * balance E z) R.2.1 + acc δ j

/-- All earlier phases are clean and the first `m` entries of the current phase
have clean reports whenever their candidate is active. -/
private def MainPartialClean (E : Environment) (η δ : ℝ) (cs : List Candidate) (j m : ℕ)
    (H : MainScheduleHistory cs.length) : Prop :=
  MainPhaseClean E η δ cs H j ∧
    ∀ i ∈ (mainPhaseTimeline η δ cs H j).1, i.val < m →
      MainPhaseEntryClean E η δ j (cs.get i) ((mainPhaseTimeline η δ cs H j).2 i) (H j i)

private theorem mainPartialClean_start (E : Environment) (η δ : ℝ) (cs : List Candidate)
    (H : MainScheduleHistory cs.length) : MainPartialClean E η δ cs 0 0 H := by
  refine ⟨fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
  intro i _ h
  exact (Nat.not_lt_zero i.val h).elim

private theorem mainPartialClean_zero_iff {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {H : MainScheduleHistory cs.length} :
    MainPartialClean E η δ cs j 0 H ↔ MainPhaseClean E η δ cs H j := by
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  intro i _ hi
  exact (Nat.not_lt_zero i.val hi).elim

private theorem mainPartialClean_finish {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {H : MainScheduleHistory cs.length} :
    MainPartialClean E η δ cs j cs.length H ↔ MainPhaseClean E η δ cs H (j + 1) := by
  rw [mainPhaseClean_succ]
  exact ⟨fun h => ⟨h.1, fun i hi => h.2 i hi i.isLt⟩,
    fun h => ⟨h.1, fun i hi _ => h.2 i hi⟩⟩

private theorem mainPartialClean_next {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {H : MainScheduleHistory cs.length} (h : MainPartialClean E η δ cs j cs.length H) :
    MainPartialClean E η δ cs (j + 1) 0 H :=
  mainPartialClean_zero_iff.mpr (mainPartialClean_finish.mp h)

private theorem mainPhaseClean_congr_prefix {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {H H' : MainScheduleHistory cs.length} (h : ∀ k < j, H k = H' k) :
    MainPhaseClean E η δ cs H j ↔ MainPhaseClean E η δ cs H' j := by
  have he (k : ℕ) (hk : k < j) : mainPhaseTimeline η δ cs H k = mainPhaseTimeline η δ cs H' k :=
    mainPhaseTimeline_congr (fun l hl => h l (hl.trans hk))
  constructor
  · intro hClean k hk
    rw [← he k hk, ← h k hk]
    exact hClean k hk
  · intro hClean k hk
    rw [he k hk, h k hk]
    exact hClean k hk

private theorem mainWriteReport_same_state {η δ : ℝ} {cs : List Candidate}
    (H : MainScheduleHistory cs.length) (j : ℕ) (i : Fin cs.length)
    (R : MainRefinementEntry) :
    mainPhaseTimeline η δ cs (mainWriteReport H j i R) j =
      mainPhaseTimeline η δ cs H j :=
  mainPhaseTimeline_congr (fun _ hk => mainWriteReport_other_phase H i R hk.ne)

private theorem mainPartialClean_write {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {i : Fin cs.length} {H : MainScheduleHistory cs.length} {R : MainRefinementEntry}
    (h : MainPartialClean E η δ cs j i.val H)
    (hEntry : i ∈ (mainPhaseTimeline η δ cs H j).1 →
      MainPhaseEntryClean E η δ j (cs.get i) ((mainPhaseTimeline η δ cs H j).2 i) R) :
    MainPartialClean E η δ cs j (i.val + 1) (mainWriteReport H j i R) := by
  refine ⟨?_, ?_⟩
  · exact (mainPhaseClean_congr_prefix (fun k hk =>
      (mainWriteReport_other_phase H i R hk.ne).symm)).mp h.1
  · intro l hl hlt
    rw [mainWriteReport_same_state] at hl ⊢
    by_cases he : l = i
    · subst l
      rw [mainWriteReport_here]
      exact hEntry hl
    · rw [mainWriteReport_other_index H j R he]
      have hh : l.val ≠ i.val := fun he' => he (Fin.ext he')
      exact h.2 l hl (by omega)

private theorem mainPartialClean_skip {E : Environment} {η δ : ℝ} {cs : List Candidate}
    {j : ℕ} {i : Fin cs.length} {H : MainScheduleHistory cs.length}
    (h : MainPartialClean E η δ cs j i.val H)
    (hi : i ∉ (mainPhaseTimeline η δ cs H j).1) :
    MainPartialClean E η δ cs j (i.val + 1) H := by
  refine ⟨h.1, fun l hl hlt => h.2 l hl ?_⟩
  have hh : l.val ≠ i.val := fun he => hi ((Fin.ext he) ▸ hl)
  omega

private theorem mainPhaseEntryClean_of_refineGood {M n : ℕ} {E : Environment} {η δ ρ : ℝ}
    {j : ℕ} {c : Candidate} {z : ℝ × ℝ} {hs : MainRefineTrajs M n}
    (hM : 0 < M) (hCalib : CalibValid E η δ c z ρ)
    (hGood : RefineGood E (ρ * balance E z) δ (acc δ j) c.region hs) :
    MainPhaseEntryClean E η δ j c z (mainRefinementReport δ ρ hs) := by
  unfold MainPhaseEntryClean
  rw [mainRefinementReport_rho]
  exact ⟨hCalib, mainRefinementReport_good hM hGood⟩

end BilateralProfitRegular
end BundlePart046


section BundlePart047



namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

namespace RandomProgram

variable {H : Type} [MeasurableSpace H]

/-- Run the second state transition on the state returned by the first transition. -/
private noncomputable def thenState (p q : RandomProgram H H) : RandomProgram H H :=
  p.bind (q.compInput Prod.snd measurable_snd)

private theorem bound_thenState (p q : RandomProgram H H) (E : Environment) (hE : OnUnit E) (T : ℕ)
    {pre middle post : H → Prop} {c₁ c₂ : ENNReal}
    (hp : p.Bound E T pre (fun _ h => middle h) c₁)
    (hq : q.Bound E T middle (fun _ h => post h) c₂) :
    (p.thenState q).Bound E T pre (fun _ h => post h) (c₁ + c₂) := by
  have hk : (q.compInput Prod.snd measurable_snd).Bound E T
      (fun p : H × H => pre p.1 ∧ middle p.2) (fun _ h => post h) c₂ := by
    intro p hp n hn f hf ht R hR
    rw [expected_compInput]
    exact hq p.2 hp.2 n hn f hf ht R hR
  exact bound_bind p _ E hE T hp hk (fun _ _ _ _ _ h => h)

end RandomProgram

section Schedule

variable {H : Type} [MeasurableSpace H] {N J : ℕ}

/-- Run candidate jobs in increasing index order through a specified prefix of a phase. -/
private noncomputable def mainSchedulePhase (runJob : Fin N → RandomProgram H H) :
    (m : ℕ) → m ≤ N → RandomProgram H H
  | 0, _ => RandomProgram.pure id measurable_id
  | m + 1, hm =>
    (mainSchedulePhase runJob m (Nat.le_of_succ_le hm)).thenState
      (runJob ⟨m, Nat.lt_of_succ_le hm⟩)

/-- Run all candidate jobs in each successive phase through a specified phase prefix. -/
private noncomputable def mainSchedulePrefix (runJob : Fin J → Fin N → RandomProgram H H) :
    (j : ℕ) → j ≤ J → RandomProgram H H
  | 0, _ => RandomProgram.pure id measurable_id
  | j + 1, hj =>
    (mainSchedulePrefix runJob j (Nat.le_of_succ_le hj)).thenState
      (mainSchedulePhase (runJob ⟨j, Nat.lt_of_succ_le hj⟩) N le_rfl)

/-- Run the finite schedule, with phase indices outside candidate indices. -/
private noncomputable def mainSchedule (runJob : Fin J → Fin N → RandomProgram H H) :
    RandomProgram H H :=
  mainSchedulePrefix runJob J le_rfl

private theorem mainSchedulePhase_bound (runJob : Fin N → RandomProgram H H)
    (E : Environment) (hE : OnUnit E) (T : ℕ) (C : ENNReal) (clean : ℕ → H → Prop)
    (hJob : ∀ i : Fin N, (runJob i).Bound E T (clean i.val)
      (fun _ h => clean (i.val + 1) h) C)
    (m : ℕ) (hm : m ≤ N) :
    (mainSchedulePhase runJob m hm).Bound E T (clean 0) (fun _ h => clean m h)
      ((m : ENNReal) * C) := by
  induction m with
  | zero =>
    intro h hh n hn f hf ht R hR
    simpa [mainSchedulePhase] using hR n le_rfl h hh
  | succ m ih =>
    let i : Fin N := ⟨m, Nat.lt_of_succ_le hm⟩
    have h := RandomProgram.bound_thenState
      (mainSchedulePhase runJob m (Nat.le_of_succ_le hm)) (runJob i) E hE T
      (ih (Nat.le_of_succ_le hm)) (hJob i)
    simpa only [mainSchedulePhase, i, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

private theorem mainSchedulePrefix_bound (runJob : Fin J → Fin N → RandomProgram H H)
    (E : Environment) (hE : OnUnit E) (T : ℕ) (C : ENNReal) (clean : ℕ → ℕ → H → Prop)
    (hJob : ∀ (j : Fin J) (i : Fin N), (runJob j i).Bound E T (clean j.val i.val)
      (fun _ h => clean j.val (i.val + 1) h) C)
    (hNext : ∀ j < J, ∀ h, clean j N h → clean (j + 1) 0 h)
    (j : ℕ) (hj : j ≤ J) :
    (mainSchedulePrefix runJob j hj).Bound E T (clean 0 0) (fun _ h => clean j 0 h)
      ((↑(j * N) : ENNReal) * C) := by
  induction j with
  | zero =>
    intro h hh n hn f hf ht R hR
    simpa [mainSchedulePrefix] using hR n le_rfl h hh
  | succ j ih =>
    let jp : Fin J := ⟨j, Nat.lt_of_succ_le hj⟩
    have hphase := mainSchedulePhase_bound (runJob jp) E hE T C (clean j) (hJob jp) N le_rfl
    have hphase' : (mainSchedulePhase (runJob jp) N le_rfl).Bound E T (clean j 0)
        (fun _ h => clean (j + 1) 0 h) ((N : ENNReal) * C) := by
      intro h hh n hn f hf ht R hR
      exact hphase h hh n hn f hf ht R
        (fun m hm h' hh' => hR m hm h' (hNext j jp.isLt h' hh'))
    have h := RandomProgram.bound_thenState
      (mainSchedulePrefix runJob j (Nat.le_of_succ_le hj))
      (mainSchedulePhase (runJob jp) N le_rfl) E hE T
      (ih (Nat.le_of_succ_le hj)) hphase'
    simpa only [mainSchedulePrefix, jp, Nat.add_mul, one_mul, Nat.cast_add, add_mul] using h

end Schedule

/-- Assuming the checked one-job transition, the deterministic schedule composes its
budget at most once for each phase and candidate index. -/
private theorem mainSchedule_clean_bound {E : Environment} {η δ : ℝ} {cs : List Candidate} {J T : ℕ}
    (runJob : Fin J → Fin cs.length →
      RandomProgram (MainScheduleHistory cs.length) (MainScheduleHistory cs.length))
    (hE : OnUnit E) (C : ENNReal)
    (hJob : ∀ (j : Fin J) (i : Fin cs.length),
      (runJob j i).Bound E T (MainPartialClean E η δ cs j.val i.val)
        (fun _ h => MainPartialClean E η δ cs j.val (i.val + 1) h) C) :
    (mainSchedule runJob).Bound E T (fun _ => True)
      (fun _ h => MainPhaseClean E η δ cs h J) ((↑(J * cs.length) : ENNReal) * C) := by
  have hb := mainSchedulePrefix_bound runJob E hE T C (MainPartialClean E η δ cs) hJob
    (fun _ _ _ h => mainPartialClean_next h) J le_rfl
  intro h _ n hn f hf ht R hR
  exact hb h (mainPartialClean_start E η δ cs h) n hn f hf ht R
    (fun m hm h' hh' => hR m hm h' hh'.1)

end BilateralProfitRegular
end BundlePart047


section BundlePart048




namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

noncomputable section

/-- The continuation has `k` remaining candidate jobs and `r` remaining physical rounds. -/
private def startedBudget (M B : ℕ) (a cost : ℝ≥0∞) (k r : ℕ) : ℝ≥0∞ :=
  a * ENNReal.ofReal (Real.sqrt (((k * M : ℕ) : ℝ) * ((r + B : ℕ) : ℝ))) +
    (k : ℝ≥0∞) * cost

@[simp]
private theorem startedBudget_zero (M B : ℕ) (a cost : ℝ≥0∞) (r : ℕ) :
    startedBudget M B a cost 0 r = 0 := by
  simp [startedBudget]

private theorem startedBudget_mono {M B : ℕ} {a cost : ℝ≥0∞} {k k' r r' : ℕ}
    (hk : k ≤ k') (hr : r ≤ r') :
    startedBudget M B a cost k r ≤ startedBudget M B a cost k' r' := by
  unfold startedBudget
  have h : (((k * M : ℕ) : ℝ) * ((r + B : ℕ) : ℝ)) ≤
      (((k' * M : ℕ) : ℝ) * ((r' + B : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_right M hk) (Nat.add_le_add_right hr B)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt h)) bot_le)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) bot_le)

namespace RandomProgram

variable {H : Type} [MeasurableSpace H]

/-- A capped program preserves a budget depending on the jobs and physical time left. -/
private def StartedBound (p : RandomProgram H H) (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞)
    (T M B : ℕ) (a cost : ℝ≥0∞) (pre post : H → Prop) (slots : ℕ) : Prop :=
  ∀ x, pre x → ∀ n ≤ T, ∀ (finish : ℕ → H → ℝ≥0∞),
    (∀ m, Measurable (finish m)) →
    (∀ m ≤ n, ∀ y, finish m y ≤ (m : ℝ≥0∞)) →
    ∀ (k : ℕ) (R : ℝ≥0∞),
    (∀ m ≤ n, ∀ y, post y → finish m y ≤ startedBudget M B a cost k m + R) →
    p.expectedCost E g x n finish ≤ startedBudget M B a cost (k + slots) n + R

private theorem startedBound_mono {p : RandomProgram H H} {E : Environment} {g : (ℝ × ℝ) → ℝ≥0∞}
    {T M B s s' : ℕ} {a cost : ℝ≥0∞} {pre post pre' post' : H → Prop}
    (hp : p.StartedBound E g T M B a cost pre post s)
    (hpre : ∀ x, pre' x → pre x) (hpost : ∀ y, post y → post' y) (hs : s ≤ s') :
    p.StartedBound E g T M B a cost pre' post' s' := by
  intro x hx n hn finish hmeas htime k R hfinish
  exact (hp x (hpre x hx) n hn finish hmeas htime k R
    (fun m hm y hy => hfinish m hm y (hpost y hy))).trans
      (add_le_add (startedBudget_mono (Nat.add_le_add_left hs k) le_rfl) le_rfl)

private theorem startedBound_thenState (p q : RandomProgram H H) (E : Environment) (hE : OnUnit E)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ y ∈ triT, g y ≤ 1)
    (T M B : ℕ) (a cost : ℝ≥0∞) {pre middle post : H → Prop} {s₁ s₂ : ℕ}
    (hp : p.StartedBound E g T M B a cost pre middle s₁)
    (hq : q.StartedBound E g T M B a cost middle post s₂) :
    (p.thenState q).StartedBound E g T M B a cost pre post (s₁ + s₂) := by
  intro x hx n hn finish hmeas htime k R hfinish
  rw [thenState, expectedCost_bind p _ E hE g hg x n hmeas]
  simp_rw [expectedCost_compInput]
  have h := hp x hx n hn (fun m y => q.expectedCost E g y m finish)
    (fun m => measurable_expectedCost q E hE g hg m hmeas)
    (fun m hm y => by
      have hqtime := expectedCost_le_time q E hE g y m 1 hg1
        (fun m' hm' y' => by simpa using htime m' (hm'.trans hm) y')
      simpa using hqtime)
    (k + s₂) R
    (fun m hm y hy => hq y hy m (hm.trans hn) finish hmeas
      (fun m' hm' y' => htime m' (hm'.trans hm) y') k R
      (fun m' hm' y' hy' => hfinish m' (hm'.trans hm) y' hy'))
  simpa only [show k + s₂ + s₁ = k + (s₁ + s₂) by omega] using h

end RandomProgram

section Schedule

variable {H : Type} [MeasurableSpace H] {N J : ℕ}

private theorem mainSchedulePhase_started_bound (runJob : Fin N → RandomProgram H H)
    (E : Environment) (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hg : Measurable g) (hg1 : ∀ y ∈ triT, g y ≤ 1)
    (T M B : ℕ) (a cost : ℝ≥0∞) (clean : ℕ → H → Prop)
    (hJob : ∀ i : Fin N, (runJob i).StartedBound E g T M B a cost (clean i.val)
      (clean (i.val + 1)) 1) (m : ℕ) (hm : m ≤ N) :
    (mainSchedulePhase runJob m hm).StartedBound E g T M B a cost (clean 0) (clean m) m := by
  induction m with
  | zero =>
    intro h hh n hn f hf ht k R hR
    simpa [mainSchedulePhase] using hR n le_rfl h hh
  | succ m ih =>
    let i : Fin N := ⟨m, Nat.lt_of_succ_le hm⟩
    exact RandomProgram.startedBound_thenState
      (mainSchedulePhase runJob m (Nat.le_of_succ_le hm)) (runJob i) E hE g hg hg1 T M B a cost
      (ih (Nat.le_of_succ_le hm)) (hJob i)

private theorem mainSchedulePrefix_started_bound (runJob : Fin J → Fin N → RandomProgram H H)
    (E : Environment) (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hg : Measurable g) (hg1 : ∀ y ∈ triT, g y ≤ 1)
    (T M B : ℕ) (a cost : ℝ≥0∞) (clean : ℕ → ℕ → H → Prop)
    (hJob : ∀ (j : Fin J) (i : Fin N),
      (runJob j i).StartedBound E g T M B a cost (clean j.val i.val)
        (clean j.val (i.val + 1)) 1)
    (hNext : ∀ j < J, ∀ h, clean j N h → clean (j + 1) 0 h)
    (j : ℕ) (hj : j ≤ J) :
    (mainSchedulePrefix runJob j hj).StartedBound E g T M B a cost (clean 0 0) (clean j 0)
      (j * N) := by
  induction j with
  | zero =>
    intro h hh n hn f hf ht k R hR
    simpa [mainSchedulePrefix] using hR n le_rfl h hh
  | succ j ih =>
    let jp : Fin J := ⟨j, Nat.lt_of_succ_le hj⟩
    have hphase := mainSchedulePhase_started_bound (runJob jp) E hE g hg hg1 T M B a cost
      (clean j) (hJob jp) N le_rfl
    have hphase' : (mainSchedulePhase (runJob jp) N le_rfl).StartedBound E g T M B a cost
        (clean j 0) (clean (j + 1) 0) N :=
      RandomProgram.startedBound_mono hphase (fun _ h => h) (hNext j jp.isLt) le_rfl
    have h := RandomProgram.startedBound_thenState
      (mainSchedulePrefix runJob j (Nat.le_of_succ_le hj))
      (mainSchedulePhase (runJob jp) N le_rfl) E hE g hg hg1 T M B a cost
      (ih (Nat.le_of_succ_le hj)) hphase'
    simpa only [mainSchedulePrefix, jp, Nat.add_mul, one_mul] using h

end Schedule

private theorem mainSchedulePrefix_started_clean_bound {E : Environment} {η δ : ℝ}
    {cs : List Candidate} {J T M B : ℕ}
    (runJob : Fin J → Fin cs.length →
      RandomProgram (MainScheduleHistory cs.length) (MainScheduleHistory cs.length))
    (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hg1 : ∀ y ∈ triT, g y ≤ 1) (a cost : ℝ≥0∞)
    (hJob : ∀ (j : Fin J) (i : Fin cs.length), (runJob j i).StartedBound E g T M B a cost
      (MainPartialClean E η δ cs j.val i.val) (MainPartialClean E η δ cs j.val (i.val + 1)) 1)
    (j : ℕ) (hj : j ≤ J) :
    (mainSchedulePrefix runJob j hj).StartedBound E g T M B a cost (fun _ => True)
      (fun h => MainPhaseClean E η δ cs h j) (j * cs.length) := by
  have hb := mainSchedulePrefix_started_bound runJob E hE g hg hg1 T M B a cost
    (MainPartialClean E η δ cs) hJob (fun _ _ _ h => mainPartialClean_next h) j hj
  exact RandomProgram.startedBound_mono hb (fun x _ => mainPartialClean_start E η δ cs x)
    (fun _ h => h.1) le_rfl

/-- The optimizer budget after the calibration cost has been charged. -/
private def startedAfterCalibration (M B : ℕ) (a cost : ℝ≥0∞) (k r : ℕ) (R : ℝ≥0∞) : ℝ≥0∞ :=
  a * ENNReal.ofReal (Real.sqrt ((((k+1) * M : ℕ) : ℝ) * ((r+B : ℕ) : ℝ))) +
    (k : ℝ≥0∞) * cost + R + 1

private theorem startedAfterCalibration_mono {M B k r r' : ℕ} {a cost R : ℝ≥0∞}
    (hr : r ≤ r') :
    startedAfterCalibration M B a cost k r R ≤ startedAfterCalibration M B a cost k r' R := by
  unfold startedAfterCalibration
  have h : ((((k+1) * M : ℕ) : ℝ) * ((r+B : ℕ) : ℝ)) ≤
      ((((k+1) * M : ℕ) : ℝ) * ((r'+B : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul_left ((k+1)*M) (Nat.add_le_add_right hr B)
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt h)) bot_le)
      le_rfl) le_rfl) le_rfl

private theorem started_batch_cost_aggregate (M B k r n : ℕ) (hn : 0 < n) (hB : n ≤ B)
    (a cost R : ℝ≥0∞) :
    ((min M (r ⌈/⌉ n) : ℕ) : ℝ≥0∞) * (a * ENNReal.ofReal (Real.sqrt n)) +
      (if M*n ≤ r then startedBudget M B a cost k (r-M*n) + R + 1 else 0) ≤
        startedAfterCalibration M B a cost k r R := by
  classical
  let s := min M (r ⌈/⌉ n)
  have cast_mul_sqrt (u : ℕ) :
      (u : ℝ≥0∞) * (a * ENNReal.ofReal (Real.sqrt n)) =
        a * ENNReal.ofReal ((u : ℝ) * Real.sqrt n) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg u), ENNReal.ofReal_natCast]
    ac_rfl
  change (s : ℝ≥0∞) * (a * ENNReal.ofReal (Real.sqrt n)) + _ ≤ _
  by_cases hr : M * n ≤ r
  · have hceil : r ≤ n * (r ⌈/⌉ n) := (ceilDiv_le_iff_le_mul hn).mp le_rfl
    have hM : M ≤ r ⌈/⌉ n := by
      by_contra! h
      have hlt := Nat.mul_lt_mul_of_pos_left h hn
      rw [Nat.mul_comm n M] at hlt
      omega
    have hs : s = M := min_eq_left hM
    have hstep := started_potential_step
      (K := (k+1)*M) (s := M) (k := k*M) (r := r) (r' := r-M*n) (n := n) (B := B)
      (by simp [Nat.add_mul, Nat.add_comm]) (by omega)
    have hstep' : (M : ℝ) * Real.sqrt n +
        Real.sqrt (((k*M : ℕ) : ℝ) * (((r - M*n : ℕ) : ℝ) + B)) ≤
          Real.sqrt ((((k+1)*M : ℕ) : ℝ) * (((r+B : ℕ) : ℝ))) := by
      exact_mod_cast hstep
    rw [hs, if_pos hr, cast_mul_sqrt, startedBudget, startedAfterCalibration]
    calc
      _ = a * ENNReal.ofReal ((M : ℝ) * Real.sqrt n +
            Real.sqrt (((k*M : ℕ) : ℝ) * ((r-M*n+B : ℕ) : ℝ))) +
              ((k : ℝ≥0∞) * cost) + R + 1 := by
          rw [ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _), mul_add]
          ac_rfl
      _ ≤ _ := by
        have hstep'' : (M : ℝ) * Real.sqrt n +
            Real.sqrt (((k*M : ℕ) : ℝ) * ((r-M*n+B : ℕ) : ℝ)) ≤
              Real.sqrt ((((k+1)*M : ℕ) : ℝ) * ((r+B : ℕ) : ℝ)) := by
          simpa only [Nat.cast_add] using hstep'
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hstep'') bot_le) le_rfl) le_rfl) le_rfl
  · have hs : s ≤ (k+1)*M := (min_le_left M _).trans (by simp [Nat.add_mul])
    have hcap : s*n ≤ r+B := by
      calc
        s*n ≤ (r ⌈/⌉ n)*n := Nat.mul_le_mul_right n (min_le_right M _)
        _ ≤ r+n-1 := by
          rw [Nat.ceilDiv_eq_add_pred_div]
          exact Nat.div_mul_le_self _ _
        _ ≤ r+B := by omega
    have hlast := started_potential_last (K := (k+1)*M) hs hcap
    rw [if_neg hr, add_zero, cast_mul_sqrt, startedAfterCalibration]
    calc
      _ ≤ a * ENNReal.ofReal (Real.sqrt ((((k+1)*M : ℕ) : ℝ) * ((r+B : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        exact ENNReal.ofReal_le_ofReal (by simpa only [Nat.cast_add] using hlast)
      _ ≤ _ := by
        exact (le_add_of_nonneg_right (bot_le : 0 ≤ (k : ℝ≥0∞) * cost)).trans
          ((le_add_of_nonneg_right (bot_le : 0 ≤ R)).trans (le_add_of_nonneg_right bot_le))

end

end BilateralProfitRegular
end BundlePart048


section BundlePart049



namespace BilateralProfitRegular.Factory

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal Classical

private noncomputable def calibrationTapeValue (T : ℕ) (η δ est off : ℝ)
    (w z : CalibrationPrices) (prob : CalibrationPrices → ℝ) (U : Stream) : ℝ :=
  let n := calibrationSamples T η δ est
  calibrationValue off
    (hitCount (prob (z.1,w.2)) (fun i : Fin n => i.val) U / n)
    (hitCount (prob (w.1,z.2)) (fun i : Fin n => n+i.val) U / n)

private theorem measurable_calibrationTapeValue (T : ℕ) (η δ est off : ℝ)
    (w z : CalibrationPrices) (prob : CalibrationPrices → ℝ) :
    Measurable (calibrationTapeValue T η δ est off w z prob) := by
  let n := calibrationSamples T η δ est
  have h1 := (measurable_hitCount (prob (z.1,w.2)) (fun i : Fin n => i.val)).div_const (n : ℝ)
  have h2 := (measurable_hitCount (prob (w.1,z.2)) (fun i : Fin n => n+i.val)).div_const (n : ℝ)
  exact measurable_calibrationValue.comp (measurable_const.prodMk (h1.prodMk h2))

private theorem calibration_prefix_congr {T : ℕ} {η δ est off : ℝ}
    {w z : CalibrationPrices} (prob gap : CalibrationPrices → ℝ)
    (finish finish' : ℕ → ℝ → ℝ≥0∞) (H : ℕ) (he : ∀ n ≤ H, ∀ r, finish n r = finish' n r) :
    ∀ n ≤ H, ∀ h,
      (calibrationProc T η δ est off w z).prefixValue prob gap finish () n h =
        (calibrationProc T η δ est off w z).prefixValue prob gap finish' () n h := by
  intro n
  induction n with
  | zero =>
    intro _ h
    cases hs : (calibrationProc T η δ est off w z).step () h with
    | inl q => simp [Proc.prefixValue, hs]
    | inr a => simp [Proc.prefixValue, hs, he 0 (Nat.zero_le H)]
  | succ n ih =>
    intro hn h
    cases hs : (calibrationProc T η δ est off w z).step () h with
    | inl q => simp only [Proc.prefixValue, hs, ih ((Nat.le_succ n).trans hn)]
    | inr a => simp [Proc.prefixValue, hs, he (n+1) hn]

private theorem measurableSet_calibValid (E : Environment) (η δ : ℝ)
    (c : Candidate) (z : CalibrationPrices) :
    MeasurableSet {r : ℝ | CalibValid E η δ c z r} := by
  unfold CalibValid
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_le (((measurable_id.mul_const _).div_const _).log.abs) measurable_const)

private theorem calibration_prefix_with_failure (T : ℕ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (hKT : gridK η ≤ T) (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region)
    (H : ℕ) (finish : ℕ → ℝ → ℝ≥0∞) (R : ℝ≥0∞)
    (hcap : ∀ n ≤ H, ∀ ρ, finish n ρ ≤ (n : ℝ≥0∞))
    (hsuccess : ∀ n ≤ H, ∀ ρ, CalibValid E η δ c z ρ → finish n ρ ≤ R) :
    let pr := calibrationProc T η δ c.est c.offset c.root z
    let gap := fun y => muStar E - mu E y
    pr.prefixValue (P E) gap finish () H [] ≤
      ENNReal.ofReal (5000000000 * Real.log T / η) +
        R + (H : ℝ≥0∞) * ENNReal.ofReal (1 / (T : ℝ)) := by
  dsimp only
  let pr := calibrationProc T η δ c.est c.offset c.root z
  let gap := fun y => muStar E - mu E y
  let ρₜ := calibrationTapeValue T η δ c.est c.offset c.root z (P E)
  let e := fun ρ => R + if CalibValid E η δ c z ρ then 0 else (H : ℝ≥0∞)
  let w := (Measure.dirac () : Measure Unit)
  let G := {ρ : ℝ | CalibValid E η δ c z ρ}
  let bad := {s : Unit × Stream | ¬ ∃ ρ, pr.out (P E) s.1 s.2 = some ρ ∧ CalibValid E η δ c z ρ}
  let f' := fun n ρ => finish (min n H) ρ
  have hp := (onUnit_facts E hE.1).1
  have hρ : Measurable ρₜ := measurable_calibrationTapeValue T η δ c.est c.offset c.root z (P E)
  have hG : MeasurableSet G := measurableSet_calibValid E η δ c z
  have he : Measurable e := measurable_const.add (Measurable.ite hG measurable_const measurable_const)
  have henv (n : ℕ) (ρ : ℝ) : f' n ρ ≤ e ρ := by
    have hn : min n H ≤ H := min_le_right _ _
    by_cases h : CalibValid E η δ c z ρ
    · simpa only [e, if_pos h, add_zero, f'] using hsuccess _ hn ρ h
    · have hh : f' n ρ ≤ (H : ℝ≥0∞) :=
        (hcap _ hn ρ).trans (Nat.cast_le.mpr hn)
      simpa only [e, if_neg h] using hh.trans (le_add_of_nonneg_left bot_le)
  have htape : Measurable (fun s : Unit × Stream =>
      pr.prefixTapeCost (P E) gap f' s.1 s.2 H 0 []) := by
    convert (pr.measurable_prefixTapeCost_fixed_seed (P E) gap f' () H 0 []).comp
      measurable_snd using 1
    funext s
    rcases s with ⟨⟨⟩, U⟩
    rfl
  have hout (s : Unit × Stream) : pr.out (P E) s.1 s.2 = some (ρₜ s.2) := by
    rcases s with ⟨⟨⟩, U⟩
    exact calibration_out T η δ c.est c.offset c.root z (P E) U
  have hEmeas : Measurable (fun s : Unit × Stream =>
      ((pr.out (P E) s.1 s.2).map e).getD 0) := by
    simp_rw [hout, Option.map_some, Option.getD_some]
    exact he.comp (hρ.comp measurable_snd)
  have hexp := pr.prefixExpected_le (P E) hp w gap f' e henv H htape.aemeasurable hEmeas.aemeasurable
  have hsame : pr.prefixValue (P E) gap finish () H [] = pr.prefixValue (P E) gap f' () H [] :=
    calibration_prefix_congr (P E) gap finish f' H (fun n hn ρ => by simp [f', min_eq_left hn])
      H le_rfl []
  have hlhs : (fun ω : Unit => pr.prefixValue (P E) gap f' ω H []) =
      fun _ => pr.prefixValue (P E) gap f' () H [] := by
    funext u
    cases u
    rfl
  rw [hlhs, lintegral_const, measure_univ, mul_one] at hexp
  change pr.prefixValue (P E) gap finish () H [] ≤ _
  rw [hsame]
  refine hexp.trans ?_
  have hcst := (calibration_cost_le T η hη hη₁ hKT E hE δ hηδ c hc z hz).2
  have hfail : Proc.law w bad ≤ ENNReal.ofReal (1 / (T : ℝ)) :=
    calibration_failure_le T η hη hη₁ hKT E hE δ hηδ c hc z hz
  have hmem (s : Unit × Stream) : s ∈ bad ↔ ¬ CalibValid E η δ c z (ρₜ s.2) := by
    simp [bad, hout]
  have hbM : MeasurableSet bad := by
    have hEq : bad = (fun s : Unit × Stream => ρₜ s.2) ⁻¹' Gᶜ := by
      ext s
      exact hmem s
    exact hEq ▸ hG.compl.preimage (hρ.comp measurable_snd)
  have hEeq (s : Unit × Stream) : ((pr.out (P E) s.1 s.2).map e).getD 0 =
      R + bad.indicator (fun _ => (H : ℝ≥0∞)) s := by
    rw [hout, Option.map_some, Option.getD_some]
    dsimp [e]
    by_cases h : s ∈ bad
    · rw [indicator_of_mem h, if_neg ((hmem s).1 h)]
    · rw [indicator_of_notMem h, if_pos (of_not_not (fun h' => h ((hmem s).2 h')))]
  have : IsProbabilityMeasure Proc.coinLaw := by unfold Proc.coinLaw; infer_instance
  have : IsProbabilityMeasure (Proc.law w) := by unfold Proc.law; infer_instance
  simp_rw [hEeq]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, lintegral_indicator hbM,
    setLIntegral_const, ← add_assoc]
  exact add_le_add (add_le_add_left hcst R) (mul_le_mul_right hfail _)

end BilateralProfitRegular.Factory
end BundlePart049


section BundlePart050




namespace BilateralProfitRegular.Factory

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem calibrationProgram_value_eq_prefix (T : ℕ) (η δ est off : ℝ)
    (w z : CalibrationPrices) (prob gap : CalibrationPrices → ℝ)
    (finish : ℕ → ℝ → ℝ≥0∞) (n : ℕ) (h : CalibrationHistory) :
    Program.value prob (fun q => ENNReal.ofReal (gap q))
      (fun bs => calibrationProgram T η δ est off w z (h.map Prod.snd ++ bs)) n finish =
    (calibrationProc T η δ est off w z).prefixValue prob gap finish () n h := by
  let F := calibrationProc T η δ est off w z
  let Z := calibrationProgram T η δ est off w z
  have root (h : CalibrationHistory) : Z (h.map Prod.snd ++ []) = (F.step () h).swap := by
    rw [List.append_nil]
    exact calibrationProgram_replay T η δ est off w z h
  have follow (h : CalibrationHistory) (y : CalibrationPrices) (b : Bool) :
      Program.after (fun bs => Z (h.map Prod.snd ++ bs)) b =
        fun bs => Z ((h ++ [(y,b)]).map Prod.snd ++ bs) := by
    funext bs
    simp [Program.after, List.map_append, List.append_assoc]
  have hroot (h : CalibrationHistory) :
      calibrationProgram T η δ est off w z (h.map Prod.snd ++ []) =
        ((calibrationProc T η δ est off w z).step () h).swap := root h
  induction n generalizing h with
  | zero =>
    rw [Program.value, Proc.prefixValue, hroot]
    cases (calibrationProc T η δ est off w z).step () h <;> rfl
  | succ n ih =>
    rw [Program.value, Proc.prefixValue, hroot]
    cases hs : (calibrationProc T η δ est off w z).step () h with
    | inl y =>
      simp only [Sum.swap, Sum.elim_inr]
      rw [show Program.after (fun bs => calibrationProgram T η δ est off w z (h.map Prod.snd ++ bs)) true =
          (fun bs => calibrationProgram T η δ est off w z ((h ++ [(y,true)]).map Prod.snd ++ bs)) from follow h y true,
        show Program.after (fun bs => calibrationProgram T η δ est off w z (h.map Prod.snd ++ bs)) false =
          (fun bs => calibrationProgram T η δ est off w z ((h ++ [(y,false)]).map Prod.snd ++ bs)) from follow h y false,
        ih, ih]
      rfl
    | inr r => rfl

private theorem calibrationProgram_with_failure (T : ℕ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (hKT : gridK η ≤ T) (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region)
    (H : ℕ) (finish : ℕ → ℝ → ℝ≥0∞) (R : ℝ≥0∞)
    (hcap : ∀ n ≤ H, ∀ ρ, finish n ρ ≤ (n : ℝ≥0∞))
    (hsuccess : ∀ n ≤ H, ∀ ρ, CalibValid E η δ c z ρ → finish n ρ ≤ R) :
    Program.value (P E) (fun y => ENNReal.ofReal (muStar E - mu E y))
      (calibrationProgram T η δ c.est c.offset c.root z) H finish ≤
      ENNReal.ofReal (5000000000 * Real.log T / η) +
        R + (H : ℝ≥0∞) * ENNReal.ofReal (1 / (T : ℝ)) := by
  have he := calibrationProgram_value_eq_prefix T η δ c.est c.offset c.root z (P E)
    (fun y => muStar E - mu E y) finish H []
  simp only [List.map_nil, List.nil_append] at he
  rw [he]
  exact calibration_prefix_with_failure T η hη hη₁ hKT E hE δ hηδ c hc z hz H finish R hcap hsuccess

private theorem calibrationProgram_legal (T : ℕ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (hKT : gridK η ≤ T) (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region) :
    Program.Legal triT (calibrationProgram T η δ c.est c.offset c.root z) := by
  intro h y hy
  have hqueries := (calibration_cost_le T η hη hη₁ hKT E hE δ hηδ c hc z hz).1
  apply hqueries () (erasePrices h) y
  unfold calibrationProgram at hy
  cases hs : (calibrationProc T η δ c.est c.offset c.root z).step () (erasePrices h) with
  | inl q => simpa [hs] using hy
  | inr a => simp [hs] at hy

end BilateralProfitRegular.Factory
end BundlePart050


section BundlePart051




namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem measurable_mainCalibProgram (T : ℕ) (δ : ℝ) (c : Candidate)
    (h : List Bool) :
    Measurable (fun z : ℝ × ℝ => Factory.calibrationProgram T (mainEta T)
      δ c.est c.offset c.root z h) := by
  let f (z : ℝ × ℝ) : ℝ × ℝ × ℝ × Factory.Prices × Factory.Prices :=
    (δ, c.est, c.offset, c.root, z)
  have hf : Measurable f :=
    measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hm := (Factory.measurable_calibrationProgram T (mainEta T) h).comp hf
  simpa only [Function.comp_def, f, Prod.fst, Prod.snd] using hm

private noncomputable def mainCalibrationRandomProgram (T : ℕ) (δ : ℝ) (c : Candidate) :
    RandomProgram (ℝ × ℝ) ℝ where
  Seed := Unit
  seedSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance
  run s := Program.mapQuery mainClampPrice
    (Factory.calibrationProgram T (mainEta T) δ c.est c.offset c.root s.1)
  measurable_run := by
    have hraw : Program.MeasurableFamily
        (fun s : (ℝ × ℝ) × Unit =>
          Factory.calibrationProgram T (mainEta T) δ c.est c.offset c.root s.1) := by
      intro h
      exact (measurable_mainCalibProgram T δ c h).comp measurable_fst
    exact Program.measurableFamily_mapQuery measurable_mainClampPrice hraw
  legal s := Program.legal_mapQuery _ mainClampPrice_legal

private theorem mainCalibrationRandomProgram_bound {T : ℕ} (hT : 2 ≤ T) (E : Environment)
    (hE : RegularUnit E) (δ : ℝ) (hδ : mainEta T < δ) (c : Candidate) (hc : c.Valid E δ) :
    (mainCalibrationRandomProgram T δ c).Bound E T (fun z => z ∈ c.region)
      (fun z ρ => CalibValid E (mainEta T) δ c z ρ)
      (ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 1) := by
  intro z hz H hHT finish _ hcap R hgood
  have hη := mainEta_pos hT
  have hη₁ := mainEta_lt_one hT
  have hKT := mainEta_grid_le_T hT
  let p : Program ℝ := Factory.calibrationProgram T (mainEta T) δ c.est c.offset c.root z
  have hlegal : Program.Legal triT p :=
    Factory.calibrationProgram_legal T (mainEta T) hη hη₁ hKT E hE δ hδ c hc z hz
  have hc' : p.mapQuery mainClampPrice = p :=
    Program.mapQuery_eq hlegal (fun _ h => mainClampPrice_eq h)
  change (∫⁻ (_ : Unit), (p.mapQuery mainClampPrice).value (P E) (regretGap E) H finish
      ∂(Measure.dirac ())) ≤ _
  rw [hc', lintegral_const, measure_univ, mul_one]
  have hb := Factory.calibrationProgram_with_failure T (mainEta T) hη hη₁ hKT E hE δ hδ c hc z hz
    H finish R hcap hgood
  refine hb.trans ?_
  have hT' : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hlog : Real.log (T : ℝ) ≤ mainLog T :=
    Real.log_le_log hT' (by linarith only [hT'])
  have hcst : ENNReal.ofReal (5000000000 * Real.log (T : ℝ) / mainEta T) ≤
      ENNReal.ofReal (5000000000 * mainLog T / mainEta T) := by
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num)) hη.le
  have hcap' : (H : ℝ≥0∞) * ENNReal.ofReal (1 / (T : ℝ)) ≤ 1 := by
    calc
      _ ≤ (T : ℝ≥0∞) * ENNReal.ofReal (1 / (T : ℝ)) :=
        mul_le_mul_left (Nat.cast_le.mpr hHT) _
      _ = _ := by rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hT'.le,
        mul_one_div_cancel hT'.ne', ENNReal.ofReal_one]
  calc
    _ ≤ (ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + R) + 1 :=
      add_le_add (add_le_add_left hcst R) hcap'
    _ = _ := by ac_rfl

end BilateralProfitRegular
end BundlePart051


section BundlePart052



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem mainCalibrationRandomProgram_expectedCost_le {T : ℕ} (hT : 2 ≤ T) (E : Environment)
    (hE : RegularUnit E) (δ : ℝ) (hδ : mainEta T < δ) (c : Candidate) (hc : c.Valid E δ)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : ∀ x ∈ triT, g x ≤ regretGap E x)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (n : ℕ) (hn : n ≤ T)
    (finish : ℕ → ℝ → ℝ≥0∞) (hf : ∀ m, Measurable (finish m))
    (htime : ∀ m ≤ n, ∀ ρ, finish m ρ ≤ (m : ℝ≥0∞)) (R : ℝ≥0∞)
    (hgood : ∀ m ≤ n, ∀ ρ, CalibValid E (mainEta T) δ c z ρ → finish m ρ ≤ R) :
    (mainCalibrationRandomProgram T δ c).expectedCost E g z n finish ≤
      ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 1 + R :=
  ((mainCalibrationRandomProgram T δ c).expectedCost_mono E hg z n finish).trans
    (mainCalibrationRandomProgram_bound hT E hE δ hδ c hc z hz n hn finish hf htime R hgood)

private theorem mainCalibrationRandomProgram_expectedCost_le_envelope {T : ℕ} (hT : 2 ≤ T)
    (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hδ : mainEta T < δ)
    (c : Candidate) (hc : c.Valid E δ)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : ∀ x ∈ triT, g x ≤ regretGap E x)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (n : ℕ) (hn : n ≤ T)
    (finish : ℕ → ℝ → ℝ≥0∞) (hf : ∀ m, Measurable (finish m))
    (htime : ∀ m ≤ n, ∀ ρ, finish m ρ ≤ (m : ℝ≥0∞))
    (B : ℕ → ℝ≥0∞) (hB : Monotone B)
    (hgood : ∀ m ≤ n, ∀ ρ, CalibValid E (mainEta T) δ c z ρ → finish m ρ ≤ B m) :
    (mainCalibrationRandomProgram T δ c).expectedCost E g z n finish ≤
      ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 1 + B n :=
  mainCalibrationRandomProgram_expectedCost_le hT E hE δ hδ c hc g hg z hz n hn finish hf htime
    (B n) (fun m hm ρ hρ => (hgood m hm ρ hρ).trans (hB hm))

end BilateralProfitRegular
end
end BundlePart052


section BundlePart053




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

private def startedGap (T : ℕ) (E : Environment) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (muStar E - mu E x - 520 * mainEta T)

private theorem measurable_startedGap (T : ℕ) (E : Environment) (hE : OnUnit E) :
    Measurable (startedGap T E) :=
  ((measurable_const.sub ((measurable_snd.sub measurable_fst).mul (measurable_P E hE))).sub
    measurable_const).ennreal_ofReal

private theorem startedGap_le_regretGap {T : ℕ} (hT : 2 ≤ T) (E : Environment) (x : ℝ × ℝ) :
    startedGap T E x ≤ regretGap E x := by
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_self _ (mul_nonneg (by norm_num) (mainEta_pos hT).le)

private theorem startedGap_le_one {T : ℕ} (hT : 2 ≤ T) (E : Environment) (hE : OnUnit E)
    (x : ℝ × ℝ) (hx : x ∈ triT) : startedGap T E x ≤ 1 :=
  (startedGap_le_regretGap hT E x).trans ((regretGap_le E hE x hx).trans
    (ENNReal.ofReal_le_one.mpr (onUnit_facts E hE).2.2.2.1.2))

private def startedJobOverhead (T : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 2

private def startedCopyCoefficient (T : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (startedCopyCostConstant * mainLog T^2)

section Job

variable {T : ℕ} {δ : ℝ} {cs : List Candidate}
variable (j : StartedPhase T) (i : Fin cs.length)

local notation "Hist" => MainScheduleHistory cs.length

private def startedReference (H : Hist) : ℝ × ℝ :=
  (mainPhaseTimeline (mainEta T) δ cs H j).2 i

private theorem measurable_startedReference :
    Measurable (startedReference (δ := δ) (cs := cs) j i) := measurable_mainPhaseRef _ _ _ _ _

private def startedActive : Set Hist :=
  {H | i ∈ (mainPhaseTimeline (mainEta T) δ cs H j).1}

private theorem measurableSet_startedActive : MeasurableSet (startedActive (δ := δ) (cs := cs) j i) :=
  (measurable_mainPhaseActive (mainEta T) δ cs j)
    (show MeasurableSet {A : Finset (Fin cs.length) | i ∈ A} from MeasurableSet.of_discrete)

private def startedCalProgram : RandomProgram Hist ℝ :=
  (mainCalibrationRandomProgram T δ (cs.get i)).compInput
    (startedReference (δ := δ) (cs := cs) j i) (measurable_startedReference (δ := δ) j i)

private def startedBatchProgram : RandomProgram (Hist × ℝ) (StartedBatchHist T j) :=
  (startedBatch (δ := δ) (cs := cs) j i).compInput (fun a => (startedReference (δ := δ) j i a.1, a.2))
    (((measurable_startedReference (δ := δ) (cs := cs) j i).comp measurable_fst).prodMk measurable_snd)

private def startedWrite (x : (Hist × ℝ) × StartedBatchHist T j) : Hist :=
  mainWriteReport x.1.1 j i (mainRefinementReport δ x.1.2 x.2)

private theorem measurable_startedWrite : Measurable (startedWrite (δ := δ) (cs := cs) j i) :=
  (measurable_mainWriteReport j i).comp (measurable_fst.fst.prodMk
    ((measurable_mainRefinementReport δ).comp (measurable_fst.snd.prodMk measurable_snd)))

private def startedBatchWithReport : RandomProgram (Hist × ℝ) Hist :=
  (startedBatchProgram (δ := δ) (cs := cs) j i).bind
    (RandomProgram.pure (startedWrite (δ := δ) j i) (measurable_startedWrite (δ := δ) j i))

private def startedActiveJob : RandomProgram Hist Hist :=
  (startedCalProgram (δ := δ) (cs := cs) j i).bind (startedBatchWithReport (δ := δ) j i)

private def startedJob : RandomProgram Hist Hist :=
  (startedActiveJob (δ := δ) (cs := cs) j i).when (startedActive (δ := δ) j i) (measurableSet_startedActive (δ := δ) j i)

private theorem startedJob_minQueries (H : Hist)
    (hi : i ∈ (mainPhaseTimeline (mainEta T) δ cs H j).1)
    (seed : (startedJob (δ := δ) (cs := cs) j i).Seed) :
    ((startedJob (δ := δ) (cs := cs) j i).run (H, seed)).MinQueries
      (numCopies startedC₀ T * phaseLen startedC₀ T j) := by
  have hs : H ∈ startedActive (δ := δ) (cs := cs) j i := hi
  have hrun : (startedJob (δ := δ) (cs := cs) j i).run (H, seed) =
      (startedActiveJob (δ := δ) (cs := cs) j i).run (H, seed) := by
    funext h
    simp [startedJob, RandomProgram.when, hs]
  rw [hrun]
  simp only [startedActiveJob, RandomProgram.bind]
  rw [← Nat.zero_add (numCopies startedC₀ T * phaseLen startedC₀ T j)]
  apply Program.minQueries_bind (fun _ h => (Nat.not_lt_zero _ h).elim)
  intro ρ
  simp only [startedBatchWithReport, RandomProgram.bind]
  rw [← Nat.add_zero (numCopies startedC₀ T * phaseLen startedC₀ T j)]
  apply Program.minQueries_bind
  · exact startedBatch_minQueries (δ := δ) j i _ _
  · exact fun _ _ h => (Nat.not_lt_zero _ h).elim

private theorem startedJob_bound (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T)
    (hInit : InitGuarantee E (mainEta T) δ cs) :
    (startedJob (δ := δ) (cs := cs) j i).StartedBound E (startedGap T E) T
      (numCopies startedC₀ T) (startedRunMax startedC₀ T) (startedCopyCoefficient T)
      (startedJobOverhead T) (MainPartialClean E (mainEta T) δ cs j i.val)
      (MainPartialClean E (mainEta T) δ cs j (i.val+1)) 1 := by
  classical
  let c := cs.get i
  let g := startedGap T E
  let M := numCopies startedC₀ T
  let n := phaseLen startedC₀ T j
  let B := startedRunMax startedC₀ T
  let a := startedCopyCoefficient T
  let overhead := startedJobOverhead T
  let z := startedReference (δ := δ) (cs := cs) j i
  let s := startedActive (δ := δ) (cs := cs) j i
  let hm := measurableSet_startedActive (δ := δ) (cs := cs) j i
  have hG := measurable_startedGap T E hE.1
  intro H hClean N hN finish hf htime k R hfinish
  by_cases hi : H ∈ s
  · rw [startedJob, RandomProgram.expectedCost_when_of_mem _ s hm E g hi,
      startedActiveJob, RandomProgram.expectedCost_bind _ _ E hE.1 g hG _ _ hf]
    let next := startedBatchWithReport (δ := δ) (cs := cs) j i
    let G := fun r ρ => next.expectedCost E g (H, ρ) r finish
    have hGmeas (r : ℕ) : Measurable (G r) :=
      (next.measurable_expectedCost E hE.1 g hG r hf).comp
        ((measurable_const (a := H)).prodMk measurable_id)
    have hGtime (r : ℕ) (hr : r ≤ N) (ρ : ℝ) : G r ρ ≤ (r : ℝ≥0∞) := by
      simpa using next.expectedCost_le_time E hE.1 g (H, ρ) r 1
        (startedGap_le_one hT E hE.1) (fun t ht h => by simpa using htime t (ht.trans hr) h)
    have hInv := (mainPhaseTimeline_from_init hE hT hInit H j hClean.1).2
    have hz : z H ∈ c.region := hInv.1 i hi
    have hCalibration (r : ℕ) (hr : r ≤ N) (ρ : ℝ)
        (hc : CalibValid E (mainEta T) δ c (z H) ρ) :
        G r ρ ≤ startedAfterCalibration M B a overhead k r R := by
      have hgap := hInv.2 i hi ρ hc
      let f := fun r tr => finish r (startedWrite (δ := δ) j i ((H, ρ), tr))
      have hfm (r : ℕ) : Measurable (f r) :=
        (hf r).comp ((measurable_startedWrite (δ := δ) (cs := cs) j i).comp
          ((measurable_const (a := (H, ρ))).prodMk measurable_id))
      have hbatch := startedBatch_expected_le j i E hE hT hInit (z H) hz ρ hc hgap
        r (hr.trans hN) f hfm (fun t ht tr => htime t (ht.trans hr) _)
        (startedBudget M B a overhead k (r - M*n) + R) (by
          intro t ht tr hGood
          have hEntry := mainPhaseEntryClean_of_refineGood (startedCopies_pos hT) hc hGood
          have hNext := mainPartialClean_write hClean (fun _ => hEntry)
          exact (hfinish t ((ht.trans (Nat.sub_le _ _)).trans hr) _ hNext).trans
            (add_le_add (startedBudget_mono le_rfl ht) le_rfl))
      have hcopy : ENNReal.ofReal (startedCopyCostConstant * Real.sqrt (n : ℝ) * mainLog T^2) =
          a * ENNReal.ofReal (Real.sqrt (n : ℝ)) := by
        change _ = ENNReal.ofReal (startedCopyCostConstant * mainLog T^2) * _
        rw [← ENNReal.ofReal_mul (mul_nonneg startedCopyCostConstant_nonneg (sq_nonneg _))]
        congr 1
        ring
      change (startedBatch (δ := δ) (cs := cs) j i).expectedCost E g (z H, ρ) r f ≤
        ((min M (r ⌈/⌉ n) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (startedCopyCostConstant * Real.sqrt (n : ℝ) * mainLog T^2) +
        (if M*n ≤ r then startedBudget M B a overhead k (r - M*n) + R + 1 else 0) at hbatch
      rw [hcopy] at hbatch
      change next.expectedCost E g (H, ρ) r finish ≤ _
      dsimp only [next]
      rw [startedBatchWithReport, RandomProgram.expectedCost_bind _ _ E hE.1 g hG _ _ hf]
      simp_rw [RandomProgram.expectedCost_pure, startedBatchProgram, RandomProgram.expectedCost_compInput]
      exact hbatch.trans (started_batch_cost_aggregate M B k r n
        (started_phaseLen_pos hT startedC₀_pos) (started_phase_bounds hT startedC₀_pos j.isLt).2
        a overhead R)
    rw [startedCalProgram, RandomProgram.expectedCost_compInput]
    have hc := hInit.2.2.2.1 c (List.get_mem cs i)
    refine (mainCalibrationRandomProgram_expectedCost_le_envelope hT E hE δ hInit.1 c hc g
      (fun x _ => startedGap_le_regretGap hT E x) (z H) hz N hN G hGmeas hGtime
      (fun r => startedAfterCalibration M B a overhead k r R)
      (fun _ _ hr => startedAfterCalibration_mono hr) hCalibration).trans ?_
    change ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 1 +
      startedAfterCalibration M B a overhead k N R ≤ startedBudget M B a overhead (k+1) N + R
    have hcast : ((k+1 : ℕ) : ℝ≥0∞) * overhead = (k : ℝ≥0∞) * overhead + overhead := by
      simp only [Nat.cast_succ, add_mul, one_mul]
    rw [startedAfterCalibration, startedBudget, hcast, show overhead =
      ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + (1+1) by
        change ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 2 = _
        norm_num]
    exact le_of_eq (by ac_rfl)
  · rw [startedJob, RandomProgram.expectedCost_when_of_not_mem _ s hm E g hi]
    exact (hfinish N le_rfl H (mainPartialClean_skip hClean hi)).trans
      (add_le_add (startedBudget_mono (Nat.le_succ k) le_rfl) le_rfl)

end Job
end BilateralProfitRegular
end
end BundlePart053


section BundlePart054




noncomputable section

namespace BilateralProfitRegular.RandomProgram

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

variable {H : Type} [MeasurableSpace H] {N : ℕ}

/-- Choose a program from a finite family using the input state. Each program has its own seed. -/
private def select (p : Fin N → RandomProgram H H) (f : H → Option (Fin N)) (hf : Measurable f) :
    RandomProgram H H where
  Seed := (i : Fin N) → (p i).Seed
  seedSpace := inferInstance
  law := Measure.pi (fun i => (p i).law)
  probability := inferInstance
  run z h := match f z.1 with
    | none => .inl z.1
    | some i => (p i).run (z.1, z.2 i) h
  measurable_run h := by
    let f' : Option (Fin N) × (H × ((i : Fin N) → (p i).Seed)) →
        H ⊕ (ℝ × ℝ) := fun z => match z.1 with
      | none => .inl z.2.1
      | some i => (p i).run (z.2.1, z.2.2 i) h
    have hf' : Measurable f' := by
      apply measurable_from_prod_countable_right
      intro i
      cases i with
      | none => exact measurable_inl.comp measurable_fst
      | some i =>
        exact ((p i).measurable_run h).comp
          (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact hf'.comp ((hf.comp measurable_fst).prodMk measurable_id)
  legal z h y hy := by
    cases he : f z.1 with
    | none =>
      change (match f z.1 with
        | none => Sum.inl z.1
        | some i => (p i).run (z.1, z.2 i) h) = Sum.inr y at hy
      simp [he] at hy
    | some i =>
      apply (p i).legal (z.1, z.2 i) h y
      change (match f z.1 with
        | none => Sum.inl z.1
        | some i => (p i).run (z.1, z.2 i) h) = Sum.inr y at hy
      simpa only [he] using hy

private theorem expectedCost_select_some (p : Fin N → RandomProgram H H) (f : H → Option (Fin N))
    (hf : Measurable f) (E : Environment) (hE : OnUnit E) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hg : Measurable g) {h : H} {i : Fin N} (hi : f h = some i) (n : ℕ)
    {finish : ℕ → H → ℝ≥0∞} (hfinish : ∀ m, Measurable (finish m)) :
    (select p f hf).expectedCost E g h n finish = (p i).expectedCost E g h n finish := by
  let value : (p i).Seed → ℝ≥0∞ := fun s => ((p i).run (h, s)).value (P E) g n finish
  have hm : Measurable value := Program.measurable_value (measurable_P E hE) hg
    (fun bs => ((p i).measurable_run bs).comp (measurable_const.prodMk measurable_id))
    n (fun r => (hfinish r).comp measurable_snd)
  have hrun (s : (j : Fin N) → (p j).Seed) : (select p f hf).run (h, s) =
      (p i).run (h, s i) := by
    funext bs
    simp [select, hi]
  change (∫⁻ s : (j : Fin N) → (p j).Seed, ((select p f hf).run (h, s)).value (P E) g n finish
    ∂Measure.pi (fun j => (p j).law)) = _
  simp_rw [hrun]
  exact (measurePreserving_eval (fun j => (p j).law) i).lintegral_comp hm

private theorem expectedCost_select_none (p : Fin N → RandomProgram H H) (f : H → Option (Fin N))
    (hf : Measurable f) (E : Environment) (g : (ℝ × ℝ) → ℝ≥0∞)
    {h : H} (hi : f h = none) (n : ℕ) (finish : ℕ → H → ℝ≥0∞) :
    (select p f hf).expectedCost E g h n finish = finish n h := by
  have hrun (s : (j : Fin N) → (p j).Seed) : (select p f hf).run (h, s) =
      Program.pure h := by
    funext bs
    simp [select, hi, Program.pure]
  change (∫⁻ s : (j : Fin N) → (p j).Seed, ((select p f hf).run (h, s)).value (P E) g n finish
    ∂Measure.pi (fun j => (p j).law)) = _
  simp_rw [hrun, Program.value_pure, lintegral_const, measure_univ, mul_one]

private theorem expectedCost_thenState (p q : RandomProgram H H) (E : Environment) (hE : OnUnit E)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (h : H) (n : ℕ)
    {finish : ℕ → H → ℝ≥0∞} (hf : ∀ m, Measurable (finish m)) :
    (p.thenState q).expectedCost E g h n finish =
      p.expectedCost E g h n (fun m t => q.expectedCost E g t m finish) := by
  rw [thenState, expectedCost_bind p _ E hE g hg h n hf]
  rfl

end BilateralProfitRegular.RandomProgram
end
end BundlePart054


section BundlePart055



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {T : ℕ}

private def trade (x : Bool × Bool) : Bool := x.1 && x.2

private def listPolicy (π : BilateralProfitMHR.Policy T Ω) : Policy T Ω where
  price t ω h := if hh : h.length = (t : ℕ) then
    π.price t ω (fun i => h.get ⟨i, by simpa only [hh] using i.isLt⟩)
    else (0,0)
  price_mem t ω h := by
    split
    · exact π.price_mem _ _ _
    · norm_num
  measurable_price t h := by
    by_cases hh : h.length = (t : ℕ)
    · simpa only [dif_pos hh] using
        π.price_measurable t (fun i => h.get ⟨i, by simpa only [hh] using i.isLt⟩)
    · simp only [dif_neg hh]
      exact measurable_const

private theorem listPolicy_price_ofFn (π : BilateralProfitMHR.Policy T Ω) (t : Fin T) (ω : Ω)
    (h : Fin t → Bool × Bool) :
    (listPolicy π).price t ω (List.ofFn h) = π.price t ω h := by
  simp [listPolicy]

private theorem listPolicy_oneBit (π : BilateralProfitMHR.Policy T Ω) (hπ : π.OneBit) :
    (listPolicy π).OneBit := by
  intro t ω h h' hh
  have he : h.length = h'.length := by simpa using congrArg List.length hh
  by_cases ht : h.length = (t : ℕ)
  · have ht' := he.symm.trans ht
    simp only [listPolicy, dif_pos ht, dif_pos ht']
    apply hπ
    intro i
    have hi : (i : ℕ) < h.length := by simpa only [ht] using i.isLt
    have hi' : (i : ℕ) < h'.length := by simpa only [ht'] using i.isLt
    have hm := congrArg (fun l : List Bool => l[i.val]?) hh
    simpa [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] using hm
  · have ht' : h'.length ≠ (t : ℕ) := fun h' => ht (he.trans h')
    simp only [listPolicy, dif_neg ht, dif_neg ht']

private theorem listPolicy_hist (π : BilateralProfitMHR.Policy T Ω) (ω : Ω)
    (v : Fin T → ℝ × ℝ) (n : ℕ) (hn : n ≤ T) :
    (listPolicy π).hist ω v n = List.ofFn (π.hist ω v n hn) := by
  induction n with
  | zero => simp [Policy.hist, BilateralProfitMHR.Policy.hist]
  | succ n ih =>
    have ht : n < T := Nat.lt_of_succ_le hn
    rw [Policy.hist, dif_pos ht, ih ht.le, listPolicy_price_ofFn,
      BilateralProfitMHR.Policy.hist, List.ofFn_succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rfl

private theorem listPolicy_regret (π : BilateralProfitMHR.Policy T Ω) (Pω : Measure Ω)
    (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) :
    (listPolicy π).regret Pω D a = π.regret Pω D a := by
  unfold Policy.regret BilateralProfitMHR.Policy.regret BilateralProfitMHR.Policy.expProfit
    BilateralProfitMHR.fixedProfit BilateralProfitMHR.runLaw
  congr 1
  funext t
  congr 2
  funext x
  rw [Policy.action, listPolicy_hist π x.1 x.2 t t.isLt.le, listPolicy_price_ofFn]
  rfl

end BilateralProfitRegular
end
end BundlePart055


section BundlePart056




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory MechanismDesign.BilateralTrade
open scoped ENNReal

namespace Program

private def play (x : ℝ × ℝ) : Program Unit := fun _ => .inr x

private def price (p : Program Unit) : ℝ × ℝ := (p []).elim (fun _ => (0, 0)) id

private def step (p : Program Unit) (b : Bool) : Program Unit :=
  (p []).elim (fun _ => Program.pure ()) (fun _ => p.after b)

private theorem price_legal {p : Program Unit} (hp : Legal triT p) : p.price ∈ triT := by
  cases he : p [] with
  | inl a => simpa [price, he] using zero_mem_triT
  | inr x => simpa [price, he] using hp [] x he

private theorem step_legal {p : Program Unit} (hp : Legal triT p) (b : Bool) : Legal triT (p.step b) := by
  cases he : p [] with
  | inl a => simp [step, he, Legal, Program.pure]
  | inr x => exact fun h y hy => hp (b :: h) y (by simpa [step, he, after] using hy)

variable {Ω : Type} [MeasurableSpace Ω]

private theorem measurable_price {p : Ω → Program Unit} (hp : MeasurableFamily p) :
    Measurable (fun ω => (p ω).price) :=
  (measurable_const.sumElim measurable_id).comp (hp [])

private theorem measurableFamily_step {p : Ω → Program Unit} (hp : MeasurableFamily p) (b : Bool) :
    MeasurableFamily (fun ω => (p ω).step b) := by
  intro h
  have hl : Measurable (fun _ : Ω × Unit => (Sum.inl () : Unit ⊕ (ℝ × ℝ))) :=
    measurable_const
  have hr : Measurable (fun a : Ω × (ℝ × ℝ) => p a.1 (b :: h)) :=
    (hp (b::h)).comp measurable_fst
  convert (measurable_sum_prod_elim hl hr).comp (measurable_id.prodMk (hp [])) using 1
  ext ω
  cases he : p ω [] <;> simp [step, after, pure, Function.comp_def, he]

private theorem measurableFamily_run (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (t : ℕ) (h : Fin t → Bool) :
    MeasurableFamily (BilateralProfitMHR.binaryRunState (fun _ => step) p t h) := by
  induction t with
  | zero => exact hp
  | succ t ih => exact measurableFamily_step (ih (Fin.init h)) _

private theorem binaryValue_pure (q : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (n : ℕ) :
    BilateralProfitMHR.binaryValue q g price step n (pure ()) =
      (n : ℝ≥0∞) * g (0, 0) := by
  induction n with
  | zero => simp [BilateralProfitMHR.binaryValue]
  | succ n ih =>
    have he : ENNReal.ofReal (q (0,0)) + ENNReal.ofReal (1 - q (0,0)) = 1 := by
      rw [← ENNReal.ofReal_add (hq _).1 (sub_nonneg.mpr (hq _).2)]
      simp
    simp only [BilateralProfitMHR.binaryValue, price, step, pure, Sum.elim_inl, ih]
    rw [← add_mul, he, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem binaryValue_eq_value (q : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (p : Program Unit) (n : ℕ) :
    BilateralProfitMHR.binaryValue q g price step n p =
      p.value q g n (fun m _ => (m : ℝ≥0∞) * g (0,0)) := by
  induction n generalizing p with
  | zero => cases h : p [] <;> simp [BilateralProfitMHR.binaryValue, value, h]
  | succ n ih =>
    cases h : p [] with
    | inl a =>
      have he : ENNReal.ofReal (q (0,0)) + ENNReal.ofReal (1 - q (0,0)) = 1 := by
        rw [← ENNReal.ofReal_add (hq _).1 (sub_nonneg.mpr (hq _).2)]
        simp
      simp only [BilateralProfitMHR.binaryValue, value, h, price, step, Sum.elim_inl,
        binaryValue_pure q g hq]
      rw [← add_mul, he, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm]
    | inr x => simp [BilateralProfitMHR.binaryValue, value, h, price, step, ih]

private abbrev LegalState := {p : Program Unit // Legal triT p}

private def legalStep (p : LegalState) (b : Bool) : LegalState :=
  ⟨p.1.step b, step_legal p.2 b⟩

private def legalAct (p : LegalState) : ℝ × ℝ := p.1.price

private theorem legalAct_mem (p : LegalState) : legalAct p ∈ BilateralProfitMHR.unitSq :=
  triT_mem_unitSq (price_legal p.2)

omit [MeasurableSpace Ω] in
private theorem legalRun_eq (p : Ω → Program Unit) (hl : ∀ ω, Legal triT (p ω))
    (t : ℕ) (h : Fin t → Bool) (ω : Ω) :
    (BilateralProfitMHR.binaryRunState (fun _ => legalStep) (fun ω => ⟨p ω, hl ω⟩) t h ω).1 =
      BilateralProfitMHR.binaryRunState (fun _ => step) p t h ω := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [BilateralProfitMHR.binaryRunState, legalStep, ih]

private theorem legalRun_measurable (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (hl : ∀ ω, Legal triT (p ω)) (t : ℕ) (h : Fin t → Bool) :
    Measurable (fun ω => legalAct
      (BilateralProfitMHR.binaryRunState (fun _ => legalStep) (fun ω => ⟨p ω, hl ω⟩) t h ω)) := by
  simp only [legalAct, legalRun_eq]
  exact measurable_price (measurableFamily_run p hp t h)

private theorem legalBinaryValue_eq (q : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → ℝ≥0∞)
    (p : LegalState) (n : ℕ) :
    BilateralProfitMHR.binaryValue q g legalAct legalStep n p =
      BilateralProfitMHR.binaryValue q g price step n p.1 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [BilateralProfitMHR.binaryValue, legalAct, legalStep, ih]

private def controller (T : ℕ) (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (hl : ∀ ω, Legal triT (p ω)) : BilateralProfitMHR.Policy T Ω :=
  BilateralProfitMHR.controllerPolicy T (fun _ => legalAct) (fun _ => legalStep)
    (fun ω => ⟨p ω, hl ω⟩) (fun _ => legalAct_mem) (legalRun_measurable p hp hl)

private def toPolicy (T : ℕ) (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (hl : ∀ ω, Legal triT (p ω)) : Policy T Ω := listPolicy (controller T p hp hl)

private theorem toPolicy_oneBit (T : ℕ) (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (hl : ∀ ω, Legal triT (p ω)) : (toPolicy T p hp hl).OneBit := by
  apply listPolicy_oneBit
  intro t ω h h' he
  simp only [controller, BilateralProfitMHR.controllerPolicy]
  rw [show (fun i => (h i).1 && (h i).2) = (fun i => (h' i).1 && (h' i).2) from funext he]

private def finalValue (E : Environment) (m : ℕ) (_ : Unit) : ℝ≥0∞ :=
  (m : ℝ≥0∞) * regretGap E (0,0)

private theorem finalValue_le (E : Environment) (hE : OnUnit E) (m : ℕ) (a : Unit) :
    finalValue E m a ≤ (m : ℝ≥0∞) * ENNReal.ofReal (muStar E) :=
  mul_le_mul' le_rfl (regretGap_le E hE (0,0) zero_mem_triT)

private theorem toPolicy_bound (T : ℕ) (p : Ω → Program Unit) (hp : MeasurableFamily p)
    (hl : ∀ ω, Legal triT (p ω)) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (E : Environment) (hE : OnUnit E) :
    (toPolicy T p hp hl).OneBit ∧
      ∀ a ∈ BilateralProfitMHR.unitSq,
        (toPolicy T p hp hl).regret Q E.prior a ≤
          (∫⁻ s, (p s).value (P E) (regretGap E) T (finalValue E) ∂Q).toReal := by
  let := (BilateralProfitMHR.positive_density_profit_facts E hE).1
  have hb := BilateralProfitMHR.binary_controller_regret_bridge T Q E.prior
    (fun _ => legalAct) (fun _ => legalStep) (fun ω => ⟨p ω, hl ω⟩)
    (fun _ => legalAct_mem) (legalRun_measurable p hp hl)
  refine ⟨listPolicy_oneBit _ hb.1, ?_⟩
  intro a ha
  rw [toPolicy, listPolicy_regret]
  have h := hb.2 (muStar E) (fun _ s => mu_le_muStar E hE (legalAct_mem s))
    a (mu_le_muStar E hE ha)
  simp only [legalBinaryValue_eq] at h
  refine h.trans_eq ?_
  congr 1
  apply lintegral_congr
  intro ω
  exact binaryValue_eq_value (P E) (regretGap E) (onUnit_facts E hE).1 (p ω) T

private theorem value_play (E : Environment) (hE : OnUnit E) (x : ℝ × ℝ) (n : ℕ)
    (finish : ℕ → Unit → ℝ≥0∞) :
    (play x).value (P E) (regretGap E) n finish = (n : ℝ≥0∞) * regretGap E x := by
  induction n with
  | zero => simp [play, value]
  | succ n ih =>
    have he : ENNReal.ofReal (P E x) + ENNReal.ofReal (1 - P E x) = 1 := by
      rw [← ENNReal.ofReal_add ((onUnit_facts E hE).1 x).1
        (sub_nonneg.mpr ((onUnit_facts E hE).1 x).2)]
      simp
    have ha (b : Bool) : (play x).after b = play x := rfl
    simp only [value, play, Sum.elim_inr, ha]
    rw [ih, ← add_mul, he, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm]

end Program

namespace RandomProgram

variable {I : Type} [MeasurableSpace I]

private def play (x : I → ℝ × ℝ) (hm : Measurable x) (hl : ∀ i, x i ∈ triT) :
    RandomProgram I Unit where
  Seed := Unit
  seedSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance
  run s := Program.play (x s.1)
  measurable_run _ := measurable_inr.comp (hm.comp measurable_fst)
  legal s h a ha := by simpa [Program.play] using (show a ∈ triT from (Sum.inr.inj ha) ▸ hl s.1)

private theorem expected_play (x : I → ℝ × ℝ) (hm : Measurable x) (hl : ∀ i, x i ∈ triT)
    (E : Environment) (hE : OnUnit E) (i : I) (n : ℕ) (finish : ℕ → Unit → ℝ≥0∞) :
    (play x hm hl).expected E i n finish = (n : ℝ≥0∞) * regretGap E (x i) := by
  change (∫⁻ (_ : Unit), (Program.play (x i)).value (P E) (regretGap E) n finish
    ∂Measure.dirac ()) = _
  rw [Program.value_play E hE, lintegral_const]
  simp

end RandomProgram

private theorem common_seed_policy (B : ℕ → ℝ) (hB : ∀ T, 2 ≤ T → 0 ≤ B T)
    (h : ∀ T : ℕ, 2 ≤ T → ∃ p : RandomProgram Unit Unit,
      ∀ E : Environment, RegularUnit E →
        p.expected E () T (Program.finalValue E) ≤ ENNReal.ofReal (B T)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω), IsProbabilityMeasure Q ∧
      ∃ π : (T : ℕ) → Policy T Ω, (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ BilateralProfitMHR.unitSq, (π T).regret Q E.prior a ≤ B T := by
  classical
  have hall (T : ℕ) : ∃ p : RandomProgram Unit Unit,
      2 ≤ T → ∀ E : Environment, RegularUnit E →
        p.expected E () T (Program.finalValue E) ≤ ENNReal.ofReal (B T) := by
    by_cases hT : 2 ≤ T
    · obtain ⟨p, hp⟩ := h T hT
      exact ⟨p, fun _ => hp⟩
    · exact ⟨RandomProgram.pure id measurable_id, fun h' => (hT h').elim⟩
  choose p hp using hall
  let Ω := (T : ℕ) → (p T).Seed
  let Q : Measure Ω := Measure.infinitePi (fun T => (p T).law)
  let r (T : ℕ) (ω : Ω) := (p T).run ((), ω T)
  have hm (T : ℕ) : Program.MeasurableFamily (r T) := fun h =>
    ((p T).measurable_run h).comp (measurable_const.prodMk (measurable_pi_apply T))
  have hl (T : ℕ) (ω : Ω) : Program.Legal triT (r T ω) := (p T).legal ((), ω T)
  let π (T : ℕ) := Program.toPolicy T (r T) (hm T) (hl T)
  refine ⟨Ω, inferInstance, Q, inferInstance, π, ?_, ?_⟩
  · intro T
    exact Program.toPolicy_oneBit T (r T) (hm T) (hl T)
  · intro T hT E hE a ha
    have hb := (Program.toPolicy_bound T (r T) (hm T) (hl T) Q E hE.1).2 a ha
    have he := (measurePreserving_eval_infinitePi (fun T => (p T).law) T).lintegral_comp
      (Program.measurable_value (measurable_P E hE.1) (measurable_regretGap E hE.1)
        (p := fun ω => (p T).run ((), ω))
        (fun h => ((p T).measurable_run h).comp (measurable_const.prodMk measurable_id)) T
        (finish := fun m v => Program.finalValue E m v.2) (fun _ => measurable_const))
    change (∫⁻ ω, (r T ω).value (P E) (regretGap E) T (Program.finalValue E) ∂Q) =
      (p T).expected E () T (Program.finalValue E) at he
    rw [he] at hb
    exact hb.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hp T hT E hE)).trans_eq
      (ENNReal.toReal_ofReal (hB T hT)))

end BilateralProfitRegular
end
end BundlePart056


section BundlePart057




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem started_phase_count_pos (C₀ : ℝ) (T : ℕ) : 0 < startedPhaseCount C₀ T := by
  unfold startedPhaseCount
  split <;> omega

private def lastPhase (T : ℕ) : StartedPhase T :=
  ⟨startedPhaseCount startedC₀ T - 1, by have := started_phase_count_pos startedC₀ T; omega⟩

private def firstActive (T : ℕ) (δ : ℝ) (cs : List Candidate)
    (H : MainScheduleHistory cs.length) : Option (Fin cs.length) :=
  mainPhaseMin (mainPhaseTimeline (mainEta T) δ cs H (lastPhase T)).1

private theorem measurable_firstActive (T : ℕ) (δ : ℝ) (cs : List Candidate) :
    Measurable (firstActive T δ cs) :=
  measurable_mainPhaseMin.comp (measurable_mainPhaseActive _ _ _ _)

/-- The first active candidate in the last phase reachable within the horizon.
Its refinement cannot finish during the horizon. -/
private def lastPhaseProgram (T : ℕ) (δ : ℝ) (cs : List Candidate) :
    RandomProgram (MainScheduleHistory cs.length) (MainScheduleHistory cs.length) :=
  RandomProgram.select (startedJob (δ := δ) (cs := cs) (lastPhase T))
    (firstActive T δ cs) (measurable_firstActive T δ cs)

/-- Execute the successive-elimination program for the bounded physical horizon.
Phases beyond the first phase with a copy longer than the horizon are unreachable. -/
private def startedTriggered (T : ℕ) (δ : ℝ) (cs : List Candidate) : RandomProgram Unit Unit :=
  let jobs := startedJob (T := T) (δ := δ) (cs := cs)
  let pre := mainSchedulePrefix jobs (lastPhase T).val (lastPhase T).isLt.le
  let run := pre.thenState (lastPhaseProgram T δ cs)
  (run.bind (RandomProgram.pure (fun _ => ()) measurable_const)).compInput
    (fun _ => mainEmptyScheduleHistory cs.length) measurable_const

private theorem lastPhase_expected_le {T : ℕ} {δ : ℝ} {cs : List Candidate}
    (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T)
    (hInit : InitGuarantee E (mainEta T) δ cs)
    (H : MainScheduleHistory cs.length)
    (hClean : MainPhaseClean E (mainEta T) δ cs H (lastPhase T))
    (r : ℕ) (hr : r ≤ T) (f : ℕ → MainScheduleHistory cs.length → ℝ≥0∞)
    (hf : ∀ m, Measurable (f m)) :
    (lastPhaseProgram T δ cs).expectedCost E (startedGap T E) H r f ≤
      startedBudget (numCopies startedC₀ T) (startedRunMax startedC₀ T)
        (startedCopyCoefficient T) (startedJobOverhead T) cs.length r := by
  let j := lastPhase T
  let s := mainPhaseTimeline (mainEta T) δ cs H j
  have hNonempty : s.1.Nonempty :=
    (mainPhaseTimeline_from_init hE hT hInit H j hClean).1
  obtain ⟨i, hi, hfirst⟩ := mainPhaseMin_exists hNonempty
  let p := startedJob (δ := δ) (cs := cs) j i
  have heq : (lastPhaseProgram T δ cs).expectedCost E (startedGap T E) H r f =
      p.expectedCost E (startedGap T E) H r f :=
    RandomProgram.expectedCost_select_some (startedJob (δ := δ) (cs := cs) j)
      (firstActive T δ cs) (measurable_firstActive T δ cs) E hE.1 _
      (measurable_startedGap T E hE.1) (h := H) hfirst r hf
  have hlong : T < phaseLen startedC₀ T j := (startedPhaseCount_spec hT startedC₀_pos).2.1
  have hmin : T < numCopies startedC₀ T * phaseLen startedC₀ T j :=
    hlong.trans_le (by
      have hm : 1 ≤ numCopies startedC₀ T := startedCopies_pos hT
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (phaseLen startedC₀ T j) hm)
  rw [heq]
  have hzero : p.expectedCost E (startedGap T E) H r f =
      p.expectedCost E (startedGap T E) H r (fun _ _ => 0) := by
    apply lintegral_congr
    intro ω
    exact Program.value_eq_minQueries (startedJob_minQueries j i H hi ω) _ _ r
      (fun m hm _ => (by omega : False).elim)
  rw [hzero]
  have hPartial : MainPartialClean E (mainEta T) δ cs j i.val H := by
    refine ⟨hClean, ?_⟩
    intro l hl hli
    have hm := Finset.min'_le s.1 l hl
    have hMin : s.1.min' hNonempty = i := by
      simpa [mainPhaseMin, hNonempty] using hfirst
    rw [hMin] at hm
    exact (Nat.not_lt_of_ge hm hli).elim
  have hjob := startedJob_bound j i E hE hT hInit H hPartial r hr (fun _ _ => 0)
    (fun _ => measurable_const) (fun _ _ _ => bot_le) 0 0 (fun _ _ _ _ => bot_le)
  rw [zero_add, add_zero] at hjob
  exact hjob.trans (startedBudget_mono ((Nat.zero_le i.val).trans_lt i.isLt) le_rfl)

private theorem startedTriggered_expected_le {T : ℕ} {δ : ℝ} {cs : List Candidate}
    (E : Environment) (hE : RegularUnit E) (hT : 2 ≤ T)
    (hInit : InitGuarantee E (mainEta T) δ cs) (n : ℕ) (hn : n ≤ T) :
    (startedTriggered T δ cs).expectedCost E (startedGap T E) () n (Program.finalValue E) ≤
      startedBudget (numCopies startedC₀ T) (startedRunMax startedC₀ T)
        (startedCopyCoefficient T) (startedJobOverhead T)
        (startedPhaseCount startedC₀ T * cs.length) n := by
  let J := startedPhaseCount startedC₀ T
  let j := lastPhase T
  let H₀ := mainEmptyScheduleHistory cs.length
  let q := lastPhaseProgram T δ cs
  let f := fun m (_ : MainScheduleHistory cs.length) => Program.finalValue E m ()
  let g := startedGap T E
  have hg := measurable_startedGap T E hE.1
  have hg1 := startedGap_le_one hT E hE.1
  have hf (m : ℕ) : Measurable (f m) := measurable_const
  have hμ := ENNReal.ofReal_le_one.mpr (onUnit_facts E hE.1).2.2.2.1.2
  have hft (m : ℕ) (H : MainScheduleHistory cs.length) : f m H ≤ (m : ℝ≥0∞) :=
    (Program.finalValue_le E hE.1 m ()).trans ((mul_le_mul' le_rfl hμ).trans_eq (mul_one _))
  have hfFinal (m : ℕ) : Measurable (Program.finalValue E m) := measurable_const
  rw [startedTriggered, RandomProgram.expectedCost_compInput,
    RandomProgram.expectedCost_bind _ _ E hE.1 _ hg _ _ hfFinal]
  simp_rw [RandomProgram.expectedCost_pure]
  rw [RandomProgram.expectedCost_thenState _ _ E hE.1 _ hg _ _ (finish := f) hf]
  have hb := mainSchedulePrefix_started_clean_bound
    (startedJob (T := T) (δ := δ) (cs := cs)) hE.1 g hg hg1
    (startedCopyCoefficient T) (startedJobOverhead T)
    (fun j i => startedJob_bound j i E hE hT hInit) j.val j.isLt.le
  have hRun := hb H₀ trivial n hn (fun m h => q.expectedCost E g h m f)
    (fun m => q.measurable_expectedCost E hE.1 g hg m hf) (by
      intro m _ h
      simpa only [mul_one] using q.expectedCost_le_time E hE.1 g h m 1 hg1
        (fun t _ h' => by simpa only [mul_one] using hft t h'))
    cs.length 0 (fun m hm h hh => by
      simpa only [add_zero] using lastPhase_expected_le E hE hT hInit h hh m (hm.trans hn) f hf)
  rw [add_zero] at hRun
  have heq : cs.length + (j : ℕ) * cs.length = J * cs.length := by
    calc
      _ = (1 + (j : ℕ)) * cs.length := by rw [Nat.add_mul, one_mul]
      _ = _ := by
        congr 1
        have hp := started_phase_count_pos startedC₀ T
        change 1 + (J-1) = J
        omega
  rw [heq] at hRun
  exact hRun

end BilateralProfitRegular
end
end BundlePart057


section BundlePart058



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory
open scoped ENNReal

private def startedTriggerConstant (C₀ Ccount Ccal Ccopy : ℝ) : ℝ :=
  3 * Ccal * Ccount +
    Ccopy * Real.sqrt (3 * Ccount * (C₀ + 1) * (1 + startedRunFactor C₀)) +
    6 * Ccount

private theorem startedTriggerConstant_nonneg {C₀ Ccount Ccal Ccopy : ℝ}
    (hCount : 0 ≤ Ccount) (hCal : 0 ≤ Ccal) (hCopy : 0 ≤ Ccopy) :
    0 ≤ startedTriggerConstant C₀ Ccount Ccal Ccopy := by
  unfold startedTriggerConstant
  positivity

private theorem started_trigger_budget_le {C₀ Ccount Ccal Ccopy δ : ℝ} {T N n : ℕ}
    (hT : 2 ≤ T) (hC₀ : 0 < C₀) (hCount : 0 ≤ Ccount)
    (hCal : 0 ≤ Ccal) (hCopy : 0 ≤ Ccopy) (hδ₁ : δ ≤ 1)
    (hN : (N : ℝ) ≤ Ccount * Real.sqrt (δ / mainEta T) * mainLog T) (hn : n ≤ T) :
    startedBudget (numCopies C₀ T) (startedRunMax C₀ T)
      (ENNReal.ofReal (Ccopy * mainLog T^2))
      (ENNReal.ofReal (Ccal * mainLog T / mainEta T) + 2)
      (startedPhaseCount C₀ T * N) n ≤
    ENNReal.ofReal (startedTriggerConstant C₀ Ccount Ccal Ccopy * startedRate T) := by
  let J := startedPhaseCount C₀ T
  let M := numCopies C₀ T
  let B := startedRunMax C₀ T
  let a := Ccopy * mainLog T^2
  let cal := Ccal * mainLog T / mainEta T
  let S := Real.sqrt (((J * N * M : ℕ) : ℝ) * ((T+B : ℕ) : ℝ))
  have ha : 0 ≤ a := mul_nonneg hCopy (sq_nonneg _)
  have hcal : 0 ≤ cal := div_nonneg (mul_nonneg hCal (zero_le_one.trans (mainLog_ge_one hT)))
    (mainEta_pos hT).le
  have hcal₂ : 0 ≤ cal + 2 := by linarith
  have hnat : (0 : ℝ) ≤ (J*N : ℕ) := Nat.cast_nonneg _
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine (startedBudget_mono (k := J*N) le_rfl hn).trans ?_
  change ENNReal.ofReal a * ENNReal.ofReal S +
      ((J*N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal cal + 2) ≤ _
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [← htwo, ← ENNReal.ofReal_add hcal (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hnat,
    ← ENNReal.ofReal_add (mul_nonneg ha hS) (mul_nonneg hnat hcal₂)]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨hc, hcopy, hfail⟩ := started_budget_bounds hT hC₀ hCount hδ₁ hN
  change (N : ℝ) * J * (mainLog T / mainEta T) ≤ _ at hc
  change Real.sqrt (((N * J * M : ℕ) : ℝ) * ((T+B : ℕ) : ℝ)) * mainLog T^2 ≤ _ at hcopy
  change 2 * (N : ℝ) * J ≤ _ at hfail
  have he : a * S + ((J*N : ℕ) : ℝ) * (cal + 2) =
      Ccal * ((N : ℝ) * J * (mainLog T / mainEta T)) +
      Ccopy * (Real.sqrt (((N * J * M : ℕ) : ℝ) * ((T+B : ℕ) : ℝ)) * mainLog T^2) +
      2 * (N : ℝ) * J := by
    dsimp only [a, S, cal]
    rw [Nat.mul_comm J N]
    push_cast
    ring
  rw [he, startedTriggerConstant, add_mul, add_mul]
  exact add_le_add
    (add_le_add (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hc hCal)
      (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hcopy hCopy)) hfail

private theorem started_noTrigger_rate {T : ℕ} (hT : 2 ≤ T) :
    (T : ℝ) / (gridK (mainEta T) : ℝ) ≤ startedRate T := by
  have he := mainEta_pos hT
  have hg : 1 / mainEta T ≤ (gridK (mainEta T) : ℝ) := Nat.le_ceil _
  have hk : 0 < (gridK (mainEta T) : ℝ) := (one_div_pos.mpr he).trans_le hg
  have hi : 1 / (gridK (mainEta T) : ℝ) ≤ mainEta T := by
    apply (div_le_iff₀ hk).mpr
    rw [mul_comm]
    exact (div_le_iff₀ he).mp hg
  rw [div_eq_mul_one_div]
  exact (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg T)).trans (started_eta_rate hT)

private theorem started_total_budget_le {Cinit Cbase D : ℝ} {T : ℕ}
    (hT : 2 ≤ T) (hInit : 0 ≤ Cinit) (hBase : 0 ≤ Cbase) (hD : 0 ≤ D) :
    (T : ℝ≥0∞) * ENNReal.ofReal (Cbase * mainEta T) +
      (ENNReal.ofReal (Cinit * (gridK (mainEta T) : ℝ) * Real.log (T : ℝ)^2) +
        ENNReal.ofReal (Cinit * (T : ℝ) / gridK (mainEta T)) +
        ENNReal.ofReal (D * startedRate T) + 1) ≤
    ENNReal.ofReal ((Cbase + 3*Cinit + D + 1) * startedRate T) := by
  let R := startedRate T
  have hR : 0 ≤ R := zero_le_one.trans (one_le_startedRate hT)
  have hI : Cinit * (gridK (mainEta T) : ℝ) * Real.log (T : ℝ)^2 ≤ 2 * Cinit * R := by
    rw [mul_assoc, mul_comm (2 : ℝ) Cinit, mul_assoc]
    exact mul_le_mul_of_nonneg_left (started_init_rate hT) hInit
  have hN : Cinit * (T : ℝ) / gridK (mainEta T) ≤ Cinit * R := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (started_noTrigger_rate hT) hInit
  have hB : (T : ℝ) * (Cbase * mainEta T) ≤ Cbase * R := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (started_eta_rate hT) hBase
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
  have hOne : (1 : ℝ≥0∞) ≤ ENNReal.ofReal R := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (one_le_startedRate hT)
  refine (add_le_add (ENNReal.ofReal_le_ofReal hB)
    (add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hI)
      (ENNReal.ofReal_le_ofReal hN)) (le_refl (ENNReal.ofReal (D * R)))) hOne)).trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * Cinit * R) (mul_nonneg hInit hR),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * Cinit * R + Cinit * R) (mul_nonneg hD hR),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * Cinit * R + Cinit * R + D * R) hR,
    ← ENNReal.ofReal_add (mul_nonneg hBase hR) (by positivity)]
  congr 1
  change Cbase * R + (2 * Cinit * R + Cinit * R + D * R + R) = (Cbase + 3*Cinit + D + 1) * R
  ring

private theorem startedRate_le_log_pow {T : ℕ} (hT : 2 ≤ T) :
    startedRate T ≤ 16 * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^((7 : ℝ)/2) := by
  have hlog : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
  have hbase : 0 ≤ (T : ℝ)^((3 : ℝ)/5) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpow : (2 : ℝ)^((7 : ℝ)/2) ≤ 16 := by
    calc
      _ ≤ (2 : ℝ)^(4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 16 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  unfold startedRate
  calc
    _ ≤ (T : ℝ)^((3 : ℝ)/5) * (2 * Real.log (T : ℝ))^((7 : ℝ)/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans (mainLog_ge_one hT))
        (mainLog_le_two_log hT) (by norm_num)) hbase
    _ = (2 : ℝ)^((7 : ℝ)/2) * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^((7 : ℝ)/2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlog]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hbase)
      (Real.rpow_nonneg hlog _)

private theorem startedRate_le_final {T : ℕ} (hT : 2 ≤ T) :
    startedRate T ≤ 32 * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^5 := by
  refine (show startedRate T ≤ mainBudget T from ?_).trans (mainBudget_le_final hT)
  unfold startedRate mainBudget
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (mainLog_ge_one hT) (by norm_num)

end BilateralProfitRegular
end
end BundlePart058


section BundlePart059


set_option autoImplicit false

namespace BilateralProfitMHR

private theorem bisectAux_bounds (f m M : ℕ) (hmM : m ≤ M) (I : ℕ × ℕ)
    (hI : I ∈ bisectAux f m M) : m ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ M := by
  induction f generalizing m M with
  | zero =>
    have : I = (m, M) := by simpa [bisectAux] using hI
    subst I
    exact ⟨le_rfl, hmM, le_rfl⟩
  | succ f ih =>
    by_cases hlt : m < M
    · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union] at hI
      rcases hI with rfl | hI | hI
      · exact ⟨le_rfl, hmM, le_rfl⟩
      · have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        obtain ⟨h1, h2, h3⟩ := ih m ((m + M) / 2) hmid.1 hI
        exact ⟨h1, h2, h3.trans hmid.2.le⟩
      · have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        obtain ⟨h1, h2, h3⟩ := ih ((m + M) / 2 + 1) M (by omega) hI
        exact ⟨by omega, h2, h3⟩
    · have : I = (m, M) := by simpa [bisectAux, hlt] using hI
      subst I
      exact ⟨le_rfl, hmM, le_rfl⟩

private theorem sPairsOf_bounds (I e : ℕ × ℕ) (hI : I.1 ≤ I.2) (he : e ∈ sPairsOf I) :
    I.1 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ I.2 := by
  have hmid : I.1 ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 ≤ I.2 := by omega
  simp only [sPairsOf, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Icc] at he
  rcases he with ⟨r, ⟨hr, hrk⟩, rfl⟩ | ⟨r, ⟨hr, hkr⟩, rfl⟩
  · exact ⟨hr.1, hrk, hmid.2⟩
  · exact ⟨hmid.1, hkr.le, hr.2⟩

private theorem Spairs_bounds {K : ℕ} {e : ℕ × ℕ} (he : e ∈ Spairs K) :
    e.1 ≤ e.2 ∧ e.2 ≤ K := by
  obtain ⟨I, hI, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨h1, h2, h3⟩ := bisectAux_bounds (K + 1) 0 K (by omega) I hI
  obtain ⟨_, h4, h5⟩ := sPairsOf_bounds I e h2 he
  exact ⟨h4, h5.trans h3⟩

private theorem sepMidAux_interval (f i j m M : ℕ) (hmi : m ≤ i) (hij : i < j)
    (hjM : j ≤ M) (hf : M - m < f) :
    ∃ I ∈ bisectAux f m M,
      I.1 ≤ i ∧ j ≤ I.2 ∧ i ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 < j ∧
      sepMidAux f i j m M = (I.1 + I.2) / 2 := by
  induction f generalizing m M with
  | zero => omega
  | succ f ih =>
    have hlt : m < M := by omega
    have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
    by_cases hj : j ≤ (m + M) / 2
    · obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
        ih m ((m + M) / 2) hmi hj (by omega)
      refine ⟨I, ?_, h1, h2, h3, h4, ?_⟩
      · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hI)
      · simpa only [sepMidAux, hlt, hj, ↓reduceIte] using h5
    · by_cases hi : (m + M) / 2 < i
      · obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
          ih ((m + M) / 2 + 1) M (by omega) hjM (by omega)
        refine ⟨I, ?_, h1, h2, h3, h4, ?_⟩
        · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr hI)
        · simpa only [sepMidAux, hlt, hj, hi, ↓reduceIte] using h5
      · refine ⟨(m, M), ?_, hmi, hjM, by omega, by omega, ?_⟩
        · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, true_or]
        · simp only [sepMidAux, hlt, hj, hi, ↓reduceIte]

private theorem sepMid_spec {K i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    i ≤ sepMid K i j ∧ sepMid K i j < j ∧
      (i, sepMid K i j) ∈ Spairs K ∧ (sepMid K i j, j) ∈ Spairs K ∧
      (sepMid K i j, sepMid K i j) ∈ Spairs K := by
  obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
    sepMidAux_interval (K + 1) i j 0 K (by omega) hij hjK (by omega)
  change sepMid K i j = (I.1 + I.2) / 2 at h5
  rw [h5]
  have hmid : I.1 ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 ≤ I.2 := by omega
  refine ⟨h3, h4, ?_, ?_, ?_⟩
  all_goals apply Finset.mem_biUnion.mpr; refine ⟨I, hI, ?_⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, h3⟩, rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h2⟩, h4⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨(I.1 + I.2) / 2,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hmid, le_rfl⟩, rfl⟩

private theorem bisectAux_self (f m : ℕ) : bisectAux f m m = {(m, m)} := by
  cases f <;> simp [bisectAux]

private theorem init_sum_insert_le {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (w : α → ℕ) : ∑ i ∈ insert a s, w i ≤ w a + ∑ i ∈ s, w i := by
  by_cases h : a ∈ s
  · simp [Finset.insert_eq_of_mem h]
  · rw [Finset.sum_insert h]

private theorem init_sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α)
    (w : α → ℕ) : ∑ i ∈ s ∪ t, w i ≤ (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := w)
  omega

/-- At depth at most `d`, each level contributes at most the initial interval length. -/
private theorem bisectAux_total_size_le (d f m M : ℕ) (hmM : m ≤ M)
    (hsize : M - m + 1 ≤ 2 ^ d) :
    ∑ I ∈ bisectAux f m M, (I.2 - I.1 + 1) ≤ (M - m + 1) * (d + 1) := by
  induction d generalizing f m M with
  | zero =>
    have : M = m := by norm_num at hsize; omega
    subst M
    simp [bisectAux_self]
  | succ d ih =>
    by_cases heq : M = m
    · subst M
      simp [bisectAux_self]
    · have hlt : m < M := by omega
      cases f with
      | zero => simp [bisectAux]
      | succ f =>
        have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        have hsizeL : (m + M) / 2 - m + 1 ≤ 2 ^ d := by
          rw [pow_succ] at hsize
          omega
        have hsizeR : M - ((m + M) / 2 + 1) + 1 ≤ 2 ^ d := by
          rw [pow_succ] at hsize
          omega
        have hL := ih f m ((m + M) / 2) hmid.1 hsizeL
        have hR := ih f ((m + M) / 2 + 1) M (by omega) hsizeR
        rw [bisectAux, if_pos hlt]
        apply (init_sum_insert_le _ _ _).trans
        apply (Nat.add_le_add_left (init_sum_union_le _ _ _) _).trans
        apply (Nat.add_le_add_left (Nat.add_le_add hL hR) _).trans
        simp only [Prod.fst, Prod.snd]
        have hpart : (m + M) / 2 - m + 1 + (M - ((m + M) / 2 + 1) + 1) = M - m + 1 := by
          omega
        nlinarith

private theorem sPairsOf_card_le (I : ℕ × ℕ) : (sPairsOf I).card ≤ I.2 - I.1 + 1 := by
  let F := Finset.Icc I.1 I.2
  have hpart := Finset.card_filter_add_card_filter_not (s := F)
    (p := fun r => r ≤ (I.1 + I.2) / 2)
  have hcard : F.card ≤ I.2 - I.1 + 1 := by simp [F, Nat.card_Icc]; omega
  unfold sPairsOf
  apply (Finset.card_union_le _ _).trans
  apply (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans
  change (F.filter (fun r => r ≤ (I.1 + I.2) / 2)).card +
    (F.filter (fun r => (I.1 + I.2) / 2 < r)).card ≤ _
  simpa only [not_le] using hpart.le.trans hcard

private theorem Spairs_card_le (K : ℕ) :
    (Spairs K).card ≤ (K + 1) * (Nat.clog 2 (K + 1) + 1) := by
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun I _ => sPairsOf_card_le I)).trans
  have h := bisectAux_total_size_le (Nat.clog 2 (K + 1)) (K + 1) 0 K (by omega)
    (by simpa using Nat.le_pow_clog (by omega : 1 < 2) (K + 1))
  simpa only [Nat.sub_zero, bisect] using h

end BilateralProfitMHR
end BundlePart059


section BundlePart060



namespace BilateralProfitRegular

private theorem bisect_toFinset (f m M : ℕ) :
    (bisect f m M).toFinset = BilateralProfitMHR.bisectAux f m M := by
  induction f generalizing m M with
  | zero => simp [bisect, BilateralProfitMHR.bisectAux]
  | succ f ih =>
    by_cases h : m < M <;> simp [bisect, BilateralProfitMHR.bisectAux, h, ih]

private theorem sampledPairs_toFinset (I : ℕ × ℕ) :
    (sampledPairs I).toFinset = BilateralProfitMHR.sPairsOf I := by
  ext e
  simp only [sampledPairs, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq, BilateralProfitMHR.sPairsOf, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨r, ⟨hr, hr'⟩, he⟩
    split at he <;> rename_i h
    · exact Or.inl ⟨r, ⟨⟨hr', by omega⟩, h⟩, he⟩
    · exact Or.inr ⟨r, ⟨⟨hr', by omega⟩, by omega⟩, he⟩
  · rintro (⟨r, ⟨⟨hr', hr⟩, h⟩, rfl⟩ | ⟨r, ⟨⟨hr', hr⟩, h⟩, rfl⟩)
    · exact ⟨r, ⟨by omega, hr'⟩, if_pos h⟩
    · exact ⟨r, ⟨by omega, hr'⟩, if_neg (Nat.not_le.mpr h)⟩

private theorem sampleSet_eq_MHR (K : ℕ) : sampleSet K = BilateralProfitMHR.Spairs K := by
  ext e
  simp only [sampleSet, List.mem_toFinset, List.mem_flatMap, BilateralProfitMHR.Spairs, Finset.mem_biUnion]
  simp_rw [← List.mem_toFinset]
  simp only [bisect_toFinset, sampledPairs_toFinset, BilateralProfitMHR.bisect]

private theorem sampleSet_bounds {K : ℕ} {e : ℕ × ℕ} (he : e ∈ sampleSet K) :
    e.1 ≤ e.2 ∧ e.2 ≤ K :=
  BilateralProfitMHR.Spairs_bounds (sampleSet_eq_MHR K ▸ he)

private theorem sepMid_eq_aux {f m M i j : ℕ} (hm : m ≤ i) (hij : i < j) (hM : j ≤ M) (hf : M - m + 1 ≤ f) :
    sepMid f m M i j = BilateralProfitMHR.sepMidAux f i j m M := by
  induction f generalizing m M with
  | zero => omega
  | succ f ih =>
    have hstrict : m < M := by omega
    simp only [sepMid, BilateralProfitMHR.sepMidAux, hstrict, if_true]
    split
    · rename_i hj
      exact ih hm hj (by omega)
    · split
      · rename_i hi
        exact ih (Nat.succ_le_of_lt hi) hM (by omega)
      · rfl

private theorem sepMid_spec {K i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    let k := sepMid (K + 1) 0 K i j
    i ≤ k ∧ k < j ∧ (i, k) ∈ sampleSet K ∧ (k, j) ∈ sampleSet K ∧ (k, k) ∈ sampleSet K := by
  simpa only [sepMid_eq_aux (Nat.zero_le i) hij hjK (by omega : K - 0 + 1 ≤ K + 1), sampleSet_eq_MHR,
    BilateralProfitMHR.sepMid] using BilateralProfitMHR.sepMid_spec hij hjK

private theorem sampleSet_diagonal {K i : ℕ} (hi : i < K) : (i, i) ∈ sampleSet K := by
  obtain ⟨hlo, hup, _, _, hmem⟩ := sepMid_spec (Nat.lt_succ_self i) (Nat.succ_le_of_lt hi)
  have he : sepMid (K + 1) 0 K i i.succ = i := by omega
  simpa only [he] using hmem

private theorem init_log_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ Real.log (2 * T) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  refine h4.trans (Real.log_le_log (by norm_num) ?_)
  have : (2 : ℝ) ≤ T := by exact_mod_cast hT
  linarith

private theorem sampleSet_real_card_le {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T) :
    ((sampleSet K).card : ℝ) ≤ 6 * K * Real.log (2 * T) := by
  rw [sampleSet_eq_MHR]
  have hT : 2 ≤ T := hK.trans hKT
  have hL := init_log_ge_one hT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2p : 0 < Real.log 2 := by linarith
  have hd : Nat.clog 2 (K + 1) ≤ Nat.log 2 (K + 1) + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by omega : 1 < 2) (K + 1)).le
  have hd' : (Nat.clog 2 (K + 1) : ℝ) ≤ (Nat.log 2 (K + 1) : ℝ) + 1 := by exact_mod_cast hd
  have hl := Real.natLog_le_logb (K + 1) 2
  rw [Real.logb] at hl
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hl
  have hlogKT : Real.log (K + 1) ≤ Real.log (2 * T) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : K + 1 ≤ 2 * T)
  have hdiv : Real.log (K + 1) / Real.log 2 ≤ 2 * Real.log (2 * T) := by
    apply (div_le_iff₀ hlog2p).2
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ Real.log (2 * T) by linarith)]
  have hdepth : (Nat.clog 2 (K + 1) : ℝ) + 1 ≤ 4 * Real.log (2 * T) := by linarith
  have hc : ((BilateralProfitMHR.Spairs K).card : ℝ) ≤
      (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := by
    exact_mod_cast BilateralProfitMHR.Spairs_card_le K
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  calc
    _ ≤ (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := hc
    _ ≤ (K + 1 : ℝ) * (4 * Real.log (2 * T)) := by gcongr
    _ ≤ 6 * K * Real.log (2 * T) := by nlinarith

end BilateralProfitRegular
end BundlePart060


section BundlePart061



namespace BilateralProfitRegular

private abbrev InitProbeIndex := Option ℕ × (ℕ × ℕ) × ℕ

private abbrev InitTapeUniforms := InitProbeIndex → unitInterval

/-- The values zero and one realize either feedback bit at the fixed decoding threshold. -/
private def initDecodeBits (bits : InitProbeIndex → Bool) : InitTapeUniforms :=
  fun i => if bits i then 0 else 1

private noncomputable def initUniformBits (K : ℕ) (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) :
    InitProbeIndex → Bool :=
  fun i => decide ((U i : ℝ) < prob (gpt K i.2.1))

private theorem initUniformBits_decode (K : ℕ) (bits : InitProbeIndex → Bool) :
    initUniformBits K (fun _ => 1 / 2) (initDecodeBits bits) = bits := by
  funext i
  rcases hb : bits i with _ | _ <;> norm_num [initUniformBits, initDecodeBits, hb]

/-- Within a stage the sampled pairs are processed in a fixed order, with all observations
of each pair taken consecutively. -/
private noncomputable def initProbeBlock (K : ℕ) (s : Option ℕ) (n : ℕ) : List InitProbeIndex :=
  (sampleSet K).toList.flatMap fun e => (List.range n).map fun m => (s, e, m)

private theorem mem_initProbeBlock {K : ℕ} {s : Option ℕ} {n : ℕ}
    {i : InitProbeIndex} :
    i ∈ initProbeBlock K s n ↔ i.1 = s ∧ i.2.1 ∈ sampleSet K ∧ i.2.2 < n := by
  rcases i with ⟨s', e, m⟩
  simp only [initProbeBlock, List.mem_flatMap, Finset.mem_toList, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨e', he, m', hm, rfl, rfl, rfl⟩
    exact ⟨rfl, he, hm⟩
  · rintro ⟨rfl, he, hm⟩
    exact ⟨e, he, m, hm, rfl, rfl, rfl⟩

private theorem initProbeBlock_nodup (K : ℕ) (s : Option ℕ) (n : ℕ) :
    (initProbeBlock K s n).Nodup := by
  unfold initProbeBlock
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro e _
    exact List.Nodup.map (fun a b h => congrArg (fun i : InitProbeIndex => i.2.2) h) List.nodup_range
  · apply List.Pairwise.imp (R := fun e e' : ℕ × ℕ => e ≠ e') _ (Finset.nodup_toList _)
    intro e e' hne
    simp only [Function.onFun, List.disjoint_left]
    intro i hi hi'
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hi
    obtain ⟨m', _, he⟩ := List.mem_map.mp hi'
    exact hne (congrArg (fun q : InitProbeIndex => q.2.1) he).symm

private theorem freq_congr_on_block {K : ℕ} {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    {s : Option ℕ} {n : ℕ} {e : ℕ × ℕ} (he : e ∈ sampleSet K)
    (h : ∀ idx ∈ initProbeBlock K s n, initUniformBits K prob U idx =
      initUniformBits K prob' U' idx) :
    freq K prob U s n e = freq K prob' U' s n e := by
  unfold freq
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have h' := h (s, e, m) (mem_initProbeBlock.mpr ⟨rfl, he, Finset.mem_range.mp hm⟩)
  unfold initUniformBits at h'
  split_ifs at * <;> simp_all

private theorem recon_congr_on_samples {K : ℕ} {F F' : ℕ × ℕ → ℝ} {i j : ℕ}
    (hij : i < j) (hjK : j ≤ K) (h : ∀ e ∈ sampleSet K, F e = F' e) :
    recon K F i j = recon K F' i j := by
  obtain ⟨_, _, hik, hkj, hkk⟩ := sepMid_spec hij hjK
  unfold recon
  rw [h _ hik, h _ hkj, h _ hkk]

private theorem mhrEst_congr_on_block {T K h : ℕ} {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    (hEq : ∀ idx ∈ initProbeBlock K (some h) (mhrRounds T h),
      initUniformBits K prob U idx = initUniformBits K prob' U' idx) (e : ℕ × ℕ) :
    mhrEst T K prob U h e = mhrEst T K prob' U' h e := by
  unfold mhrEst
  split_ifs with he
  · rw [recon_congr_on_samples he.2.1 (he.2.2.trans (Nat.sub_le ..))
      (fun _ hm => freq_congr_on_block hm hEq)]
  · rfl

private theorem phat_congr_on_block {T K : ℕ} {δ : ℝ} {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    (hEq : ∀ idx ∈ initProbeBlock K none (step2Rounds T δ),
      initUniformBits K prob U idx = initUniformBits K prob' U' idx) (e : ℕ × ℕ) :
    phat T K δ prob U e = phat T K δ prob' U' e := by
  rcases e with ⟨i, j⟩
  unfold phat
  split_ifs with he he'
  · exact recon_congr_on_samples he.2.1 (he.2.2.trans (Nat.sub_le ..))
      (fun _ hm => freq_congr_on_block hm hEq)
  · have hh : i = j := he'.1
    subst j
    exact freq_congr_on_block (sampleSet_diagonal (by obtain ⟨_,_,h⟩ := he'; omega)) hEq
  · rfl

private theorem mhrTriggers_congr_on_block {T K h : ℕ} {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    (he : ∀ idx ∈ initProbeBlock K (some h) (mhrRounds T h),
      initUniformBits K prob U idx = initUniformBits K prob' U' idx) :
    mhrTriggers T K prob U h ↔ mhrTriggers T K prob' U' h := by
  unfold mhrTriggers
  simp only [mhrEst_congr_on_block he]

private theorem candidates_congr_of_phat {T : ℕ} {η δ : ℝ} {ord : List (ℕ × ℕ)}
    {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    (hp : phat T (gridK η) δ prob U = phat T (gridK η) δ prob' U') :
    candidates T η δ ord prob U = candidates T η δ ord prob' U' := by
  have hm : muhat T (gridK η) δ prob U = muhat T (gridK η) δ prob' U' := by
    unfold muhat
    rw [hp]
  have hmstar : muhatStar T (gridK η) δ prob U = muhatStar T (gridK η) δ prob' U' := by
    unfold muhatStar
    rw [hm]
  have hpasses : passes T (gridK η) δ prob U = passes T (gridK η) δ prob' U' := by
    unfold passes
    rw [hm, hmstar, hp]
  have ha (x : ℕ × ℕ) (gs : List ((ℕ × ℕ) × List (ℕ × ℕ))) :
      addToGroups T (gridK η) δ prob U x gs =
        addToGroups T (gridK η) δ prob' U' x gs := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have hs : passes T (gridK η) δ prob U x g.1 ↔
          passes T (gridK η) δ prob' U' x g.1 :=
        Iff.of_eq (congrFun (congrFun hpasses x) g.1)
      by_cases hw : passes T (gridK η) δ prob U x g.1
      · simp only [addToGroups, if_pos hw, if_pos (hs.mp hw)]
      · simp only [addToGroups, if_neg hw, if_neg (hs.not.mp hw), ih]
  have hg : groups T (gridK η) δ ord prob U = groups T (gridK η) δ ord prob' U' := by
    simp only [groups, hmstar, hm, ha]
  unfold candidates
  rw [hg, hp]

private theorem candidates_congr_on_block {T : ℕ} {η δ : ℝ} {ord : List (ℕ × ℕ)}
    {prob prob' : ℝ × ℝ → ℝ} {U U' : InitTapeUniforms}
    (hEq : ∀ idx ∈ initProbeBlock (gridK η) none (step2Rounds T δ),
      initUniformBits (gridK η) prob U idx = initUniformBits (gridK η) prob' U' idx) :
    candidates T η δ ord prob U = candidates T η δ ord prob' U' :=
  candidates_congr_of_phat (funext (phat_congr_on_block hEq))

end BilateralProfitRegular
end BundlePart061


section BundlePart062



namespace BilateralProfitRegular

open scoped Classical

private abbrev InitTreeOutput := Option (ℝ × List Candidate)

private noncomputable def initCheckedScales (K : ℕ) : List ℕ :=
  (List.range (K + 1)).filter fun h => decide (2 ^ h ≤ K)

private theorem initCheckedScales_pairwise (K : ℕ) :
    (initCheckedScales K).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private theorem find_initCheckedScales_eq_mhrScale (T K : ℕ) (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) :
    (initCheckedScales K).find? (fun h => decide (mhrTriggers T K prob U h)) =
      mhrScale T K prob U := by
  classical
  unfold initCheckedScales mhrScale
  rw [List.find?_filter]
  congr 1
  funext h
  by_cases ht : mhrTriggers T K prob U h
  · simp [ht, ht.1]
  · simp [ht]

private noncomputable def initProbeTreeAux (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ)) :
    List ℕ → (InitProbeIndex → Bool) → ProbeTree InitProbeIndex InitTreeOutput
  | [], _ => .leaf none
  | h :: hs, acc =>
      let K := gridK η
      ProbeTree.readBlock (initProbeBlock K (some h) (mhrRounds T h)) acc fun tape =>
        if mhrTriggers T K (fun _ => 1 / 2) (initDecodeBits tape) h then
          if scale h < (2 : ℝ)^16 / (K : ℝ) then .leaf none
          else
            ProbeTree.readBlock (initProbeBlock K none (step2Rounds T (scale h))) tape
              fun tape' => .leaf (some (scale h,
                candidates T η (scale h) ord (fun _ => 1 / 2) (initDecodeBits tape')))
        else initProbeTreeAux T η ord hs tape

private noncomputable def initProbeTree (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ)) :
    ProbeTree InitProbeIndex InitTreeOutput :=
  initProbeTreeAux T η ord (initCheckedScales (gridK η)) (fun _ => false)

private noncomputable def initProbePath (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) : List ℕ → List InitProbeIndex × InitTreeOutput
  | [] => ([], none)
  | h :: hs =>
      let K := gridK η
      let block := initProbeBlock K (some h) (mhrRounds T h)
      if mhrTriggers T K prob U h then
        if scale h < (2 : ℝ)^16 / (K : ℝ) then (block, none)
        else (block ++ initProbeBlock K none (step2Rounds T (scale h)),
          some (scale h, candidates T η (scale h) ord prob U))
      else
        let next := initProbePath T η ord prob U hs
        (block ++ next.1, next.2)

private theorem initProbeTreeAux_eval (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) (stages : List ℕ) (acc : InitProbeIndex → Bool) :
    (initProbeTreeAux T η ord stages acc).eval (initUniformBits (gridK η) prob U) =
      initProbePath T η ord prob U stages := by
  classical
  induction stages generalizing acc with
  | nil => rfl
  | cons h hs ih =>
    let K := gridK η
    let bits := initUniformBits K prob U
    let block := initProbeBlock K (some h) (mhrRounds T h)
    let tape := ProbeTree.fillBits block acc bits
    have hsame : ∀ idx ∈ block,
        initUniformBits K (fun _ => 1 / 2) (initDecodeBits tape) idx = bits idx := by
      intro i hi
      rw [initUniformBits_decode]
      change ProbeTree.fillBits block acc bits i = bits i
      rw [ProbeTree.fillBits, if_pos hi]
    have hiff := mhrTriggers_congr_on_block hsame
    simp only [initProbeTreeAux, initProbePath, ProbeTree.readBlock_eval]
    try dsimp only
    change (block ++ _, _) =
      (if mhrTriggers T K prob U h then
        if scale h < (2 : ℝ)^16 / (K : ℝ) then (block, none)
        else (block ++ initProbeBlock K none (step2Rounds T (scale h)),
          some (scale h, candidates T η (scale h) ord prob U))
      else (block ++ (initProbePath T η ord prob U hs).1,
        (initProbePath T η ord prob U hs).2))
    dsimp only [K] at hiff ⊢
    dsimp only [tape, block, bits, K] at hiff
    by_cases htr : mhrTriggers T (gridK η) prob U h
    · have htr' := hiff.mpr htr
      simp only [if_pos htr, if_pos htr']
      by_cases hsmall : scale h < (2 : ℝ)^16 / (gridK η : ℝ)
      · simp only [if_pos hsmall, ProbeTree.eval, List.append_nil]
      · simp only [if_neg hsmall, ProbeTree.readBlock_eval, ProbeTree.eval, List.append_nil]
        congr 3
        apply candidates_congr_on_block
        intro i hi
        rw [initUniformBits_decode, ProbeTree.fillBits, if_pos hi]
    · have htr' := hiff.not.mpr htr
      simp only [if_neg htr', if_neg htr, ih]

private theorem initProbePath_output (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) (stages : List ℕ) :
    (initProbePath T η ord prob U stages).2 =
      match stages.find? (fun h => decide (mhrTriggers T (gridK η) prob U h)) with
      | none => none
      | some h => if scale h < (2 : ℝ)^16 / (gridK η : ℝ) then none
        else some (scale h, candidates T η (scale h) ord prob U) := by
  classical
  induction stages with
  | nil => rfl
  | cons h hs ih =>
    by_cases htr : mhrTriggers T (gridK η) prob U h
    · by_cases hsmall : scale h < (2 : ℝ)^16 / (gridK η : ℝ) <;>
        simp [initProbePath, htr, hsmall]
    · simp [initProbePath, htr, ih]

private theorem initProbeTree_output (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) :
    ((initProbeTree T η ord).eval (initUniformBits (gridK η) prob U)).2 =
      initRegular T η ord prob U := by
  rw [initProbeTree, initProbeTreeAux_eval, initProbePath_output, find_initCheckedScales_eq_mhrScale]
  rfl

private theorem initProbeTreeAux_valid (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (stages : List ℕ) (hnd : stages.Nodup) (acc : InitProbeIndex → Bool)
    (seen : Finset InitProbeIndex)
    (hfresh : ∀ idx ∈ seen, idx.1 ≠ none ∧ ∀ h ∈ stages, idx.1 ≠ some h) :
    ProbeTree.ValidSeen seen (initProbeTreeAux T η ord stages acc) := by
  classical
  induction stages generalizing seen acc with
  | nil => trivial
  | cons h hs ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnd
    simp only [initProbeTreeAux]
    apply ProbeTree.readBlock_valid _ _ _ _ (initProbeBlock_nodup _ _ _)
    · intro i hi hseen
      exact (hfresh i hseen).2 h (by simp) (mem_initProbeBlock.mp hi).1
    · intro tape
      by_cases htr : mhrTriggers T (gridK η) (fun _ => 1 / 2) (initDecodeBits tape) h
      · rw [if_pos htr]
        split_ifs with hsmall
        · trivial
        · apply ProbeTree.readBlock_valid _ _ _ _ (initProbeBlock_nodup _ _ _)
          · intro i hi' hin
            obtain hi' := (mem_initProbeBlock.mp hi').1
            rcases Finset.mem_union.mp hin with hin | hin
            · exact (hfresh i hin).1 hi'
            · have hi := (mem_initProbeBlock.mp (List.mem_toFinset.mp hin)).1
              rw [hi'] at hi
              cases hi
          · intro _
            trivial
      · rw [if_neg htr]
        apply ih hnodup
        intro i hin
        rcases Finset.mem_union.mp hin with hin | hin
        · exact ⟨(hfresh i hin).1, fun j hj => (hfresh i hin).2 j (List.mem_cons_of_mem _ hj)⟩
        · have hi := (mem_initProbeBlock.mp (List.mem_toFinset.mp hin)).1
          refine ⟨by rw [hi]; simp, ?_⟩
          intro j hj hj'
          have he := Option.some.inj (hi.symm.trans hj')
          exact hnot (he.symm ▸ hj)

private theorem initProbeTree_valid (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ)) :
    ProbeTree.ValidSeen ∅ (initProbeTree T η ord) := by
  unfold initProbeTree
  apply initProbeTreeAux_valid _ _ _ _ (initCheckedScales_pairwise _).nodup
  simp

end BilateralProfitRegular
end BundlePart062


section BundlePart063




namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal Classical

private theorem initTransport_gpt_coord_mem {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  exact ⟨div_nonneg (Nat.cast_nonneg _) hK'.le, (div_le_one hK').2 (by exact_mod_cast hi)⟩

private theorem initTransport_gpt_tri {K i j : ℕ} (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K) :
    gpt K (i, j) ∈ triT := by
  obtain ⟨hi0, _⟩ := initTransport_gpt_coord_mem hK (hij.trans hjK)
  obtain ⟨_, hj1⟩ := initTransport_gpt_coord_mem hK hjK
  exact ⟨hi0, div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg _), hj1⟩

private theorem initTransport_gpt_profit_nonneg {K i j : ℕ} (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K)
    (E : Environment) (hE : OnUnit E) :
    0 ≤ mu E (gpt K (i, j)) := by
  rw [mu_formula]
  exact mul_nonneg (sub_nonneg.mpr (initTransport_gpt_tri hK hij hjK).2.1) ((onUnit_facts E hE).1 _).1

private theorem initTransport_triT_subset_unitSq : triT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1, hx.2.1.trans hx.2.2⟩, ⟨hx.1.trans hx.2.1, hx.2.2⟩⟩

private theorem initProbeBlock_sum (K : ℕ) (s : Option ℕ) (n : ℕ) (f : ℕ × ℕ → ℝ) :
    ((initProbeBlock K s n).map (fun idx => f idx.2.1)).sum =
      (n : ℝ) * (∑ e ∈ sampleSet K, f e) := by
  unfold initProbeBlock
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten]
  simp only [List.map_map]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp [Function.comp_def, List.map_const']

private noncomputable def initProbePrefix (needle : ℕ → Bool) (stages : List ℕ) : List ℕ :=
  stages.filter fun j => decide (∀ h ∈ stages.find? needle, j ≤ h)

private theorem nth_checked_eq_testedScales (T K : ℕ) (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) :
    initProbePrefix (fun h => decide (mhrTriggers T K prob U h)) (initCheckedScales K) =
      testedScales T K prob U := by
  unfold initProbePrefix
  rw [find_initCheckedScales_eq_mhrScale]
  simp only [initCheckedScales, testedScales, List.filter_filter]
  congr 1
  funext j
  by_cases hK : 2 ^ j ≤ K <;>
    by_cases hL : ∀ h' ∈ mhrScale T K prob U, j ≤ h' <;> simp [hK, hL]

private theorem initProbePath_cost (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) (f : ℕ × ℕ → ℝ) (stages : List ℕ)
    (hnd : stages.Pairwise (· < ·)) :
    let K := gridK η
    let g := ∑ e ∈ sampleSet K, f e
    let p := fun h => decide (mhrTriggers T K prob U h)
    ((initProbePath T η ord prob U stages).1.map (fun idx => f idx.2.1)).sum =
      (∑ h ∈ (initProbePrefix p stages).toFinset, (mhrRounds T h : ℝ) * g) +
      match stages.find? p with
      | none => 0
      | some h => if scale h < (2 : ℝ)^16 / (K : ℝ) then 0 else (step2Rounds T (scale h) : ℝ) * g := by
  classical
  induction stages with
  | nil => simp [initProbePath, initProbePrefix]
  | cons h hs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hnd
    let K := gridK η
    let g := ∑ e ∈ sampleSet K, f e
    let p := fun h => decide (mhrTriggers T K prob U h)
    have hind := ih htail
    dsimp only at hind ⊢
    by_cases htr : mhrTriggers T (gridK η) prob U h
    · have he : (h :: hs).find? p = some h := by simp [p, K, htr]
      have hshort : initProbePrefix p (h :: hs) = [h] := by
        unfold initProbePrefix
        rw [he]
        have hel : hs.filter (fun j => decide (∀ h' ∈ some h, j ≤ h')) = [] := by
          apply List.filter_eq_nil_iff.2
          intro j hj
          intro hf
          exact (not_le.mpr (hhead j hj)) (of_decide_eq_true hf h (by simp))
        have hkeep : ∀ j ∈ some h, h ≤ j := by
          intro j hj
          have hj' : h = j := Option.mem_some_iff.mp hj
          exact hj' ▸ le_rfl
        rw [List.filter_cons_of_pos (p := fun j => decide (∀ a ∈ some h, j ≤ a))
          (a := h) (decide_eq_true hkeep), hel]
      change _ = (∑ h ∈ (initProbePrefix p (h :: hs)).toFinset, (mhrRounds T h : ℝ) * g) + _
      rw [hshort]
      have he' : (h :: hs).find? (fun j => decide (mhrTriggers T (gridK η) prob U j)) = some h := he
      simp only [he', List.toFinset_cons, List.toFinset_nil, Finset.sum_insert (by simp : h ∉ (∅ : Finset ℕ)), Finset.sum_empty, add_zero,
        initProbePath, if_pos htr]
      by_cases hsmall : scale h < (2 : ℝ)^16 / (gridK η : ℝ)
      · simp only [if_pos hsmall, initProbeBlock_sum, add_zero]
        rfl
      · simp only [if_neg hsmall, List.map_append, List.sum_append, initProbeBlock_sum]
        rfl
    · have he : (h :: hs).find? p = hs.find? p := by simp [p, K, htr]
      have hkeep : ∀ h' ∈ hs.find? p, h ≤ h' := by
        intro h' hh'
        exact (hhead h' (List.mem_of_find?_eq_some (Option.mem_def.mp hh'))).le
      have hcons : initProbePrefix p (h :: hs) = h :: initProbePrefix p hs := by
        unfold initProbePrefix
        rw [he]
        rw [List.filter_cons_of_pos (p := fun j => decide (∀ a ∈ hs.find? p, j ≤ a))
          (a := h) (decide_eq_true hkeep)]
      have hnot : h ∉ (initProbePrefix p hs).toFinset := by
        rw [List.mem_toFinset]
        intro hh
        exact (lt_irrefl h) (hhead h (List.mem_of_mem_filter hh))
      change _ = (∑ j ∈ (initProbePrefix p (h :: hs)).toFinset, (mhrRounds T j : ℝ) * g) + _
      rw [hcons]
      have he' : (h :: hs).find? (fun j => decide (mhrTriggers T (gridK η) prob U j)) =
          hs.find? (fun j => decide (mhrTriggers T (gridK η) prob U j)) := he
      simp only [he', List.toFinset_cons, Finset.sum_insert hnot, initProbePath, if_neg htr,
        List.map_append, List.sum_append, initProbeBlock_sum]
      change ((mhrRounds T h : ℝ) * g) + _ = _
      rw [hind, add_assoc]

private theorem initProbeTree_cost_eq_initRegret (E : Environment) (T : ℕ) (η : ℝ)
    (ord : List (ℕ × ℕ)) (U : InitTapeUniforms) :
    (((initProbeTree T η ord).eval (initUniformBits (gridK η) (P E) U)).1.map
      (fun i => muStar E - mu E (gpt (gridK η) i.2.1))).sum = initRegret E T η U := by
  rw [initProbeTree, initProbeTreeAux_eval]
  rw [initProbePath_cost T η ord (P E) U (fun e => muStar E - mu E (gpt (gridK η) e))
    (initCheckedScales (gridK η)) (initCheckedScales_pairwise _)]
  rw [nth_checked_eq_testedScales, find_initCheckedScales_eq_mhrScale]
  rfl

private theorem initProbePath_probes (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) (stages : List ℕ) :
    ∀ idx ∈ (initProbePath T η ord prob U stages).1, idx.2.1 ∈ sampleSet (gridK η) := by
  induction stages with
  | nil => simp [initProbePath]
  | cons h hs ih =>
    simp only [initProbePath]
    split
    · split
      · intro idx hi
        exact (mem_initProbeBlock.mp hi).2.1
      · intro idx hi
        rcases List.mem_append.mp hi with hi | hi <;> exact (mem_initProbeBlock.mp hi).2.1
    · intro idx hi
      rcases List.mem_append.mp hi with hi | hi
      · exact (mem_initProbeBlock.mp hi).2.1
      · exact ih idx hi

private theorem initProbeTree_eval_probes (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (prob : ℝ × ℝ → ℝ) (U : InitTapeUniforms) :
    ∀ idx ∈ ((initProbeTree T η ord).eval (initUniformBits (gridK η) prob U)).1,
      idx.2.1 ∈ sampleSet (gridK η) := by
  rw [initProbeTree, initProbeTreeAux_eval]
  exact initProbePath_probes _ _ _ _ _ _

private theorem sum_map_ofReal {α : Type} (xs : List α) (f : α → ℝ)
    (hf : ∀ x ∈ xs, 0 ≤ f x) :
    (xs.map (fun x => ENNReal.ofReal (f x))).sum = ENNReal.ofReal (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hf' (y : α) (hy : y ∈ xs) := hf y (List.mem_cons_of_mem _ hy)
    have hsum : 0 ≤ (xs.map f).sum := by
      apply List.sum_nonneg
      intro a ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact hf' y hy
    simp only [List.map_cons, List.sum_cons, ih hf', ENNReal.ofReal_add (hf x (by simp)) hsum]

private theorem initProbeTree_tapeCost_le (E : Environment) (hE : OnUnit E)
    (T : ℕ) (η : ℝ) (hK : 0 < gridK η) (ord : List (ℕ × ℕ)) (U : InitTapeUniforms)
    (n : ℕ) (finish : ℕ → InitTreeOutput → ℝ≥0∞) :
    let bits := initUniformBits (gridK η) (P E) U
    let tree := initProbeTree T η ord
    let g := fun idx : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt (gridK η) idx.2.1))
    ProbeTree.tapeCost bits g finish n tree ≤
      ENNReal.ofReal (initRegret E T η U) +
        finish (n - (tree.eval bits).1.length) (initRegular T η ord (P E) U) := by
  dsimp only
  refine (ProbeTree.tapeCost_le_full _ _ _ _ _).trans_eq ?_
  rw [initProbeTree_output, sum_map_ofReal, initProbeTree_cost_eq_initRegret]
  intro idx hi
  obtain ⟨h₁, h₂⟩ := sampleSet_bounds (initProbeTree_eval_probes T η ord (P E) U idx hi)
  exact sub_nonneg.mpr (mu_le_muStar E hE (initTransport_triT_subset_unitSq (initTransport_gpt_tri hK h₁ h₂)))

end BilateralProfitRegular

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal Classical

private theorem initProbeTree_value_eq_uniform (E : Environment) (hE : OnUnit E) (T : ℕ) (η : ℝ)
    (ord : List (ℕ × ℕ)) (n : ℕ) (finish : ℕ → InitTreeOutput → ℝ≥0∞) :
    let tree := initProbeTree T η ord
    let q := fun idx : InitProbeIndex => P E (gpt (gridK η) idx.2.1)
    let g := fun idx : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt (gridK η) idx.2.1))
    tree.value q g finish n =
      ∫⁻ U, tree.tapeCost (initUniformBits (gridK η) (P E) U) g finish n ∂initCoinLaw := by
  dsimp only
  let q := fun idx : InitProbeIndex => P E (gpt (gridK η) idx.2.1)
  let g := fun idx : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt (gridK η) idx.2.1))
  let F (i : InitProbeIndex) : Set unitInterval := {u | (u : ℝ) < q i}
  have hq (i : InitProbeIndex) : q i ∈ Set.Icc (0 : ℝ) 1 := (onUnit_facts E hE).1 _
  have hF (i : InitProbeIndex) : MeasurableSet (F i) :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hmass (i : InitProbeIndex) : (volume : Measure unitInterval) (F i) =
      ENNReal.ofReal (q i) := unitInterval.volume_Iio ⟨q i, hq i⟩
  exact ProbeTree.value_eq_lintegral volume F hF q hq hmass g finish n
    (initProbeTree T η ord) (initProbeTree_valid T η ord)

private theorem tapeCost_le_min_mul {I R : Type} (tree : ProbeTree I R) (bits : I → Bool)
    (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞)
    (h : ∀ i ∈ (tree.eval bits).1, g i ≤ c) :
    tree.tapeCost bits g finish n ≤
      (min n (tree.eval bits).1.length : ℕ) * c +
        finish (n - (tree.eval bits).1.length) (tree.eval bits).2 := by
  induction tree generalizing n with
  | leaf a => simp [ProbeTree.tapeCost, ProbeTree.eval]
  | node i yes no ihY ihN =>
    cases n with
    | zero => exact bot_le
    | succ n =>
      cases hb : bits i
      · simp only [ProbeTree.eval, hb, Bool.false_eq_true, if_false, List.mem_cons] at h
        have h0 := h i (Or.inl rfl)
        have hY := ihY n fun j hj => h j (Or.inr hj)
        simp only [ProbeTree.tapeCost, ProbeTree.eval, hb, Bool.false_eq_true, if_false,
          List.length_cons, Nat.succ_sub_succ_eq_sub, Nat.succ_min_succ, Nat.cast_succ, add_mul,
          one_mul]
        rw [add_comm _ c, add_assoc]
        exact add_le_add h0 hY
      · simp only [ProbeTree.eval, hb, if_true, List.mem_cons] at h
        have h0 := h i (Or.inl rfl)
        have hN := ihN n fun j hj => h j (Or.inr hj)
        simp only [ProbeTree.tapeCost, ProbeTree.eval, hb, if_true, List.length_cons,
          Nat.succ_sub_succ_eq_sub, Nat.succ_min_succ, Nat.cast_succ, add_mul, one_mul]
        rw [add_comm _ c, add_assoc]
        exact add_le_add h0 hN

private theorem initProbeTree_tapeCost_le_time (E : Environment) (hE : OnUnit E) (T : ℕ) (η : ℝ)
    (hK : 0 < gridK η) (ord : List (ℕ × ℕ)) (U : InitTapeUniforms) (n : ℕ)
    (finish : ℕ → InitTreeOutput → ℝ≥0∞) :
    let bits := initUniformBits (gridK η) (P E) U
    let tree := initProbeTree T η ord
    let g := fun idx : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt (gridK η) idx.2.1))
    tree.tapeCost bits g finish n ≤
      (min n (tree.eval bits).1.length : ℕ) * ENNReal.ofReal (muStar E) +
        finish (n - (tree.eval bits).1.length) (initRegular T η ord (P E) U) := by
  dsimp only
  rw [← initProbeTree_output T η ord (P E) U]
  apply tapeCost_le_min_mul
  intro i hi
  obtain ⟨hle, hmax⟩ := sampleSet_bounds (initProbeTree_eval_probes T η ord (P E) U i hi)
  exact ENNReal.ofReal_le_ofReal (sub_le_self _ (initTransport_gpt_profit_nonneg hK hle hmax E hE))

end BilateralProfitRegular
end BundlePart063


section BundlePart064


namespace ProbeTree

private def AllIndices {I R : Type} (P : I → Prop) : ProbeTree I R → Prop
  | .leaf _ => True
  | .node i no yes => P i ∧ AllIndices P no ∧ AllIndices P yes

private theorem readBlock_allIndices {I R : Type} [DecidableEq I] (P : I → Prop)
    (block : List I) (acc : I → Bool) (cont : (I → Bool) → ProbeTree I R)
    (hblock : ∀ i ∈ block, P i) (hcont : ∀ tape, AllIndices P (cont tape)) :
    AllIndices P (readBlock block acc cont) := by
  induction block generalizing acc with
  | nil => exact hcont acc
  | cons i rest ih =>
    exact ⟨hblock i (by simp), ih _ (fun j hj => hblock j (List.mem_cons_of_mem _ hj)),
      ih _ (fun j hj => hblock j (List.mem_cons_of_mem _ hj))⟩

end ProbeTree

namespace BilateralProfitRegular

open scoped Classical

private theorem initTransport_mem_actList_iff {K : ℕ} {e : ℕ × ℕ} :
    e ∈ actList K ↔ e.1 ≤ e.2 ∧ e.2 ≤ K := by
  rcases e with ⟨i,j⟩
  simp only [actList, List.mem_filter, decide_eq_true_eq]
  change ((i,j) ∈ List.range (K + 1) ×ˢ List.range (K + 1) ∧ i ≤ j) ↔ i ≤ j ∧ j ≤ K
  simp only [List.mem_product, List.mem_range, Nat.lt_succ_iff]
  omega

private theorem actList_isOrder (K : ℕ) : IsOrder K (actList K) := by
  refine ⟨?_, fun _ => initTransport_mem_actList_iff⟩
  unfold actList
  exact (List.nodup_range.product List.nodup_range).filter _

private theorem initProbeTreeAux_allIndices (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ))
    (stages : List ℕ) (acc : InitProbeIndex → Bool) :
    (initProbeTreeAux T η ord stages acc).AllIndices
      (fun idx => idx.2.1 ∈ sampleSet (gridK η)) := by
  induction stages generalizing acc with
  | nil => trivial
  | cons h hs ih =>
    simp only [initProbeTreeAux]
    apply ProbeTree.readBlock_allIndices
    · intro idx hi
      exact (mem_initProbeBlock.mp hi).2.1
    · intro tape
      split
      · split
        · trivial
        · apply ProbeTree.readBlock_allIndices
          · intro idx hi
            exact (mem_initProbeBlock.mp hi).2.1
          · intro _
            trivial
      · exact ih tape

private theorem initProbeTree_allIndices (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ)) :
    (initProbeTree T η ord).AllIndices
      (fun idx => idx.2.1 ∈ sampleSet (gridK η)) :=
  initProbeTreeAux_allIndices T η ord _ _

end BilateralProfitRegular
end BundlePart064


section BundlePart065


namespace ProbeTree

open MeasureTheory
open scoped Classical

/-- A predicate of the complete path and its leaf value is measurable under measurable
coordinate tests. No measurable-space structure on the leaf values is needed. -/
private theorem measurableSet_eval_pred {I R V : Type} [MeasurableSpace V]
    (tree : ProbeTree I R) (tests : I → Set V) (ht : ∀ i, MeasurableSet (tests i))
    (p : List I × R → Prop) :
    MeasurableSet {v : I → V | p (tree.eval (bitsFromSets tests v))} := by
  induction tree generalizing p with
  | leaf a =>
    by_cases h : p ([], a)
    · simpa [ProbeTree.eval, h] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (I → V)))
    · simpa [ProbeTree.eval, h] using (MeasurableSet.empty : MeasurableSet (∅ : Set (I → V)))
  | node i no yes ihno ihyes =>
    let A : Set (I → V) := {v | v i ∈ tests i}
    have hA : MeasurableSet A := (ht i).preimage (measurable_pi_apply i)
    let p' := fun t : List I × R => p (i :: t.1, t.2)
    have heq : {v : I → V | p ((node i no yes).eval (bitsFromSets tests v))} =
        (A ∩ {v | p' (yes.eval (bitsFromSets tests v))}) ∪
        (Aᶜ ∩ {v | p' (no.eval (bitsFromSets tests v))}) := by
      ext v
      by_cases hv : v i ∈ tests i <;> simp [A, p', eval, bitsFromSets, hv]
    rw [heq]
    exact (hA.inter (ihyes p')).union (hA.compl.inter (ihno p'))

end ProbeTree

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal Classical

/-- The initializer outcome and total-cost condition in Lemma 6.4, with its supplied constant. -/
private def InitOutcomeGood (C : ℝ) (T : ℕ) (η : ℝ) (E : Environment)
    (ord : List (ℕ × ℕ)) (U : InitTapeUniforms) : Prop :=
  match initRegular T η ord (P E) U with
  | none => muStar E ≤ C / gridK η
  | some (δ, cs) =>
      InitGuarantee E η δ cs ∧
      (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * T) ∧
      initRegret E T η U ≤ C * gridK η * Real.log T ^ 2

private theorem initOutcomeGood_measurable (C : ℝ) (T : ℕ) (η : ℝ) (E : Environment)
    (ord : List (ℕ × ℕ)) :
    MeasurableSet {U : InitTapeUniforms | InitOutcomeGood C T η E ord U} := by
  let K := gridK η
  let g := fun i : InitProbeIndex => muStar E - mu E (gpt K i.2.1)
  let tests : InitProbeIndex → Set unitInterval := fun i => {u | (u : ℝ) < P E (gpt K i.2.1)}
  let good (p : List InitProbeIndex × InitTreeOutput) : Prop :=
    match p.2 with
    | none => muStar E ≤ C / (K : ℝ)
    | some (δ, cs) =>
      InitGuarantee E η δ cs ∧
      (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * (T : ℝ)) ∧
      (p.1.map g).sum ≤ C * (K : ℝ) * Real.log (T : ℝ)^2
  have h := (initProbeTree T η ord).measurableSet_eval_pred tests
    (fun _ => measurableSet_lt measurable_subtype_coe measurable_const) good
  change MeasurableSet {U : InitTapeUniforms | good
    ((initProbeTree T η ord).eval (initUniformBits K (P E) U))} at h
  have heq : {U : InitTapeUniforms | good ((initProbeTree T η ord).eval (initUniformBits K (P E) U))} =
      {U : InitTapeUniforms | InitOutcomeGood C T η E ord U} := by
    ext U
    unfold good InitOutcomeGood
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, initProbeTree_output, initProbeTree_cost_eq_initRegret]
    rfl
  exact heq ▸ h

private theorem gridK_ge_two_event {η : ℝ} (hη : 0 < η) (hη₁ : η < 1) : 2 ≤ gridK η := by
  have hu : 1 < 1 / η := (lt_div_iff₀ hη).2 (by simpa)
  have h := Nat.le_ceil (1 / η)
  change 1 / η ≤ (gridK η : ℝ) at h
  exact_mod_cast hu.trans_le h

/-- The finite-horizon initializer with an arbitrary continuation. On the joint probing event,
a trigger is charged the full initialization regret and the good-trigger continuation bound.
A no-trigger transcript is charged the optimum times the entire physical horizon. The exceptional
transcripts are charged at most their probability times the horizon. -/
private theorem initProbeTree_continuation_bound_of_failure {T : ℕ} {η C : ℝ}
        (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (ord : List (ℕ × ℕ))
    (hfailure : initCoinLaw {U | ¬ InitOutcomeGood C T η E ord U} ≤ ENNReal.ofReal (1 / (T : ℝ)))
    (finish : ℕ → InitTreeOutput → ℝ≥0∞) (R : ℝ≥0∞)
    (hcap : ∀ n ≤ T, ∀ o, finish n o ≤ (n : ℝ≥0∞))
    (hnone : ∀ n ≤ T, finish n none ≤ (n : ℝ≥0∞) * ENNReal.ofReal (muStar E))
    (hgood : ∀ n ≤ T, ∀ δ cs, InitGuarantee E η δ cs →
      (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * (T : ℝ)) →
      finish n (some (δ, cs)) ≤ R) :
    let K := gridK η
    let q := fun i : InitProbeIndex => P E (gpt K i.2.1)
    let g := fun i : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt K i.2.1))
    (initProbeTree T η ord).value q g finish T ≤
      ENNReal.ofReal (C * (K : ℝ) * Real.log (T : ℝ)^2) +
        ENNReal.ofReal (C * (T : ℝ) / K) + R + 1 := by
  let K := gridK η
  let B := ENNReal.ofReal (C * (K : ℝ) * Real.log (T : ℝ)^2) +
    ENNReal.ofReal (C * (T : ℝ) / K) + R
  let bad : Set InitTapeUniforms := {U | ¬ InitOutcomeGood C T η E ord U}
  let tree := initProbeTree T η ord
  let g := fun i : InitProbeIndex => ENNReal.ofReal (muStar E - mu E (gpt K i.2.1))
  have hK : 2 ≤ K := gridK_ge_two_event hη hη₁
  have hKpos : 0 < K := by omega
  have hT : 0 < T := hKpos.trans_le hKT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hμ := (onUnit_facts E hE.1).2.2.2.1
  have hμcap : ENNReal.ofReal (muStar E) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hμ.2
  have hbad_meas : MeasurableSet bad := (initOutcomeGood_measurable C T η E ord).compl
  have hbad : initCoinLaw bad ≤ ENNReal.ofReal (1 / (T : ℝ)) := hfailure
  have : IsProbabilityMeasure initCoinLaw := by unfold initCoinLaw; infer_instance
  dsimp only
  rw [initProbeTree_value_eq_uniform E hE.1 T η ord T finish]
  have hpoint (U : InitTapeUniforms) :
      tree.tapeCost (initUniformBits K (P E) U) g finish T ≤
        B + bad.indicator (fun _ => (T : ℝ≥0∞)) U := by
    let m := (tree.eval (initUniformBits K (P E) U)).1.length
    let n := T - m
    let o := initRegular T η ord (P E) U
    have hn : n ≤ T := Nat.sub_le _ _
    have hm : min T m + n = T := by dsimp [n]; omega
    have htime := initProbeTree_tapeCost_le_time E hE.1 T η hKpos ord U T finish
    change tree.tapeCost (initUniformBits K (P E) U) g finish T ≤
      (min T m : ℕ) * ENNReal.ofReal (muStar E) + finish n o at htime
    by_cases hU : InitOutcomeGood C T η E ord U
    · have hb : U ∉ bad := fun hf => hf hU
      rw [Set.indicator_of_notMem hb, add_zero]
      have hout := hU
      unfold InitOutcomeGood at hout
      cases ho : initRegular T η ord (P E) U with
      | none =>
        have hmub : muStar E ≤ C / (K : ℝ) := by simpa only [ho] using hout
        have he : (T : ℝ≥0∞) * ENNReal.ofReal (muStar E) ≤
            ENNReal.ofReal (C * (T : ℝ) / K) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            ((mul_le_mul_of_nonneg_left hmub (by positivity)).trans_eq (by ring))
        apply htime.trans
        rw [show o = none from ho]
        calc
          _ ≤ (min T m : ℕ) * ENNReal.ofReal (muStar E) +
              (n : ℝ≥0∞) * ENNReal.ofReal (muStar E) :=
            add_le_add_right (hnone n hn) _
          _ = (T : ℝ≥0∞) * ENNReal.ofReal (muStar E) := by
            rw [← add_mul, ← Nat.cast_add, hm]
          _ ≤ _ := by
            exact he.trans ((le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le))
      | some out =>
        obtain ⟨δ, cs⟩ := out
        have hcert' : InitGuarantee E η δ cs ∧
            (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * (T : ℝ)) ∧
            initRegret E T η U ≤ C * (K : ℝ) * Real.log (T : ℝ)^2 := by
          simpa only [ho] using hout
        obtain ⟨hcert, hcount, hreg⟩ := hcert' 
        have hcost := initProbeTree_tapeCost_le E hE.1 T η hKpos ord U T finish
        change tree.tapeCost (initUniformBits K (P E) U) g finish T ≤
          ENNReal.ofReal (initRegret E T η U) + finish n o at hcost
        rw [show o = some (δ, cs) from ho] at hcost
        apply hcost.trans
        have hb := add_le_add (ENNReal.ofReal_le_ofReal hreg) (hgood n hn δ cs hcert hcount)
        exact hb.trans (add_le_add_left (le_add_of_nonneg_right bot_le) R)
    · have hb : U ∈ bad := hU
      rw [Set.indicator_of_mem hb]
      apply htime.trans
      calc
        _ ≤ ((min T m : ℕ) : ℝ≥0∞) * 1 + (n : ℝ≥0∞) :=
          add_le_add (mul_le_mul_right hμcap _) (hcap n hn o)
        _ = (T : ℝ≥0∞) := by rw [mul_one, ← Nat.cast_add, hm]
        _ ≤ _ := le_add_of_nonneg_left bot_le
  calc
    _ ≤ ∫⁻ U, B + bad.indicator (fun _ => (T : ℝ≥0∞)) U ∂initCoinLaw :=
      lintegral_mono hpoint
    _ = B + (T : ℝ≥0∞) * initCoinLaw bad := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_indicator hbad_meas, setLIntegral_const]
    _ ≤ B + 1 := by
      apply add_le_add_right
      calc
        _ ≤ (T : ℝ≥0∞) * ENNReal.ofReal (1 / (T : ℝ)) := mul_le_mul_right hbad _
        _ = 1 := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hT'.le,
            mul_one_div_cancel hT'.ne', ENNReal.ofReal_one]
    _ = _ := rfl

end BilateralProfitRegular
end BundlePart065


section BundlePart066



noncomputable section

namespace ProbeTree

open BilateralProfitRegular MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem allIndices_imp {I R : Type} {P Q : I → Prop} {tree : ProbeTree I R}
    (h : tree.AllIndices P) (hPQ : ∀ i, P i → Q i) : tree.AllIndices Q := by
  induction tree with
  | leaf a => trivial
  | node i no yes ihno ihyes =>
    exact ⟨hPQ i h.1, ihno h.2.1, ihyes h.2.2⟩

/-- Give each leaf its own continuation seed. At a node, the seeds of the two branches
are independent and the incoming feedback bit determines which branch is run. -/
private def attach {I R A : Type} [MeasurableSpace A] (price : I → ℝ × ℝ)
    (finish : R → RandomProgram Unit A) :
    (tree : ProbeTree I R) →
    tree.AllIndices (fun i => price i ∈ triT) → RandomProgram Unit A
  | .leaf a, _ => finish a
  | .node i no yes, h =>
    let pn := attach price finish no h.2.1
    let py := attach price finish yes h.2.2
    { Seed := pn.Seed × py.Seed
      seedSpace := inferInstance
      law := pn.law.prod py.law
      probability := inferInstance
      run s
        | [] => .inr (price i)
        | false :: bs => pn.run (s.1, s.2.1) bs
        | true :: bs => py.run (s.1, s.2.2) bs
      measurable_run := by
        intro bs
        cases bs with
        | nil => exact measurable_const
        | cons b bs =>
          cases b
          · exact (pn.measurable_run bs).comp (measurable_fst.prodMk measurable_snd.fst)
          · exact (py.measurable_run bs).comp (measurable_fst.prodMk measurable_snd.snd)
      legal := by
        intro s bs x hx
        cases bs with
        | nil =>
          cases hx
          exact h.1
        | cons b bs =>
          cases b
          · exact pn.legal _ bs x hx
          · exact py.legal _ bs x hx }

private theorem attach_expected {I R A : Type} [MeasurableSpace A] (price : I → ℝ × ℝ)
    (finish : R → RandomProgram Unit A) (tree : ProbeTree I R)
    (hlegal : tree.AllIndices (fun i => price i ∈ triT))
    (E : Environment) (hE : OnUnit E) (n : ℕ) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ m, Measurable (final m)) :
    (tree.attach price finish hlegal).expected E () n final =
      tree.value (fun i => P E (price i)) (fun i => regretGap E (price i))
        (fun m o => (finish o).expected E () m final) n := by
  induction tree generalizing n with
  | leaf o =>
    simp [attach, value]
  | node i no yes ihno ihyes =>
    let pn := no.attach price finish hlegal.2.1
    let py := yes.attach price finish hlegal.2.2
    cases n with
    | zero =>
      change (∫⁻ (_ : pn.Seed × py.Seed), 0 ∂(pn.law.prod py.law)) = _
      simp [value]
    | succ n =>
      let fn (ω : pn.Seed) := (pn.run ((), ω)).value (P E) (regretGap E) n final
      let fy (ω : py.Seed) := (py.run ((), ω)).value (P E) (regretGap E) n final
      have hfn : Measurable fn := Program.measurable_value (measurable_P E hE)
        (measurable_regretGap E hE)
        (fun b => (pn.measurable_run b).comp (measurable_const.prodMk measurable_id))
        n (fun m => (hM m).comp measurable_snd)
      have hfy : Measurable fy := Program.measurable_value (measurable_P E hE)
        (measurable_regretGap E hE)
        (fun b => (py.measurable_run b).comp (measurable_const.prodMk measurable_id))
        n (fun m => (hM m).comp measurable_snd)
      let q := ENNReal.ofReal (P E (price i))
      let qb := ENNReal.ofReal (1 - P E (price i))
      let g := regretGap E (price i)
      let F := fun m o => (finish o).expected E () m final
      change (∫⁻ s : pn.Seed × py.Seed, g + (q * fy s.2 + qb * fn s.1) ∂(pn.law.prod py.law)) =
        g + (q * yes.value (fun i => P E (price i)) (fun i => regretGap E (price i)) F n +
          qb * no.value (fun i => P E (price i)) (fun i => regretGap E (price i)) F n)
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      have hn' : Measurable (fun s : pn.Seed × py.Seed => fn s.1) := hfn.comp measurable_fst
      have hy' : Measurable (fun s : pn.Seed × py.Seed => fy s.2) := hfy.comp measurable_snd
      rw [lintegral_add_left (hy'.const_mul q), lintegral_const_mul _ hy', lintegral_const_mul _ hn']
      have hnEq := (measurePreserving_fst (μ := pn.law) (ν := py.law)).lintegral_comp hfn
      have hyEq := (measurePreserving_snd (μ := pn.law) (ν := py.law)).lintegral_comp hfy
      rw [hnEq, hyEq]
      change g + (q * py.expected E () n final + qb * pn.expected E () n final) = _
      rw [ihyes hlegal.2.2, ihno hlegal.2.1]

end ProbeTree

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem initProbeTree_allPricesLegal (T : ℕ) (η : ℝ) (hK : 0 < gridK η)
    (ord : List (ℕ × ℕ)) :
    (initProbeTree T η ord).AllIndices (fun i => gpt (gridK η) i.2.1 ∈ triT) := by
  apply ProbeTree.allIndices_imp (initProbeTree_allIndices T η ord)
  intro i hi
  obtain ⟨hle, hmax⟩ := sampleSet_bounds hi
  exact initTransport_gpt_tri hK hle hmax

private def initRegularWith {A : Type} [MeasurableSpace A] (T : ℕ) (η : ℝ)
    (hK : 0 < gridK η) (ord : List (ℕ × ℕ)) (finish : InitTreeOutput → RandomProgram Unit A) :
    RandomProgram Unit A :=
  (initProbeTree T η ord).attach (fun i => gpt (gridK η) i.2.1) finish
    (initProbeTree_allPricesLegal T η hK ord)

private theorem initRegularWith_expected {A : Type} [MeasurableSpace A] (T : ℕ) (η : ℝ)
    (hK : 0 < gridK η) (ord : List (ℕ × ℕ)) (finish : InitTreeOutput → RandomProgram Unit A)
    (E : Environment) (hE : OnUnit E) (n : ℕ) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ m, Measurable (final m)) :
    (initRegularWith T η hK ord finish).expected E () n final =
      (initProbeTree T η ord).value
        (fun i => P E (gpt (gridK η) i.2.1))
        (fun i => regretGap E (gpt (gridK η) i.2.1))
        (fun m o => (finish o).expected E () m final) n :=
  ProbeTree.attach_expected _ _ _ _ E hE n final hM

private theorem initRegularWith_expected_le {A : Type} [MeasurableSpace A] {T : ℕ} {η C : ℝ}
    (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (ord : List (ℕ × ℕ))
    (hfailure : initCoinLaw {U | ¬ InitOutcomeGood C T η E ord U} ≤ ENNReal.ofReal (1 / (T : ℝ)))
    (finish : InitTreeOutput → RandomProgram Unit A) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ n, Measurable (final n)) (R : ℝ≥0∞)
    (hcap : ∀ n ≤ T, ∀ a, final n a ≤ (n : ℝ≥0∞))
    (hnone : ∀ n ≤ T, (finish none).expected E () n final ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (muStar E))
    (hgood : ∀ n ≤ T, ∀ δ cs, InitGuarantee E η δ cs →
      (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * (T : ℝ)) →
      (finish (some (δ, cs))).expected E () n final ≤ R) :
    (initRegularWith T η (Nat.ceil_pos.mpr (one_div_pos.mpr hη)) ord finish).expected E () T final ≤
      ENNReal.ofReal (C * (gridK η : ℝ) * Real.log (T : ℝ)^2) +
        ENNReal.ofReal (C * (T : ℝ) / gridK η) + R + 1 := by
  have hK : 0 < gridK η := Nat.ceil_pos.mpr (one_div_pos.mpr hη)
  change (initRegularWith T η hK ord finish).expected E () T final ≤ _
  rw [initRegularWith_expected T η hK ord finish E hE.1 T final hM]
  apply initProbeTree_continuation_bound_of_failure hη hη₁ hKT E hE ord hfailure _ R _ hnone hgood
  intro m hm o
  have hμ := (onUnit_facts E hE.1).2.2.2.1.2
  have hμ' : ENNReal.ofReal (muStar E) ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hμ
  simpa using (finish o).expected_le_time E hE.1 () m 1 hμ'
    (fun k hk a => by simpa using hcap k (hk.trans hm) a)

end BilateralProfitRegular
end
end BundlePart066


section BundlePart067



noncomputable section

namespace ProbeTree

open BilateralProfitRegular MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem value_cost_mono {I R : Type} {q : I → ℝ} {g g' : I → ℝ≥0∞}
    {tree : ProbeTree I R} (hcost : tree.AllIndices (fun i => g i ≤ g' i))
    (finish : ℕ → R → ℝ≥0∞) (n : ℕ) :
    tree.value q g finish n ≤ tree.value q g' finish n := by
  induction tree generalizing n with
  | leaf o => simp [value]
  | node i no yes ihno ihyes =>
    cases n with
    | zero => simp [value]
    | succ n =>
      simp only [value]
      exact add_le_add hcost.1 (add_le_add
        (mul_le_mul' le_rfl (ihyes hcost.2.2 n))
        (mul_le_mul' le_rfl (ihno hcost.2.1 n)))

private theorem attach_expectedCost {I R A : Type} [MeasurableSpace A] (price : I → ℝ × ℝ)
    (finish : R → RandomProgram Unit A) (tree : ProbeTree I R)
    (hlegal : tree.AllIndices (fun i => price i ∈ triT))
    (E : Environment) (hE : OnUnit E) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (hgap : Measurable gap) (n : ℕ) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ m, Measurable (final m)) :
    (tree.attach price finish hlegal).expectedCost E gap () n final =
      tree.value (fun i => P E (price i)) (fun i => gap (price i))
        (fun m o => (finish o).expectedCost E gap () m final) n := by
  induction tree generalizing n with
  | leaf o =>
    simp [attach, value]
  | node i no yes ihno ihyes =>
    let pn := no.attach price finish hlegal.2.1
    let py := yes.attach price finish hlegal.2.2
    cases n with
    | zero =>
      change (∫⁻ (_ : pn.Seed × py.Seed), 0 ∂(pn.law.prod py.law)) = _
      simp [value]
    | succ n =>
      let fn (ω : pn.Seed) := (pn.run ((), ω)).value (P E) gap n final
      let fy (ω : py.Seed) := (py.run ((), ω)).value (P E) gap n final
      have hfn : Measurable fn := Program.measurable_value (measurable_P E hE)
        hgap
        (fun b => (pn.measurable_run b).comp (measurable_const.prodMk measurable_id))
        n (fun m => (hM m).comp measurable_snd)
      have hfy : Measurable fy := Program.measurable_value (measurable_P E hE)
        hgap
        (fun b => (py.measurable_run b).comp (measurable_const.prodMk measurable_id))
        n (fun m => (hM m).comp measurable_snd)
      let q := ENNReal.ofReal (P E (price i))
      let qb := ENNReal.ofReal (1 - P E (price i))
      let g := gap (price i)
      let F := fun m o => (finish o).expectedCost E gap () m final
      change (∫⁻ s : pn.Seed × py.Seed, g + (q * fy s.2 + qb * fn s.1) ∂(pn.law.prod py.law)) =
        g + (q * yes.value (fun i => P E (price i)) (fun i => gap (price i)) F n +
          qb * no.value (fun i => P E (price i)) (fun i => gap (price i)) F n)
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      have hn' : Measurable (fun s : pn.Seed × py.Seed => fn s.1) := hfn.comp measurable_fst
      have hy' : Measurable (fun s : pn.Seed × py.Seed => fy s.2) := hfy.comp measurable_snd
      rw [lintegral_add_left (hy'.const_mul q), lintegral_const_mul _ hy', lintegral_const_mul _ hn']
      have hnEq := (measurePreserving_fst (μ := pn.law) (ν := py.law)).lintegral_comp hfn
      have hyEq := (measurePreserving_snd (μ := pn.law) (ν := py.law)).lintegral_comp hfy
      rw [hnEq, hyEq]
      change g + (q * py.expectedCost E gap () n final + qb * pn.expectedCost E gap () n final) = _
      rw [ihyes hlegal.2.2, ihno hlegal.2.1]

end ProbeTree

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem initRegularWith_expectedCost {A : Type} [MeasurableSpace A] (T : ℕ) (η : ℝ)
    (hK : 0 < gridK η) (ord : List (ℕ × ℕ)) (finish : InitTreeOutput → RandomProgram Unit A)
    (E : Environment) (hE : OnUnit E) (gap : (ℝ × ℝ) → ℝ≥0∞)
    (hgap : Measurable gap) (n : ℕ) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ m, Measurable (final m)) :
    (initRegularWith T η hK ord finish).expectedCost E gap () n final =
      (initProbeTree T η ord).value
        (fun i => P E (gpt (gridK η) i.2.1))
        (fun i => gap (gpt (gridK η) i.2.1))
        (fun m o => (finish o).expectedCost E gap () m final) n :=
  ProbeTree.attach_expectedCost _ _ _ _ E hE gap hgap n final hM

private theorem initRegularWith_expectedCost_le {A : Type} [MeasurableSpace A] {T : ℕ} {η C : ℝ}
    (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (ord : List (ℕ × ℕ))
    (hfailure : initCoinLaw {U | ¬ InitOutcomeGood C T η E ord U} ≤ ENNReal.ofReal (1 / (T : ℝ)))
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (hgap : ∀ x ∈ triT, g x ≤ regretGap E x)
    (finish : InitTreeOutput → RandomProgram Unit A) (final : ℕ → A → ℝ≥0∞)
    (hM : ∀ n, Measurable (final n)) (R : ℝ≥0∞)
    (hcap : ∀ n ≤ T, ∀ a, final n a ≤ (n : ℝ≥0∞))
    (hnone : ∀ n ≤ T, (finish none).expectedCost E g () n final ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (muStar E))
    (hgood : ∀ n ≤ T, ∀ δ cs, InitGuarantee E η δ cs →
      (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * (T : ℝ)) →
      (finish (some (δ, cs))).expectedCost E g () n final ≤ R) :
    (initRegularWith T η (Nat.ceil_pos.mpr (one_div_pos.mpr hη)) ord finish).expectedCost
      E g () T final ≤
      ENNReal.ofReal (C * (gridK η : ℝ) * Real.log (T : ℝ)^2) +
        ENNReal.ofReal (C * (T : ℝ) / gridK η) + R + 1 := by
  have hK : 0 < gridK η := Nat.ceil_pos.mpr (one_div_pos.mpr hη)
  change (initRegularWith T η hK ord finish).expectedCost E g () T final ≤ _
  rw [initRegularWith_expectedCost T η hK ord finish E hE.1 g hg T final hM]
  have hmono := ProbeTree.value_cost_mono
    (q := fun i : InitProbeIndex => P E (gpt (gridK η) i.2.1))
    (ProbeTree.allIndices_imp (initProbeTree_allPricesLegal T η hK ord)
      (fun i hi => hgap (gpt (gridK η) i.2.1) hi))
    (fun n o => (finish o).expectedCost E g () n final) T
  refine hmono.trans (initProbeTree_continuation_bound_of_failure hη hη₁ hKT
    E hE ord hfailure _ R ?_ hnone hgood)
  intro n hn o
  have hμ := (onUnit_facts E hE.1).2.2.2.1.2
  have hμ' : ENNReal.ofReal (muStar E) ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hμ
  simpa using (finish o).expectedCost_le_time E hE.1 g () n 1
    (fun x hx => (hgap x hx).trans ((regretGap_le E hE.1 x hx).trans hμ'))
    (fun k hk a => by simpa using hcap k (hk.trans hn) a)

end BilateralProfitRegular
end
end BundlePart067


section BundlePart068




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

section Initialization

variable (trigger : ℕ → ℝ → List Candidate → RandomProgram Unit Unit)

private def startedAfterInit (T : ℕ) : InitTreeOutput → RandomProgram Unit Unit
  | none => RandomProgram.play (fun _ => (0,0)) measurable_const (fun _ => zero_mem_triT)
  | some (δ, cs) => trigger T δ cs

/-- Use the candidates and scale returned by the initializer to run the refinement policy. -/
private def startedRegularProgram {T : ℕ} (hT : 2 ≤ T) : RandomProgram Unit Unit :=
  initRegularWith T (mainEta T) (Nat.ceil_pos.mpr (one_div_pos.mpr (mainEta_pos hT)))
    (actList (gridK (mainEta T))) (startedAfterInit trigger T)

/-- Pay the per-round baseline once over the full physical horizon. -/
private theorem startedRegularProgram_bound {T : ℕ} {Cinit Cbase D : ℝ} (hT : 2 ≤ T)
    (hInit : 0 ≤ Cinit) (hBase : 0 ≤ Cbase) (hD : 0 ≤ D)
    (E : Environment) (hE : RegularUnit E)
    (g : (ℝ × ℝ) → ℝ≥0∞) (hg : Measurable g) (hle : ∀ x ∈ triT, g x ≤ regretGap E x)
    (hbaseline : ∀ x ∈ triT, regretGap E x ≤ ENNReal.ofReal (Cbase * mainEta T) + g x)
    (hfailure : initCoinLaw
      {U | ¬ InitOutcomeGood Cinit T (mainEta T) E (actList (gridK (mainEta T))) U} ≤
        ENNReal.ofReal (1 / (T : ℝ)))
    (htrigger : ∀ δ cs, InitGuarantee E (mainEta T) δ cs →
      (cs.length : ℝ) ≤ Cinit * Real.sqrt (δ / mainEta T) * mainLog T →
      ∀ n ≤ T, (trigger T δ cs).expectedCost E g () n (Program.finalValue E) ≤
        ENNReal.ofReal (D * startedRate T)) :
    (startedRegularProgram trigger hT).expected E () T (Program.finalValue E) ≤
      ENNReal.ofReal ((Cbase + 3*Cinit + D + 1) * startedRate T) := by
  let b := ENNReal.ofReal (Cbase * mainEta T)
  let f := Program.finalValue E
  let R := ENNReal.ofReal (D * startedRate T)
  let p := startedRegularProgram trigger hT
  have hreg : p.expected E () T f ≤ (T : ℝ≥0∞) * b + p.expectedCost E g () T f :=
    p.expectedCost_le_add_baseline E hE.1 () T b hbaseline (fun _ _ _ => le_add_self)
  have hMu : ENNReal.ofReal (muStar E) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (onUnit_facts E hE.1).2.2.2.1.2
  have hcap (n : ℕ) (a : Unit) : f n a ≤ (n : ℝ≥0∞) :=
    (Program.finalValue_le E hE.1 n a).trans
      ((mul_le_mul' le_rfl hMu).trans_eq (mul_one _))
  have hsmall (n : ℕ) :
      (startedAfterInit trigger T none).expectedCost E g () n f ≤
        (n : ℝ≥0∞) * ENNReal.ofReal (muStar E) :=
    (startedAfterInit trigger T none).expectedCost_le_time E hE.1 g () n
      (ENNReal.ofReal (muStar E)) (fun x hx => (hle x hx).trans (regretGap_le E hE.1 x hx))
      (fun r _ a => Program.finalValue_le E hE.1 r a)
  have hb := initRegularWith_expectedCost_le (mainEta_pos hT) (mainEta_lt_one hT)
    (mainEta_grid_le_T hT) E hE (actList (gridK (mainEta T))) hfailure g hg hle
    (startedAfterInit trigger T) f (fun _ => measurable_const) R (fun n _ => hcap n)
    (fun n _ => hsmall n) (fun n hn δ cs hi hc => htrigger δ cs hi hc n hn)
  exact hreg.trans ((add_le_add_right hb _).trans (started_total_budget_le hT hInit hBase hD))

end Initialization

/-- The same family of one-bit policies has both the started-copy rate and its weaker
integer-logarithm-exponent form. -/
private theorem startedRegular_policy
    (trigger : ℕ → ℝ → List Candidate → RandomProgram Unit Unit)
    (g : ℕ → Environment → (ℝ × ℝ) → ℝ≥0∞)
    {Cinit Cbase D : ℝ} (hInit : 0 ≤ Cinit) (hBase : 0 ≤ Cbase) (hD : 0 ≤ D)
    (hg : ∀ T E, OnUnit E → Measurable (g T E))
    (hle : ∀ T, 2 ≤ T → ∀ E x, x ∈ triT → g T E x ≤ regretGap E x)
    (hbaseline : ∀ T, 2 ≤ T → ∀ E x, x ∈ triT →
      regretGap E x ≤ ENNReal.ofReal (Cbase * mainEta T) + g T E x)
    (hfailure : ∀ T, 2 ≤ T → ∀ E, RegularUnit E →
      initCoinLaw {U | ¬ InitOutcomeGood Cinit T (mainEta T) E (actList (gridK (mainEta T))) U} ≤
        ENNReal.ofReal (1 / (T : ℝ)))
    (htrigger : ∀ T, 2 ≤ T → ∀ E, RegularUnit E → ∀ δ cs, InitGuarantee E (mainEta T) δ cs →
      (cs.length : ℝ) ≤ Cinit * Real.sqrt (δ / mainEta T) * mainLog T →
      ∀ n ≤ T, (trigger T δ cs).expectedCost E (g T E) () n (Program.finalValue E) ≤
        ENNReal.ofReal (D * startedRate T)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret Q E.prior a ≤
              C * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^((7 : ℝ)/2) ∧
            (π T).regret Q E.prior a ≤ C * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^5 := by
  let Dtotal := Cbase + 3*Cinit + D + 1
  have hTotal : 0 < Dtotal := by dsimp only [Dtotal]; positivity
  obtain ⟨Ω, mΩ, Q, hQ, π, hBit, hBound⟩ :=
    common_seed_policy (fun T => Dtotal * startedRate T)
      (fun T hT => mul_nonneg hTotal.le (zero_le_one.trans (one_le_startedRate hT))) (by
        intro T hT
        exact ⟨startedRegularProgram trigger hT, fun E hE =>
          startedRegularProgram_bound trigger hT hInit hBase hD E hE (g T E) (hg T E hE.1)
            (hle T hT E) (hbaseline T hT E) (hfailure T hT E hE) (htrigger T hT E hE)⟩)
  refine ⟨32 * Dtotal, by positivity, Ω, mΩ, Q, hQ, π, hBit, ?_⟩
  intro T hT E hE a ha
  have h := hBound T hT E hE a ha
  constructor
  · refine h.trans ((mul_le_mul_of_nonneg_left (startedRate_le_log_pow hT) hTotal.le).trans ?_)
    have hP : 0 ≤ (T : ℝ)^((3 : ℝ)/5) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hL : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
    have hD' : Dtotal * 16 ≤ 32 * Dtotal := by linarith only [hTotal]
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD' hP) (Real.rpow_nonneg hL _)
  · exact h.trans ((mul_le_mul_of_nonneg_left (startedRate_le_final hT) hTotal.le).trans_eq (by ring))

end BilateralProfitRegular
end
end BundlePart068


section BundlePart069




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem started_policy_from_trigger
    (trigger : ℕ → ℝ → List Candidate → RandomProgram Unit Unit)
    (htrigger : ∀ T, 2 ≤ T → ∀ E, RegularUnit E → ∀ δ cs, InitGuarantee E (mainEta T) δ cs →
      ∀ n ≤ T,
        (trigger T δ cs).expectedCost E
          (fun x => ENNReal.ofReal (muStar E - mu E x - 520 * mainEta T))
          () n (Program.finalValue E) ≤
        startedBudget (numCopies startedC₀ T) (startedRunMax startedC₀ T)
          (ENNReal.ofReal (startedCopyCostConstant * mainLog T^2))
          (ENNReal.ofReal (5000000000 * mainLog T / mainEta T) + 2)
          (startedPhaseCount startedC₀ T * cs.length) n) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret Q E.prior a ≤
              C * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^((7 : ℝ)/2) ∧
            (π T).regret Q E.prior a ≤ C * (T : ℝ)^((3 : ℝ)/5) * Real.log (T : ℝ)^5 := by
  obtain ⟨Cinit, hInit, hFailure⟩ := lemma_6_4
  let g (T : ℕ) (E : Environment) (x : ℝ × ℝ) :=
    ENNReal.ofReal (muStar E - mu E x - 520 * mainEta T)
  have hCal : (0 : ℝ) ≤ 5000000000 := by norm_num
  have hBase : (0 : ℝ) ≤ 520 := by norm_num
  have hMeas (T : ℕ) (E : Environment) (hE : OnUnit E) : Measurable (g T E) :=
    ((measurable_const.sub ((measurable_snd.sub measurable_fst).mul (measurable_P E hE))).sub
      measurable_const).ennreal_ofReal
  have hle (T : ℕ) (hT : 2 ≤ T) (E : Environment) (x : ℝ × ℝ) :
      g T E x ≤ regretGap E x :=
    ENNReal.ofReal_le_ofReal (sub_le_self _ (mul_nonneg hBase (mainEta_pos hT).le))
  have hbaseline (T : ℕ) (E : Environment) (x : ℝ × ℝ) :
      regretGap E x ≤ ENNReal.ofReal (520 * mainEta T) + g T E x := by
    have h := ENNReal.ofReal_add_le (p := 520 * mainEta T)
      (q := muStar E - mu E x - 520 * mainEta T)
    rwa [add_sub_cancel] at h
  refine startedRegular_policy trigger g hInit.le hBase
    (startedTriggerConstant_nonneg (C₀ := startedC₀) hInit.le hCal startedCopyCostConstant_nonneg)
    hMeas (fun T hT E x _ => hle T hT E x) (fun T _ E x _ => hbaseline T E x) ?_ ?_
  · intro T hT E hE
    exact hFailure T (mainEta T) (mainEta_pos hT) (mainEta_lt_one hT) (mainEta_grid_le_T hT)
      E hE _ (actList_isOrder _)
  · intro T hT E hE δ cs hCert hCount n hn
    have hδ₁ := hCert.2.1.trans (onUnit_facts E hE.1).2.2.2.1.2
    exact (htrigger T hT E hE δ cs hCert n hn).trans
      (started_trigger_budget_le hT startedC₀_pos hInit.le hCal startedCopyCostConstant_nonneg
        hδ₁ hCount hn)

end BilateralProfitRegular
end
end BundlePart069


section BundlePart070



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- The one-bit regular policy achieves the started-copy rate and the stated regret rate. -/
private theorem theorem_6_1_started_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret P E.prior a ≤
              C * (T : ℝ) ^ ((3 : ℝ) / 5) * Real.log (T : ℝ)^((7 : ℝ) / 2) ∧
            (π T).regret P E.prior a ≤ C * (T : ℝ) ^ ((3 : ℝ) / 5) * Real.log (T : ℝ)^5 :=
  started_policy_from_trigger startedTriggered
    (fun _ hT E hE _ _ hi n hn => startedTriggered_expected_le E hE hT hi n hn)

private theorem theorem_6_1_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret P E.prior a ≤ C * (T : ℝ) ^ ((3 : ℝ) / 5) * Real.log T ^ 5 := by
  obtain ⟨C, hC, Ω, mΩ, P, hP, π, hBit, hRegret⟩ := theorem_6_1_started_regret_bound
  exact ⟨C, hC, Ω, mΩ, P, hP, π, hBit, fun T hT E hE a ha => (hRegret T hT E hE a ha).2⟩

end BilateralProfitRegular
end
end BundlePart070

open BilateralProfitRegular
open MeasureTheory MechanismDesign.BilateralTrade

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret P E.prior a ≤ C * (T : ℝ) ^ ((3 : ℝ) / 5) * Real.log T ^ 5 := by
  exact BilateralProfitRegular.theorem_6_1_regret_bound
