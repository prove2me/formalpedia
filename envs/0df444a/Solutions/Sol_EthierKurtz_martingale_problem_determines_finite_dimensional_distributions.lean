-- Prove2me | solution 1 for EthierKurtz.martingale_problem_determines_finite_dimensional_distributions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T23:48:34.597799+00:00
-- url     : https://prove2.me/submissions/ccf2e40b-09d0-4761-a9c9-7dd97f89be9f

import Mathlib
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

set_option autoImplicit false

section S_K3

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped Topology

namespace P_e7f29b55

lemma intOn_exp_mul {g : ℝ → ℝ} {M : ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ))))
    (hM : ∀ t, 0 < t → |g t| ≤ M) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => Real.exp (-c * t) * g t) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-c * t) * M) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).mul_const M
  refine Integrable.mono' hb
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-c * t)).aestronglyMeasurable.mul hg) ?_
  refine (ae_restrict_iff' (measurableSet_Ioi (a := (0:ℝ)))).2 (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM t ht) (Real.exp_pos _).le

/-- K3: uniqueness of the Laplace transform for bounded functions continuous on [0,∞). -/
theorem K3_laplace_unique (d : ℝ → ℝ) (hd : ContinuousOn d (Set.Ici 0))
    (hC : ∃ C, ∀ t, 0 ≤ t → |d t| ≤ C)
    (hL : ∀ lam : ℝ, 0 < lam → ∫ t in Set.Ioi (0:ℝ), Real.exp (-lam * t) * d t = 0) :
    ∀ t, 0 ≤ t → d t = 0 := by
  obtain ⟨C, hC⟩ := hC
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 le_rfl)
  have hdm : AEStronglyMeasurable d (volume.restrict (Ioi (0:ℝ))) :=
    (hd.mono Ioi_subset_Ici_self).aestronglyMeasurable (measurableSet_Ioi (a := (0:ℝ)))
  have hexp01 : ∀ t : ℝ, 0 < t → Real.exp (-t) ∈ Icc (0:ℝ) 1 := fun t ht =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
  -- moments
  have hmom : ∀ n : ℕ,
      ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) * (Real.exp (-t) ^ n * d t) = 0 := by
    intro n
    refine Eq.trans ?_ (hL ((n : ℝ) + 1) (by positivity))
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) (fun t _ => ?_)
    show Real.exp (-1 * t) * (Real.exp (-t) ^ n * d t) = Real.exp (-((n : ℝ) + 1) * t) * d t
    rw [← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  -- integrability of polynomial-weighted terms
  have hint : ∀ (q : ℝ → ℝ), Continuous q →
      IntegrableOn (fun t => Real.exp (-1 * t) * (q (Real.exp (-t)) * d t)) (Ioi 0) := by
    intro q hq
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
      hq.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
    refine intOn_exp_mul (g := fun t => q (Real.exp (-t)) * d t) (M := B * C)
      ((hq.comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable.mul hdm)
      (fun t ht => ?_) one_pos
    rw [abs_mul]
    have := hB _ (hexp01 t ht)
    rw [Real.norm_eq_abs] at this
    exact mul_le_mul this (hC t ht.le) (abs_nonneg _) hB0
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) * (p.eval (Real.exp (-t)) * d t) = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have e : ∀ t, Real.exp (-1 * t) * ((p + q).eval (Real.exp (-t)) * d t) =
          Real.exp (-1 * t) * (p.eval (Real.exp (-t)) * d t) +
            Real.exp (-1 * t) * (q.eval (Real.exp (-t)) * d t) := by
        intro t; rw [Polynomial.eval_add]; ring
      simp_rw [e]
      rw [integral_add (hint _ p.continuous) (hint _ q.continuous), hp, hq, add_zero]
    | monomial n a =>
      have : ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) *
            ((Polynomial.monomial n a).eval (Real.exp (-t)) * d t)
          = a * ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) * (Real.exp (-t) ^ n * d t) := by
        rw [← integral_const_mul]; congr 1; funext t; rw [Polynomial.eval_monomial]; ring
      rw [this, hmom n, mul_zero]
  -- continuous compactly supported test functions inside (0,∞)
  have htest : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      ∫ t, φ t • d t = 0 := by
    intro φ hφ hφc hφs
    obtain ⟨b, hb⟩ := hφc.isCompact.bddAbove
    have hzero : ∀ s : ℝ, b < s → φ s = 0 := fun s hs =>
      image_eq_zero_of_notMem_tsupport (fun h => absurd (hb h) (not_le.2 hs))
    set ψ : ℝ → ℝ := fun u => if 0 < u then φ (-Real.log u) / u else 0 with hψdef
    have hψ : Continuous ψ := by
      refine continuous_iff_continuousAt.2 fun u => ?_
      by_cases hu : 0 < u
      · have h1 : ContinuousAt (fun v => φ (-Real.log v) / v) u :=
          ((hφ.continuousAt.comp (Real.continuousAt_log hu.ne').neg)).div continuousAt_id hu.ne'
        refine h1.congr ((lt_mem_nhds hu).mono fun v hv => ?_)
        simp [ψ, hv]
      · have hu' : u < Real.exp (-b) := lt_of_le_of_lt (not_lt.1 hu) (Real.exp_pos _)
        refine (continuousAt_const (y := (0:ℝ))).congr ((gt_mem_nhds hu').mono fun v hv => ?_)
        by_cases hv0 : 0 < v
        · have : b < -Real.log v := by
            have := (Real.log_lt_iff_lt_exp hv0).2 hv
            linarith
          simp [ψ, hv0, hzero _ this]
        · simp [ψ, hv0]
    have hkey : ∀ t : ℝ, 0 < t → Real.exp (-1 * t) * ψ (Real.exp (-t)) = φ t := by
      intro t _
      simp only [ψ, Real.exp_pos, if_true, Real.log_exp, neg_neg, neg_one_mul]
      field_simp
    have hφd : ∫ t, φ t • d t = ∫ t in Ioi (0:ℝ), φ t * d t := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · rfl
      · intro t ht
        rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hφs h)), zero_mul]
    rw [hφd]
    set X := ∫ t in Ioi (0:ℝ), φ t * d t with hX
    set I := ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) with hI
    have hI0 : 0 ≤ I := setIntegral_nonneg (measurableSet_Ioi (a := (0:ℝ))) fun t _ => (Real.exp_pos _).le
    have hbound : ∀ ε : ℝ, 0 < ε → |X| ≤ I * (ε * C) := by
      intro ε hε
      obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 ψ hψ.continuousOn ε hε
      have hsplit : X = ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) *
          ((ψ (Real.exp (-t)) - p.eval (Real.exp (-t))) * d t) := by
        have h2 : ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) *
            ((ψ (Real.exp (-t)) - p.eval (Real.exp (-t))) * d t) =
            (∫ t in Ioi (0:ℝ), Real.exp (-1 * t) * ((ψ (Real.exp (-t))) * d t)) -
            ∫ t in Ioi (0:ℝ), Real.exp (-1 * t) * (p.eval (Real.exp (-t)) * d t) := by
          rw [← integral_sub (hint _ hψ) (hint _ p.continuous)]
          congr 1; funext t; ring
        rw [h2, hpoly p, sub_zero, hX]
        refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) (fun t ht => ?_)
        show φ t * d t = Real.exp (-1 * t) * (ψ (Real.exp (-t)) * d t)
        rw [← mul_assoc, hkey t ht]
      rw [hsplit, ← Real.norm_eq_abs, hI, ← integral_mul_const]
      refine norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 one_pos).mul_const _) ?_
      refine (ae_restrict_iff' (measurableSet_Ioi (a := (0:ℝ)))).2 (Eventually.of_forall fun t ht => ?_)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have := hp _ (hexp01 t ht)
      rw [abs_sub_comm] at this
      exact mul_le_mul this.le (hC t (le_of_lt ht)) (abs_nonneg _) hε.le
    by_contra hne
    have hpos : 0 < |X| := abs_pos.2 hne
    have hK : 0 ≤ I * C := mul_nonneg hI0 hC0
    have := hbound (|X| / (I * C + 1)) (by positivity)
    have h3 : I * (|X| / (I * C + 1) * C) = |X| * (I * C / (I * C + 1)) := by ring
    rw [h3] at this
    have h4 : I * C / (I * C + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    nlinarith
  -- a.e. vanishing on (0,∞), then continuity
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (f := d)
    ((hd.mono Ioi_subset_Ici_self).locallyIntegrableOn (measurableSet_Ioi (a := (0:ℝ))))
    (fun g hg hgc hgs => htest g hg.continuous hgc hgs)
  have hae' : d =ᵐ[volume.restrict (Ioi (0:ℝ))] fun _ => (0:ℝ) :=
    (ae_restrict_iff' (measurableSet_Ioi (a := (0:ℝ)))).2 hae
  have hEq : EqOn d (fun _ => (0:ℝ)) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi (hd.mono Ioi_subset_Ici_self) continuousOn_const
  intro t ht
  rcases ht.lt_or_eq with ht | rfl
  · exact hEq ht
  · have h1 : Tendsto d (𝓝[>] 0) (𝓝 (d 0)) := (hd 0 (le_refl (0:ℝ))).mono Ioi_subset_Ici_self
    have h2 : Tendsto d (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hEq hx).symm)
    exact tendsto_nhds_unique h1 h2

end P_e7f29b55

end S_K3

section S_K2

set_option autoImplicit false

open Filter
open scoped Topology

namespace P_e7f29b55

section HY
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section relation

variable (A : Submodule ℝ (E × E))

/-- Dissipativity of a linear relation. -/
def Diss : Prop := ∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖

variable {A}

lemma diss_zero (hA : Diss A) {l : ℝ} (hl : 0 < l) {f g : E} (h : (f, g) ∈ A)
    (h0 : l • f - g = 0) : f = 0 := by
  have := hA (f, g) h l hl
  simp only [h0, norm_zero] at this
  have : ‖f‖ ≤ 0 := by nlinarith [norm_nonneg f]
  exact norm_le_zero_iff.mp this

/-- Step 1: dense range of `l - A` is full range, for closed dissipative `A`. -/
lemma range_full [CompleteSpace E] (hcl : IsClosed (A : Set (E × E))) (hA : Diss A) {l : ℝ}
    (hl : 0 < l) (h : E) (hr : ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < δ) :
    ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hex : ∀ k : ℕ, ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < 1 / ((k : ℝ) + 1) :=
    fun k => hr _ (by positivity)
  choose p hpA hpn using hex
  have hcau : ∀ m k : ℕ, ‖(p m).1 - (p k).1‖ ≤ l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((k : ℝ) + 1)) := by
    intro m k
    have hd := hA (p m - p k) (A.sub_mem (hpA m) (hpA k)) l hl
    simp only [Prod.fst_sub, Prod.snd_sub] at hd
    have e : l • ((p m).1 - (p k).1) - ((p m).2 - (p k).2)
        = ((l • (p m).1 - (p m).2) - h) - ((l • (p k).1 - (p k).2) - h) := by
      rw [smul_sub]; abel
    rw [e] at hd
    have h2 := norm_sub_le ((l • (p m).1 - (p m).2) - h) ((l • (p k).1 - (p k).2) - h)
    rw [le_inv_mul_iff₀ hl]
    linarith [hpn m, hpn k]
  have hC : CauchySeq (fun k => (p k).1) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (l * ε))
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hcau m N) ?_
    have hN' : (0 : ℝ) < N + 1 := by positivity
    have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hN' hm'
    have h3 : 2 / ((N : ℝ) + 1) < l * ε / 2 := by
      have : 4 / (l * ε) < N + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hN']
      nlinarith [mul_pos hl hε]
    calc l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((N : ℝ) + 1)) ≤ l⁻¹ * (2 / ((N : ℝ) + 1)) := by
          gcongr
          rw [show (2:ℝ) / ((N:ℝ) + 1) = 1 / ((N:ℝ) + 1) + 1 / ((N:ℝ) + 1) by ring]
          linarith
      _ < l⁻¹ * (l * ε / 2) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hC
  have hres : Tendsto (fun k => (l • (p k).1 - (p k).2) - h) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hpn k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun k => (p k).2) atTop (𝓝 (l • f - h)) := by
    have : Tendsto (fun k => l • (p k).1 - ((l • (p k).1 - (p k).2) - h) - h) atTop
        (𝓝 (l • f - 0 - h)) :=
      ((hf.const_smul l).sub hres).sub tendsto_const_nhds
    simp only [sub_zero] at this
    refine this.congr (fun k => ?_)
    abel
  have hmem : (f, l • f - h) ∈ A :=
    hcl.mem_of_tendsto (hf.prodMk_nhds hg) (Eventually.of_forall hpA)
  exact ⟨(f, l • f - h), hmem, by simp⟩

/-- Step 4: the resolvent as a bounded operator. -/
lemma exists_resolvent (hA : Diss A) {l : ℝ} (hl : 0 < l)
    (hs : ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h) :
    ∃ R : E →L[ℝ] E, (∀ h, (R h, l • R h - h) ∈ A) ∧ (∀ h, ‖R h‖ ≤ l⁻¹ * ‖h‖) := by
  have hex : ∀ h : E, ∃ f : E, (f, l • f - h) ∈ A := by
    intro h
    obtain ⟨fg, hfg, he⟩ := hs h
    refine ⟨fg.1, ?_⟩
    have : l • fg.1 - h = fg.2 := by rw [← he]; abel
    rw [this]; exact hfg
  choose r hr using hex
  have uniq : ∀ h : E, ∀ f : E, (f, l • f - h) ∈ A → r h = f := by
    intro h f hf
    have hm := A.sub_mem (hr h) hf
    have := diss_zero hA hl hm (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [smul_sub]; abel)
    exact sub_eq_zero.mp this
  let L : E →ₗ[ℝ] E :=
    { toFun := r
      map_add' := fun x y => by
        refine (uniq (x + y) (r x + r y) ?_).trans rfl
        have := A.add_mem (hr x) (hr y)
        convert this using 1
        simp only [Prod.mk_add_mk, smul_add]; congr 1; abel
      map_smul' := fun s x => by
        refine (uniq (s • x) (s • r x) ?_).trans rfl
        have := A.smul_mem s (hr x)
        convert this using 1
        simp only [Prod.smul_mk, smul_sub, smul_comm l s] }
  have hb : ∀ h, ‖r h‖ ≤ l⁻¹ * ‖h‖ := by
    intro h
    have := hA _ (hr h) l hl
    simp only [sub_sub_cancel] at this
    rw [le_inv_mul_iff₀ hl]; exact this
  exact ⟨L.mkContinuous l⁻¹ hb, fun h => hr h, hb⟩

/-- Step 3a: surjectivity of `l - A` propagates from `l₁` to `(0, 2 l₁)` (Neumann series). -/
lemma range_step [CompleteSpace E] (hA : Diss A) {l₁ : ℝ} (hl₁ : 0 < l₁)
    (hs₁ : ∀ h : E, ∃ fg ∈ A, l₁ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) (hll : l < 2 * l₁) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  obtain ⟨R, hR, hRb⟩ := exists_resolvent hA hl₁ hs₁
  have hRn : ‖R‖ ≤ l₁⁻¹ := ContinuousLinearMap.opNorm_le_bound _ (by positivity) hRb
  set K : E →L[ℝ] E := (l₁ - l) • R with hK
  have hKn : ‖K‖ < 1 := by
    calc ‖K‖ ≤ |l₁ - l| * ‖R‖ := by rw [hK, norm_smul, Real.norm_eq_abs]
      _ ≤ |l₁ - l| * l₁⁻¹ := by gcongr
      _ < 1 := by
          rw [← div_eq_mul_inv, div_lt_one hl₁, abs_lt]
          constructor <;> linarith
  intro h
  set U := Units.oneSub K hKn
  set f : E := (↑U⁻¹ : E →L[ℝ] E) (R h) with hf
  have hU : f - K f = R h := by
    have e := congrArg (fun T : E →L[ℝ] E => T (R h)) (Units.mul_inv U)
    simp only [ContinuousLinearMap.mul_apply, Units.val_oneSub, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at e
    rw [← hf] at e
    exact e
  set h' : E := h + (l₁ - l) • f with hh'
  have hRf : R h' = f := by
    rw [hh', map_add, map_smul]
    have : K f = (l₁ - l) • R f := by rw [hK]; rfl
    rw [← this]
    rw [← hU]; abel
  refine ⟨(R h', l₁ • R h' - h'), hR h', ?_⟩
  show l • R h' - (l₁ • R h' - h') = h
  rw [hRf, hh', sub_smul]; abel

/-- Step 3b: full range for every positive `l`. -/
lemma range_all [CompleteSpace E] (hA : Diss A) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hs₀ : ∀ h : E, ∃ fg ∈ A, l₀ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hk : ∀ k : ℕ, ∀ h : E, ∃ fg ∈ A, (l₀ * (3 / 2 : ℝ) ^ k) • fg.1 - fg.2 = h := by
    intro k
    induction k with
    | zero => simpa using hs₀
    | succ k ih =>
      have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
      refine range_step hA hp ih (by positivity) ?_
      rw [pow_succ]; nlinarith
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (l / l₀) (by norm_num : (1 : ℝ) < 3 / 2)
  have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
  refine range_step hA hp (hk k) hl ?_
  rw [div_lt_iff₀ hl₀] at hk'
  nlinarith

end relation
end HY

open EthierKurtz in
/-- K2: full range of `lam - closure A'` on `L` for every `lam > 0` (EK Prop 1.2.6 / Thm 1.2.12 step). -/
theorem K2_range_all {E : Type*}
    (A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (L : Submodule ℝ (UniformBoundedFunction E)) (a : ℝ) (ha : 0 < a)
    (hdiss : ∀ fg ∈ A', ∀ b : ℝ, 0 < b → b * ‖fg.1‖ ≤ ‖b • fg.1 - fg.2‖)
    (hr : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _))
    (hd : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set _)) :
    ∀ lam : ℝ, 0 < lam → ∀ h ∈ L, ∃ fg ∈ A'.topologicalClosure,
      lam • fg.1 - fg.2 = h ∧ fg.1 ∈ L ∧ fg.2 ∈ L := by
  set G := A'.topologicalClosure with hG
  have hGc : IsClosed (G : Set (UniformBoundedFunction E × UniformBoundedFunction E)) :=
    A'.isClosed_topologicalClosure
  have hGd : Diss G := by
    intro fg hfg b hb
    have hS : IsClosed {fg : UniformBoundedFunction E × UniformBoundedFunction E |
        b * ‖fg.1‖ ≤ ‖b • fg.1 - fg.2‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : (A' : Set (UniformBoundedFunction E × UniformBoundedFunction E)) ⊆
        {fg | b * ‖fg.1‖ ≤ ‖b • fg.1 - fg.2‖} :=
      fun fg hfg => hdiss fg hfg b hb
    have hcl := closure_minimal hsub hS
    rw [hG, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hfg
    exact hcl hfg
  have hG1 : ∀ fg ∈ G, fg.1 ∈ L := by
    intro fg hfg
    rw [hG, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hfg
    have := image_closure_subset_closure_image
      (f := fun fg : UniformBoundedFunction E × UniformBoundedFunction E => fg.1) continuous_fst
      ⟨fg, hfg, rfl⟩
    rw [hd] at this; exact this
  have hG2 : ∀ fg ∈ G, a • fg.1 - fg.2 ∈ L := by
    intro fg hfg
    rw [hG, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hfg
    have := image_closure_subset_closure_image
      (f := fun fg : UniformBoundedFunction E × UniformBoundedFunction E => a • fg.1 - fg.2)
      (by fun_prop) ⟨fg, hfg, rfl⟩
    rw [hr] at this; exact this
  have hG2' : ∀ fg ∈ G, fg.2 ∈ L := by
    intro fg hfg
    have := L.sub_mem (L.smul_mem a (hG1 fg hfg)) (hG2 fg hfg)
    rwa [sub_sub_cancel] at this
  have hLc : IsClosed (L : Set (UniformBoundedFunction E)) := hr ▸ isClosed_closure
  haveI : CompleteSpace L := hLc.completeSpace_coe
  set φ : (L × L) →ₗ[ℝ] (UniformBoundedFunction E × UniformBoundedFunction E) :=
    L.subtype.prodMap L.subtype with hφ
  set G' := G.comap φ with hG'
  have hφa : ∀ x : L × L, φ x = ((x.1 : UniformBoundedFunction E), (x.2 : UniformBoundedFunction E)) :=
    fun x => rfl
  have hG'd : Diss G' := by
    intro fg hfg b hb
    have := hGd (φ fg) hfg b hb
    rw [hφa] at this
    simpa using this
  have hs₀ : ∀ h : L, ∃ fg ∈ G', a • fg.1 - fg.2 = h := by
    intro h
    have hh : (h : UniformBoundedFunction E) ∈ closure
        ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E => a • fg.1 - fg.2) ''
          (A' : Set _)) := by
      rw [hr]; exact h.2
    obtain ⟨fg, hfg, he⟩ := range_full hGc hGd ha (h : UniformBoundedFunction E) (fun δ hδ => by
      obtain ⟨y, ⟨fg, hfg, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hh δ hδ
      refine ⟨fg, A'.le_topologicalClosure hfg, ?_⟩
      rw [← dist_eq_norm, dist_comm]; exact hy)
    refine ⟨(⟨fg.1, hG1 fg hfg⟩, ⟨fg.2, hG2' fg hfg⟩), ?_, ?_⟩
    · show φ _ ∈ G
      rw [hφa]; exact hfg
    · apply Subtype.ext; simpa using he
  intro lam hlam h hh
  obtain ⟨fg, hfg, he⟩ := range_all hG'd ha hs₀ hlam ⟨h, hh⟩
  refine ⟨φ fg, hfg, ?_, fg.1.2, fg.2.2⟩
  rw [hφa]
  have := congrArg Subtype.val he
  simpa using this

end P_e7f29b55

end S_K2

section S_K1

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace P_e7f29b55

open EthierKurtz in
lemma ubf_bound {E : Type*} (f : UniformBoundedFunction E) (x : E) : |f x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  rwa [Real.norm_eq_abs] at this

open EthierKurtz in
lemma prod_bound {E : Type*} {n : ℕ} (k : Fin n → UniformBoundedFunction E) (x : Fin n → E) :
    |∏ i, k i (x i)| ≤ ∏ i, ‖k i‖ := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ubf_bound _ _)

open EthierKurtz in
/-- K1a (generic weight): the martingale identity gives
`φ(t) - φ(0) = ∫_0^t ψ`, with `φ(u) = E[f(X(s+u)) W]`, `ψ(u) = E[g(X(s+u)) W]`. -/
lemma K1a_fubini_W {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (f g : UniformBoundedFunction E) (hf : Measurable (f : E → ℝ)) (hg : Measurable (g : E → ℝ))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (hmp : ∀ τ : ℝ≥0, ∫ ω, (f (X (s + τ) ω) - f (X s ω) -
        ∫ u in (s : ℝ)..((s + τ : ℝ≥0) : ℝ), g (X u.toNNReal ω)) * W ω ∂P = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, f (X (s + t.toNNReal) ω) * W ω ∂P - ∫ ω, f (X s ω) * W ω ∂P
      = ∫ u in (0:ℝ)..t, ∫ ω, g (X (s + u.toNNReal) ω) * W ω ∂P := by
  have hXt : ∀ τ : ℝ≥0, Measurable (X τ) := fun τ =>
    hXm.comp (measurable_const.prodMk measurable_id)
  have hint1 : ∀ τ : ℝ≥0, Integrable (fun ω => f (X τ ω) * W ω) P := by
    intro τ
    refine Integrable.of_bound ((hf.comp (hXt τ)).mul hW).aestronglyMeasurable (‖f‖ * CW)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ubf_bound _ _) (hWb ω) (abs_nonneg _) (norm_nonneg _)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hFint : Integrable (Function.uncurry fun (u : ℝ) (ω : Ω) => g (X (s + u.toNNReal) ω) * W ω)
      ((volume.restrict (Set.uIoc (0:ℝ) t)).prod P) := by
    refine Integrable.of_bound ?_ (‖g‖ * CW) (Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (hg.comp (hXm.comp ((measurable_const.add measurable_fst.real_toNNReal).prodMk
        measurable_snd))).mul (hW.comp measurable_snd)
    · show ‖g (X (s + p.1.toNNReal) p.2) * W p.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (ubf_bound _ _) (hWb _) (abs_nonneg _) (norm_nonneg _)
  have hcW : Integrable (fun ω => ∫ u in (0:ℝ)..t, g (X (s + u.toNNReal) ω) * W ω) P := by
    refine hFint.integral_prod_right.congr (Eventually.of_forall fun ω => ?_)
    show ∫ u in Set.uIoc (0:ℝ) t, g (X (s + u.toNNReal) ω) * W ω =
      ∫ u in (0:ℝ)..t, g (X (s + u.toNNReal) ω) * W ω
    rw [intervalIntegral.integral_of_le ht, Set.uIoc_of_le ht]
  have hpt : ∀ ω, (∫ u in (s:ℝ)..((s + t.toNNReal : ℝ≥0) : ℝ), g (X u.toNNReal ω)) * W ω
      = ∫ u in (0:ℝ)..t, g (X (s + u.toNNReal) ω) * W ω := by
    intro ω
    rw [intervalIntegral.integral_mul_const]
    congr 1
    rw [NNReal.coe_add, Real.coe_toNNReal t ht]
    have e := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := t)
      (fun u : ℝ => g (X u.toNNReal ω)) (s : ℝ)
    beta_reduce at e
    rw [zero_add, add_comm t] at e
    rw [← e]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le ht] at hu
    have hu' : (u + (s:ℝ)).toNNReal = s + u.toNNReal := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by linarith [hu.1, NNReal.coe_nonneg s]), NNReal.coe_add,
        Real.coe_toNNReal _ hu.1, add_comm]
    simp only [hu']
  have hMP : ∫ ω, ((f (X (s + t.toNNReal) ω) * W ω - f (X s ω) * W ω) -
      ∫ u in (0:ℝ)..t, g (X (s + u.toNNReal) ω) * W ω) ∂P = 0 := by
    refine Eq.trans ?_ (hmp t.toNNReal)
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show _ = (f (X (s + t.toNNReal) ω) - f (X s ω) -
        ∫ u in (s : ℝ)..((s + t.toNNReal : ℝ≥0) : ℝ), g (X u.toNNReal ω)) * W ω
    rw [sub_mul, hpt ω, sub_mul]
  rw [integral_sub (f := fun ω => f (X (s + t.toNNReal) ω) * W ω - f (X s ω) * W ω)
    ((hint1 _).sub (hint1 _)) hcW, integral_sub (hint1 _) (hint1 _), sub_eq_zero] at hMP
  rw [hMP, intervalIntegral_integral_swap hFint]

open EthierKurtz in
/-- K1a for the martingale problem with a past-product weight. -/
theorem K1a_fubini {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)
    (fg : UniformBoundedFunction E × UniformBoundedFunction E) (hfg : fg ∈ A)
    (hf : Measurable (fg.1 : E → ℝ)) (hg : Measurable (fg.2 : E → ℝ))
    (s : ℝ≥0) (n : ℕ) (r : Fin n → ℝ≥0) (hr : ∀ i, r i ≤ s)
    (k : Fin n → UniformBoundedFunction E) (hk : ∀ i, Measurable (k i))
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, fg.1 (X (s + t.toNNReal) ω) * ∏ i, k i (X (r i) ω) ∂P
      - ∫ ω, fg.1 (X s ω) * ∏ i, k i (X (r i) ω) ∂P
      = ∫ u in (0:ℝ)..t, ∫ ω, fg.2 (X (s + u.toNNReal) ω) * ∏ i, k i (X (r i) ω) ∂P := by
  have hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) := hX.1
  have hXt : ∀ τ : ℝ≥0, Measurable (X τ) := fun τ =>
    hXm.comp (measurable_const.prodMk measurable_id)
  exact K1a_fubini_W P X hXm fg.1 fg.2 hf hg s (fun ω => ∏ i, k i (X (r i) ω))
    (Finset.measurable_prod _ (fun i _ => (hk i).comp (hXt (r i)))) _
    (fun ω => prod_bound k (fun i => X (r i) ω))
    (fun τ => hX.2.2 fg hfg s (s + τ) le_self_add n r hr k hk) t ht

end P_e7f29b55

end S_K1

section S_K1b

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped Topology

namespace P_e7f29b55

lemma exp_Ioi_eq (lam : ℝ) (hlam : 0 < lam) (c : ℝ) :
    ∫ t in Ioi c, Real.exp (-lam * t) = Real.exp (-lam * c) / lam := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hlam) c, neg_div_neg_eq]

/-- Fubini on the triangle `0 < u ≤ t`: the Laplace transform of a primitive. -/
lemma K1b_key (lam C : ℝ) (hlam : 0 < lam) (ψ : ℝ → ℝ)
    (hψb : ∀ t, |ψ t| ≤ C) (hψm : AEStronglyMeasurable ψ volume) :
    IntegrableOn (fun t => lam * Real.exp (-lam * t) * ∫ u in (0:ℝ)..t, ψ u) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), lam * Real.exp (-lam * t) * ∫ u in (0:ℝ)..t, ψ u
      = ∫ u in Ioi (0:ℝ), Real.exp (-lam * u) * ψ u := by
  let F : ℝ → ℝ → ℝ := fun t u => if u ≤ t then lam * Real.exp (-lam * t) * ψ u else 0
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hFeq : Function.uncurry F = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
      (fun p => lam * Real.exp (-lam * p.1) * ψ p.2) := by
    funext p
    simp only [Function.uncurry, F, Set.indicator_apply, Set.mem_ofPred_eq]
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [hFeq]
    refine AEStronglyMeasurable.indicator ?_ hS
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
      lam * Real.exp (-lam * p.1)).aestronglyMeasurable).mul (hψm.restrict.comp_snd)
  have he : Integrable (fun t : ℝ => Real.exp (-(lam/2) * t)) (volume.restrict (Ioi (0:ℝ))) :=
    exp_neg_integrableOn_Ioi 0 (half_pos hlam)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Integrable.mono' ((he.const_mul (lam * C)).mul_prod he) hmeas
      (Eventually.of_forall fun p => ?_)
    show ‖F p.1 p.2‖ ≤ lam * C * Real.exp (-(lam/2) * p.1) * Real.exp (-(lam/2) * p.2)
    simp only [F]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp (-lam * p.1) ≤
          Real.exp (-(lam/2) * p.1) * Real.exp (-(lam/2) * p.2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc lam * Real.exp (-lam * p.1) * |ψ p.2|
          ≤ lam * (Real.exp (-(lam/2) * p.1) * Real.exp (-(lam/2) * p.2)) * C := by
            gcongr
            exact hψb _
        _ = _ := by ring
    · rw [norm_zero]
      have hC : 0 ≤ C := le_trans (abs_nonneg _) (hψb 0)
      positivity
  have hpt : ∀ t ∈ Ioi (0:ℝ), lam * Real.exp (-lam * t) * ∫ u in (0:ℝ)..t, ψ u
      = ∫ u in Ioi (0:ℝ), F t u := by
    intro t ht
    have : (fun u => F t u) = (Iic t).indicator (fun u => lam * Real.exp (-lam * t) * ψ u) := by
      funext u
      simp only [F, Set.indicator_apply, Set.mem_Iic]
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      intervalIntegral.integral_of_le (le_of_lt ht), integral_const_mul]
  have hR : ∀ u ∈ Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), F t u = Real.exp (-lam * u) * ψ u := by
    intro u hu
    have : (fun t => F t u) = (Ici u).indicator (fun t => lam * Real.exp (-lam * t) * ψ u) := by
      funext t
      simp only [F, Set.indicator_apply, Set.mem_Ici]
    rw [this, setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr hu), integral_Ici_eq_integral_Ioi,
      integral_mul_const, integral_const_mul, exp_Ioi_eq lam hlam u]
    field_simp
  refine ⟨?_, ?_⟩
  · refine (hint.integral_prod_left).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    exact (hpt t ht).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_integral_swap hint]
    exact setIntegral_congr_fun measurableSet_Ioi hR

/-- K1b: if `φ t - φ 0 = ∫_0^t ψ` on `[0,∞)` with `ψ` bounded measurable, then
`∫_0^∞ e^{-λt} (λ φ t - ψ t) dt = φ 0`. -/
lemma K1b (lam C : ℝ) (hlam : 0 < lam) (φ ψ : ℝ → ℝ)
    (hψb : ∀ t, |ψ t| ≤ C) (hψm : AEStronglyMeasurable ψ volume)
    (hφ : ∀ t, 0 ≤ t → φ t - φ 0 = ∫ u in (0:ℝ)..t, ψ u) :
    ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * (lam * φ t - ψ t) = φ 0 := by
  obtain ⟨hΨI, hk⟩ := K1b_key lam C hlam ψ hψb hψm
  have heI : IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have hψI : IntegrableOn (fun t => Real.exp (-lam * t) * ψ t) (Ioi 0) := by
    refine Integrable.mono' (heI.mul_const C)
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-lam * t)).aestronglyMeasurable.mul
        hψm.restrict) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hψb t) (Real.exp_pos _).le
  calc ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * (lam * φ t - ψ t)
      = ∫ t in Ioi (0:ℝ), (lam * φ 0 * Real.exp (-lam * t) +
          (lam * Real.exp (-lam * t) * (∫ u in (0:ℝ)..t, ψ u) -
            Real.exp (-lam * t) * ψ t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have h := hφ t (le_of_lt ht)
        rw [← h]
        ring
    _ = lam * φ 0 * (∫ t in Ioi (0:ℝ), Real.exp (-lam * t)) +
          ((∫ t in Ioi (0:ℝ), lam * Real.exp (-lam * t) * ∫ u in (0:ℝ)..t, ψ u) -
            ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * ψ t) := by
        have h2 : IntegrableOn (fun t => lam * Real.exp (-lam * t) * (∫ u in (0:ℝ)..t, ψ u) -
            Real.exp (-lam * t) * ψ t) (Ioi 0) := hΨI.sub hψI
        have h1 : IntegrableOn (fun t => lam * φ 0 * Real.exp (-lam * t)) (Ioi 0) :=
          heI.const_mul _
        rw [integral_add h1 h2, integral_sub hΨI hψI, integral_const_mul]
    _ = φ 0 := by
        rw [hk, sub_self, add_zero, exp_Ioi_eq lam hlam 0]
        field_simp
        simp

end P_e7f29b55

end S_K1b

section S_K4

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace P_e7f29b55

open EthierKurtz in
/-- weighted expectation along the path from time `s`. -/
noncomputable def phiW {E Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → E)
    (s : ℝ≥0) (W : Ω → ℝ) (f : UniformBoundedFunction E) (t : ℝ) : ℝ :=
  ∫ ω, f (X (s + t.toNNReal) ω) * W ω ∂P

open EthierKurtz in
lemma ubf_tendsto_apply {E : Type*} {fn : ℕ → UniformBoundedFunction E}
    {f : UniformBoundedFunction E} (h : Tendsto fn atTop (𝓝 f)) (x : E) :
    Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
  rw [tendsto_iff_dist_tendsto_zero] at h ⊢
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h
  rw [Real.dist_eq, dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub]
  exact ubf_bound _ _

open EthierKurtz in
lemma ubf_measurable_of_tendsto {E : Type*} [MeasurableSpace E]
    {fn : ℕ → UniformBoundedFunction E}
    {f : UniformBoundedFunction E} (hm : ∀ n, Measurable (fn n : E → ℝ))
    (h : Tendsto fn atTop (𝓝 f)) : Measurable (f : E → ℝ) :=
  measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr fun x => ubf_tendsto_apply h x)

open EthierKurtz in
lemma phiW_bound {E Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E) (s : ℝ≥0) (W : Ω → ℝ) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (f : UniformBoundedFunction E) (t : ℝ) : |phiW P X s W f t| ≤ ‖f‖ * CW := by
  have h := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => f (X (s + t.toNNReal) ω) * W ω) (C := ‖f‖ * CW)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (ubf_bound _ _) (hWb ω) (abs_nonneg _) (norm_nonneg _))
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

open EthierKurtz in
lemma phiW_sub {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (f g : UniformBoundedFunction E) (hf : Measurable (f : E → ℝ)) (hg : Measurable (g : E → ℝ))
    (t : ℝ) : phiW P X s W f t - phiW P X s W g t = phiW P X s W (f - g) t := by
  have hXt : ∀ τ : ℝ≥0, Measurable (X τ) := fun τ =>
    hXm.comp (measurable_const.prodMk measurable_id)
  have hint : ∀ h : UniformBoundedFunction E, Measurable (h : E → ℝ) →
      Integrable (fun ω => h (X (s + t.toNNReal) ω) * W ω) P := by
    intro h hh
    refine Integrable.of_bound ((hh.comp (hXt _)).mul hW).aestronglyMeasurable (‖h‖ * CW)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ubf_bound _ _) (hWb ω) (abs_nonneg _) (norm_nonneg _)
  unfold phiW
  rw [← integral_sub (hint f hf) (hint g hg)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [lp.coeFn_sub, Pi.sub_apply, sub_mul]

open EthierKurtz in
lemma phiW_aesm {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W)
    (g : UniformBoundedFunction E) (hg : Measurable (g : E → ℝ)) (μ : Measure ℝ) :
    AEStronglyMeasurable (phiW P X s W g) μ := by
  have hm : Measurable (fun p : ℝ × Ω => g (X (s + p.1.toNNReal) p.2) * W p.2) :=
    (hg.comp (hXm.comp ((measurable_const.add measurable_fst.real_toNNReal).prodMk
        measurable_snd))).mul (hW.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := P)).aestronglyMeasurable

open EthierKurtz in
/-- K1c: the relation `φ_f t - φ_f 0 = ∫_0^t φ_g` (with measurability) is closed in `(f, g)`. -/
lemma K1c_closure {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (S : Set (UniformBoundedFunction E × UniformBoundedFunction E))
    (hS : ∀ fg ∈ S, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ) ∧
      ∀ t : ℝ, 0 ≤ t → phiW P X s W fg.1 t - phiW P X s W fg.1 0
        = ∫ u in (0:ℝ)..t, phiW P X s W fg.2 u) :
    ∀ fg ∈ closure S, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ) ∧
      ∀ t : ℝ, 0 ≤ t → phiW P X s W fg.1 t - phiW P X s W fg.1 0
        = ∫ u in (0:ℝ)..t, phiW P X s W fg.2 u := by
  intro fg hfg
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.mp hfg
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 fg.1) := (continuous_fst.tendsto _).comp hx
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 fg.2) := (continuous_snd.tendsto _).comp hx
  have hm1 := ubf_measurable_of_tendsto (fun n => (hS _ (hxS n)).1) h1
  have hm2 := ubf_measurable_of_tendsto (fun n => (hS _ (hxS n)).2.1) h2
  -- convergence of φ at a fixed time, with a uniform-in-time bound
  have hdist : ∀ (fn : ℕ → UniformBoundedFunction E) (f : UniformBoundedFunction E),
      (∀ n, Measurable (fn n : E → ℝ)) → Measurable (f : E → ℝ) → ∀ n u,
      |phiW P X s W (fn n) u - phiW P X s W f u| ≤ ‖fn n - f‖ * CW := by
    intro fn f hfn hf n u
    rw [phiW_sub P X hXm s W hW CW hWb _ _ (hfn n) hf]
    exact phiW_bound P X s W CW hWb _ u
  have hlim : ∀ (fn : ℕ → UniformBoundedFunction E) (f : UniformBoundedFunction E),
      Tendsto fn atTop (𝓝 f) → Tendsto (fun n => ‖fn n - f‖ * CW) atTop (𝓝 0) := by
    intro fn f h
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const CW
  have hconv : ∀ u, Tendsto (fun n => phiW P X s W (x n).1 u) atTop
      (𝓝 (phiW P X s W fg.1 u)) := by
    intro u
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (hlim _ _ h1)
    rw [Real.dist_eq]
    exact hdist (fun n => (x n).1) fg.1 (fun n => (hS _ (hxS n)).1) hm1 n u
  refine ⟨hm1, hm2, fun t ht => ?_⟩
  have hII : ∀ h : UniformBoundedFunction E, Measurable (h : E → ℝ) →
      IntervalIntegrable (phiW P X s W h) volume 0 t := by
    intro h hh
    refine (intervalIntegrable_const (c := ‖h‖ * CW)).mono_fun'
      (phiW_aesm P X hXm s W hW h hh _) (Eventually.of_forall fun u => ?_)
    show ‖phiW P X s W h u‖ ≤ ‖h‖ * CW
    rw [Real.norm_eq_abs]
    exact phiW_bound P X s W CW hWb h u
  have hint : Tendsto (fun n => ∫ u in (0:ℝ)..t, phiW P X s W (x n).2 u) atTop
      (𝓝 (∫ u in (0:ℝ)..t, phiW P X s W fg.2 u)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hl := (hlim _ _ h2).mul_const |t - 0|
    rw [zero_mul] at hl
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hl
    rw [Real.dist_eq, ← intervalIntegral.integral_sub (hII _ (hS _ (hxS n)).2.1) (hII _ hm2)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
      (f := fun u => phiW P X s W (x n).2 u - phiW P X s W fg.2 u) (C := ‖(x n).2 - fg.2‖ * CW)
      (fun u _ => by
        rw [Real.norm_eq_abs]
        exact hdist (fun n => (x n).2) fg.2 (fun n => (hS _ (hxS n)).2.1) hm2 n u)
    rwa [Real.norm_eq_abs] at this
  have hseq : Tendsto (fun n => phiW P X s W (x n).1 t - phiW P X s W (x n).1 0) atTop
      (𝓝 (∫ u in (0:ℝ)..t, phiW P X s W fg.2 u)) :=
    hint.congr (fun n => ((hS _ (hxS n)).2.2 t ht).symm)
  exact tendsto_nhds_unique ((hconv t).sub (hconv 0)) hseq

open EthierKurtz in
lemma phiW_tendsto {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (fn : ℕ → UniformBoundedFunction E) (f : UniformBoundedFunction E)
    (hfn : ∀ n, Measurable (fn n : E → ℝ)) (hf : Measurable (f : E → ℝ))
    (h : Tendsto fn atTop (𝓝 f)) (t : ℝ) :
    Tendsto (fun n => phiW P X s W (fn n) t) atTop (𝓝 (phiW P X s W f t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hl : Tendsto (fun n => ‖fn n - f‖ * CW) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const CW
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hl
  rw [Real.dist_eq, phiW_sub P X hXm s W hW CW hWb _ _ (hfn n) hf]
  exact phiW_bound P X s W CW hWb _ t

open EthierKurtz in
lemma phiW_II {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (h : UniformBoundedFunction E) (hh : Measurable (h : E → ℝ)) (a b : ℝ) :
    IntervalIntegrable (phiW P X s W h) volume a b := by
  refine (intervalIntegrable_const (c := ‖h‖ * CW)).mono_fun'
    (phiW_aesm P X hXm s W hW h hh _) (Eventually.of_forall fun u => ?_)
  show ‖phiW P X s W h u‖ ≤ ‖h‖ * CW
  rw [Real.norm_eq_abs]
  exact phiW_bound P X s W CW hWb h u

open EthierKurtz in
lemma phiW_smul {E Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → E)
    (s : ℝ≥0) (W : Ω → ℝ) (c : ℝ) (f : UniformBoundedFunction E) (t : ℝ) :
    phiW P X s W (c • f) t = c * phiW P X s W f t := by
  unfold phiW
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

open EthierKurtz in
lemma intOn_exp_phiW {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (h : UniformBoundedFunction E) (hh : Measurable (h : E → ℝ)) (lam : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun t => Real.exp (-lam * t) * phiW P X s W h t) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const (‖h‖ * CW))
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-lam * t)).aestronglyMeasurable.mul
      (phiW_aesm P X hXm s W hW h hh _)) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (phiW_bound P X s W CW hWb h t) (Real.exp_pos _).le

/-- the conclusion of K1b, as a hypothesis (instantiated by `K1b` at assembly). -/
def K1bProp : Prop :=
  ∀ (lam C : ℝ), 0 < lam → ∀ (φ ψ : ℝ → ℝ), (∀ t, |ψ t| ≤ C) →
    AEStronglyMeasurable ψ volume → (∀ t, 0 ≤ t → φ t - φ 0 = ∫ u in (0:ℝ)..t, ψ u) →
    ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * (lam * φ t - ψ t) = φ 0

/-- the conclusion of K3, as a hypothesis (instantiated by `K3_laplace_unique` at assembly). -/
def K3Prop : Prop :=
  ∀ (d : ℝ → ℝ), ContinuousOn d (Ici 0) → (∃ C, ∀ t, 0 ≤ t → |d t| ≤ C) →
    (∀ lam : ℝ, 0 < lam → ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * d t = 0) →
    ∀ t, 0 ≤ t → d t = 0

open EthierKurtz in
lemma K4_laplace (hK1b : K1bProp) {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (f g : UniformBoundedFunction E) (hf : Measurable (f : E → ℝ)) (hg : Measurable (g : E → ℝ))
    (hrel : ∀ t : ℝ, 0 ≤ t → phiW P X s W f t - phiW P X s W f 0
        = ∫ u in (0:ℝ)..t, phiW P X s W g u)
    (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * phiW P X s W (lam • f - g) t = phiW P X s W f 0 := by
  have hsf : Measurable ((lam • f : UniformBoundedFunction E) : E → ℝ) := by
    rw [lp.coeFn_smul]
    exact hf.const_smul lam
  have he : ∀ t, phiW P X s W (lam • f - g) t = lam * phiW P X s W f t - phiW P X s W g t := by
    intro t
    rw [← phiW_sub P X hXm s W hW CW hWb _ _ hsf hg, phiW_smul]
  simp only [he]
  exact hK1b lam (‖g‖ * CW) hlam _ _ (fun t => phiW_bound P X s W CW hWb g t)
    (phiW_aesm P X hXm s W hW g hg _) hrel

open EthierKurtz in
/-- K4: weighted one-dimensional step (EK Thm 4.4.1 with past weights). -/
theorem K4_step (hK1b : K1bProp) (hK3 : K3Prop) {E Ω Ω' : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hK2 : ∀ lam : ℝ, 0 < lam → ∀ h ∈ L, ∃ fg ∈ closure (A' : Set (UniformBoundedFunction E × UniformBoundedFunction E)),
      lam • fg.1 - fg.2 = h)
    (hdom : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set _))
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : ℝ≥0 → Ω' → E)
    (hYm : Measurable (fun z : ℝ≥0 × Ω' => Y z.1 z.2))
    (s : ℝ≥0) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (W' : Ω' → ℝ) (hW' : Measurable W') (CW' : ℝ) (hW'b : ∀ ω, |W' ω| ≤ CW')
    (hrelP : ∀ fg ∈ A', Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ) ∧
      ∀ t : ℝ, 0 ≤ t → phiW P X s W fg.1 t - phiW P X s W fg.1 0
        = ∫ u in (0:ℝ)..t, phiW P X s W fg.2 u)
    (hrelQ : ∀ fg ∈ A', ∀ t : ℝ, 0 ≤ t → phiW Q Y s W' fg.1 t - phiW Q Y s W' fg.1 0
        = ∫ u in (0:ℝ)..t, phiW Q Y s W' fg.2 u)
    (h0 : ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      phiW P X s W f 0 = phiW Q Y s W' f 0) :
    ∀ h ∈ L, Measurable (h : E → ℝ) ∧ ∀ t : ℝ, 0 ≤ t → phiW P X s W h t = phiW Q Y s W' h t := by
  have hrelQ' : ∀ fg ∈ A', Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ) ∧
      ∀ t : ℝ, 0 ≤ t → phiW Q Y s W' fg.1 t - phiW Q Y s W' fg.1 0
        = ∫ u in (0:ℝ)..t, phiW Q Y s W' fg.2 u :=
    fun fg hfg => ⟨(hrelP fg hfg).1, (hrelP fg hfg).2.1, hrelQ fg hfg⟩
  have hPc := K1c_closure P X hXm s W hW CW hWb
    (A' : Set (UniformBoundedFunction E × UniformBoundedFunction E)) hrelP
  have hQc := K1c_closure Q Y hYm s W' hW' CW' hW'b
    (A' : Set (UniformBoundedFunction E × UniformBoundedFunction E)) hrelQ'
  -- Laplace transforms agree on L
  have hLap : ∀ h ∈ L, ∀ lam : ℝ, 0 < lam →
      ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * phiW P X s W h t =
        ∫ t in Ioi (0:ℝ), Real.exp (-lam * t) * phiW Q Y s W' h t := by
    intro h hh lam hlam
    obtain ⟨fg, hfg, rfl⟩ := hK2 lam hlam h hh
    obtain ⟨hf, hg, hr⟩ := hPc fg hfg
    rw [K4_laplace hK1b P X hXm s W hW CW hWb _ _ hf hg hr lam hlam,
      K4_laplace hK1b Q Y hYm s W' hW' CW' hW'b _ _ hf hg (hQc fg hfg).2.2 lam hlam]
    exact h0 _ hf
  -- the one-dimensional step on the domain of A'
  have hdomstep : ∀ fg ∈ A', ∀ t : ℝ, 0 ≤ t →
      phiW P X s W fg.1 t - phiW Q Y s W' fg.1 t = 0 := by
    intro fg hfg
    obtain ⟨hf, hg, hr⟩ := hrelP fg hfg
    have hr' := hrelQ fg hfg
    have hfL : fg.1 ∈ L := by
      rw [← SetLike.mem_coe, ← hdom]
      exact subset_closure (Set.mem_image_of_mem _ hfg)
    refine hK3 (fun t => phiW P X s W fg.1 t - phiW Q Y s W' fg.1 t) ?_ ?_ ?_
    · have hcP : ContinuousOn (phiW P X s W fg.1) (Ici 0) :=
        ((continuous_const.add (intervalIntegral.continuous_primitive
          (phiW_II P X hXm s W hW CW hWb _ hg) 0)).continuousOn).congr
          (fun t ht => by
            show phiW P X s W fg.1 t = phiW P X s W fg.1 0 + ∫ u in (0:ℝ)..t, phiW P X s W fg.2 u
            rw [← hr t ht]; ring)
      have hcQ : ContinuousOn (phiW Q Y s W' fg.1) (Ici 0) :=
        ((continuous_const.add (intervalIntegral.continuous_primitive
          (phiW_II Q Y hYm s W' hW' CW' hW'b _ hg) 0)).continuousOn).congr
          (fun t ht => by
            show phiW Q Y s W' fg.1 t = phiW Q Y s W' fg.1 0 + ∫ u in (0:ℝ)..t, phiW Q Y s W' fg.2 u
            rw [← hr' t ht]; ring)
      exact hcP.sub hcQ
    · refine ⟨‖fg.1‖ * CW + ‖fg.1‖ * CW', fun t _ => ?_⟩
      exact (abs_sub _ _).trans (add_le_add (phiW_bound P X s W CW hWb _ t)
        (phiW_bound Q Y s W' CW' hW'b _ t))
    · intro lam hlam
      simp only [mul_sub]
      rw [integral_sub (intOn_exp_phiW P X hXm s W hW CW hWb _ hf lam hlam)
        (intOn_exp_phiW Q Y hYm s W' hW' CW' hW'b _ hf lam hlam), hLap _ hfL lam hlam, sub_self]
  intro h hh
  have hhc : h ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) := by
    rw [hdom]
    exact hh
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.mp hhc
  choose fgn hfgn hfe using hxS
  have hxm : ∀ n, Measurable (x n : E → ℝ) := fun n => by
    rw [← hfe n]
    exact (hrelP _ (hfgn n)).1
  have hm : Measurable (h : E → ℝ) := ubf_measurable_of_tendsto hxm hx
  refine ⟨hm, fun t ht => ?_⟩
  have hP := phiW_tendsto P X hXm s W hW CW hWb x h hxm hm hx t
  have hQ := phiW_tendsto Q Y hYm s W' hW' CW' hW'b x h hxm hm hx t
  refine tendsto_nhds_unique hP (hQ.congr (fun n => ?_))
  have := hdomstep _ (hfgn n) t ht
  have hfe' : (fgn n).1 = x n := hfe n
  rw [hfe'] at this
  linarith

end P_e7f29b55

end S_K4

section S_K5
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace P_e7f29b55

open EthierKurtz in
/-- indicator of a set, as a uniformly bounded function. -/
noncomputable def indUBF {E : Type*} (B : Set E) : UniformBoundedFunction E :=
  ⟨B.indicator 1, memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ B <;> simp [hx]⟩⟩

open EthierKurtz in
lemma indUBF_apply {E : Type*} (B : Set E) (x : E) : indUBF B x = B.indicator 1 x := rfl

open EthierKurtz in
lemma indUBF_meas {E : Type*} [MeasurableSpace E] (B : Set E) (hB : MeasurableSet B) :
    Measurable (indUBF B : E → ℝ) := by
  have : (indUBF B : E → ℝ) = B.indicator 1 := rfl
  rw [this]; exact measurable_one.indicator hB

open EthierKurtz in
lemma indUBF_nonneg {E : Type*} (B : Set E) (x : E) : 0 ≤ indUBF B x := by
  rw [indUBF_apply]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

open EthierKurtz in
/-- pointwise product, as a uniformly bounded function. -/
noncomputable def mulUBF {E : Type*} (f g : UniformBoundedFunction E) : UniformBoundedFunction E :=
  ⟨fun x => f x * g x, memℓp_infty ⟨‖f‖ * ‖g‖, by
    rintro _ ⟨x, rfl⟩
    show ‖f x * g x‖ ≤ ‖f‖ * ‖g‖
    rw [norm_mul]
    exact mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero f x)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero g x) (norm_nonneg _) (norm_nonneg _)⟩⟩

open EthierKurtz in
lemma mulUBF_apply {E : Type*} (f g : UniformBoundedFunction E) (x : E) :
    mulUBF f g x = f x * g x := rfl

open EthierKurtz in
lemma mulUBF_meas {E : Type*} [MeasurableSpace E] (f g : UniformBoundedFunction E)
    (hf : Measurable (f : E → ℝ)) (hg : Measurable (g : E → ℝ)) :
    Measurable (mulUBF f g : E → ℝ) := by
  have : (mulUBF f g : E → ℝ) = fun x => f x * g x := rfl
  rw [this]; exact hf.mul hg

open EthierKurtz in
/-- two finite measures with equal mass and equal integrals on `L` agree (from `hsep`). -/
lemma sep_ext {E : Type*} [MeasurableSpace E] (L : Submodule ℝ (UniformBoundedFunction E))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (ν₁ ν₂ : Measure E) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hmass : ν₁ univ = ν₂ univ)
    (hL : ∀ h ∈ L, ∫ x, (h : E → ℝ) x ∂ν₁ = ∫ x, (h : E → ℝ) x ∂ν₂) : ν₁ = ν₂ := by
  by_cases h0 : ν₁ univ = 0
  · have h0' : ν₂ univ = 0 := by rw [← hmass]; exact h0
    rw [Measure.measure_univ_eq_zero.mp h0, Measure.measure_univ_eq_zero.mp h0']
  have hcT : ν₁ univ ≠ ⊤ := measure_ne_top ν₁ univ
  have key : (ν₁ univ)⁻¹ • ν₁ = (ν₁ univ)⁻¹ • ν₂ := by
    apply hsep
    · constructor
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hcT]
    · constructor
      rw [Measure.smul_apply, smul_eq_mul, hmass, ENNReal.inv_mul_cancel (hmass ▸ h0) (hmass ▸ hcT)]
    · intro f
      rw [integral_smul_measure, integral_smul_measure, hL f.val f.2]
  have := congrArg (fun m => (ν₁ univ) • m) key
  simpa only [smul_smul, ENNReal.mul_inv_cancel h0 hcT, one_smul] using this

lemma wlaw_integral {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    (Xs : Ω → E) (hXs : Measurable Xs) (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (f : E → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(Measure.map Xs (P.withDensity (fun ω => ENNReal.ofReal (W ω))))
      = ∫ ω, f (Xs ω) * W ω ∂P := by
  rw [integral_map hXs.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hW.ennreal_ofReal
      (Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top))]
  congr 1; ext ω
  rw [ENNReal.toReal_ofReal (hW0 ω), smul_eq_mul, mul_comm]

lemma wlaw_finite {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xs : Ω → E) (W : Ω → ℝ) (hW : Measurable W) (CW : ℝ)
    (hWb : ∀ ω, |W ω| ≤ CW) :
    IsFiniteMeasure (Measure.map Xs (P.withDensity (fun ω => ENNReal.ofReal (W ω)))) := by
  have hWi : Integrable W P :=
    (integrable_const CW).mono' hW.aestronglyMeasurable
      (Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hWb ω))
  haveI := isFiniteMeasure_withDensity_ofReal hWi.hasFiniteIntegral
  infer_instance

open EthierKurtz in
/-- K5: equal weighted integrals on `L` (and equal mass) give equal weighted integrals of every
bounded measurable function (separation through `hsep`). -/
lemma K5_ext {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (P : Measure Ω) [IsProbabilityMeasure P] (Xs : Ω → E) (hXs : Measurable Xs)
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (CW : ℝ) (hWb : ∀ ω, |W ω| ≤ CW)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Ys : Ω' → E) (hYs : Measurable Ys)
    (W' : Ω' → ℝ) (hW' : Measurable W') (hW'0 : ∀ ω, 0 ≤ W' ω) (CW' : ℝ)
    (hW'b : ∀ ω, |W' ω| ≤ CW')
    (hmass : ∫ ω, W ω ∂P = ∫ ω, W' ω ∂Q)
    (hL : ∀ h ∈ L, Measurable (h : E → ℝ) ∧
      ∫ ω, h (Xs ω) * W ω ∂P = ∫ ω, h (Ys ω) * W' ω ∂Q) :
    ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      ∫ ω, f (Xs ω) * W ω ∂P = ∫ ω, f (Ys ω) * W' ω ∂Q := by
  obtain ⟨ν₁, hν₁⟩ : ∃ ν : Measure E,
      ν = Measure.map Xs (P.withDensity (fun ω => ENNReal.ofReal (W ω))) := ⟨_, rfl⟩
  obtain ⟨ν₂, hν₂⟩ : ∃ ν : Measure E,
      ν = Measure.map Ys (Q.withDensity (fun ω => ENNReal.ofReal (W' ω))) := ⟨_, rfl⟩
  have e1 : ∀ f : E → ℝ, Measurable f → ∫ x, f x ∂ν₁ = ∫ ω, f (Xs ω) * W ω ∂P :=
    fun f hf => by rw [hν₁]; exact wlaw_integral P Xs hXs W hW hW0 f hf
  have e2 : ∀ f : E → ℝ, Measurable f → ∫ x, f x ∂ν₂ = ∫ ω, f (Ys ω) * W' ω ∂Q :=
    fun f hf => by rw [hν₂]; exact wlaw_integral Q Ys hYs W' hW' hW'0 f hf
  haveI : IsFiniteMeasure ν₁ := by rw [hν₁]; exact wlaw_finite P Xs W hW CW hWb
  haveI : IsFiniteMeasure ν₂ := by rw [hν₂]; exact wlaw_finite Q Ys W' hW' CW' hW'b
  have hm : ν₁ univ = ν₂ univ := by
    have a1 := e1 (fun _ => 1) measurable_const
    have a2 := e2 (fun _ => 1) measurable_const
    simp only [one_mul] at a1 a2
    have h12 := a1.trans (hmass.trans a2.symm)
    rw [integral_const, integral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h12
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h12
  have heq : ν₁ = ν₂ := sep_ext L hsep ν₁ ν₂ hm (fun h hh => by
    rw [e1 _ (hL h hh).1, e2 _ (hL h hh).1]; exact (hL h hh).2)
  intro f hf
  rw [← e1 _ hf, ← e2 _ hf, heq]

open EthierKurtz in
/-- one step: equal weighted laws at `s0` give equal weighted laws at every `s ≥ s0`
(K1 + K2 + K3 + K4 + K5). -/
theorem K_step {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E)) (a : ℝ) (ha : 0 < a)
    (hr : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _))
    (hd : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set _))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : ℝ≥0 → Ω' → E)
    (hY : SolvesMartingaleProblem A μ Q Y)
    (s0 : ℝ≥0) (n : ℕ) (r : Fin n → ℝ≥0) (hr0 : ∀ i, r i ≤ s0)
    (k : Fin n → UniformBoundedFunction E) (hk : ∀ i, Measurable (k i))
    (hk0 : ∀ i x, 0 ≤ k i x)
    (h0 : ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      ∫ ω, f (X s0 ω) * ∏ i, k i (X (r i) ω) ∂P = ∫ ω, f (Y s0 ω) * ∏ i, k i (Y (r i) ω) ∂Q) :
    ∀ s : ℝ≥0, s0 ≤ s → ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      ∫ ω, f (X s ω) * ∏ i, k i (X (r i) ω) ∂P = ∫ ω, f (Y s ω) * ∏ i, k i (Y (r i) ω) ∂Q := by
  have hXm : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) := hX.1
  have hYm : Measurable (fun z : ℝ≥0 × Ω' => Y z.1 z.2) := hY.1
  have hXt : ∀ τ : ℝ≥0, Measurable (X τ) := fun τ =>
    hXm.comp (measurable_const.prodMk measurable_id)
  have hYt : ∀ τ : ℝ≥0, Measurable (Y τ) := fun τ =>
    hYm.comp (measurable_const.prodMk measurable_id)
  have hW : Measurable (fun ω => ∏ i, k i (X (r i) ω)) :=
    Finset.measurable_prod _ (fun i _ => (hk i).comp (hXt (r i)))
  have hW' : Measurable (fun ω => ∏ i, k i (Y (r i) ω)) :=
    Finset.measurable_prod _ (fun i _ => (hk i).comp (hYt (r i)))
  have hWb : ∀ ω, |∏ i, k i (X (r i) ω)| ≤ ∏ i, ‖k i‖ := fun ω => prod_bound k _
  have hW'b : ∀ ω, |∏ i, k i (Y (r i) ω)| ≤ ∏ i, ‖k i‖ := fun ω => prod_bound k _
  have hW0 : ∀ ω, 0 ≤ ∏ i, k i (X (r i) ω) := fun ω => Finset.prod_nonneg (fun i _ => hk0 i _)
  have hW'0 : ∀ ω, 0 ≤ ∏ i, k i (Y (r i) ω) := fun ω => Finset.prod_nonneg (fun i _ => hk0 i _)
  have hK2 : ∀ lam : ℝ, 0 < lam → ∀ h ∈ L, ∃ fg ∈ closure (A' : Set (UniformBoundedFunction E ×
      UniformBoundedFunction E)), lam • fg.1 - fg.2 = h := by
    intro lam hlam h hh
    obtain ⟨fg, hfg, he, -, -⟩ :=
      K2_range_all A' L a ha (fun fg hfg => hdiss fg (hsub hfg)) hr hd lam hlam h hh
    refine ⟨fg, ?_, he⟩
    rw [← Submodule.topologicalClosure_coe]; exact hfg
  have hrelP : ∀ fg ∈ A', Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ) ∧
      ∀ t : ℝ, 0 ≤ t → phiW P X s0 (fun ω => ∏ i, k i (X (r i) ω)) fg.1 t
          - phiW P X s0 (fun ω => ∏ i, k i (X (r i) ω)) fg.1 0
        = ∫ u in (0:ℝ)..t, phiW P X s0 (fun ω => ∏ i, k i (X (r i) ω)) fg.2 u := by
    intro fg hfg
    obtain ⟨hf, hg⟩ := hAmeas fg (hsub hfg)
    refine ⟨hf, hg, fun t ht => ?_⟩
    have := K1a_fubini A μ P X hX fg (hsub hfg) hf hg s0 n r hr0 k hk t ht
    simpa only [phiW, Real.toNNReal_zero, add_zero] using this
  have hrelQ : ∀ fg ∈ A', ∀ t : ℝ, 0 ≤ t →
      phiW Q Y s0 (fun ω => ∏ i, k i (Y (r i) ω)) fg.1 t
          - phiW Q Y s0 (fun ω => ∏ i, k i (Y (r i) ω)) fg.1 0
        = ∫ u in (0:ℝ)..t, phiW Q Y s0 (fun ω => ∏ i, k i (Y (r i) ω)) fg.2 u := by
    intro fg hfg t ht
    obtain ⟨hf, hg⟩ := hAmeas fg (hsub hfg)
    have := K1a_fubini A μ Q Y hY fg (hsub hfg) hf hg s0 n r hr0 k hk t ht
    simpa only [phiW, Real.toNNReal_zero, add_zero] using this
  have h0' : ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      phiW P X s0 (fun ω => ∏ i, k i (X (r i) ω)) f 0
        = phiW Q Y s0 (fun ω => ∏ i, k i (Y (r i) ω)) f 0 := by
    intro f hf
    simp only [phiW, Real.toNNReal_zero, add_zero]
    exact h0 f hf
  have hK4 := K4_step (fun lam C hlam φ ψ hψb hψm hφ => K1b lam C hlam φ ψ hψb hψm hφ)
    (fun d hd' hC hL => K3_laplace_unique d hd' hC hL) A' L hK2 hd P X hXm Q Y hYm s0
    _ hW _ hWb _ hW' _ hW'b hrelP hrelQ h0'
  intro s hs
  have hst : s0 + (((s - s0 : ℝ≥0) : ℝ)).toNNReal = s := by
    rw [Real.toNNReal_coe, add_tsub_cancel_of_le hs]
  have hmass : ∫ ω, ∏ i, k i (X (r i) ω) ∂P = ∫ ω, ∏ i, k i (Y (r i) ω) ∂Q := by
    have := h0 (indUBF univ) (indUBF_meas univ MeasurableSet.univ)
    simpa only [indUBF_apply, Set.indicator_univ, Pi.one_apply, one_mul] using this
  refine K5_ext L hsep P (X s) (hXt s) _ hW hW0 _ hWb Q (Y s) (hYt s) _ hW' hW'0 _ hW'b
    hmass (fun h hh => ⟨(hK4 h hh).1, ?_⟩)
  have := (hK4 h hh).2 ((s - s0 : ℝ≥0) : ℝ) (NNReal.coe_nonneg _)
  simpa only [phiW, hst] using this

open EthierKurtz in
lemma prod_split {E Ω : Type*} {n : ℕ} (X : ℝ≥0 → Ω → E) (r : Fin (n + 1) → ℝ≥0)
    (k : Fin (n + 1) → UniformBoundedFunction E) (m : Fin (n + 1))
    (g : UniformBoundedFunction E) (ω : Ω) :
    g (X (r m) ω) * ∏ i, k i (X (r i) ω)
      = mulUBF g (k m) (X (r m) ω) * ∏ i : Fin n, k (m.succAbove i) (X (r (m.succAbove i)) ω) := by
  rw [Fin.prod_univ_succAbove _ m, mulUBF_apply]; ring

open EthierKurtz in
/-- fdd induction: equal weighted laws for nonnegative product weights at any later time. -/
theorem K_U {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E)) (a : ℝ) (ha : 0 < a)
    (hr : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _))
    (hd : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set _))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : ℝ≥0 → Ω' → E)
    (hY : SolvesMartingaleProblem A μ Q Y) :
    ∀ (n : ℕ) (r : Fin n → ℝ≥0) (s : ℝ≥0), (∀ i, r i ≤ s) →
      ∀ k : Fin n → UniformBoundedFunction E, (∀ i, Measurable (k i)) → (∀ i x, 0 ≤ k i x) →
      ∀ f : UniformBoundedFunction E, Measurable (f : E → ℝ) →
      ∫ ω, f (X s ω) * ∏ i, k i (X (r i) ω) ∂P = ∫ ω, f (Y s ω) * ∏ i, k i (Y (r i) ω) ∂Q := by
  intro n
  induction n with
  | zero =>
    intro r s _ k hk hk0 f hf
    refine K_step A A' hAmeas hsub hdiss L a ha hr hd hsep μ P X hX Q Y hY 0 0 r
      (fun i => i.elim0) k hk hk0 ?_ s (by positivity) f hf
    intro g hg
    simp only [Fin.prod_univ_zero, mul_one]
    have hX0 : Measurable (X 0) := hX.1.comp (measurable_const.prodMk measurable_id)
    have hY0 : Measurable (Y 0) := hY.1.comp (measurable_const.prodMk measurable_id)
    have eP := integral_map (μ := P) hX0.aemeasurable hg.aestronglyMeasurable
    have eQ := integral_map (μ := Q) hY0.aemeasurable hg.aestronglyMeasurable
    rw [hX.2.1] at eP
    rw [hY.2.1] at eQ
    rw [← eP, ← eQ]
  | succ n ih =>
    intro r s hrs k hk hk0 f hf
    obtain ⟨m, hm⟩ := Finite.exists_max r
    refine K_step A A' hAmeas hsub hdiss L a ha hr hd hsep μ P X hX Q Y hY (r m) (n + 1) r
      hm k hk hk0 ?_ s (hrs m) f hf
    intro g hg
    simp_rw [prod_split X r k m g, prod_split Y r k m g]
    exact ih (fun i => r (m.succAbove i)) (r m) (fun i => hm _) (fun i => k (m.succAbove i))
      (fun i => hk _) (fun i x => hk0 _ x) (mulUBF g (k m)) (mulUBF_meas g (k m) hg (hk m))

lemma prod_ind_eq {E ι : Type*} [Fintype ι] (B : ι → Set E) (x : ι → E) :
    ∏ i, (B i).indicator (1 : E → ℝ) (x i) = (Set.pi univ B).indicator 1 x := by
  by_cases h : x ∈ Set.pi univ B
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_eq_one (fun i _ => by
      rw [Set.indicator_of_mem (h i (mem_univ i))]; rfl)
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ B i := by simpa [Set.mem_pi] using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

end P_e7f29b55
end S_K5

open MeasureTheory Filter TopologicalSpace Set
open scoped ENNReal NNReal Topology

open MeasureTheory Filter TopologicalSpace NNReal ENNReal Topology EthierKurtz in
theorem solution
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MetricSpace E] [BorelSpace E]
    [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E) (hX : SolvesMartingaleProblem A μ P X) :
    ∀ (Q : Measure Ω'), IsProbabilityMeasure Q →
      ∀ Y : ℝ≥0 → Ω' → E,
        SolvesMartingaleProblem A μ Q Y →
        ∀ (n : ℕ) (t : Fin n → ℝ≥0),
          Measure.map (fun ω i => X (t i) ω) P =
            Measure.map (fun ω i => Y (t i) ω) Q := by
  intro Q hQ Y hY n t
  obtain ⟨a, ha, hr, hd⟩ := hrange
  have hU := P_e7f29b55.K_U A A' hAmeas hsub hdiss L a ha hr hd hsep μ P X hX Q Y hY
  have hXmeas : Measurable (fun ω i => X (t i) ω) :=
    measurable_pi_lambda _ (fun i => hX.1.comp (measurable_const.prodMk measurable_id))
  have hYmeas : Measurable (fun ω i => Y (t i) ω) :=
    measurable_pi_lambda _ (fun i => hY.1.comp (measurable_const.prodMk measurable_id))
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro S ⟨B, hB, rfl⟩
    have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (mem_univ i)
    have hbox : MeasurableSet (Set.pi univ B) := MeasurableSet.univ_pi hB'
    rw [Measure.map_apply hXmeas hbox, Measure.map_apply hYmeas hbox]
    have key := hU n t (Finset.univ.sup t) (fun i => Finset.le_sup (Finset.mem_univ i))
      (fun i => P_e7f29b55.indUBF (B i)) (fun i => P_e7f29b55.indUBF_meas _ (hB' i)) (fun i x => P_e7f29b55.indUBF_nonneg _ x)
      (P_e7f29b55.indUBF univ) (P_e7f29b55.indUBF_meas univ MeasurableSet.univ)
    simp only [P_e7f29b55.indUBF_apply, Set.indicator_univ, Pi.one_apply, one_mul] at key
    simp only [P_e7f29b55.prod_ind_eq B] at key
    have eP : ∫ ω, (Set.pi univ B).indicator (1 : (Fin n → E) → ℝ) (fun i => X (t i) ω) ∂P
        = P.real ((fun ω i => X (t i) ω) ⁻¹' Set.pi univ B) := by
      rw [← integral_indicator_one (hXmeas hbox)]; rfl
    have eQ : ∫ ω, (Set.pi univ B).indicator (1 : (Fin n → E) → ℝ) (fun i => Y (t i) ω) ∂Q
        = Q.real ((fun ω i => Y (t i) ω) ⁻¹' Set.pi univ B) := by
      rw [← integral_indicator_one (hYmeas hbox)]; rfl
    have hreal := eP.symm.trans (key.trans eQ)
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  · rw [Measure.map_apply hXmeas MeasurableSet.univ, Measure.map_apply hYmeas MeasurableSet.univ,
      preimage_univ, preimage_univ, measure_univ, measure_univ]
