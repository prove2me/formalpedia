-- Prove2me | solution 1 for EthierKurtz.smoothed_sum_density_cramer_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:40:08.196333+00:00
-- url     : https://prove2.me/submissions/65214509-9fe2-4d17-88ce-02ef2319c06e

import Mathlib
import Theorems.Thm_EthierKurtz_tilted_local_limit_smoothed_sum_density
import Theorems.Thm_EthierKurtz_legendre_transform_third_order_expansion

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X5_Cg1

/-! R4 / Q3: cumulants of a law with exponential moments (uniform local bounds).
* `taylor_an`: Taylor with Lagrange remainder for a function analytic on a neighbourhood;
* `itd_itd`: `iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (k + m) f`;
* `ioo_sub_int`, `an_cgf`, `V_zero`: the cgf `ψ` is analytic on `(-a0, a0)` and `ψ''(0) = 1`;
* `cum_local`: `∃ t1 B`, on `[-2t1, 2t1]`: `1/2 ≤ ψ'' ≤ 2`, `|ψ'''| ≤ B`;
* `cum_T0/T1/T2`: Taylor bounds of `ψ'', ψ', ψ` on `[-t1, t1]`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal Nat

namespace P99bcb804

lemma taylor_an {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    {x₀ x : ℝ} (hsub : uIcc x₀ x ⊆ U) (n : ℕ) {B : ℝ}
    (hB : ∀ y ∈ U, |iteratedDeriv (n + 1) f y| ≤ B) :
    |f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / (k ! : ℝ)|
      ≤ B * |x - x₀| ^ (n + 1) / ((n + 1) ! : ℝ) := by
  rcases eq_or_ne x₀ x with h | h
  · subst h
    rw [Finset.sum_range_succ']
    simp
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc h
  have hcd : ContDiffOn ℝ (n + 1) f (uIcc x₀ x) := (hf.mono hsub).contDiffOn hu
  obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv h hcd
  have hx0 : x₀ ∈ uIcc x₀ x := left_mem_uIcc
  have e : taylorWithinEval f n (uIcc x₀ x) x₀ x
      = ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / (k ! : ℝ) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hf x₀ (hsub hx0)).contDiffAt) hx0, smul_eq_mul]
    ring
  rw [← e, heq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hB x' (hsub (Set.uIoo_subset_uIcc_self hx'))

lemma itd_itd (f : ℝ → ℝ) (k m : ℕ) :
    iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (k + m) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]

section Cum

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma ioo_sub_int (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) :
    Ioo (-a0) a0 ⊆ interior (integrableExpSet (fun x : ℝ => x) G) :=
  interior_maximal (fun t ht => hexp t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)) isOpen_Ioo

lemma an_cgf (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) (k : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv k (cgf (fun x : ℝ => x) G)) (Ioo (-a0) a0) := by
  rw [iteratedDeriv_eq_iterate]
  exact (analyticOnNhd_cgf.mono (ioo_sub_int hexp)).iterated_deriv k

/-- Taylor bounds for the cgf `ψ` and its first two derivatives on `[-t1, t1]`. -/
lemma cum_taylor {t1 B : ℝ} (ht1 : 0 < t1) (h2a : 2 * t1 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {t s : ℝ} (ht : |t| ≤ t1) (hs : |s| ≤ t1) :
    |iteratedDeriv 2 (cgf (fun x : ℝ => x) G) s - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t|
        ≤ B * |s - t| ∧
    |iteratedDeriv 1 (cgf (fun x : ℝ => x) G) s - iteratedDeriv 1 (cgf (fun x : ℝ => x) G) t
        - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t)| ≤ B * |s - t| ^ 2 / 2 ∧
    |cgf (fun x : ℝ => x) G s - cgf (fun x : ℝ => x) G t
        - iteratedDeriv 1 (cgf (fun x : ℝ => x) G) t * (s - t)
        - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) ^ 2 / 2| ≤ B * |s - t| ^ 3 / 6 := by
  set ψ := cgf (fun x : ℝ => x) G with hψ
  set U := Ioo (-(2 * t1)) (2 * t1) with hU
  have hUa : U ⊆ Ioo (-a0) a0 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub : uIcc t s ⊆ U := by
    intro x hx
    rcases abs_le.1 ht with ⟨h1, h2⟩
    rcases abs_le.1 hs with ⟨h3, h4⟩
    rcases Set.mem_uIcc.1 hx with hx | hx <;>
      exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hB : ∀ (m n : ℕ), m + n = 2 → ∀ y ∈ U, |iteratedDeriv (n + 1) (iteratedDeriv m ψ) y| ≤ B := by
    intro m n hmn y hy
    rw [itd_itd, show n + 1 + m = 3 by omega]
    exact hW y ⟨hy.1.le, hy.2.le⟩
  have an : ∀ m : ℕ, AnalyticOnNhd ℝ (iteratedDeriv m ψ) U := fun m => (an_cgf hexp m).mono hUa
  refine ⟨?_, ?_, ?_⟩
  · have := taylor_an (an 2) hsub 0 (hB 2 0 rfl)
    simpa using this
  · have := taylor_an (an 1) hsub 1 (hB 1 1 rfl)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, itd_itd] at this
    simp [Nat.factorial] at this
    rw [sub_add_eq_sub_sub] at this
    simpa [iteratedDeriv_one] using this
  · have := taylor_an (an 0) hsub 2 (hB 0 2 rfl)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, itd_itd, iteratedDeriv_zero] at this
    have e : ∀ x : ℝ, x - (0 + ψ t * (s - t) ^ 0 / ((0 : ℕ)! : ℝ)
        + iteratedDeriv 1 ψ t * (s - t) ^ 1 / ((1 : ℕ)! : ℝ)
        + iteratedDeriv 2 ψ t * (s - t) ^ 2 / ((2 : ℕ)! : ℝ))
        = x - ψ t - iteratedDeriv 1 ψ t * (s - t) - iteratedDeriv 2 ψ t * (s - t) ^ 2 / 2 := by
      intro x; simp [Nat.factorial]; ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    simp [Nat.factorial]

end Cum

end P99bcb804

end X5_Cg1

section X7_Cg3

/-! R4 / Q3: hypotheses of `lclt_dens` for the centred tilted law `Hc G t`.
* `smooth_taylor`: Gaussian smoothing keeps a cubic Taylor bound of `charFun`;
* `Hc G t = (G.tilted (t·)).map (· - tmu G t)`: `Hc_prob`, `int_Hc`, `Hc_mean`, `Hc_var`;
* `Hc_m3`: uniform third absolute moment on `|t| ≤ t1`;
* `Hc_far`: `‖charFun (Hc G t) s · e^{-σ²s²/2}‖ ≤ 1 - (p/2)(1-e^{-v/2}) min(s²,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Hc

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- The tilted mean `ψ'(t)`. -/
noncomputable def tmu (G : Measure ℝ) (t : ℝ) : ℝ := deriv (cgf (fun x : ℝ => x) G) t

lemma mem_int_of (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| < a0) : t ∈ interior (integrableExpSet (fun x : ℝ => x) G) :=
  ioo_sub_int hexp ⟨by linarith [(abs_lt.1 ht).1], (abs_lt.1 ht).2⟩

end Hc

end P99bcb804

end X7_Cg3

section X9_Cr1

/-! R4 / Cr1: local CLT for the smoothed iid-sum density at ANY small tilt `t`.
`lc_any`: for `G = p N(m,v) + (1-p) F2` (exp moments, mean 0, var 1), uniformly in `|t| ≤ t1`, `σ ∈ (0,1]`, `N ≥ 2`:
`f(a) = M^N e^{t²Nσ²/2} e^{-ta} (φ_{N(V_t+σ²)}(a - tNσ² - N μ_t) ± (C/N + C(1-κ')^{N-1}/σ))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Cr1

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem lc_any :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
        ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
          (0 : ℝ) < p →
            p ≤ (1 : ℝ) →
              (0 : NNReal) < v →
                G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                  ∀ {t1 : ℝ},
                    (0 : ℝ) < t1 →
                      (2 : ℝ) * t1 < a0 →
                        (∀ (t : ℝ),
                            |t| ≤ t1 →
                              (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                          (∀ (t : ℝ),
                              |t| ≤ t1 →
                                (1 / 2 : ℝ) ≤
                                  ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                            ∃ (C : ℝ) (κ' : ℝ),
                              (0 : ℝ) < C ∧
                                (0 : ℝ) < κ' ∧
                                  κ' ≤ (1 : ℝ) ∧
                                    ∀ (ι : Type) [inst : Fintype ι] (t σ a : ℝ),
                                      |t| ≤ t1 →
                                        (0 : ℝ) < σ →
                                          σ ≤ (1 : ℝ) →
                                            (2 : ℕ) ≤ Fintype.card ι →
                                              |∫ (y : ℝ),
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                        (a -
                                                          y) ∂MeasureTheory.Measure.map (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                        (MeasureTheory.Measure.pi fun (x : ι) => G) -
                                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                          Real.exp
                                                            (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                        Real.exp (-(t * a)) *
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal
                                                          (↑(Fintype.card ι) *
                                                            (iteratedDeriv (2 : ℕ)
                                                                (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t +
                                                              σ ^ (2 : ℕ))))
                                                        (a - t * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) -
                                                          ↑(Fintype.card ι) * P99bcb804.tmu G t)| ≤
                                                ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                      Real.exp (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                    Real.exp (-(t * a)) *
                                                  (C / ↑(Fintype.card ι) +
                                                    C * ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ) := EthierKurtz.tilted_local_limit_smoothed_sum_density

end Cr1

end P99bcb804

end X9_Cr1

section X10_Cr2

/-! R4 / Cr2: abstract Legendre-transform expansion (pure real algebra).
If `c = L1 t`, `c' = L1 t'` and `L, L1, L2` satisfy second/third-order Taylor bounds at `t`, then
`Λ*(c') - Λ*(c) = t (c'-c) + (c'-c)²/(2 L2 t) + O(|c'-c|³)` where `Λ*(c) = t c - L t` at the saddle. -/

open Real Set

namespace P99bcb804

theorem leg_exp :
    ∀ (L L1 L2 : ℝ → ℝ) {t t' B R : ℝ},
      (1 / 2 : ℝ) ≤ L2 t →
        |t' - t| ≤ (2 : ℝ) * |L1 t' - L1 t| →
          (0 : ℝ) ≤ B →
            |L1 t' - L1 t| ≤ R →
              |L1 t' - L1 t - L2 t * (t' - t)| ≤ B * |t' - t| ^ (2 : ℕ) / (2 : ℝ) →
                |L t' - L t - L1 t * (t' - t) - L2 t * (t' - t) ^ (2 : ℕ) / (2 : ℝ)| ≤ B * |t' - t| ^ (3 : ℕ) / (6 : ℝ) →
                  |t' * L1 t' - L t' - (t * L1 t - L t) - t * (L1 t' - L1 t) -
                        (L1 t' - L1 t) ^ (2 : ℕ) / ((2 : ℝ) * L2 t)| ≤
                    ((4 : ℝ) * B ^ (2 : ℕ) * R + (2 : ℝ) * B) * |L1 t' - L1 t| ^ (3 : ℕ) := EthierKurtz.legendre_transform_third_order_expansion

end P99bcb804

end X10_Cr2

section X11_Cr3

/-! R4 / Cr3: smoothed cumulant functions, saddle point, Legendre expansion.
`Ls G σ t = cgf t + t²σ²/2` (cgf of `G ∗ N(0,σ²)`), `L1s = Ls'`, `L2s = Ls''`.
* `L1s_mono`: `L1s` increases at rate `≥ 1/2` on `[-t1,t1]`; `saddle`: `L1s t = c` solvable for `|c| ≤ t1/2`, `|t| ≤ 2|c|`;
* `Ls_taylor`: Taylor bounds; `leg_at`: Legendre expansion of `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def Ls (G : Measure ℝ) (σ t : ℝ) : ℝ := cgf (fun x : ℝ => x) G t + t ^ 2 * σ ^ 2 / 2
noncomputable def L1s (G : Measure ℝ) (σ t : ℝ) : ℝ := tmu G t + t * σ ^ 2
noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma tmu_hasDeriv (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t : ℝ} (ht : |t| < a0) :
    HasDerivAt (tmu G) (iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t) t := by
  have h1 : tmu G = iteratedDeriv 1 (cgf (fun x : ℝ => x) G) := by
    funext s; rw [iteratedDeriv_one]; rfl
  have hmem : t ∈ Ioo (-a0) a0 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hd := (an_cgf hexp 1 t hmem).differentiableAt
  have e : iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t
      = deriv (iteratedDeriv 1 (cgf (fun x : ℝ => x) G)) t :=
    congrFun (iteratedDeriv_succ (n := 1)) t
  rw [h1, e]
  exact hd.hasDerivAt

lemma tmu_zero (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) : tmu G 0 = 0 := by
  rw [tmu, deriv_cgf_zero (mem_int_of hexp (by simpa using ha0))]
  simp [hm]

lemma L1s_hasDeriv (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (σ : ℝ) {t : ℝ} (ht : |t| < a0) : HasDerivAt (L1s G σ) (L2s G σ t) t := by
  have h := (tmu_hasDeriv hexp ht).add ((hasDerivAt_id' t).mul_const (σ ^ 2))
  have e : L1s G σ = fun s => tmu G s + s * σ ^ 2 := rfl
  rw [e, L2s]
  exact h.congr_deriv (by ring)

lemma L1s_mono (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {s t : ℝ} (hs : |s| ≤ t1) (ht : |t| ≤ t1) (hst : s ≤ t) :
    (t - s) / 2 ≤ L1s G σ t - L1s G σ s := by
  have hder : ∀ u, |u| ≤ t1 → HasDerivAt (L1s G σ) (L2s G σ u) u := fun u hu =>
    L1s_hasDeriv hexp σ (by linarith)
  have hcont : ContinuousOn (L1s G σ) (Icc (-t1) t1) := fun u hu =>
    (hder u (abs_le.2 hu)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (L1s G σ) (interior (Icc (-t1) t1)) := fun u hu =>
    (hder u (abs_le.2 (mem_Icc.1 (interior_subset hu)))).differentiableAt.differentiableWithinAt
  have hge : ∀ x ∈ interior (Icc (-t1) t1), 1 / 2 ≤ deriv (L1s G σ) x := by
    intro x hx
    have hx' : |x| ≤ t1 := abs_le.2 (mem_Icc.1 (interior_subset hx))
    rw [(hder x hx').deriv, L2s]
    have := (hV x hx').1
    nlinarith [sq_nonneg σ]
  have := (convex_Icc (-t1) t1).mul_sub_le_image_sub_of_le_deriv hcont hdiff hge s (abs_le.1 hs)
    t (abs_le.1 ht) hst
  linarith

lemma L1s_low (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {s t : ℝ} (hs : |s| ≤ t1) (ht : |t| ≤ t1) :
    |s - t| ≤ 2 * |L1s G σ s - L1s G σ t| := by
  rcases le_total s t with hst | hst
  · have := L1s_mono hexp h2 ht1 hV σ hs ht hst
    rw [abs_sub_comm s t, abs_of_nonneg (by linarith), abs_sub_comm]
    have := le_abs_self (L1s G σ t - L1s G σ s)
    linarith
  · have := L1s_mono hexp h2 ht1 hV σ ht hs hst
    rw [abs_of_nonneg (by linarith)]
    have := le_abs_self (L1s G σ s - L1s G σ t)
    linarith

lemma saddle (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {c : ℝ} (hc : |c| ≤ t1 / 2) :
    ∃ t, |t| ≤ t1 ∧ L1s G σ t = c ∧ |t| ≤ 2 * |c| := by
  have h0 : L1s G σ 0 = 0 := by simp [L1s, tmu_zero ha0 hexp hm]
  have hz : |(0 : ℝ)| ≤ t1 := by simp [ht1.le]
  have ht1a : |t1| ≤ t1 := by rw [abs_of_pos ht1]
  have ht1b : |-t1| ≤ t1 := by rw [abs_neg, abs_of_pos ht1]
  have hup := L1s_mono hexp h2 ht1 hV σ hz ht1a ht1.le
  have hlo := L1s_mono hexp h2 ht1 hV σ ht1b hz (by linarith)
  have hcont : ContinuousOn (L1s G σ) (Icc (-t1) t1) := fun u hu =>
    (L1s_hasDeriv hexp σ (by have := abs_le.2 hu; linarith)).continuousAt.continuousWithinAt
  have hmem : c ∈ Icc (L1s G σ (-t1)) (L1s G σ t1) := by
    have := abs_le.1 hc
    constructor <;> linarith
  obtain ⟨t, htI, htc⟩ := intermediate_value_Icc (by linarith) hcont hmem
  have ht : |t| ≤ t1 := abs_le.2 htI
  refine ⟨t, ht, htc, ?_⟩
  have := L1s_low hexp h2 ht1 hV σ ht hz
  rwa [sub_zero, htc, h0, sub_zero] at this

lemma Ls_taylor (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (σ : ℝ) {t s : ℝ} (ht : |t| ≤ t1) (hs : |s| ≤ t1) :
    |L1s G σ s - L1s G σ t - L2s G σ t * (s - t)| ≤ B * |s - t| ^ 2 / 2 ∧
    |Ls G σ s - Ls G σ t - L1s G σ t * (s - t) - L2s G σ t * (s - t) ^ 2 / 2|
      ≤ B * |s - t| ^ 3 / 6 := by
  obtain ⟨-, hb1, hb0⟩ := cum_taylor ht1 h2 hexp hW ht hs
  rw [iteratedDeriv_one] at hb1 hb0
  constructor
  · have e : L1s G σ s - L1s G σ t - L2s G σ t * (s - t)
        = deriv (cgf (fun x : ℝ => x) G) s - deriv (cgf (fun x : ℝ => x) G) t
          - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) := by
      simp only [L1s, L2s, tmu]; ring
    rw [e]; exact hb1
  · have e : Ls G σ s - Ls G σ t - L1s G σ t * (s - t) - L2s G σ t * (s - t) ^ 2 / 2
        = cgf (fun x : ℝ => x) G s - cgf (fun x : ℝ => x) G t
          - deriv (cgf (fun x : ℝ => x) G) t * (s - t)
          - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) ^ 2 / 2 := by
      simp only [Ls, L1s, L2s, tmu]; ring
    rw [e]; exact hb0

/-- Legendre expansion: `Λ(t) = t L1s t - Ls t` near a saddle. -/
lemma leg_at (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B R : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (σ : ℝ) {t t' : ℝ} (ht : |t| ≤ t1) (ht' : |t'| ≤ t1)
    (hR : |L1s G σ t' - L1s G σ t| ≤ R) :
    |(t' * L1s G σ t' - Ls G σ t') - (t * L1s G σ t - Ls G σ t) - t * (L1s G σ t' - L1s G σ t)
        - (L1s G σ t' - L1s G σ t) ^ 2 / (2 * L2s G σ t)|
      ≤ (4 * B ^ 2 * R + 2 * B) * |L1s G σ t' - L1s G σ t| ^ 3 := by
  obtain ⟨h1, h0⟩ := Ls_taylor hexp ht1 h2 hW σ ht ht'
  refine leg_exp (Ls G σ) (L1s G σ) (L2s G σ) ?_ (L1s_low hexp h2 ht1 hV σ ht' ht) hB hR h1 h0
  have := (hV t ht).1
  simp only [L2s]; nlinarith [sq_nonneg σ]

end Cr3

end P99bcb804

end X11_Cr3

section X12_Cr4

/-! R4 / Cr4: local Cramér form of the smoothed iid-sum density at the saddle point.
`lc_at`: `f(N L1s t) = exp(-N Λ(t)) (φ_{N L2s t}(0) ± (C/N + C(1-κ')^{N-1}/σ))`, `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Cr4

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma mgf_pow_exp (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t : ℝ} (ht : |t| ≤ a0) (N : ℕ) (σ a : ℝ) :
    mgf (fun x : ℝ => x) G t ^ N * exp (t ^ 2 * (N * σ ^ 2) / 2) * exp (-(t * a))
      = exp (N * Ls G σ t - t * a) := by
  rw [← exp_cgf (hexp t ht), ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Ls]
  congr 1
  ring

theorem lc_at (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C κ' : ℝ, 0 < C ∧ 0 < κ' ∧ κ' ≤ 1 ∧
      ∀ (ι : Type) [Fintype ι] (t σ : ℝ), |t| ≤ t1 → 0 < σ → σ ≤ 1 → 2 ≤ Fintype.card ι →
        |(∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal
              (Fintype.card ι * L1s G σ t - y)
              ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i)))
            - exp (-(Fintype.card ι * (t * L1s G σ t - Ls G σ t))) *
              gaussianPDFReal 0 (Fintype.card ι * L2s G σ t).toNNReal 0|
          ≤ exp (-(Fintype.card ι * (t * L1s G σ t - Ls G σ t))) *
              (C / Fintype.card ι + C * (1 - κ') ^ (Fintype.card ι - 1) / σ) := by
  obtain ⟨C, κ', hC, hκ'0, hκ'1, H⟩ := lc_any hexp p m v F2 hp0 hp1 hv0 hG ht1 h2 hV hpt
  refine ⟨C, κ', hC, hκ'0, hκ'1, ?_⟩
  intro ι _ t σ ht hσ hσ1 hN
  have h := H ι t σ (Fintype.card ι * L1s G σ t) ht hσ hσ1 hN
  have hta : |t| ≤ a0 := by linarith
  have harg : (Fintype.card ι : ℝ) * L1s G σ t - t * (Fintype.card ι * σ ^ 2)
      - Fintype.card ι * tmu G t = 0 := by
    simp only [L1s]; ring
  have hE : (Fintype.card ι : ℝ) * Ls G σ t - t * (Fintype.card ι * L1s G σ t)
      = -(Fintype.card ι * (t * L1s G σ t - Ls G σ t)) := by ring
  rw [mgf_pow_exp hexp hta, harg, hE] at h
  exact h

end Cr4

end P99bcb804

end X12_Cr4

section X13_Nd1

/-! R4 / Nd1 (Q5 node, near region): ratio of the smoothed density at `N(c±δ)` to `N c`.
`near_ratio`: `f(N(c+δ)) f(N(c-δ)) = f(Nc)² exp(-Nδ²/L2s tc) exp(±K(1/√N + |δ| + N|δ|³))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

/-- density of the smoothed iid sum `Σ_ι G + N(0, card·σ²)` at `a`. -/
noncomputable def fS (G : Measure ℝ) (ι : Type) [Fintype ι] (σ a : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
    ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))

section Nd1

lemma pt_rel {f E φ e η : ℝ} (hE : 0 < E) (hφ : 0 < φ) (h : |f - E * φ| ≤ E * e)
    (he : e ≤ η * φ) (hη : η ≤ 1 / 2) :
    E * φ * exp (-(2 * η)) ≤ f ∧ f ≤ E * φ * exp (2 * η) := by
  have h1 := abs_le.1 h
  have he0 : 0 ≤ e := by
    have := abs_nonneg (f - E * φ)
    by_contra hc; push Not at hc; nlinarith
  have hη0 : 0 ≤ η := by
    by_contra hc; push Not at hc; nlinarith
  have hEφ : 0 < E * φ := mul_pos hE hφ
  have hEe : E * e ≤ E * φ * η := by nlinarith
  have h2 : 1 + 2 * η ≤ exp (2 * η) := by linarith [add_one_le_exp (2 * η)]
  constructor
  · have hp : exp (-(2 * η)) * exp (2 * η) = 1 := by rw [← exp_add]; simp
    have hx : exp (-(2 * η)) ≤ 1 - η := by
      have hq := mul_le_mul_of_nonneg_left h2 (exp_pos (-(2 * η))).le
      nlinarith [exp_pos (-(2 * η))]
    nlinarith [mul_le_mul_of_nonneg_left hx hEφ.le]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hEφ.le]

lemma isqrt_ratio {a b r : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (hab : a - b ≤ r)
    (hba : b - a ≤ r) (hr : 0 ≤ r) :
    (√b)⁻¹ ≤ (√a)⁻¹ * exp r ∧ (√a)⁻¹ * exp (-r) ≤ (√b)⁻¹ := by
  have hpa : 0 < √a := Real.sqrt_pos.2 (by linarith)
  have hpb : 0 < √b := Real.sqrt_pos.2 (by linarith)
  have he2 : 1 + 2 * r ≤ exp r ^ 2 := by
    rw [← exp_nat_mul]; push_cast; linarith [add_one_le_exp (2 * r)]
  have key : ∀ x y : ℝ, 1 / 2 ≤ x → 1 / 2 ≤ y → x - y ≤ r → √x ≤ √y * exp r := by
    intro x y hx hy hxy
    rw [show √y * exp r = √(y * exp r ^ 2) by
      rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (exp_pos r).le]]
    apply Real.sqrt_le_sqrt
    nlinarith
  constructor
  · have k := key a b ha hb hab
    calc (√b)⁻¹ = (√a)⁻¹ * (√a / √b) := by field_simp
      _ ≤ (√a)⁻¹ * exp r := by
          gcongr
          rw [div_le_iff₀ hpb]; linarith
  · have k := key b a hb ha hba
    calc (√a)⁻¹ * exp (-r) = (√b)⁻¹ * ((√b / √a) * exp (-r)) := by field_simp
      _ ≤ (√b)⁻¹ * 1 := by
          gcongr
          rw [div_mul_eq_mul_div, div_le_one hpa, exp_neg, ← div_eq_mul_inv,
            div_le_iff₀ (exp_pos r)]
          linarith
      _ = (√b)⁻¹ := mul_one _

lemma gpdf0 {N L : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) :
    gaussianPDFReal 0 (N * L).toNNReal 0 = (√(2 * π * N))⁻¹ * (√L)⁻¹ := by
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ (mul_nonneg hN hL)]
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
    zero_div, exp_zero, mul_one]
  rw [← mul_inv, ← Real.sqrt_mul (by positivity)]
  congr 2; ring

end Nd1

end P99bcb804

end X13_Nd1

section X15_Kr1

/-! R4 / Kr1 (root, single factor): pointwise local Cramér for the smoothed sum density
`fS(Nδ) ≈ φ_{N L2s 0}(0) e^{-Nδ²/(2 L2s 0)}` with relative error `e^{±K(1/√N + |δ| + N|δ|³)}`
(`near_single`, the one-factor analogue of `near_ratio`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma comb1 {f E q q0 η a Q r s : ℝ} (hq : 0 < q) (hq0 : 0 < q0)
    (hf : E * q * exp (-(2 * η)) ≤ f ∧ f ≤ E * q * exp (2 * η)) (hE : E = exp (-a))
    (ha : |a - Q| ≤ r) (hqq : q ≤ q0 * exp s ∧ q0 * exp (-s) ≤ q) :
    q0 * exp (-Q) * exp (-(r + s + 2 * η)) ≤ f ∧ f ≤ q0 * exp (-Q) * exp (r + s + 2 * η) := by
  have ha' := abs_le.1 ha
  have h1 : exp (-a) ≤ exp (-Q) * exp r := by
    rw [← exp_add]; exact exp_le_exp.2 (by linarith)
  have h2 : exp (-Q) * exp (-r) ≤ exp (-a) := by
    rw [← exp_add]; exact exp_le_exp.2 (by linarith)
  constructor
  · calc q0 * exp (-Q) * exp (-(r + s + 2 * η))
          = (exp (-Q) * exp (-r)) * (q0 * exp (-s)) * exp (-(2 * η)) := by
            rw [show -(r + s + 2 * η) = -r + -s + -(2 * η) by ring, exp_add, exp_add]; ring
      _ ≤ E * q * exp (-(2 * η)) := by
            rw [hE]
            exact mul_le_mul_of_nonneg_right (mul_le_mul h2 hqq.2 (by positivity)
              (exp_pos _).le) (exp_pos _).le
      _ ≤ f := hf.1
  · calc f ≤ E * q * exp (2 * η) := hf.2
      _ ≤ (exp (-Q) * exp r) * (q0 * exp s) * exp (2 * η) := by
            rw [hE]
            exact mul_le_mul_of_nonneg_right (mul_le_mul h1 hqq.1 hq.le (by positivity))
              (exp_pos _).le
      _ = q0 * exp (-Q) * exp (r + s + 2 * η) := by
            rw [exp_add, exp_add]; ring

lemma hK_l {η0 B KL u d w : ℝ} (hη : 0 ≤ η0) (hB : 0 ≤ B) (hKL : 0 ≤ KL) (hu : 0 ≤ u)
    (hd : 0 ≤ d) (hw : 0 ≤ w) :
    w * KL + 2 * B * d + 2 * (η0 * u) ≤ (2 * η0 + 2 * B + KL) * (u + d + w) := by
  nlinarith [mul_nonneg hη hd, mul_nonneg hη hw, mul_nonneg hB hu, mul_nonneg hB hw,
    mul_nonneg hKL hu, mul_nonneg hKL hd]

section Kr1

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem near_single (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ κ' K N1 : ℝ, 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ K ∧
      ∀ (ι : Type) [Fintype ι] (σ δ : ℝ), 0 < σ → σ ≤ 1 →
        N1 ≤ (Fintype.card ι : ℝ) → 2 ≤ Fintype.card ι →
        (1 - κ') ^ (Fintype.card ι - 1) / σ ≤ 1 / (Fintype.card ι : ℝ) →
        |δ| ≤ t1 / 2 →
        (√(2 * π * Fintype.card ι))⁻¹ * (√(L2s G σ 0))⁻¹ *
            exp (-(Fintype.card ι * δ ^ 2 / (2 * L2s G σ 0))) *
            exp (-(K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)))
          ≤ fS G ι σ (Fintype.card ι * δ) ∧
        fS G ι σ (Fintype.card ι * δ) ≤
          (√(2 * π * Fintype.card ι))⁻¹ * (√(L2s G σ 0))⁻¹ *
            exp (-(Fintype.card ι * δ ^ 2 / (2 * L2s G σ 0))) *
            exp (K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)) := by
  obtain ⟨C, κ', hC, hκ0, hκ1, H⟩ := lc_at hexp p m v F2 hp0 hp1 hv0 hG ht1 h2 hV hpt
  set η0 := 2 * C * √(6 * π) with hη0
  have hη00 : 0 ≤ η0 := by positivity
  set KL := 4 * B ^ 2 * t1 + 2 * B with hKL
  have hKL0 : 0 ≤ KL := by positivity
  refine ⟨κ', 2 * η0 + 2 * B + KL, (2 * η0) ^ 2, hκ0, hκ1, by positivity, ?_⟩
  intro ι _ σ δ hσ hσ1 hN1 hN2 hκN hδ
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN2' : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN2
  have hN : 0 < N := by linarith
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  set η := η0 / √N with hηdef
  have hη0' : 0 ≤ η := by positivity
  have hη : η ≤ 1 / 2 := by
    have h1 : 2 * η0 ≤ √N := Real.le_sqrt_of_sq_le hN1
    rw [hηdef, div_le_iff₀ hsN]; linarith
  have hL2 : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ L2s G σ t ∧ L2s G σ t ≤ 3 := by
    intro t ht
    have := hV t ht
    have hs2 : σ ^ 2 ≤ 1 := by nlinarith
    simp only [L2s]; constructor <;> nlinarith [sq_nonneg σ]
  have hpt' : ∀ t : ℝ, |t| ≤ t1 →
      exp (-(N * (t * L1s G σ t - Ls G σ t))) * gaussianPDFReal 0 (N * L2s G σ t).toNNReal 0 *
          exp (-(2 * η)) ≤ fS G ι σ (N * L1s G σ t) ∧
        fS G ι σ (N * L1s G σ t) ≤ exp (-(N * (t * L1s G σ t - Ls G σ t))) *
          gaussianPDFReal 0 (N * L2s G σ t).toNNReal 0 * exp (2 * η) := by
    intro t ht
    have h := H ι t σ ht hσ hσ1 hN2
    obtain ⟨hl, hu⟩ := hL2 t ht
    have hq : gaussianPDFReal 0 (N * L2s G σ t).toNNReal 0
        = (√(2 * π * N))⁻¹ * (√(L2s G σ t))⁻¹ := gpdf0 hN.le (by linarith)
    have hqpos : 0 < gaussianPDFReal 0 (N * L2s G σ t).toNNReal 0 := by
      rw [hq]; have : 0 < √(L2s G σ t) := Real.sqrt_pos.2 (by linarith); positivity
    refine pt_rel (exp_pos _) hqpos h ?_ hη
    have he1 : C / N + C * (1 - κ') ^ (Fintype.card ι - 1) / σ ≤ 2 * C / N := by
      have : C * (1 - κ') ^ (Fintype.card ι - 1) / σ ≤ C * (1 / N) := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hκN hC.le
      rw [mul_one_div] at this; linarith [show 2 * C / N = C / N + C / N by ring]
    refine le_trans he1 ?_
    have hs6 : 0 < √(6 * π) := Real.sqrt_pos.2 (by positivity)
    have hsq : √(2 * π * N) * √(L2s G σ t) ≤ √(6 * π) * √N := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℝ) ≤ 2 * π * N)
      linarith
    have hpos : 0 < √(2 * π * N) * √(L2s G σ t) := by
      have : 0 < √(L2s G σ t) := Real.sqrt_pos.2 (by linarith)
      have : 0 < √(2 * π * N) := Real.sqrt_pos.2 (by positivity)
      positivity
    rw [hq, ← mul_inv, hηdef, hη0]
    rw [div_mul_eq_mul_div, le_div_iff₀ hsN, div_mul_eq_mul_div, div_le_iff₀ hN]
    have : 2 * C * √(6 * π) * (√(2 * π * N) * √(L2s G σ t))⁻¹ * N
        ≥ 2 * C * √(6 * π) * (√(6 * π) * √N)⁻¹ * N := by
      gcongr
    have e : 2 * C * √(6 * π) * (√(6 * π) * √N)⁻¹ * N = 2 * C * √N := by
      calc 2 * C * √(6 * π) * (√(6 * π) * √N)⁻¹ * N
          = 2 * C * (√(6 * π) * (√(6 * π))⁻¹) * (N / √N) := by rw [mul_inv]; ring
        _ = 2 * C * √N := by rw [mul_inv_cancel₀ hs6.ne', Real.div_sqrt, mul_one]
    nlinarith
  -- base point 0
  have h0 : |(0 : ℝ)| ≤ t1 := by simp [ht1.le]
  have hL0 : L1s G σ 0 = 0 := by simp [L1s, tmu_zero ha0 hexp hm]
  have hLs0 : Ls G σ 0 = 0 := by simp [Ls]
  obtain ⟨tp, htp, hLp, htp2⟩ := saddle ha0 hexp hm h2 ht1 hV σ hδ
  have hδt1 : |δ| ≤ t1 := by linarith
  have legp := leg_at hexp ht1 h2 hB hV hW σ (R := t1) h0 htp
    (by rw [hLp, hL0, sub_zero]; exact hδt1)
  rw [hLp, hL0, hLs0, sub_zero] at legp
  have e0 : tp * δ - Ls G σ tp - 0 * 0 - 0 * (δ - 0) - (δ - 0) ^ 2 / (2 * L2s G σ 0)
      = (tp * δ - Ls G σ tp) - δ ^ 2 / (2 * L2s G σ 0) := by ring
  rw [e0, sub_zero] at legp
  -- L2 Lipschitz
  have hlip : |L2s G σ 0 - L2s G σ tp| ≤ 2 * B * |δ| := by
    have h1 := (cum_taylor ht1 h2 hexp hW h0 htp).1
    have e : L2s G σ 0 - L2s G σ tp = -(iteratedDeriv 2 (cgf (fun x : ℝ => x) G) tp
        - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) 0) := by simp only [L2s]; ring
    rw [e, abs_neg]
    calc _ ≤ B * |tp - 0| := h1
      _ ≤ B * (2 * |δ|) := by gcongr; rw [sub_zero]; exact htp2
      _ = 2 * B * |δ| := by ring
  have hBd : 0 ≤ 2 * B * |δ| := by positivity
  have hq : ∀ t : ℝ, |t| ≤ t1 → gaussianPDFReal 0 (N * L2s G σ t).toNNReal 0
      = (√(2 * π * N))⁻¹ * (√(L2s G σ t))⁻¹ := fun t ht => gpdf0 hN.le (by linarith [(hL2 t ht).1])
  have qp : gaussianPDFReal 0 (N * L2s G σ tp).toNNReal 0
        ≤ (√(2 * π * N))⁻¹ * (√(L2s G σ 0))⁻¹ * exp (2 * B * |δ|) ∧
      (√(2 * π * N))⁻¹ * (√(L2s G σ 0))⁻¹ * exp (-(2 * B * |δ|))
        ≤ gaussianPDFReal 0 (N * L2s G σ tp).toNNReal 0 := by
    have hl' := abs_le.1 hlip
    obtain ⟨r1, r2⟩ := isqrt_ratio (hL2 0 h0).1 (hL2 tp htp).1 (by linarith) (by linarith) hBd
    rw [hq tp htp]
    have hpos : 0 ≤ (√(2 * π * N))⁻¹ := by positivity
    constructor
    · exact le_of_le_of_eq (mul_le_mul_of_nonneg_left r1 hpos) (by ring)
    · exact le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left r2 hpos)
  have Fp := hpt' tp htp
  rw [hLp] at Fp
  have hqpos : 0 < gaussianPDFReal 0 (N * L2s G σ tp).toNNReal 0 := by
    rw [hq tp htp]
    have : 0 < √(L2s G σ tp) := Real.sqrt_pos.2 (by linarith [(hL2 tp htp).1])
    positivity
  have hq0pos : 0 < (√(2 * π * N))⁻¹ * (√(L2s G σ 0))⁻¹ := by
    have : 0 < √(L2s G σ 0) := Real.sqrt_pos.2 (by linarith [(hL2 0 h0).1])
    have : 0 < √(2 * π * N) := Real.sqrt_pos.2 (by positivity)
    positivity
  have haQ : |N * (tp * δ - Ls G σ tp) - N * δ ^ 2 / (2 * L2s G σ 0)| ≤ N * (KL * |δ| ^ 3) := by
    have e : N * (tp * δ - Ls G σ tp) - N * δ ^ 2 / (2 * L2s G σ 0)
        = N * ((tp * δ - Ls G σ tp) - δ ^ 2 / (2 * L2s G σ 0)) := by ring
    rw [e, abs_mul, abs_of_pos hN]
    gcongr
  have hfin := comb1 hqpos hq0pos Fp rfl haQ qp
  have hK : N * (KL * |δ| ^ 3) + 2 * B * |δ| + 2 * η
      ≤ (2 * η0 + 2 * B + KL) * (1 / √N + |δ| + N * |δ| ^ 3) := by
    have e : η = η0 * (1 / √N) := by rw [hηdef]; ring
    have e2 : N * (KL * |δ| ^ 3) = (N * |δ| ^ 3) * KL := by ring
    rw [e, e2]
    exact hK_l hη00 hB hKL0 (by positivity) (abs_nonneg δ) (by positivity)
  constructor
  · refine le_trans ?_ hfin.1
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg hK)) (by positivity)
  · refine le_trans hfin.2 ?_
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 hK) (by positivity)

end Kr1

end P99bcb804

end X15_Kr1

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (0 : ℝ) < a0 →
        (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
          ∫ (x : ℝ), x ∂G = (0 : ℝ) →
            ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
              (0 : ℝ) < p →
                p ≤ (1 : ℝ) →
                  (0 : NNReal) < v →
                    G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                      ∀ {t1 B : ℝ},
                        (0 : ℝ) < t1 →
                          (2 : ℝ) * t1 < a0 →
                            (0 : ℝ) ≤ B →
                              (∀ (t : ℝ),
                                  |t| ≤ t1 →
                                    (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                      iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                                (∀ t ∈ Set.Icc (-((2 : ℝ) * t1)) ((2 : ℝ) * t1),
                                    |iteratedDeriv (3 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t| ≤ B) →
                                  (∀ (t : ℝ),
                                      |t| ≤ t1 →
                                        (1 / 2 : ℝ) ≤
                                          ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                            ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                                    ∃ (κ' : ℝ) (K : ℝ) (N1 : ℝ),
                                      (0 : ℝ) < κ' ∧
                                        κ' ≤ (1 : ℝ) ∧
                                          (0 : ℝ) ≤ K ∧
                                            ∀ (ι : Type) [inst : Fintype ι] (σ δ : ℝ),
                                              (0 : ℝ) < σ →
                                                σ ≤ (1 : ℝ) →
                                                  N1 ≤ ↑(Fintype.card ι) →
                                                    (2 : ℕ) ≤ Fintype.card ι →
                                                      ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ ≤
                                                          (1 : ℝ) / ↑(Fintype.card ι) →
                                                        |δ| ≤ t1 / (2 : ℝ) →
                                                          (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(iteratedDeriv (2 : ℕ)
                                                                            (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                            (0 : ℝ) +
                                                                          σ ^ (2 : ℕ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) *
                                                                          (iteratedDeriv (2 : ℕ)
                                                                              (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                              (0 : ℝ) +
                                                                            σ ^ (2 : ℕ))))) *
                                                                Real.exp
                                                                  (-(K *
                                                                      ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                        ↑(Fintype.card ι) * |δ| ^ (3 : ℕ)))) ≤
                                                              ∫ (y : ℝ),
                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                  (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                  (↑(Fintype.card ι) * δ -
                                                                    y) ∂MeasureTheory.Measure.map
                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                  (MeasureTheory.Measure.pi fun (x : ι) => G) ∧
                                                            ∫ (y : ℝ),
                                                                ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                                  (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                                  (↑(Fintype.card ι) * δ -
                                                                    y) ∂MeasureTheory.Measure.map
                                                                  (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                                  (MeasureTheory.Measure.pi fun (x : ι) => G) ≤
                                                              (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(iteratedDeriv (2 : ℕ)
                                                                            (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                            (0 : ℝ) +
                                                                          σ ^ (2 : ℕ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) *
                                                                          (iteratedDeriv (2 : ℕ)
                                                                              (ProbabilityTheory.cgf (fun (x : ℝ) => x) G)
                                                                              (0 : ℝ) +
                                                                            σ ^ (2 : ℕ))))) *
                                                                Real.exp
                                                                  (K *
                                                                    ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                      ↑(Fintype.card ι) * |δ| ^ (3 : ℕ))) := by
  first
  | exact P99bcb804.near_single
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.near_single <;> assumption)
