-- Prove2me | solution 1 for EthierKurtz.kmt_permutation_conditional_quantile_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:13:42.685506+00:00
-- url     : https://prove2.me/submissions/59530da0-791e-4f07-b5be-a4ae8ee55147

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_finite_population_cramer_average
import Theorems.Thm_EthierKurtz_cramer_weighted_rademacher_sums
import Theorems.Thm_EthierKurtz_tusnady_quantile_sandwich

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X11_Cr3

/-! R4 / Cr3: smoothed cumulant functions, saddle point, Legendre expansion.
`Ls G σ t = cgf t + t²σ²/2` (cgf of `G ∗ N(0,σ²)`), `L1s = Ls'`, `L2s = Ls''`.
* `L1s_mono`: `L1s` increases at rate `≥ 1/2` on `[-t1,t1]`; `saddle`: `L1s t = c` solvable for `|c| ≤ t1/2`, `|t| ≤ 2|c|`;
* `Ls_taylor`: Taylor bounds; `leg_at`: Legendre expansion of `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

end Cr3

end P99bcb804

end X11_Cr3

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

end Nd1

end P99bcb804

end X13_Nd1

section X19_Mills

/-! Gaussian toolkit for 99bcb804 (KMT): standard normal density, cdf, Mills-ratio bounds. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

/-- Standard normal density. -/
noncomputable def phi (t : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2))

lemma phi_pos (t : ℝ) : 0 < phi t := by
  unfold phi; positivity

lemma gaussianPDFReal_std (t : ℝ) : gaussianPDFReal 0 1 t = phi t := by
  simp [gaussianPDFReal_def, phi, neg_div]

lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

lemma integrable_phi : Integrable phi := by
  have := integrable_gaussianPDFReal 0 1
  simpa [funext gaussianPDFReal_std] using this

/-- Standard normal cdf as an integral of the density. -/
lemma cdf_std_eq (x : ℝ) : cdf (gaussianReal 0 1) x = ∫ t in Iic x, phi t := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  simp [gaussianPDFReal_std]

lemma integral_phi : ∫ t, phi t = 1 := by
  have := integral_gaussianPDFReal_eq_one 0 (v := 1) one_ne_zero
  simpa [funext gaussianPDFReal_std] using this

/-- Upper tail of the standard normal. -/
lemma one_sub_cdf_std (x : ℝ) : 1 - cdf (gaussianReal 0 1) x = ∫ t in Ioi x, phi t := by
  rw [cdf_std_eq, ← integral_phi, ← integral_add_compl (measurableSet_Iic (a := x)) integrable_phi,
    compl_Iic]
  ring

lemma phi_neg (t : ℝ) : phi (-t) = phi t := by
  simp [phi]

/-- The standard normal cdf has derivative `φ`. -/
lemma hasDerivAt_cdf_std (x : ℝ) :
    HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (phi x) x := by
  have e : (fun y => cdf (gaussianReal 0 1) y)
      = fun y => (∫ t in Iic 0, phi t) + ∫ t in (0 : ℝ)..y, phi t := by
    funext y
    rw [cdf_std_eq, ← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn
      integrable_phi.integrableOn]
    ring
  rw [e]
  exact ((continuous_phi.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

lemma continuous_cdf_std : Continuous (fun y => cdf (gaussianReal 0 1) y) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cdf_std x).continuousAt

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_std_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq, one_sub_cdf_std]
  have : ∫ t in Iic (-x), phi t = ∫ t in Iic (-x), phi (-t) := by
    simp_rw [phi_neg]
  rw [this, integral_comp_neg_Iic, neg_neg]

lemma cdf_std_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq]
  have hsupp : Function.support phi = univ := by
    ext t; simp [(phi_pos t).ne']
  have hpos : 0 < volume (Function.support phi ∩ Iic x) := by
    rw [hsupp, univ_inter, Real.volume_Iic]; exact ENNReal.zero_lt_top
  exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (phi_pos t).le)
    integrable_phi.integrableOn).mpr hpos

lemma cdf_std_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 := by
  have := cdf_std_pos (-x)
  rw [cdf_std_neg] at this
  linarith

/-! ### Stein solution for the indicator `1{w ≤ z}` (Chen–Goldstein–Shao, Lemma 2.3) -/

/-- Standard normal cdf as a real function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-! ## Child C (Tusnády quantile inequality), generic over the family of sum laws. -/

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := hasDerivAt_cdf_std x

lemma continuous_Phi' : Continuous Phi := continuous_cdf_std

lemma one_sub_Phi_pos (w : ℝ) : 0 < 1 - Phi w := by
  have := cdf_std_lt_one w; unfold Phi; linarith

/-! ## Gaussian hazard `Hz = φ/(1-Φ)` and the two-sided log-tail Taylor bound (KMT 1976 II, (4.5)). -/

end P99bcb804

end X19_Mills

section X23_Nd5

/-! R4 / Nd5: the standardised conditional density of the half-difference given the total.
`ffN x = fS(Nc + s x/2) fS(Nc - s x/2)`, `s = √(2N L2s tc)`, `hN = ffN / ZN`. Integrability,
`near_x` (near bounds in the `x` variable) and `ZN_low` (`ZN ≥ 2 fS(Nc)² e^{-1}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ tc : ℝ) : ℝ :=
  √(2 * Fintype.card ι * L2s G σ tc)

noncomputable def ffN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  fS G ι σ (Fintype.card ι * c + sN G ι σ tc * x / 2) *
    fS G ι σ (Fintype.card ι * c - sN G ι σ tc * x / 2)

noncomputable def ZN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc : ℝ) : ℝ :=
  ∫ x, ffN G ι σ c tc x

noncomputable def hN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  ffN G ι σ c tc x / ZN G ι σ c tc

section Nd5

variable {G : Measure ℝ} [IsProbabilityMeasure G]

end Nd5

end P99bcb804

end X23_Nd5

section X31_Sym

/-! KMT 1976 II, p.42 symmetrisation: a uniform permutation of the half-sample statistic equals
a uniform pairing `π` followed by independent sign flips inside the pairs. -/

open Finset

namespace P99bcb804

/-- Swap `inl i ↔ inr i` exactly for the `i` with `ε i = true`. -/
def swapE {N : ℕ} (ε : Fin N → Bool) : Equiv.Perm (Fin N ⊕ Fin N) where
  toFun s := match s with
    | Sum.inl i => if ε i then Sum.inr i else Sum.inl i
    | Sum.inr i => if ε i then Sum.inl i else Sum.inr i
  invFun s := match s with
    | Sum.inl i => if ε i then Sum.inr i else Sum.inl i
    | Sum.inr i => if ε i then Sum.inl i else Sum.inr i
  left_inv s := by
    rcases s with i | i <;> by_cases h : ε i <;> simp [h]
  right_inv s := by
    rcases s with i | i <;> by_cases h : ε i <;> simp [h]

/-- Half-sample difference on `Fin N ⊕ Fin N`. -/
noncomputable def hdS {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (π : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  ∑ i, (x (π (Sum.inl i)) - x (π (Sum.inr i)))

/-- Signed pair sum `Σ ± (x_{π(inl i)} - x_{π(inr i)})`. -/
noncomputable def sgnSum {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (π : Equiv.Perm (Fin N ⊕ Fin N))
    (ε : Fin N → Bool) : ℝ :=
  ∑ i, (if ε i then (-1 : ℝ) else 1) * (x (π (Sum.inl i)) - x (π (Sum.inr i)))

lemma hdS_swap {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (π : Equiv.Perm (Fin N ⊕ Fin N))
    (ε : Fin N → Bool) : hdS x (π * swapE ε) = sgnSum x π ε := by
  unfold hdS sgnSum
  refine sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [swapE, h]

/-- Symmetrisation identity, counting form:
`2^N · #{π : E(Ũ(π))} = Σ_π #{ε : E(Σ ±dᵢ(π))}`. -/
theorem sym_count {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (E : ℝ → Prop) [DecidablePred E] :
    2 ^ N * (univ.filter (fun π : Equiv.Perm (Fin N ⊕ Fin N) => E (hdS x π))).card =
      ∑ π : Equiv.Perm (Fin N ⊕ Fin N),
        (univ.filter (fun ε : Fin N → Bool => E (sgnSum x π ε))).card := by
  simp only [card_filter]
  have h1 : ∀ π : Equiv.Perm (Fin N ⊕ Fin N),
      (∑ ε : Fin N → Bool, if E (sgnSum x π ε) then 1 else 0) =
        ∑ ε : Fin N → Bool, if E (hdS x (π * swapE ε)) then 1 else 0 := fun π =>
    sum_congr rfl fun ε _ => by rw [hdS_swap]
  rw [sum_congr rfl fun π _ => h1 π, sum_comm]
  have h2 : ∀ ε : Fin N → Bool,
      (∑ π : Equiv.Perm (Fin N ⊕ Fin N), if E (hdS x (π * swapE ε)) then 1 else 0) =
        ∑ π : Equiv.Perm (Fin N ⊕ Fin N), if E (hdS x π) then 1 else 0 := fun ε =>
    Fintype.sum_equiv (Equiv.mulRight (swapE ε)) _ _ (fun π => rfl)
  rw [sum_congr rfl fun ε _ => h2 ε, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, smul_eq_mul]

end P99bcb804

end X31_Sym

section X33_Stein

/-! Stein solution layer for 99bcb804 (copied from _be.lean). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

lemma phi_le_half (t : ℝ) : phi t ≤ 1 / 2 := by
  unfold phi
  have h1 : (2 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2 : (√(2 * π))⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h1
  have h3 : rexp (-(t ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have h4 : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)) ≤ (√(2 * π))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h3 h4
    _ ≤ 1 / 2 := by rw [mul_one]; exact h2

end P99bcb804

end X33_Stein

section X41_Dperm

/-! KMT 1976 II, (4.7) instantiated for pairings `w : Perm (Fin N ⊕ Fin N)`:
the pair variance `sw2 x w = σ_w²/N` and the averaged Gaussian tail. Iteration file: imports the
helper modules `P99bcb804Mills/Delta/L4` (oleans built by scratch/probe/99bcb804_mods/build.sh). -/

open Finset Real

namespace P99bcb804

/-- Pair variance `σ_w²/N` for the pairing `(w (inl i), w (inr i))`. -/
noncomputable def sw2 {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  (∑ i, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ 2) / N

/-! Constants. -/

/-! Named quantities: `s = sS x`, `α = kα x y`, `L = kL c y N`, `Y = kY y N`. -/
noncomputable def sS {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) : ℝ := √((∑ i, x i ^ 2) / N)
noncomputable def kY (y : ℝ) (N : ℕ) : ℝ := (y ^ 3 + 1) / √(N : ℝ)

/-- KMT 1976 II, (4.7) for pairings: with `s = sS x` and `Y = (y³+1)/√N`,
`Σ_good G(y/s_w) = card·G(y/s)·exp(±C·Y)`, and the bad pairings number at most `card·G(y/s)/√N`. -/
theorem dperm (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ ε C N0 : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → c * N ≤ ∑ i, x i ^ 2 →
      ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
        ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
            (1 - Phi (y / √(sw2 x w))) ≤
          (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
            exp (C * kY y N) ∧
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) ≤
          (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) / √(N : ℝ) ∧
        (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
            exp (-(C * kY y N)) ≤
          ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
            (1 - Phi (y / √(sw2 x w))) := by
  have hfact := @EthierKurtz.kmt_finite_population_cramer_average
  apply hfact <;> assumption

end P99bcb804

end X41_Dperm

section X42_Cram3

/-! KMT 1976 II, Lemma B (pp.42-43): Cramér estimate for Rademacher-weighted sums. -/

open Real Finset

namespace P99bcb804

/-- copy of the statement in `99bcb804_fpc.lean`. -/
def SignCramer : Prop :=
  ∀ M b : ℝ, 0 < M → 0 < b → ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
    ∀ d : Fin N → ℝ, (∀ i, |d i| ≤ M) → b * N ≤ ∑ i, d i ^ 2 →
    ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
      (1 - Phi (y * √(N : ℝ) / √(∑ i, d i ^ 2))) * exp (-(C * kY y N)) ≤
        ((univ.filter (fun e : Fin N → Bool =>
          y * √(N : ℝ) < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N ∧
      ((univ.filter (fun e : Fin N → Bool =>
          y * √(N : ℝ) < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N ≤
        (1 - Phi (y * √(N : ℝ) / √(∑ i, d i ^ 2))) * exp (C * kY y N)

/-- KMT 1976 II, Lemma B. -/
theorem signCramer_holds : SignCramer := by
  have hfact := @EthierKurtz.cramer_weighted_rademacher_sums
  apply hfact <;> assumption

end P99bcb804

end X42_Cram3

section X43_Fpc

/-! KMT 1976 II, Lemma 3 (finite-population Cramér, right tail) from Lemma B (`SignCramer`),
the symmetrisation identity `sym_count` and the pairing average `dperm` ((4.7)). -/

open Finset Real

namespace P99bcb804

lemma exp_add_le {a Y : ℝ} (ha : 0 ≤ a) (hY : 0 ≤ Y) : exp (a * Y) + Y ≤ exp ((a + 1) * Y) := by
  have h1 := add_one_le_exp Y
  have h2 : 1 ≤ exp (a * Y) := Real.one_le_exp (mul_nonneg ha hY)
  have e : exp ((a + 1) * Y) = exp (a * Y) * exp Y := by rw [← exp_add]; ring_nf
  rw [e]
  nlinarith

/-- KMT 1976 II, Lemma 3, right tail, conditional on Lemma B. -/
theorem finpop_right (hB : SignCramer) (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → c * N ≤ ∑ i, x i ^ 2 →
      ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
        (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
          ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
          (1 - Phi (y / sS x)) * exp (C * kY y N) := by
  obtain ⟨εΔ, CΔ, NΔ, hεΔ0, -, hCΔ, hΔ⟩ := dperm K c hK hc
  obtain ⟨εB, CB, NB, hεB0, hCB, hBB⟩ := hB (2 * K) (c / 2) (by positivity) (by positivity)
  refine ⟨min εΔ εB, CΔ + CB + 1, max NΔ NB, lt_min hεΔ0 hεB0, by linarith, ?_⟩
  intro N hN hN0 x hx hs hcS y hy hyε
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < √(N : ℝ) := Real.sqrt_pos.2 hn
  have hyΔ : y ≤ εΔ * √(N : ℝ) :=
    hyε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hyB : y ≤ εB * √(N : ℝ) :=
    hyε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le)
  obtain ⟨hU, hbad, hL⟩ := hΔ N hN ((le_max_left _ _).trans hN0) x hx hs hcS y hy hyΔ
  have hcard0 : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) := by
    exact_mod_cast Fintype.card_pos
  have hG0 : 0 < 1 - Phi (y / sS x) := one_sub_Phi_pos _
  have hY0 : 0 ≤ kY y N := by unfold kY; positivity
  have hY1 : 1 / √(N : ℝ) ≤ kY y N := by
    unfold kY; exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hy 3]) hr.le
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  -- the conditional probabilities
  set P : Equiv.Perm (Fin N ⊕ Fin N) → ℝ := fun w =>
    ((univ.filter (fun e : Fin N → Bool => y * √(N : ℝ) < sgnSum x w e)).card : ℝ) / 2 ^ N
    with hPdef
  have hP1 : ∀ w, P w ≤ 1 := by
    intro w
    rw [hPdef, div_le_one h2N]
    have : (univ.filter (fun e : Fin N → Bool => y * √(N : ℝ) < sgnSum x w e)).card ≤ 2 ^ N := by
      calc _ ≤ (univ : Finset (Fin N → Bool)).card := card_filter_le _ _
        _ = 2 ^ N := by rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact_mod_cast this
  have hP0 : ∀ w, 0 ≤ P w := fun w => by rw [hPdef]; positivity
  have hsym : ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
      y * √(N : ℝ) < hdS x w)).card : ℝ) = ∑ w, P w := by
    have h := sym_count x (fun t => y * √(N : ℝ) < t)
    have h' : (2 : ℝ) ^ N * ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
        y * √(N : ℝ) < hdS x w)).card : ℝ) = ∑ w : Equiv.Perm (Fin N ⊕ Fin N),
          ((univ.filter (fun e : Fin N → Bool => y * √(N : ℝ) < sgnSum x w e)).card : ℝ) := by
      exact_mod_cast h
    rw [hPdef, ← sum_div, ← h']
    field_simp
  have hgood : ∀ w, c / 2 ≤ sw2 x w →
      (1 - Phi (y / √(sw2 x w))) * exp (-(CB * kY y N)) ≤ P w ∧
        P w ≤ (1 - Phi (y / √(sw2 x w))) * exp (CB * kY y N) := by
    intro w hw
    have hd : ∀ i, |x (w (Sum.inl i)) - x (w (Sum.inr i))| ≤ 2 * K := fun i =>
      (abs_sub _ _).trans (by linarith [hx (w (Sum.inl i)), hx (w (Sum.inr i))])
    have hsum : ∑ i, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ 2 = N * sw2 x w := by
      unfold sw2; field_simp
    have hbN : c / 2 * N ≤ ∑ i, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ 2 := by
      rw [hsum]; have := mul_le_mul_of_nonneg_left hw hn.le; linarith
    obtain ⟨h1, h2⟩ := hBB N hN ((le_max_right _ _).trans hN0) _ hd hbN y hy hyB
    have harg : y * √(N : ℝ) / √(∑ i, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ 2) =
        y / √(sw2 x w) := by
      rw [hsum, Real.sqrt_mul hn.le, mul_comm y, mul_div_mul_left _ _ hr.ne']
    rw [harg] at h1 h2
    exact ⟨h1, h2⟩
  have hsplit := sum_filter_add_sum_filter_not univ
    (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w) P
  rw [hsym]
  set card := (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) with hcard
  set G0 := 1 - Phi (y / sS x) with hG0def
  set Y := kY y N with hYdef
  constructor
  · -- lower bound
    rw [le_div_iff₀ hcard0]
    have hgoodL : ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
        (1 - Phi (y / √(sw2 x w))) * exp (-(CB * Y)) ≤
        ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w), P w :=
      sum_le_sum fun w hw => (hgood w (mem_filter.1 hw).2).1
    rw [← sum_mul] at hgoodL
    have hbadnn : 0 ≤ ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w),
        P w := sum_nonneg fun w _ => hP0 w
    have h3 : card * G0 * exp (-(CΔ * Y)) * exp (-(CB * Y)) ≤
        (∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
          (1 - Phi (y / √(sw2 x w)))) * exp (-(CB * Y)) :=
      mul_le_mul_of_nonneg_right hL (exp_pos _).le
    have e : card * G0 * exp (-(CΔ * Y)) * exp (-(CB * Y)) = G0 * exp (-((CΔ + CB) * Y)) * card := by
      rw [mul_assoc (card * G0), ← exp_add]; ring_nf
    have h4 : G0 * exp (-((CΔ + CB + 1) * Y)) * card ≤ G0 * exp (-((CΔ + CB) * Y)) * card := by
      apply mul_le_mul_of_nonneg_right _ hcard0.le
      apply mul_le_mul_of_nonneg_left _ hG0.le
      exact exp_le_exp.2 (by linarith)
    linarith
  · -- upper bound
    rw [div_le_iff₀ hcard0]
    have hgoodU : ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w), P w ≤
        ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
        (1 - Phi (y / √(sw2 x w))) * exp (CB * Y) :=
      sum_le_sum fun w hw => (hgood w (mem_filter.1 hw).2).2
    rw [← sum_mul] at hgoodU
    have hbadU : ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w), P w ≤
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) := by
      calc _ ≤ ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w),
            (1 : ℝ) := sum_le_sum fun w _ => hP1 w
        _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]
    have h3 : (∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
          (1 - Phi (y / √(sw2 x w)))) * exp (CB * Y) ≤ card * G0 * exp (CΔ * Y) * exp (CB * Y) :=
      mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h5 : card * G0 / √(N : ℝ) ≤ card * G0 * Y := by
      rw [div_eq_mul_one_div (card * G0)]
      exact mul_le_mul_of_nonneg_left hY1 (mul_nonneg hcard0.le hG0.le)
    have e : card * G0 * exp (CΔ * Y) * exp (CB * Y) = card * G0 * exp ((CΔ + CB) * Y) := by
      rw [mul_assoc (card * G0), ← exp_add]; ring_nf
    have h6 := exp_add_le (by linarith : 0 ≤ CΔ + CB) hY0
    have h7 : card * G0 * (exp ((CΔ + CB) * Y) + Y) ≤ card * G0 * exp ((CΔ + CB + 1) * Y) :=
      mul_le_mul_of_nonneg_left h6 (mul_nonneg hcard0.le hG0.le)
    linarith

/-- KMT 1976 II, Lemma 3, right tail (unconditional). -/
theorem finpop_right_u (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → c * N ≤ ∑ i, x i ^ 2 →
      ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
        (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
          ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
          (1 - Phi (y / sS x)) * exp (C * kY y N) :=
  finpop_right signCramer_holds K c hK hc

lemma hdS_neg {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    hdS (fun i => -x i) w = -hdS x w := by
  unfold hdS; rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sS_neg {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) : sS (fun i => -x i) = sS x := by
  unfold sS; simp only [neg_sq]

/-- KMT 1976 II, Lemma 3, left tail, by reflection `x ↦ -x`. -/
theorem finpop_left (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → c * N ≤ ∑ i, x i ^ 2 →
      ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
        (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
          ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
            hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
          (1 - Phi (y / sS x)) * exp (C * kY y N) := by
  obtain ⟨ε, C, N0, hε, hC, h⟩ := finpop_right_u K c hK hc
  refine ⟨ε, C, N0, hε, hC, ?_⟩
  intro N hN hN0 x hx hs hcS y hy hyε
  have := h N hN hN0 (fun i => -x i) (fun i => by rw [abs_neg]; exact hx i)
    (by rw [Finset.sum_neg_distrib, hs, neg_zero]) (by simpa only [neg_sq] using hcS) y hy hyε
  have hf : (univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
      y * √(N : ℝ) < hdS (fun i => -x i) w)) =
      univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => hdS x w < -(y * √(N : ℝ))) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [hdS_neg]; constructor <;> intro h' <;> linarith
  rw [hf, sS_neg] at this
  exact this

end P99bcb804

end X43_Fpc

section X44_Qt

/-! Quantile toolkit (from _qt.lean) and Tusnady arithmetic (from _tq.lean), plus a uniform
single-measure Tusnady sandwich `tusnady_one` for the dyadic node (4.12). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_deriv_pos (fun x => by rw [(hasDerivAt_Phi x).deriv]; exact phi_pos x)

/-- Generalized inverse (quantile function) of a law on `ℝ`. -/
noncomputable def qnt (L : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf L x}

lemma qnt_le_iff (L : Measure ℝ) [IsProbabilityMeasure L] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (x : ℝ) : qnt L u ≤ x ↔ u ≤ cdf L x := by
  set A := {x | u ≤ cdf L x} with hA
  have hne : A.Nonempty := ((tendsto_cdf_atTop L).eventually (lt_mem_nhds hu1)).exists.imp
    fun x hx => hx.le
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot L).eventually (gt_mem_nhds hu0))
  have hbdd : BddBelow A := ⟨b, fun a ha => by
    by_contra h
    have := hb a (not_le.mp h).le
    exact absurd ha (not_le.mpr this)⟩
  constructor
  · intro hq
    have hq0 : u ≤ cdf L (qnt L u) := by
      have hyy : ∀ y ∈ Set.Ioi (qnt L u), u ≤ cdf L y := by
        intro y hy
        obtain ⟨a, ha, hay⟩ := exists_lt_of_csInf_lt hne hy
        exact ha.trans ((cdf L).mono hay.le)
      have ht : Tendsto (cdf L) (𝓝[>] (qnt L u)) (𝓝 (cdf L (qnt L u))) :=
        ((cdf L).right_continuous _).mono Set.Ioi_subset_Ici_self
      exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hyy)
    exact hq0.trans ((cdf L).mono hq)
  · intro hx
    exact csInf_le hbdd hx

lemma Phi_pos' (w : ℝ) : 0 < Phi w := cdf_std_pos w

lemma Phi_lt_one (w : ℝ) : Phi w < 1 := cdf_std_lt_one w

/-- A Tusnády sandwich turns into a pointwise bound on the quantile transform. -/
lemma qnt_close (L : Measure ℝ) [IsProbabilityMeasure L] {s E : ℝ} (hs : 0 < s)
    (δ : ℝ → ℝ) (hδ : Continuous δ)
    (H : ∀ y : ℝ, |y| ≤ E → Phi (y / s) ≤ cdf L (y + δ y) ∧ cdf L (y - δ y) ≤ Phi (y / s))
    {w : ℝ} (hw : |w| < E) : |qnt L (Phi (w / s)) - w| ≤ δ w := by
  have hu0 := Phi_pos' (w / s)
  have hu1 := Phi_lt_one (w / s)
  rw [abs_le]
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    set x := qnt L (Phi (w / s)) with hx
    have hxw : x < w - δ w := by linarith
    have hux : Phi (w / s) ≤ cdf L x := (qnt_le_iff L hu0 hu1 x).mp le_rfl
    have hopen : IsOpen {y : ℝ | x < y - δ y ∧ |y| < E} :=
      (isOpen_lt continuous_const (continuous_id.sub hδ)).inter
        (isOpen_lt continuous_abs continuous_const)
    have hev : ∀ᶠ y in 𝓝[<] w, x < y - δ y ∧ |y| < E ∧ y < w := by
      have h1 : ∀ᶠ y in 𝓝[<] w, x < y - δ y ∧ |y| < E :=
        nhdsWithin_le_nhds (hopen.mem_nhds ⟨hxw, hw⟩)
      filter_upwards [h1, self_mem_nhdsWithin] with y hy hy' using ⟨hy.1, hy.2, hy'⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := hev.exists
    have hH := (H y hy2.le).2
    have hlt2 : Phi (y / s) < Phi (w / s) := Phi_strictMono (div_lt_div_of_pos_right hy3 hs)
    have hmono : cdf L x ≤ cdf L (y - δ y) := (cdf L).mono hy1.le
    linarith
  · have := (H w hw.le).1
    have := (qnt_le_iff L hu0 hu1 (w + δ w)).mpr this
    linarith

lemma cdf_eq_one_sub_tail (S : Measure ℝ) [IsProbabilityMeasure S] (x : ℝ) :
    cdf S x = 1 - S.real (Set.Ioi x) := by
  rw [cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  ring

theorem tusnady_one (cR εR cL εL K : ℝ) (hcR : 0 < cR) (hεR : 0 < εR) (hcL : 0 < cL)
    (hεL : 0 < εL) (hK : 0 < K) :
    ∃ c ε : ℝ, ∃ m₀ : ℕ, 0 < c ∧ 0 < ε ∧ 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ (L : Measure ℝ) [IsProbabilityMeasure L],
      (∀ y : ℝ, √(m : ℝ) ≤ y → y ≤ εR * m →
        L.real (Ioi y) ≤ (1 - Phi (y / √(m : ℝ))) * exp (cR * (y ^ 3 / (m : ℝ) ^ 2)) ∧
        (1 - Phi (y / √(m : ℝ))) * exp (-(cR * (y ^ 3 / (m : ℝ) ^ 2))) ≤ L.real (Ioi y)) →
      (∀ y : ℝ, √(m : ℝ) ≤ y → y ≤ εL * m →
        L.real (Iio (-y)) ≤ (1 - Phi (y / √(m : ℝ))) * exp (cL * (y ^ 3 / (m : ℝ) ^ 2)) ∧
        (1 - Phi (y / √(m : ℝ))) * exp (-(cL * (y ^ 3 / (m : ℝ) ^ 2))) ≤ L.real (Iio (-y))) →
      (∀ z : ℝ, |z| ≤ 3 → Phi z - K / √(m : ℝ) ≤ cdf L (√(m : ℝ) * z) ∧
        cdf L (√(m : ℝ) * z) ≤ Phi z + K / √(m : ℝ)) →
      ∀ y : ℝ, |y| ≤ ε * m →
        Phi (y / √(m : ℝ)) ≤ cdf L (y + c * (1 + y ^ 2 / m)) ∧
        cdf L (y - c * (1 + y ^ 2 / m)) ≤ Phi (y / √(m : ℝ)) := by
  have hfact := @EthierKurtz.tusnady_quantile_sandwich
  apply hfact <;> assumption

end P99bcb804

end X44_Qt

section X48_Node

/-! KMT 1976 II, node estimate (4.12): the conditional quantile transform of the half-difference
under a uniform permutation (Lemma 3 = `finpop_right_u`/`finpop_left`, fed into `tusnady_one`). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Law of `f` under the uniform permutation of `Fin N ⊕ Fin N`. -/
noncomputable def pLaw {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) : Measure ℝ :=
  ((Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ≥0∞)⁻¹) • ∑ w, Measure.dirac (f w)

lemma pLaw_apply {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    [DecidablePred (fun w => f w ∈ S)] :
    pLaw f S = ((Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ≥0∞)⁻¹) *
      ((Finset.univ.filter (fun w => f w ∈ S)).card : ℝ≥0∞) := by
  rw [pLaw, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.dirac_apply' _ hS, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

instance pLaw_isProb {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) :
    IsProbabilityMeasure (pLaw f) := by
  constructor
  simp only [pLaw, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  have h0 : (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)

lemma pLaw_real {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    [DecidablePred (fun w => f w ∈ S)] :
    (pLaw f).real S = ((Finset.univ.filter (fun w => f w ∈ S)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) := by
  rw [measureReal_def, pLaw_apply f hS, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]

/-- The half-difference is invariant under a common shift. -/
lemma hdS_shift {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (a : ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    hdS (fun i => x i - a) w = hdS x w := by
  unfold hdS
  exact Finset.sum_congr rfl fun i _ => by ring

lemma Phi_lip {a b : ℝ} (hab : a ≤ b) : Phi b - Phi a ≤ b - a := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  obtain ⟨ξ, -, hξd⟩ := exists_hasDerivAt_eq_slope Phi phi h continuous_Phi'.continuousOn
    (fun x _ => hasDerivAt_Phi x)
  have h1 := phi_le_half ξ
  rw [hξd, div_le_iff₀ (by linarith)] at h1
  linarith

lemma exp_le_two {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) : exp ρ ≤ 1 + 2 * ρ := by
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; simp
  have := Real.exp_bound_div_one_sub_of_interval' h (by linarith)
  have h2 : 1 / (1 - ρ) ≤ 1 + 2 * ρ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- Scale factor turning the half-difference into a variable of variance proxy `m = 2N`. -/
noncomputable def kS {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) : ℝ :=
  √(((2 * N : ℕ) : ℝ)) / (sS x * √(N : ℝ))

lemma filter_scale {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (hN : 1 ≤ N) (ha : 0 < sS x) (y : ℝ) :
    (Finset.univ.filter (fun w => hdS x w * kS x ∈ Ioi y)) =
      Finset.univ.filter (fun w => y * sS x / √(((2 * N : ℕ) : ℝ)) * √(N : ℝ) < hdS x w) ∧
    (Finset.univ.filter (fun w => hdS x w * kS x ∈ Iio (-y))) =
      Finset.univ.filter (fun w => hdS x w < -(y * sS x / √(((2 * N : ℕ) : ℝ)) * √(N : ℝ))) := by
  have hq : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hs : 0 < √(((2 * N : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by push_cast; positivity)
  have hk : 0 < kS x := div_pos hs (mul_pos ha hq)
  have e : y * sS x / √(((2 * N : ℕ) : ℝ)) * √(N : ℝ) = y / kS x := by
    unfold kS; field_simp
  have e2 : -(y * sS x / √(((2 * N : ℕ) : ℝ)) * √(N : ℝ)) = -y / kS x := by
    rw [e, neg_div]
  constructor
  · refine Finset.filter_congr fun w _ => ?_
    rw [Set.mem_Ioi, e, div_lt_iff₀ hk]
  · refine Finset.filter_congr fun w _ => ?_
    rw [Set.mem_Iio, e2, lt_div_iff₀ hk]

end P99bcb804

end X48_Node

section X49_Node2

/-! Node (4.12), step 2: Lemma 3 (Fpc) gives the hypotheses of `tusnady_one` for the
rescaled half-difference law `pLaw (hdS x · kS x)` at `m = 2N`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma kY_le {q s a y : ℝ} (hq : 0 < q) (hs : 0 < s) (hsq : s ≤ 2 * q) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hy : s ≤ y) : ((y * a / s) ^ 3 + 1) / q ≤ 18 * (y ^ 3 / (s ^ 2) ^ 2) := by
  set u := y / s with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hs]; linarith
  have e1 : y * a / s = u * a := by rw [hu]; ring
  have e2 : y ^ 3 / (s ^ 2) ^ 2 = u ^ 3 / s := by rw [hu]; field_simp
  rw [e1, e2]
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
  have ha3 : a ^ 3 ≤ 8 := by nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ a) ha2 3]
  have h1 : (u * a) ^ 3 + 1 ≤ 9 * u ^ 3 := by
    rw [mul_pow]; nlinarith
  rw [div_le_iff₀ hq]
  calc (u * a) ^ 3 + 1 ≤ 9 * u ^ 3 := h1
    _ = 18 * (u ^ 3 / s) * (s / 2) := by field_simp; ring
    _ ≤ 18 * (u ^ 3 / s) * q := by
        apply mul_le_mul_of_nonneg_left (by linarith); positivity

lemma kY_le_small {q t : ℝ} (hq : 0 < q) (ht0 : 0 ≤ t) (ht : t ≤ 6) : (t ^ 3 + 1) / q ≤ 217 / q := by
  apply div_le_div_of_nonneg_right _ hq.le
  nlinarith [pow_le_pow_left₀ ht0 ht 3]

lemma hb_right {P G ρ : ℝ} (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (lo : G * exp (-ρ) ≤ P) (hi : P ≤ G * exp ρ) : 1 - G - 2 * ρ ≤ 1 - P ∧ 1 - P ≤ 1 - G + ρ := by
  have h1 := exp_le_two hρ0 hρ1
  have h2 : 1 - ρ ≤ exp (-ρ) := by have := add_one_le_exp (-ρ); linarith
  constructor <;> nlinarith

lemma hb_left {P G ρ : ℝ} (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (lo : G * exp (-ρ) ≤ P) (hi : P ≤ G * exp ρ) : G - ρ ≤ P ∧ P ≤ G + 2 * ρ := by
  have h1 := exp_le_two hρ0 hρ1
  have h2 : 1 - ρ ≤ exp (-ρ) := by have := add_one_le_exp (-ρ); linarith
  constructor <;> nlinarith

/-- Ratio bounds weaken when the constant grows. -/
lemma ratio_weaken {P G C C' k : ℝ} (hG : 0 ≤ G) (hk : 0 ≤ k) (hC : C ≤ C')
    (lo : G * exp (-(C * k)) ≤ P) (hi : P ≤ G * exp (C * k)) :
    G * exp (-(C' * k)) ≤ P ∧ P ≤ G * exp (C' * k) := by
  have h1 : C * k ≤ C' * k := mul_le_mul_of_nonneg_right hC hk
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hG) lo
  · exact le_trans hi (mul_le_mul_of_nonneg_left (exp_le_exp.mpr h1) hG)

lemma sq_facts {N : ℕ} (hN : 1 ≤ N) :
    0 < √(N : ℝ) ∧ 0 < √(((2 * N : ℕ) : ℝ)) ∧ √(((2 * N : ℕ) : ℝ)) ^ 2 = ((2 * N : ℕ) : ℝ) ∧
    √(((2 * N : ℕ) : ℝ)) ≤ 2 * √(N : ℝ) ∧ √(N : ℝ) ≤ √(((2 * N : ℕ) : ℝ)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq := Real.sqrt_pos.mpr (show (0 : ℝ) < N by linarith)
  have hs := Real.sqrt_pos.mpr (show (0 : ℝ) < ((2 * N : ℕ) : ℝ) by push_cast; linarith)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) by positivity)
  have hq2 := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  push_cast at hs hs2 ⊢
  refine ⟨hq, hs, hs2, ?_, Real.sqrt_le_sqrt (by linarith)⟩
  refine (pow_le_pow_iff_left₀ hs.le (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, hs2, hq2]; linarith

/-- Right-tail hypothesis of `tusnady_one` from Lemma 3 (right tail) at fixed `N`, `x`. -/
lemma HR_of {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (hN : 1 ≤ N) (ha1 : 1 ≤ sS x) (ha2 : sS x ≤ 2)
    {εF C : ℝ} (hC : 0 < C)
    (HF : ∀ y : ℝ, 0 ≤ y → y ≤ εF * √(N : ℝ) →
      (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
      ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
        (1 - Phi (y / sS x)) * exp (C * kY y N))
    (y : ℝ) (hy1 : √(((2 * N : ℕ) : ℝ)) ≤ y) (hy2 : y ≤ εF / 4 * ((2 * N : ℕ) : ℝ)) :
    (pLaw (fun w => hdS x w * kS x)).real (Ioi y) ≤
        (1 - Phi (y / √(((2 * N : ℕ) : ℝ)))) * exp ((18 * C) * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2)) ∧
      (1 - Phi (y / √(((2 * N : ℕ) : ℝ)))) * exp (-((18 * C) * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2))) ≤
        (pLaw (fun w => hdS x w * kS x)).real (Ioi y) := by
  obtain ⟨hq, hs, hs2, hsq, hqs⟩ := sq_facts hN
  have ha0 : 0 < sS x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hs hy1
  have hεF : 0 ≤ εF := by
    by_contra h0
    have h := lt_of_not_ge h0
    have : εF / 4 * ((2 * N : ℕ) : ℝ) < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  set t := y * sS x / √(((2 * N : ℕ) : ℝ)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htr : t ≤ εF * √(N : ℝ) := by
    have h1 : t ≤ 2 * y / √(((2 * N : ℕ) : ℝ)) := by
      rw [ht]; exact div_le_div_of_nonneg_right (by nlinarith) hs.le
    have h2 : 2 * y / √(((2 * N : ℕ) : ℝ)) ≤ εF / 2 * √(((2 * N : ℕ) : ℝ)) := by
      rw [div_le_iff₀ hs]; nlinarith
    nlinarith
  obtain ⟨lo, hi⟩ := HF t ht0 htr
  rw [pLaw_real _ measurableSet_Ioi]
  beta_reduce
  rw [(filter_scale x hN ha0 y).1]
  have e : t / sS x = y / √(((2 * N : ℕ) : ℝ)) := by rw [ht]; field_simp
  rw [e] at lo hi
  have hk : kY t N ≤ 18 * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2) := by
    have := kY_le hq hs hsq ha1 ha2 hy1
    rw [hs2] at this; unfold kY; exact this
  have hG : 0 ≤ 1 - Phi (y / √(((2 * N : ℕ) : ℝ))) := (one_sub_Phi_pos _).le
  have hk' : C * kY t N ≤ 18 * C * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2) := by nlinarith
  constructor
  · exact hi.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hk') hG)
  · exact le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hG) lo

/-- Left-tail hypothesis of `tusnady_one` from Lemma 3 (left tail) at fixed `N`, `x`. -/
lemma HL_of {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (hN : 1 ≤ N) (ha1 : 1 ≤ sS x) (ha2 : sS x ≤ 2)
    {εF C : ℝ} (hC : 0 < C)
    (HF : ∀ y : ℝ, 0 ≤ y → y ≤ εF * √(N : ℝ) →
      (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
      ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
        (1 - Phi (y / sS x)) * exp (C * kY y N))
    (y : ℝ) (hy1 : √(((2 * N : ℕ) : ℝ)) ≤ y) (hy2 : y ≤ εF / 4 * ((2 * N : ℕ) : ℝ)) :
    (pLaw (fun w => hdS x w * kS x)).real (Iio (-y)) ≤
        (1 - Phi (y / √(((2 * N : ℕ) : ℝ)))) * exp ((18 * C) * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2)) ∧
      (1 - Phi (y / √(((2 * N : ℕ) : ℝ)))) * exp (-((18 * C) * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2))) ≤
        (pLaw (fun w => hdS x w * kS x)).real (Iio (-y)) := by
  obtain ⟨hq, hs, hs2, hsq, hqs⟩ := sq_facts hN
  have ha0 : 0 < sS x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hs hy1
  have hεF : 0 ≤ εF := by
    by_contra h0
    have h := lt_of_not_ge h0
    have : εF / 4 * ((2 * N : ℕ) : ℝ) < 0 := mul_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  set t := y * sS x / √(((2 * N : ℕ) : ℝ)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htr : t ≤ εF * √(N : ℝ) := by
    have h1 : t ≤ 2 * y / √(((2 * N : ℕ) : ℝ)) := by
      rw [ht]; exact div_le_div_of_nonneg_right (by nlinarith) hs.le
    have h2 : 2 * y / √(((2 * N : ℕ) : ℝ)) ≤ εF / 2 * √(((2 * N : ℕ) : ℝ)) := by
      rw [div_le_iff₀ hs]; nlinarith
    nlinarith
  obtain ⟨lo, hi⟩ := HF t ht0 htr
  rw [pLaw_real _ measurableSet_Iio]
  beta_reduce
  rw [(filter_scale x hN ha0 y).2]
  have e : t / sS x = y / √(((2 * N : ℕ) : ℝ)) := by rw [ht]; field_simp
  rw [e] at lo hi
  have hk : kY t N ≤ 18 * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2) := by
    have := kY_le hq hs hsq ha1 ha2 hy1
    rw [hs2] at this; unfold kY; exact this
  have hG : 0 ≤ 1 - Phi (y / √(((2 * N : ℕ) : ℝ))) := (one_sub_Phi_pos _).le
  have hk' : C * kY t N ≤ 18 * C * (y ^ 3 / ((2 * N : ℕ) : ℝ) ^ 2) := by nlinarith
  constructor
  · exact hi.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hk') hG)
  · exact le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hG) lo

lemma rho_small {N : ℕ} (hN : 1 ≤ N) {C t : ℝ} (hC : 0 < C) (hqC : 434 * C ≤ √(N : ℝ))
    (ht0 : 0 ≤ t) (ht6 : t ≤ 6) :
    0 ≤ C * kY t N ∧ C * kY t N ≤ 1 / 2 ∧ 2 * (C * kY t N) ≤ 868 * C / √(((2 * N : ℕ) : ℝ)) := by
  obtain ⟨hq, hs, hs2, hsq, hqs⟩ := sq_facts hN
  have h1 := kY_le_small hq ht0 ht6
  unfold kY
  have hk0 : 0 ≤ (t ^ 3 + 1) / √(N : ℝ) := by positivity
  have h2 : C * ((t ^ 3 + 1) / √(N : ℝ)) ≤ C * (217 / √(N : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hC.le
  refine ⟨by positivity, ?_, ?_⟩
  · refine h2.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hq]; linarith
  · have h3 : 2 * (C * (217 / √(N : ℝ))) ≤ 868 * C / √(((2 * N : ℕ) : ℝ)) := by
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hq hs]; nlinarith
    linarith

end P99bcb804

end X49_Node2

section X50_Node3

/-! Node (4.12), step 3: the Berry–Esseen-type hypothesis of `tusnady_one` on `|z| ≤ 3`
from Lemma 3 at small arguments. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma one_sub_Phi_neg (z : ℝ) : 1 - Phi (-z) = Phi z := by
  have : Phi (-z) = 1 - Phi z := by unfold Phi; exact cdf_std_neg z
  linarith

lemma HB_of {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (hN : 1 ≤ N) (ha1 : 1 ≤ sS x) (ha2 : sS x ≤ 2)
    {εF C : ℝ} (hC : 0 < C)
    (HF : ∀ y : ℝ, 0 ≤ y → y ≤ εF * √(N : ℝ) →
      (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
      ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          y * √(N : ℝ) < hdS x w)).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
        (1 - Phi (y / sS x)) * exp (C * kY y N))
    (HFL : ∀ y : ℝ, 0 ≤ y → y ≤ εF * √(N : ℝ) →
      (1 - Phi (y / sS x)) * exp (-(C * kY y N)) ≤
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ∧
      ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
          hdS x w < -(y * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) ≤
        (1 - Phi (y / sS x)) * exp (C * kY y N))
    (hq6 : 6 ≤ εF * √(N : ℝ)) (hqC : 434 * C ≤ √(N : ℝ)) (z : ℝ) (hz : |z| ≤ 3) :
    Phi z - (1 + 868 * C) / √(((2 * N : ℕ) : ℝ)) ≤
        cdf (pLaw (fun w => hdS x w * kS x)) (√(((2 * N : ℕ) : ℝ)) * z) ∧
      cdf (pLaw (fun w => hdS x w * kS x)) (√(((2 * N : ℕ) : ℝ)) * z) ≤
        Phi z + (1 + 868 * C) / √(((2 * N : ℕ) : ℝ)) := by
  obtain ⟨hq, hs, hs2, hsq, hqs⟩ := sq_facts hN
  have ha0 : 0 < sS x := by linarith
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  set s := √(((2 * N : ℕ) : ℝ)) with hsdef
  set L := pLaw (fun w => hdS x w * kS x) with hL
  have hKs : 868 * C / s ≤ (1 + 868 * C) / s := div_le_div_of_nonneg_right (by linarith) hs.le
  have hKs1 : 1 / s + 868 * C / s = (1 + 868 * C) / s := (add_div _ _ _).symm
  have h1s : 0 < 1 / s := one_div_pos.mpr hs
  -- the left-tail probability at `-y`, `y = -(s * u)` for `u ≤ 0`
  have Ltail : ∀ u : ℝ, -3 ≤ u → u ≤ 0 →
      Phi u - 868 * C / s ≤ L.real (Iio (s * u)) ∧ L.real (Iio (s * u)) ≤ Phi u + 868 * C / s := by
    intro u hu1 hu2
    set t := -(s * u) * sS x / s with ht
    have ht' : t = -u * sS x := by rw [ht]; field_simp
    have ht0 : 0 ≤ t := by rw [ht']; nlinarith
    have ht6 : t ≤ 6 := by rw [ht']; nlinarith
    obtain ⟨lo, hi⟩ := HFL t ht0 (by linarith)
    have e : t / sS x = -u := by rw [ht']; field_simp
    rw [e, one_sub_Phi_neg] at lo hi
    have hP : L.real (Iio (s * u)) = ((Finset.univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
        hdS x w < -(t * √(N : ℝ)))).card : ℝ) / Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) := by
      have e2 : s * u = -(-(s * u)) := by ring
      rw [e2, hL, pLaw_real _ measurableSet_Iio]
      beta_reduce
      rw [(filter_scale x hN ha0 (-(s * u))).2]
    rw [hP]
    obtain ⟨r0, r1, r2⟩ := rho_small hN hC hqC ht0 ht6
    rw [← hsdef] at r2
    obtain ⟨c1, c2⟩ := hb_left (Phi_pos' u).le (Phi_lt_one u).le r0 r1 lo hi
    constructor <;> linarith
  rcases le_or_gt 0 z with hz0 | hz0
  · set t := s * z * sS x / s with ht
    have ht' : t = z * sS x := by rw [ht]; field_simp
    have ht0 : 0 ≤ t := by rw [ht']; positivity
    have ht6 : t ≤ 6 := by rw [ht']; nlinarith
    obtain ⟨lo, hi⟩ := HF t ht0 (by linarith)
    have e : t / sS x = z := by rw [ht']; field_simp
    rw [e] at lo hi
    rw [cdf_eq_one_sub_tail, hL, pLaw_real _ measurableSet_Ioi]
    beta_reduce
    rw [(filter_scale x hN ha0 (s * z)).1]
    obtain ⟨r0, r1, r2⟩ := rho_small hN hC hqC ht0 ht6
    rw [← hsdef] at r2
    obtain ⟨c1, c2⟩ := hb_right (one_sub_Phi_pos z).le (by linarith [Phi_pos' z]) r0 r1 lo hi
    constructor <;> linarith
  · constructor
    · have h1 := (Ltail z hz1 hz0.le).1
      have h2 : L.real (Iio (s * z)) ≤ cdf L (s * z) := by
        rw [cdf_eq_real]; exact measureReal_mono Iio_subset_Iic_self
      linarith
    · set z2 := min (z + 1 / s) 0 with hz2d
      have hzz : z < z2 := lt_min (by linarith) hz0
      have hz20 : z2 ≤ 0 := min_le_right _ _
      have hz21 : z2 - z ≤ 1 / s := by have := min_le_left (z + 1 / s) 0; linarith
      have h1 := (Ltail z2 (by linarith) hz20).2
      have h2 : cdf L (s * z) ≤ L.real (Iio (s * z2)) := by
        rw [cdf_eq_real]
        exact measureReal_mono (Iic_subset_Iio.mpr (by nlinarith))
      have h3 := Phi_lip hzz.le
      linarith

end P99bcb804

end X50_Node3

section X51_Node4

/-! Node (4.12), step 4: the uniform quantile bound for the rescaled half-difference law. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma sS_bounds {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (hN : 1 ≤ N) (hlo : (N : ℝ) ≤ ∑ i, x i ^ 2)
    (hhi : ∑ i, x i ^ 2 ≤ 4 * N) : 1 ≤ sS x ∧ sS x ≤ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sS
  constructor
  · rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hN']; linarith)
  · rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hN']; linarith)

theorem node_qnt (K : ℝ) (hK : 0 < K) :
    ∃ c ε : ℝ, ∃ N1 : ℕ, 0 < c ∧ 0 < ε ∧ 1 ≤ N1 ∧ ∀ N : ℕ, N1 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → (N : ℝ) ≤ ∑ i, x i ^ 2 →
        ∑ i, x i ^ 2 ≤ 4 * N → ∀ w : ℝ, |w| < ε * ((2 * N : ℕ) : ℝ) →
          |qnt (pLaw (fun p => hdS x p * kS x)) (Phi (w / √(((2 * N : ℕ) : ℝ)))) - w| ≤
            c * (1 + w ^ 2 / ((2 * N : ℕ) : ℝ)) := by
  obtain ⟨εF, CF, N0F, hεF, hCF, HFR⟩ := finpop_right_u K 1 hK one_pos
  obtain ⟨εL, CL, N0L, hεL, hCL, HFL⟩ := finpop_left K 1 hK one_pos
  set C := CF + CL with hCdef
  have hC : 0 < C := by positivity
  set ε0 := min εF εL with hε0
  have hε0p : 0 < ε0 := lt_min hεF hεL
  obtain ⟨c, εT, m₀, hc, hεT, hm₀, TUS⟩ := tusnady_one (18 * C) (ε0 / 4) (18 * C) (ε0 / 4)
    (1 + 868 * C) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  set Q := 6 / ε0 + 434 * C with hQ
  have hQ0 : 0 < Q := by positivity
  refine ⟨c, εT, ⌈max N0F N0L⌉₊ + ⌈Q ^ 2⌉₊ + m₀ + 1, hc, hεT, by omega, ?_⟩
  intro N hN x hx hsum hlo hhi w hw
  have hN1 : 1 ≤ N := by omega
  have hm : m₀ ≤ 2 * N := by omega
  have hNr : (⌈max N0F N0L⌉₊ : ℝ) + ⌈Q ^ 2⌉₊ ≤ N := by exact_mod_cast (show _ ≤ N by omega)
  have hNF : max N0F N0L ≤ N := by
    have := Nat.le_ceil (max N0F N0L); have := Nat.cast_nonneg (α := ℝ) ⌈Q ^ 2⌉₊; linarith
  have hNQ : Q ^ 2 ≤ N := by
    have := Nat.le_ceil (Q ^ 2); have := Nat.cast_nonneg (α := ℝ) ⌈max N0F N0L⌉₊; linarith
  have hqQ : Q ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le hNQ
  have hq6 : 6 ≤ ε0 * √(N : ℝ) := by
    have h1 : 6 / ε0 ≤ √(N : ℝ) := by linarith
    rw [div_le_iff₀ hε0p] at h1; linarith
  have hqC : 434 * C ≤ √(N : ℝ) := by linarith [div_pos (show (0:ℝ) < 6 by norm_num) hε0p]
  obtain ⟨ha1, ha2⟩ := sS_bounds x hN1 hlo hhi
  have hlo1 : 1 * (N : ℝ) ≤ ∑ i, x i ^ 2 := by linarith
  have hG : ∀ y : ℝ, 0 ≤ 1 - Phi (y / sS x) := fun y => (one_sub_Phi_pos _).le
  have hkY : ∀ y : ℝ, 0 ≤ y → 0 ≤ kY y N := fun y hy => by unfold kY; positivity
  have HR' := fun y (hy : 0 ≤ y) (hy2 : y ≤ ε0 * √(N : ℝ)) =>
    let h := HFR N hN1 (le_trans (le_max_left _ _) hNF) x hx hsum hlo1 y hy
      (hy2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)))
    ratio_weaken (hG y) (hkY y hy) (show CF ≤ C by linarith) h.1 h.2
  have HL' := fun y (hy : 0 ≤ y) (hy2 : y ≤ ε0 * √(N : ℝ)) =>
    let h := HFL N hN1 (le_trans (le_max_right _ _) hNF) x hx hsum hlo1 y hy
      (hy2.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
    ratio_weaken (hG y) (hkY y hy) (show CL ≤ C by linarith) h.1 h.2
  have S := TUS (2 * N) hm (pLaw (fun p => hdS x p * kS x))
    (fun y h1 h2 => HR_of x hN1 ha1 ha2 hC HR' y h1 h2)
    (fun y h1 h2 => HL_of x hN1 ha1 ha2 hC HL' y h1 h2)
    (fun z hz => HB_of x hN1 ha1 ha2 hC HR' HL' hq6 hqC z hz)
  obtain ⟨-, hs, -, -, -⟩ := sq_facts hN1
  exact qnt_close (pLaw (fun p => hdS x p * kS x)) hs (fun y => c * (1 + y ^ 2 / ((2 * N : ℕ) : ℝ)))
    (by fun_prop) (fun y hy => S y hy) hw

end P99bcb804

end X51_Node4

section X52_Node5

/-! Node (4.12), step 5: KMT II (4.12) for an uncentred bounded block: quantile scaling,
centring and the variance correction. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma qnt_scale {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) {k : ℝ} (hk : 0 < k) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    qnt (pLaw (fun p => f p * k)) u = k * qnt (pLaw f) u := by
  classical
  have key : ∀ z, qnt (pLaw (fun p => f p * k)) u ≤ z ↔ k * qnt (pLaw f) u ≤ z := by
    intro z
    rw [qnt_le_iff _ hu0 hu1, cdf_eq_real, pLaw_real _ measurableSet_Iic]
    have h2 : k * qnt (pLaw f) u ≤ z ↔ qnt (pLaw f) u ≤ z / k := by
      rw [le_div_iff₀ hk, mul_comm]
    rw [h2, qnt_le_iff _ hu0 hu1, cdf_eq_real, pLaw_real _ measurableSet_Iic]
    have hS : (Finset.univ.filter (fun w => f w * k ∈ Iic z)) =
        Finset.univ.filter (fun w => f w ∈ Iic (z / k)) :=
      Finset.filter_congr (fun w _ => by simp only [Set.mem_Iic, le_div_iff₀ hk])
    rw [hS]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

lemma sqrt_sub_one_le {t : ℝ} (ht : 0 ≤ t) : |√t - 1| ≤ |t - 1| := by
  have hs := Real.sq_sqrt ht
  have h0 := Real.sqrt_nonneg t
  have e : t - 1 = (√t - 1) * (√t + 1) := by nlinarith
  rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < √t + 1)]
  nlinarith [abs_nonneg (√t - 1)]

lemma am_gm_abs (W v : ℝ) : |W| * |v| ≤ (W ^ 2 + v ^ 2) / 2 := by
  nlinarith [sq_nonneg (|W| - |v|), sq_abs W, sq_abs v]

lemma fin_arith {c a b d X : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (h : X ≤ 2 * (c * (1 + a)) + (b + a + d)) : X ≤ (2 * c + 1) * (1 + a + d + b) := by
  nlinarith [mul_nonneg hc.le hd, mul_nonneg hc.le hb]

/-- KMT 1976 II, (4.12), in rescaled form: for a bounded block `y` of size `m = 2N` with
total `U` and `W = Σ (y² - 1)`, the conditional quantile transform of the half-difference law
(under a uniform permutation) at the Gaussian level `v` stays within
`C (1 + (v² + U² + W²)/m)` of `v`. -/
theorem node_bound (K : ℝ) (hK : 0 < K) :
    ∃ C ε : ℝ, ∃ N1 : ℕ, 0 < C ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ 1 ≤ N1 ∧ ∀ N : ℕ, N1 ≤ N →
      ∀ y : Fin N ⊕ Fin N → ℝ, (∀ i, |y i| ≤ K) →
        |∑ i, y i| ≤ ε * ((2 * N : ℕ) : ℝ) → |∑ i, (y i ^ 2 - 1)| ≤ ε * ((2 * N : ℕ) : ℝ) →
        ∀ v : ℝ, |v| < ε * ((2 * N : ℕ) : ℝ) →
          |qnt (pLaw (hdS y)) (Phi (v / √(((2 * N : ℕ) : ℝ)))) - v| ≤
            C * (1 + v ^ 2 / ((2 * N : ℕ) : ℝ) + (∑ i, y i) ^ 2 / ((2 * N : ℕ) : ℝ) +
              (∑ i, (y i ^ 2 - 1)) ^ 2 / ((2 * N : ℕ) : ℝ)) := by
  obtain ⟨c, ε1, N1, hc, hε1, hN1, NQ⟩ := node_qnt (K + 1) (by linarith)
  refine ⟨2 * c + 1, min ε1 (1 / 4), N1, by positivity, lt_min hε1 (by norm_num),
    min_le_right _ _, hN1, ?_⟩
  intro N hN y hy hU hW v hv
  have hN1' : 1 ≤ N := le_trans hN1 hN
  set m : ℝ := ((2 * N : ℕ) : ℝ) with hmdef
  have hmN : m = 2 * N := by rw [hmdef]; push_cast; ring
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hm : 0 < m := by rw [hmN]; linarith
  set U := ∑ i, y i with hUdef
  set W := ∑ i, (y i ^ 2 - 1) with hWdef
  have hεq : min ε1 (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hεm : min ε1 (1 / 4) * m ≤ 1 / 4 * m := mul_le_mul_of_nonneg_right hεq hm.le
  have hU4 : |U| ≤ m / 4 := hU.trans (by linarith)
  have hW4 : |W| ≤ m / 4 := hW.trans (by linarith)
  have hv1 : |v| ≤ m := hv.le.trans (by linarith)
  set a := U / m with hadef
  have ha : |a| ≤ 1 / 4 := by
    rw [hadef, abs_div, abs_of_pos hm, div_le_iff₀ hm]; linarith
  set x : Fin N ⊕ Fin N → ℝ := fun i => y i - a with hxdef
  have hcard : ∑ _i : Fin N ⊕ Fin N, (1 : ℝ) = m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hmN]; push_cast; ring
  have hcst : ∀ b : ℝ, ∑ _i : Fin N ⊕ Fin N, b = m * b := by
    intro b
    rw [← hcard, Finset.sum_mul, one_mul]
  have hx : ∀ i, |x i| ≤ K + 1 := by
    intro i
    have := hy i
    calc |x i| = |y i - a| := rfl
      _ ≤ |y i| + |a| := abs_sub _ _
      _ ≤ K + 1 := by linarith
  have hsum : ∑ i, x i = 0 := by
    simp only [hxdef, Finset.sum_sub_distrib, hcst, ← hUdef, hadef]
    field_simp; ring
  have hy2 : ∑ i, y i ^ 2 = W + m := by
    rw [hWdef, Finset.sum_sub_distrib, hcard]; ring
  have hS : ∑ i, x i ^ 2 = m + W - U ^ 2 / m := by
    have e : ∀ i, x i ^ 2 = y i ^ 2 - 2 * a * y i + a ^ 2 := fun i => by
      simp only [hxdef]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, hcst, ← Finset.mul_sum,
      ← hUdef, hy2, hadef]
    field_simp; ring
  have hUm : U ^ 2 / m ≤ m / 16 := by
    rw [div_le_iff₀ hm]
    have : U ^ 2 ≤ (m / 4) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hU4 2
    linarith [this, show (m / 4) ^ 2 = m / 16 * m by ring]
  have hUm0 : 0 ≤ U ^ 2 / m := by positivity
  have hW' := abs_le.mp hW4
  have hlo : (N : ℝ) ≤ ∑ i, x i ^ 2 := by rw [hS]; linarith [hW'.1, hW'.2]
  have hhi : ∑ i, x i ^ 2 ≤ 4 * N := by rw [hS]; linarith [hW'.1, hW'.2]
  have hS0 : 0 < ∑ i, x i ^ 2 := by linarith
  have NQ' := NQ N hN x hx hsum hlo hhi v (hv.trans_le (by
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hm.le))
  -- the scale factor
  set S := ∑ i, x i ^ 2 with hSdef
  have hsq : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  have hsS : 0 < √S := Real.sqrt_pos.mpr hS0
  have hsSN : sS x * √(N : ℝ) = √S := by
    unfold sS
    rw [← Real.sqrt_mul (div_nonneg hS0.le (by linarith)), div_mul_cancel₀ _ (by linarith)]
  have hk : kS x = √m / √S := by
    unfold kS; rw [hsSN]
  have hkpos : 0 < kS x := by rw [hk]; positivity
  have hshift : hdS x = hdS y := funext fun p => hdS_shift y a p
  have hu0 := Phi_pos' (v / √m)
  have hu1 := Phi_lt_one (v / √m)
  rw [qnt_scale (hdS x) hkpos hu0 hu1, hshift] at NQ'
  set Q := qnt (pLaw (hdS y)) (Phi (v / √m)) with hQ
  set r := √(S / m) with hrdef
  have hr : r = √S / √m := Real.sqrt_div' S hm.le
  have hrk : r * kS x = 1 := by
    rw [hr, hk]; field_simp
  have hr2 : r ≤ 2 := by
    rw [hrdef, show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hm]; nlinarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hdec : Q - v = r * (kS x * Q - v) + (r - 1) * v := by
    have : Q = r * (kS x * Q) := by rw [← mul_assoc, hrk, one_mul]
    linear_combination this
  have hr1 : |r - 1| ≤ |S / m - 1| := sqrt_sub_one_le (div_nonneg hS0.le hm.le)
  have hS' : S = m + W - U ^ 2 / m := hS
  have e1 : S / m - 1 = (W - U ^ 2 / m) / m := by
    rw [hS']; field_simp; ring
  have hUv : U ^ 2 / m * |v| ≤ U ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left hv1 (sq_nonneg U)
  have hWv : |W| * |v| ≤ (W ^ 2 + v ^ 2) / 2 := am_gm_abs W v
  have h3 : |W - U ^ 2 / m| * |v| ≤ (W ^ 2 + v ^ 2) / 2 + U ^ 2 := by
    calc |W - U ^ 2 / m| * |v| ≤ (|W| + U ^ 2 / m) * |v| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg v)
          calc |W - U ^ 2 / m| ≤ |W| + |U ^ 2 / m| := abs_sub _ _
            _ = |W| + U ^ 2 / m := by rw [abs_of_nonneg hUm0]
      _ = |W| * |v| + U ^ 2 / m * |v| := by ring
      _ ≤ (W ^ 2 + v ^ 2) / 2 + U ^ 2 := by linarith
  have h4 : |r - 1| * |v| ≤ (W ^ 2 + v ^ 2 + U ^ 2) / m := by
    calc |r - 1| * |v| ≤ |S / m - 1| * |v| := mul_le_mul_of_nonneg_right hr1 (abs_nonneg v)
      _ = |W - U ^ 2 / m| * |v| / m := by
          rw [e1, abs_div, abs_of_pos hm]; ring
      _ ≤ ((W ^ 2 + v ^ 2) / 2 + U ^ 2) / m := by
          exact div_le_div_of_nonneg_right h3 hm.le
      _ ≤ (W ^ 2 + v ^ 2 + U ^ 2) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          linarith [sq_nonneg W, sq_nonneg v]
  have h5 : |Q - v| ≤ 2 * (c * (1 + v ^ 2 / m)) + (W ^ 2 + v ^ 2 + U ^ 2) / m := by
    rw [hdec]
    calc |r * (kS x * Q - v) + (r - 1) * v| ≤ |r * (kS x * Q - v)| + |(r - 1) * v| :=
          abs_add_le _ _
      _ = r * |kS x * Q - v| + |r - 1| * |v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      _ ≤ 2 * (c * (1 + v ^ 2 / m)) + (W ^ 2 + v ^ 2 + U ^ 2) / m := by
          have := mul_le_mul hr2 NQ' (abs_nonneg _) (by norm_num)
          linarith
  have hv2 : 0 ≤ v ^ 2 / m := by positivity
  have hW2 : 0 ≤ W ^ 2 / m := by positivity
  have e2 : (W ^ 2 + v ^ 2 + U ^ 2) / m = W ^ 2 / m + v ^ 2 / m + U ^ 2 / m := by ring
  rw [e2] at h5
  exact fin_arith hc hv2 hW2 hUm0 h5

end P99bcb804

end X52_Node5

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ (K : ℝ),
      (0 : ℝ) < K →
        ∃ (C : ℝ) (ε : ℝ) (N1 : ℕ),
          (0 : ℝ) < C ∧
            (0 : ℝ) < ε ∧
              ε ≤ (1 / 4 : ℝ) ∧
                (1 : ℕ) ≤ N1 ∧
                  ∀ (N : ℕ),
                    N1 ≤ N →
                      ∀ (y : Fin N ⊕ Fin N → ℝ),
                        (∀ (i : Fin N ⊕ Fin N), |y i| ≤ K) →
                          |∑ i : Fin N ⊕ Fin N, y i| ≤ ε * ↑((2 : ℕ) * N) →
                            |∑ i : Fin N ⊕ Fin N, (y i ^ (2 : ℕ) - (1 : ℝ))| ≤ ε * ↑((2 : ℕ) * N) →
                              ∀ (v : ℝ),
                                |v| < ε * ↑((2 : ℕ) * N) →
                                  |InfSet.sInf
                                          {x : ℝ |
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (v / √↑((2 : ℕ) * N)) ≤
                                              (ProbabilityTheory.cdf
                                                    (((Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ENNReal))⁻¹ •
                                                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N),
                                                        MeasureTheory.Measure.dirac
                                                          (∑ i : Fin N, (y (w (Sum.inl i)) - y (w (Sum.inr i))))))
                                                x} -
                                        v| ≤
                                    C *
                                      ((1 : ℝ) + v ^ (2 : ℕ) / ↑((2 : ℕ) * N) +
                                          (∑ i : Fin N ⊕ Fin N, y i) ^ (2 : ℕ) / ↑((2 : ℕ) * N) +
                                        (∑ i : Fin N ⊕ Fin N, (y i ^ (2 : ℕ) - (1 : ℝ))) ^ (2 : ℕ) / ↑((2 : ℕ) * N)) := by
  first
  | exact P99bcb804.node_bound
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.node_bound <;> assumption)
