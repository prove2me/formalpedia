-- Prove2me | solution 1 for EthierKurtz.kmt_bounded_dyadic_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:54:57.176988+00:00
-- url     : https://prove2.me/submissions/e2edae01-6311-411a-b332-c6428cbf9fbe

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_permutation_conditional_quantile_bound
import Theorems.Thm_EthierKurtz_kmt_iid_sum_quantile_coupling_bound

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

/-- Half-sample difference on `Fin N ⊕ Fin N`. -/
noncomputable def hdS {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (π : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  ∑ i, (x (π (Sum.inl i)) - x (π (Sum.inr i)))

end P99bcb804

end X31_Sym

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

/-- `{w | Φ w ≤ t}` has standard Gaussian mass `t` for `t ∈ [0,1]`. -/
lemma gauss_Phi_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (gaussianReal 0 1).real {w | Phi w ≤ t} = t := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1
    have : {w | Phi w ≤ 1} = Set.univ := Set.eq_univ_of_forall fun w => (Phi_lt_one w).le
    rw [this, probReal_univ]
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0
    have : {w | Phi w ≤ 0} = ∅ := Set.eq_empty_of_forall_notMem fun w hw =>
      absurd (Phi_pos' w) (not_lt.mpr hw)
    rw [this, measureReal_empty]
  -- intermediate value
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp
    ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually (gt_mem_nhds h0))
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually (lt_mem_nhds h1))
  have hab : min a b ≤ max a b := min_le_max
  have hmem : t ∈ Set.Icc (Phi (min a b)) (Phi (max a b)) :=
    ⟨(ha _ (min_le_left _ _)).le, (hb _ (le_max_right _ _)).le⟩
  obtain ⟨w0, -, hw0⟩ := intermediate_value_Icc hab continuous_Phi'.continuousOn hmem
  have : {w | Phi w ≤ t} = Set.Iic w0 := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_Iic]; rw [← hw0]; exact Phi_strictMono.le_iff_le
  rw [this, ← cdf_eq_real]; exact hw0

lemma measurable_qnt_Phi (L : Measure ℝ) [IsProbabilityMeasure L] {s : ℝ} :
    Measurable fun w => qnt L (Phi (w / s)) := by
  refine measurable_of_Iic fun x => ?_
  have : (fun w => qnt L (Phi (w / s))) ⁻¹' Set.Iic x = {w | Phi (w / s) ≤ cdf L x} := by
    ext w; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact qnt_le_iff L (Phi_pos' _) (Phi_lt_one _) x
  rw [this]
  exact measurableSet_le ((continuous_Phi'.comp (continuous_id.div_const s)).measurable)
    measurable_const

/-- Quantile transform of a standard Gaussian has law `L`. -/
lemma map_qnt_Phi (L : Measure ℝ) [IsProbabilityMeasure L] :
    (gaussianReal 0 1).map (fun w => qnt L (Phi (w / 1))) = L := by
  have hm := measurable_qnt_Phi L (s := 1)
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun w => qnt L (Phi (w / 1)))) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hm measurableSet_Iic]
  have : (fun w => qnt L (Phi (w / 1))) ⁻¹' Set.Iic x = {w | Phi w ≤ cdf L x} := by
    ext w; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, div_one]
    exact qnt_le_iff L (Phi_pos' _) (Phi_lt_one _) x
  rw [this, ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
    gauss_Phi_le _ (cdf_nonneg _ _) (cdf_le_one _ _), cdf_eq_real, ofReal_measureReal]

lemma map_qnt_Phi' (L : Measure ℝ) [IsProbabilityMeasure L] :
    (gaussianReal 0 1).map (fun w => qnt L (Phi w)) = L := by
  simpa using map_qnt_Phi L

lemma measurable_qnt_kernel (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    Measurable fun p : ℝ × ℝ => qnt (κ p.1) (Phi p.2) := by
  refine measurable_of_Iic fun x => ?_
  have : (fun p : ℝ × ℝ => qnt (κ p.1) (Phi p.2)) ⁻¹' Set.Iic x
      = {p : ℝ × ℝ | Phi p.2 ≤ cdf (κ p.1) x} := by
    ext p; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact qnt_le_iff _ (Phi_pos' _) (Phi_lt_one _) x
  rw [this]
  have hc : Measurable fun p : ℝ × ℝ => cdf (κ p.1) x := by
    have : (fun p : ℝ × ℝ => cdf (κ p.1) x) = fun p => ((κ p.1) (Set.Iic x)).toReal := by
      funext p; rw [cdf_eq_real, measureReal_def]
    rw [this]
    exact ((κ.measurable_coe measurableSet_Iic).comp measurable_fst).ennreal_toReal
  exact measurableSet_le ((continuous_Phi'.comp continuous_snd).measurable) hc

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

end P99bcb804

end X48_Node

section X52_Node5

/-! Node (4.12), step 5: KMT II (4.12) for an uncentred bounded block: quantile scaling,
centring and the variance correction. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

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
  have hfact := @EthierKurtz.kmt_permutation_conditional_quantile_bound
  apply hfact <;> assumption

end P99bcb804

end X52_Node5

section X53_Pick

/-! KMT 1976 II, (4.14): the conditional quantile transform of a uniformly chosen element of a
finite set, realised by a rank-based choice driven by a single Gaussian. The chosen element is
exactly uniform and its `f`-value is the quantile transform of the law of `f`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Law of `f` under the uniform distribution on a finite type. -/
noncomputable def uLaw {α : Type} [Fintype α] (f : α → ℝ) : Measure ℝ :=
  ((Fintype.card α : ℝ≥0∞)⁻¹) • ∑ a, Measure.dirac (f a)

lemma pLaw_eq_uLaw {N : ℕ} (f : Equiv.Perm (Fin N ⊕ Fin N) → ℝ) : pLaw f = uLaw f := rfl

lemma uLaw_apply {α : Type} [Fintype α] (f : α → ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    [DecidablePred (fun a => f a ∈ S)] :
    uLaw f S = ((Fintype.card α : ℝ≥0∞)⁻¹) * ((Finset.univ.filter (fun a => f a ∈ S)).card : ℝ≥0∞) := by
  rw [uLaw, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.dirac_apply' _ hS, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

instance uLaw_isProb {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
    IsProbabilityMeasure (uLaw f) := by
  constructor
  simp only [uLaw, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  have h0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)

lemma uLaw_real {α : Type} [Fintype α] (f : α → ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    [DecidablePred (fun a => f a ∈ S)] :
    (uLaw f).real S = ((Finset.univ.filter (fun a => f a ∈ S)).card : ℝ) / Fintype.card α := by
  rw [measureReal_def, uLaw_apply f hS, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]

lemma uLaw_equiv {α β : Type} [Fintype α] [Fintype β] (e : β ≃ α) (f : α → ℝ) :
    uLaw (f ∘ e) = uLaw f := by
  unfold uLaw
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e (fun a => Measure.dirac (f a))

/-- Index of the `u`-quantile among `n` equally likely sorted values. -/
noncomputable def kIdx (n : ℕ) (u : ℝ) : ℕ := ⌈u * n⌉₊ - 1

lemma kIdx_eq_iff {n : ℕ} {u : ℝ} (hpos : 0 < u * n) (j : ℕ) :
    kIdx n u = j ↔ (j : ℝ) < u * n ∧ u * n ≤ j + 1 := by
  have h1 : 0 < ⌈u * n⌉₊ := Nat.ceil_pos.mpr hpos
  unfold kIdx
  have e : ⌈u * n⌉₊ - 1 = j ↔ ⌈u * n⌉₊ = j + 1 := by omega
  rw [e, Nat.ceil_eq_iff (by omega)]
  push_cast
  simp only [add_sub_cancel_right]

lemma kIdx_lt {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : kIdx n u < n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : ⌈u * n⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  unfold kIdx; omega

lemma kIdx_spec {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (kIdx n u : ℝ) < u * n ∧ u * n ≤ kIdx n u + 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (kIdx_eq_iff (by positivity) _).mp rfl

/-- The quantile transform of the uniform law of a monotone `g : Fin n → ℝ`. -/
lemma qnt_sorted {n : ℕ} (hn : 1 ≤ n) (g : Fin n → ℝ) (hg : Monotone g) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) : qnt (uLaw g) u = g ⟨kIdx n u, kIdx_lt hn hu0 hu1⟩ := by
  classical
  obtain ⟨hk1, hk2⟩ := kIdx_spec hn hu0 hu1
  set k : Fin n := ⟨kIdx n u, kIdx_lt hn hu0 hu1⟩ with hkdef
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply le_antisymm
  · rw [qnt_le_iff _ hu0 hu1, cdf_eq_real, uLaw_real _ measurableSet_Iic, Fintype.card_fin,
      le_div_iff₀ hn']
    have hsub : Finset.Iic k ⊆ Finset.univ.filter (fun i => g i ∈ Iic (g k)) := fun i hi => by
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iic]
      exact hg hi
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h
    have h' : (kIdx n u : ℝ) + 1 ≤ ((Finset.univ.filter (fun i => g i ∈ Iic (g k))).card : ℝ) := by
      exact_mod_cast h
    linarith
  · by_contra hlt
    push_neg at hlt
    set z := qnt (uLaw g) u with hz
    have hz1 : u ≤ cdf (uLaw g) z := (qnt_le_iff _ hu0 hu1 z).1 le_rfl
    rw [cdf_eq_real, uLaw_real _ measurableSet_Iic, Fintype.card_fin, le_div_iff₀ hn'] at hz1
    have hsub : Finset.univ.filter (fun i => g i ∈ Iic z) ⊆ Finset.Iio k := fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iic] at hi
      simp only [Finset.mem_Iio]
      by_contra hki
      push_neg at hki
      have := hg hki
      linarith
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h
    have h' : ((Finset.univ.filter (fun i => g i ∈ Iic z)).card : ℝ) ≤ (kIdx n u : ℝ) := by
      exact_mod_cast h
    linarith

lemma kIdx_set (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    {w : ℝ | kIdx n (Phi w) = j} = {w | Phi w ≤ (j + 1) / n} \ {w | Phi w ≤ j / n} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_diff, kIdx_eq_iff (mul_pos (Phi_pos' w) hn'),
    le_div_iff₀ hn', not_le]
  exact and_comm

lemma measurableSet_kIdx (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    MeasurableSet {w : ℝ | kIdx n (Phi w) = j} := by
  rw [kIdx_set n hn j]
  exact (measurableSet_le continuous_Phi'.measurable measurable_const).diff
    (measurableSet_le continuous_Phi'.measurable measurable_const)

lemma kIdx_prob (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j < n) :
    (gaussianReal 0 1) {w : ℝ | kIdx n (Phi w) = j} = (n : ℝ≥0∞)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  rw [← ofReal_measureReal, kIdx_set n hn j, measureReal_sdiff (fun w hw => by
      simp only [Set.mem_setOf_eq] at hw ⊢
      exact hw.trans (div_le_div_of_nonneg_right (by linarith) hn'.le))
    (measurableSet_le continuous_Phi'.measurable measurable_const),
    gauss_Phi_le _ (by positivity) (by rw [div_le_one hn']; exact hjn),
    gauss_Phi_le _ (by positivity) (by rw [div_le_one hn']; linarith)]
  rw [show ((j : ℝ) + 1) / n - j / n = (n : ℝ)⁻¹ by field_simp; ring,
    ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]

section rank

variable {α : Type} [Fintype α]

/-- Sorting key: lexicographic in `(f a, enumeration index)`; injective. -/
noncomputable def rkey (f : α → ℝ) (a : α) : ℝ ×ₗ Fin (Fintype.card α) :=
  toLex (f a, Fintype.equivFin α a)

lemma rkey_lt_iff (f : α → ℝ) (a b : α) :
    rkey f b < rkey f a ↔ f b < f a ∨ (f b = f a ∧ Fintype.equivFin α b < Fintype.equivFin α a) :=
  Prod.Lex.toLex_lt_toLex

lemma rkey_inj (f : α → ℝ) : Function.Injective (rkey f) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  exact (Fintype.equivFin α).injective this

open Classical in
/-- Rank of `a` in the sorted order of `f`. -/
noncomputable def rk (f : α → ℝ) (a : α) : ℕ := (Finset.univ.filter (fun b => rkey f b < rkey f a)).card

lemma rk_lt_rk (f : α → ℝ) {a b : α} (h : rkey f b < rkey f a) : rk f b < rk f a := by
  classical
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨b, by simp [h], by simp⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans h

lemma rk_lt_card (f : α → ℝ) (a : α) : rk f a < Fintype.card α := by
  classical
  unfold rk
  calc _ < (Finset.univ : Finset α).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨a, Finset.mem_univ _, by simp⟩
    _ = Fintype.card α := Finset.card_univ

lemma rk_inj (f : α → ℝ) : Function.Injective (rk f) := by
  intro a b h
  by_contra hab
  have hk : rkey f a ≠ rkey f b := fun h' => hab (rkey_inj f h')
  rcases lt_or_gt_of_ne hk with h1 | h1
  · exact absurd h (rk_lt_rk f h1).ne
  · exact absurd h (rk_lt_rk f h1).ne'

/-- The rank map as an equivalence with `Fin (card α)`. -/
noncomputable def rkE (f : α → ℝ) : α ≃ Fin (Fintype.card α) :=
  Equiv.ofBijective (fun a => ⟨rk f a, rk_lt_card f a⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => rk_inj f (congrArg Fin.val h), (Fintype.card_fin _).symm⟩)

lemma rkE_val (f : α → ℝ) (a : α) : (rkE f a).val = rk f a := rfl

lemma sorted_mono (f : α → ℝ) : Monotone (f ∘ (rkE f).symm) := by
  intro i j hij
  by_contra hlt
  push_neg at hlt
  simp only [Function.comp] at hlt
  have h1 : rkey f ((rkE f).symm j) < rkey f ((rkE f).symm i) :=
    (rkey_lt_iff f _ _).2 (Or.inl hlt)
  have h2 := rk_lt_rk f h1
  rw [← rkE_val, ← rkE_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  exact absurd hij (not_le.mpr h2)

/-- Rank-based quantile choice: the element whose rank is the `u`-quantile index. -/
noncomputable def pick [Nonempty α] (f : α → ℝ) (u : ℝ) : α :=
  (rkE f).symm ⟨min (kIdx (Fintype.card α) u) (Fintype.card α - 1),
    by have := Fintype.card_pos (α := α); omega⟩

lemma rk_pick [Nonempty α] (f : α → ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    rk f (pick f u) = kIdx (Fintype.card α) u := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  have hl := kIdx_lt hn hu0 hu1
  unfold pick
  rw [← rkE_val, Equiv.apply_symm_apply]
  simp only
  omega

/-- The picked element realises the quantile transform of the law of `f`. -/
theorem qnt_pick [Nonempty α] (f : α → ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    qnt (uLaw f) u = f (pick f u) := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  rw [← uLaw_equiv (rkE f).symm f, qnt_sorted hn _ (sorted_mono f) hu0 hu1]
  simp only [Function.comp]
  congr 1
  apply (rkE f).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [rkE_val, rk_pick f hu0 hu1]

/-- Driven by a standard Gaussian `w` through `u = Φ(w)`, the pick is uniform. -/
theorem pick_prob [Nonempty α] (f : α → ℝ) (a : α) :
    (gaussianReal 0 1) {w : ℝ | pick f (Phi w) = a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  have e : {w : ℝ | pick f (Phi w) = a} = {w : ℝ | kIdx (Fintype.card α) (Phi w) = rk f a} := by
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h; rw [← h, rk_pick f (Phi_pos' w) (Phi_lt_one w)]
    · intro h
      apply rk_inj f
      rw [rk_pick f (Phi_pos' w) (Phi_lt_one w), h]
  rw [e, kIdx_prob _ hn _ (rk_lt_card f a)]

lemma measurable_rk {X : Type} [MeasurableSpace X] (F : X → α → ℝ)
    (hF : ∀ a, Measurable fun x => F x a) (a : α) : Measurable fun x => (rk (F x) a : ℝ) := by
  classical
  have e : (fun x => (rk (F x) a : ℝ)) = fun x => ∑ b, if rkey (F x) b < rkey (F x) a then (1 : ℝ) else 0 := by
    funext x
    unfold rk
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [e]
  refine Finset.measurable_sum _ fun b _ => Measurable.ite ?_ measurable_const measurable_const
  simp only [rkey_lt_iff]
  exact (measurableSet_lt (hF b) (hF a)).union
    ((measurableSet_eq_fun (hF b) (hF a)).inter (MeasurableSet.const _))

/-- Joint measurability of the pick when `f` depends measurably on a parameter. -/
theorem measurableSet_pick [Nonempty α] {X : Type} [MeasurableSpace X] (F : X → α → ℝ)
    (hF : ∀ a, Measurable fun x => F x a) (a : α) :
    MeasurableSet {p : X × ℝ | pick (F p.1) (Phi p.2) = a} := by
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos
  have e : {p : X × ℝ | pick (F p.1) (Phi p.2) = a} =
      {p : X × ℝ | (kIdx (Fintype.card α) (Phi p.2) : ℝ) = (rk (F p.1) a : ℝ)} := by
    ext p
    simp only [Set.mem_setOf_eq, Nat.cast_inj]
    constructor
    · intro h; rw [← h, rk_pick _ (Phi_pos' _) (Phi_lt_one _)]
    · intro h
      apply rk_inj (F p.1)
      rw [rk_pick _ (Phi_pos' _) (Phi_lt_one _), h]
  rw [e]
  have hk : Measurable fun w : ℝ => kIdx (Fintype.card α) (Phi w) :=
    measurable_to_countable' fun j => measurableSet_kIdx _ hn j
  exact measurableSet_eq_fun
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (hk.comp measurable_snd))
    ((measurable_rk F hF a).comp measurable_fst)

end rank

end P99bcb804

end X53_Pick

section X54_Tree

/-! KMT 1976 II, §4: the dyadic tree construction on a block of length `2^n` (P1) and the
deterministic path inequality (P5): every partial-sum error is at most `2|e_root| + 2 D`,
where `D` is the largest sum of node errors `|Ũ - Ṽ|` along a root-to-leaf path. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Dyadic index type: `Idx 0 = Unit`, `Idx (n+1) = Idx n ⊕ Idx n` (left half first). -/
@[reducible] def Idx : ℕ → Type
  | 0 => Unit
  | n + 1 => Idx n ⊕ Idx n

instance instFintypeIdx : ∀ n, Fintype (Idx n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => haveI := instFintypeIdx n; inferInstanceAs (Fintype (Idx n ⊕ Idx n))

instance instDecEqIdx : ∀ n, DecidableEq (Idx n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => haveI := instDecEqIdx n; inferInstanceAs (DecidableEq (Idx n ⊕ Idx n))

instance instUniqueIdx0 : Unique (Idx 0) := inferInstanceAs (Unique Unit)

/-- Node Gaussians: one real per internal node. -/
@[reducible] def Zn : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × Zn n × Zn n

/-- Constructor for `Zn (n+1)`. -/
@[reducible] def Zn.mk {n : ℕ} (z0 : ℝ) (zL zR : Zn n) : Zn (n + 1) := (z0, zL, zR)

/-- In-order position of a leaf. -/
def toNat : (n : ℕ) → Idx n → ℕ
  | 0, _ => 0
  | n + 1, Sum.inl i => toNat n i
  | n + 1, Sum.inr i => 2 ^ n + toNat n i

lemma toNat_lt : ∀ (n : ℕ) (i : Idx n), toNat n i < 2 ^ n
  | 0, _ => by simp [toNat]
  | n + 1, Sum.inl i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega
  | n + 1, Sum.inr i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega

/-- Partial sum over the first `k` leaves. -/
noncomputable def ps (n : ℕ) (f : Idx n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => toNat n i < k), f i

lemma ps_zero (n : ℕ) (f : Idx n → ℝ) : ps n f 0 = 0 := by
  simp [ps]

lemma ps_full (n : ℕ) (f : Idx n → ℝ) {k : ℕ} (hk : 2 ^ n ≤ k) : ps n f k = ∑ i, f i := by
  unfold ps
  rw [Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le (toNat_lt n i) hk]

lemma ps_succ (n : ℕ) (f : Idx (n + 1) → ℝ) (k : ℕ) :
    ps (n + 1) f k = ps n (fun i => f (Sum.inl i)) k + ps n (fun i => f (Sum.inr i)) (k - 2 ^ n) := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [show (∑ a : Idx (n + 1), if toNat (n + 1) a < k then f a else 0) =
      ∑ a : Idx n ⊕ Idx n, if toNat (n + 1) a < k then f a else 0 from rfl, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toNat]
  congr 1
  apply propext
  omega

/-- Half-difference of a split arrangement. -/
noncomputable def hdG {ι : Type} [Fintype ι] (x : ι ⊕ ι → ℝ) (σ : Equiv.Perm (ι ⊕ ι)) : ℝ :=
  ∑ i, (x (σ (Sum.inl i)) - x (σ (Sum.inr i)))

/-- X side: at each node pick the arrangement by the node Gaussian and recurse on the halves. -/
noncomputable def R : (n : ℕ) → (Idx n → ℝ) → Zn n → (Idx n → ℝ)
  | 0, x, _ => x
  | n + 1, x, (z0, zL, zR) =>
      Sum.elim (R n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inl i))) zL)
        (R n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inr i))) zR)

/-- Gaussian side: the block sum `T` splits as `(T ± √(2^(n+1)) z0)/2`. -/
noncomputable def G : (n : ℕ) → ℝ → Zn n → (Idx n → ℝ)
  | 0, T, _ => fun _ => T
  | n + 1, T, (z0, zL, zR) =>
      Sum.elim (G n ((T + √((2 : ℝ) ^ (n + 1)) * z0) / 2) zL)
        (G n ((T - √((2 : ℝ) ^ (n + 1)) * z0) / 2) zR)

/-- Largest path sum of node errors `|Ũ - Ṽ|`. -/
noncomputable def D : (n : ℕ) → (Idx n → ℝ) → Zn n → ℝ
  | 0, _, _ => 0
  | n + 1, x, (z0, zL, zR) =>
      |hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) - √((2 : ℝ) ^ (n + 1)) * z0| +
        max (D n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inl i))) zL)
          (D n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inr i))) zR)

lemma halves_sum {ι : Type} [Fintype ι] (x : ι ⊕ ι → ℝ) (σ : Equiv.Perm (ι ⊕ ι)) :
    (∑ i, x (σ (Sum.inl i))) + ∑ i, x (σ (Sum.inr i)) = ∑ j, x j := by
  rw [← Fintype.sum_sum_type (fun j => x (σ j)), Equiv.sum_comp σ x]

lemma halves_diff {ι : Type} [Fintype ι] (x : ι ⊕ ι → ℝ) (σ : Equiv.Perm (ι ⊕ ι)) :
    (∑ i, x (σ (Sum.inl i))) - ∑ i, x (σ (Sum.inr i)) = hdG x σ := by
  rw [hdG, Finset.sum_sub_distrib]

lemma sum_R : ∀ (n : ℕ) (x : Idx n → ℝ) (z : Zn n), ∑ i, R n x z i = ∑ i, x i
  | 0, x, _ => rfl
  | n + 1, x, (z0, zL, zR) => by
      show ∑ i : Idx n ⊕ Idx n, R (n + 1) x (Zn.mk z0 zL zR) i = ∑ i : Idx n ⊕ Idx n, x i
      rw [Fintype.sum_sum_type]
      simp only [R, Sum.elim_inl, Sum.elim_inr]
      rw [sum_R n, sum_R n]
      exact halves_sum (ι := Idx n) x _

lemma sum_G : ∀ (n : ℕ) (T : ℝ) (z : Zn n), ∑ i, G n T z i = T
  | 0, T, _ => by simp [G]
  | n + 1, T, (z0, zL, zR) => by
      show ∑ i : Idx n ⊕ Idx n, G (n + 1) T (Zn.mk z0 zL zR) i = T
      rw [Fintype.sum_sum_type]
      simp only [G, Sum.elim_inl, Sum.elim_inr]
      rw [sum_G n, sum_G n]
      ring

/-- KMT path inequality (deterministic): every partial-sum error is at most
`2 |Σ x - T| + 2 D`. -/
theorem path_bound : ∀ (n : ℕ) (x : Idx n → ℝ) (T : ℝ) (z : Zn n) (k : ℕ),
    |ps n (R n x z) k - ps n (G n T z) k| ≤ 2 * |∑ i, x i - T| + 2 * D n x z
  | 0, x, T, _, k => by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [ps_zero, D]
      · rw [ps_full 0 _ (by rw [pow_zero]; omega), ps_full 0 _ (by rw [pow_zero]; omega)]
        simp only [R, G, D, Fintype.sum_unique, mul_zero, add_zero]
        have := abs_nonneg (x default - T)
        linarith
  | n + 1, x, T, (z0, zL, zR), k => by
      set σ := pick (hdG (ι := Idx n) x) (Phi z0) with hσ
      set xL : Idx n → ℝ := fun i => x (σ (Sum.inl i)) with hxL
      set xR : Idx n → ℝ := fun i => x (σ (Sum.inr i)) with hxR
      set V := √((2 : ℝ) ^ (n + 1)) * z0 with hV
      set δ := hdG (ι := Idx n) x σ - V with hδ
      set e := ∑ i, x i - T with he
      have hs := halves_sum (ι := Idx n) x σ
      have hd := halves_diff (ι := Idx n) x σ
      have hsx : ∑ i : Idx (n + 1), x i = ∑ j : Idx n ⊕ Idx n, x j := rfl
      have eL : ∑ i, xL i - (T + V) / 2 = (e + δ) / 2 := by
        rw [he, hδ, hsx]; simp only [hxL]; linarith
      have eR : ∑ i, xR i - (T - V) / 2 = (e - δ) / 2 := by
        rw [he, hδ, hsx]; simp only [hxR]; linarith
      have hD : D (n + 1) x (Zn.mk z0 zL zR) = |δ| + max (D n xL zL) (D n xR zR) := rfl
      have hRL : (fun i => R (n + 1) x (Zn.mk z0 zL zR) (Sum.inl i)) = R n xL zL := rfl
      have hRR : (fun i => R (n + 1) x (Zn.mk z0 zL zR) (Sum.inr i)) = R n xR zR := rfl
      have hGL : (fun i => G (n + 1) T (Zn.mk z0 zL zR) (Sum.inl i)) = G n ((T + V) / 2) zL := rfl
      have hGR : (fun i => G (n + 1) T (Zn.mk z0 zL zR) (Sum.inr i)) = G n ((T - V) / 2) zR := rfl
      rw [ps_succ, ps_succ, hRL, hRR, hGL, hGR, hD]
      have hmL := le_max_left (D n xL zL) (D n xR zR)
      have hmR := le_max_right (D n xL zL) (D n xR zR)
      have a1 := abs_add_le e δ
      have a2 := abs_sub e δ
      have hDL0 : 0 ≤ |δ| := abs_nonneg δ
      have he0 : 0 ≤ |e| := abs_nonneg e
      rcases le_or_gt k (2 ^ n) with hk | hk
      · rw [show k - 2 ^ n = 0 by omega, ps_zero, ps_zero, add_zero, add_zero]
        have IH := path_bound n xL ((T + V) / 2) zL k
        rw [eL, abs_div, abs_two] at IH
        linarith
      · rw [ps_full n _ hk.le, ps_full n _ hk.le, sum_R, sum_G]
        have IH := path_bound n xR ((T - V) / 2) zR (k - 2 ^ n)
        rw [eR, abs_div, abs_two] at IH
        have e1 : ∑ i, xL i + ps n (R n xR zR) (k - 2 ^ n) -
            ((T + V) / 2 + ps n (G n ((T - V) / 2) zR) (k - 2 ^ n)) =
            (∑ i, xL i - (T + V) / 2) +
              (ps n (R n xR zR) (k - 2 ^ n) - ps n (G n ((T - V) / 2) zR) (k - 2 ^ n)) := by ring
        rw [e1, eL]
        have a3 := abs_add_le ((e + δ) / 2)
          (ps n (R n xR zR) (k - 2 ^ n) - ps n (G n ((T - V) / 2) zR) (k - 2 ^ n))
        rw [abs_div, abs_two] at a3
        linarith

end P99bcb804

end X54_Tree

section X55_Rot

/-! P2 ingredient: the 2-D rotation `(a, b) ↦ ((a+b)/√2, (a-b)/√2)` preserves the standard
Gaussian on `ℝ × ℝ`; hence the Gaussian split `T ↦ (T ± √(2^(n+1)) z)/2` of the tree `G`
turns `N(0, 2^(n+1)) ⊗ N(0,1)` into `N(0, 2^n) ⊗ N(0, 2^n)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma sqrt2_mul : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)

/-- The rotation on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def rotL : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := WithLp.toLp 2 ![(v 0 + v 1) / √2, (v 0 - v 1) / √2]
  map_add' v w := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i; fin_cases i <;> simp <;> ring

lemma rotL_apply0 (v : EuclideanSpace ℝ (Fin 2)) : rotL v 0 = (v 0 + v 1) / √2 := rfl
lemma rotL_apply1 (v : EuclideanSpace ℝ (Fin 2)) : rotL v 1 = (v 0 - v 1) / √2 := rfl

lemma rot_arith (a b c d : ℝ) :
    (a + b) / √2 * ((c + d) / √2) + (a - b) / √2 * ((c - d) / √2) = a * c + b * d := by
  rw [div_mul_div_comm, div_mul_div_comm, sqrt2_mul]; ring

lemma rotL_inner (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rotL x) (rotL y) = inner ℝ x y := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, rotL_apply0, rotL_apply1, RCLike.inner_apply,
    conj_trivial]
  have := rot_arith (y 0) (y 1) (x 0) (x 1)
  linarith

noncomputable def rotE : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (rotL.isometryOfInner rotL_inner).toLinearIsometryEquiv rfl

lemma rotE_apply (v : EuclideanSpace ℝ (Fin 2)) : rotE v = rotL v := rfl

/-- `ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def e2 : ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma e2_apply0 (p : ℝ × ℝ) : e2 p 0 = p.1 := by simp [e2]
lemma e2_apply1 (p : ℝ × ℝ) : e2 p 1 = p.2 := by simp [e2]

/-- The rotation of `ℝ × ℝ`. -/
noncomputable def rot2 (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + p.2) / √2, (p.1 - p.2) / √2)

lemma measurable_rot2 : Measurable rot2 := by
  unfold rot2; fun_prop

theorem rot2_law :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map rot2 =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  set γ := gaussianReal 0 1
  have h1 : (γ.prod γ).map e2 = stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    rw [← (measurePreserving_finTwoArrow γ).map_eq,
      Measure.map_map e2.measurable MeasurableEquiv.finTwoArrow.measurable]
    convert map_pi_eq_stdGaussian (ι := Fin 2) using 2
    funext v
    ext i
    fin_cases i <;> simp [e2]
  have hc : (e2 : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) ∘ rot2 = rotE ∘ e2 := by
    funext p
    ext i
    fin_cases i <;> simp [e2_apply0, e2_apply1, rotE_apply, rotL_apply0, rotL_apply1, rot2]
  apply MeasurableEquiv.map_measurableEquiv_injective e2
  rw [Measure.map_map e2.measurable measurable_rot2, hc,
    ← Measure.map_map rotE.continuous.measurable e2.measurable, h1, stdGaussian_map rotE]

lemma gauss_scale (c : ℝ) (v : ℝ≥0) (h : c ^ 2 = v) :
    (gaussianReal 0 1).map (c * ·) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp [h]

lemma sc_arith_p (d a b : ℝ) : (√2 * d * a + √2 * d * b) / 2 = d * ((a + b) / √2) := by
  have hs : √2 ≠ 0 := by positivity
  rw [eq_comm, mul_div_assoc', div_eq_div_iff hs two_ne_zero]
  linear_combination (-(d * (a + b))) * sqrt2_mul

lemma sc_arith_m (d a b : ℝ) : (√2 * d * a - √2 * d * b) / 2 = d * ((a - b) / √2) := by
  have hs : √2 ≠ 0 := by positivity
  rw [eq_comm, mul_div_assoc', div_eq_div_iff hs two_ne_zero]
  linear_combination (-(d * (a - b))) * sqrt2_mul

/-- The Gaussian split of the tree at level `n+1`. -/
theorem split_law (n : ℕ) :
    ((gaussianReal 0 (2 ^ (n + 1))).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2) / 2,
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2) / 2)) =
      (gaussianReal 0 (2 ^ n)).prod (gaussianReal 0 (2 ^ n)) := by
  set c := √((2 : ℝ) ^ (n + 1)) with hcdef
  set d := √((2 : ℝ) ^ n) with hddef
  have hc2 : c ^ 2 = ((2 ^ (n + 1) : ℝ≥0) : ℝ) := by
    rw [hcdef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hd2 : d ^ 2 = ((2 ^ n : ℝ≥0) : ℝ) := by
    rw [hddef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hcd : c = √2 * d := by
    rw [hcdef, hddef, ← Real.sqrt_mul (by norm_num), pow_succ, mul_comm]
  set γ := gaussianReal 0 1
  have hT : gaussianReal 0 (2 ^ (n + 1)) = γ.map (c * ·) := (gauss_scale c _ hc2).symm
  have hD : gaussianReal 0 (2 ^ n) = γ.map (d * ·) := (gauss_scale d _ hd2).symm
  have hmc : Measurable (c * · : ℝ → ℝ) := measurable_const_mul c
  have hmd : Measurable (d * · : ℝ → ℝ) := measurable_const_mul d
  have hf : Measurable (fun p : ℝ × ℝ => ((p.1 + c * p.2) / 2, (p.1 - c * p.2) / 2)) := by
    fun_prop
  rw [hT, hD, ← Measure.map_id (μ := γ), Measure.map_prod_map _ _ hmc measurable_id,
    Measure.map_prod_map _ _ hmd hmd, Measure.map_id, Measure.map_map hf (hmc.prodMap measurable_id)]
  have e : (fun p : ℝ × ℝ => ((p.1 + c * p.2) / 2, (p.1 - c * p.2) / 2)) ∘
      Prod.map (c * ·) id = Prod.map (d * ·) (d * ·) ∘ rot2 := by
    funext p
    ext
    · show (c * p.1 + c * p.2) / 2 = d * ((p.1 + p.2) / √2)
      rw [hcd]; exact sc_arith_p d p.1 p.2
    · show (c * p.1 - c * p.2) / 2 = d * ((p.1 - p.2) / √2)
      rw [hcd]; exact sc_arith_m d p.1 p.2
  rw [e, ← Measure.map_map (hmd.prodMap hmd) measurable_rot2, rot2_law]

end P99bcb804

end X55_Rot

section X56_GLaw

/-! P2: the Gaussian side `G n T z` of the tree has iid `N(0,1)` leaves when `T ~ N(0, 2^n)`
and the node Gaussians are iid `N(0,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

instance instMeasZn : ∀ n, MeasurableSpace (Zn n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => haveI := instMeasZn n; inferInstanceAs (MeasurableSpace (ℝ × Zn n × Zn n))

/-- iid standard Gaussians on the internal nodes. -/
noncomputable def γZ : (n : ℕ) → Measure (Zn n)
  | 0 => Measure.dirac ()
  | n + 1 => (gaussianReal 0 1).prod ((γZ n).prod (γZ n))

instance instProbγZ : ∀ n, IsProbabilityMeasure (γZ n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | n + 1 => haveI := instProbγZ n
      inferInstanceAs (IsProbabilityMeasure ((gaussianReal 0 1).prod ((γZ n).prod (γZ n))))

/-- `((a,b),(c,d)) ↦ ((a,c),(b,d))` is measure preserving for product measures. -/
lemma shuffle_mp {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μ1 : Measure α) (μ2 : Measure β) (μ3 : Measure γ) (μ4 : Measure δ)
    [SFinite μ1] [SFinite μ2] [SFinite μ3] [SFinite μ4] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μ1.prod μ2).prod (μ3.prod μ4)) ((μ1.prod μ3).prod (μ2.prod μ4)) := by
  have h1 := measurePreserving_prodAssoc μ1 μ2 (μ3.prod μ4)
  have h2 := (measurePreserving_prodAssoc μ2 μ3 μ4).symm
  have h3 := (MeasurePreserving.id μ1).prod (h2)
  have h4 := (MeasurePreserving.id μ1).prod
    ((Measure.measurePreserving_swap (μ := μ2) (ν := μ3)).prod (MeasurePreserving.id μ4))
  have h5 := (MeasurePreserving.id μ1).prod (measurePreserving_prodAssoc μ3 μ2 μ4)
  have h6 := (measurePreserving_prodAssoc μ1 μ3 (μ2.prod μ4)).symm
  have h := h6.comp (h5.comp (h4.comp (h3.comp h1)))
  convert h using 1
  try (funext p; rfl)

lemma measurable_G : ∀ n : ℕ, Measurable fun p : ℝ × Zn n => G n p.1 p.2
  | 0 => measurable_pi_lambda _ fun _ => measurable_fst
  | n + 1 => by
      have ih := measurable_G n
      have hL : Measurable fun p : ℝ × Zn (n + 1) =>
          G n ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2) p.2.2.1 :=
        ih.comp ((by fun_prop : Measurable fun p : ℝ × Zn (n + 1) =>
          (p.1 + √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2).prodMk (measurable_fst.comp
            (measurable_snd.comp measurable_snd)))
      have hR : Measurable fun p : ℝ × Zn (n + 1) =>
          G n ((p.1 - √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2) p.2.2.2 :=
        ih.comp ((by fun_prop : Measurable fun p : ℝ × Zn (n + 1) =>
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2).prodMk (measurable_snd.comp
            (measurable_snd.comp measurable_snd)))
      have := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)).symm.measurable.comp
        (hL.prodMk hR)
      exact this

lemma split_mp (n : ℕ) :
    MeasurePreserving (fun p : ℝ × ℝ => ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2) / 2,
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2) / 2))
      ((gaussianReal 0 (2 ^ (n + 1))).prod (gaussianReal 0 1))
      ((gaussianReal 0 (2 ^ n)).prod (gaussianReal 0 (2 ^ n))) :=
  ⟨by fun_prop, split_law n⟩

/-- P2: the Gaussian side has iid standard Gaussian leaves. -/
theorem gLaw : ∀ n : ℕ, MeasurePreserving (fun p : ℝ × Zn n => G n p.1 p.2)
    ((gaussianReal 0 (2 ^ n)).prod (γZ n)) (Measure.pi fun _ : Idx n => gaussianReal 0 1)
  | 0 => by
      have h := (measurePreserving_funUnique (gaussianReal 0 1) (Idx 0)).symm
      have h2 : MeasurePreserving (fun p : ℝ × Zn 0 => p.1)
          ((gaussianReal 0 (2 ^ 0)).prod (γZ 0)) (gaussianReal 0 1) := by
        refine ⟨measurable_fst, ?_⟩
        have : IsProbabilityMeasure (γZ 0) := instProbγZ 0
        rw [Measure.map_fst_prod]; simp
      convert h.comp h2 using 1
      funext p i; rfl
  | n + 1 => by
      have ih := gLaw n
      have := instProbγZ n
      have h1 := (measurePreserving_prodAssoc (gaussianReal 0 (2 ^ (n + 1))) (gaussianReal 0 1)
        ((γZ n).prod (γZ n))).symm
      have h2 := (split_mp n).prod (MeasurePreserving.id ((γZ n).prod (γZ n)))
      have h3 := shuffle_mp (gaussianReal 0 (2 ^ n)) (gaussianReal 0 (2 ^ n)) (γZ n) (γZ n)
      have h4 := ih.prod ih
      have h5 := measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Idx n ⊕ Idx n => gaussianReal 0 1)
      have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
      convert h using 1
      · funext ⟨T, z0, zL, zR⟩ i
        rcases i with i | i <;> rfl
      · rfl

end P99bcb804

end X56_GLaw

section X60_IidA

/-! E (iid Cramér, KMT 1975 Part I (2.6) / Petrov): cumulant facts for a bounded, centred law
with unit second moment: `Λ = cgf id F`, `μ_t = Λ'(t)`, `V t = Λ''(t)`;
`V t ∈ [e^{-2|t|K}, e^{|t|K}]`, `|Λ t - t²/2| ≤ 2K t³`, `|μ_t - t| ≤ 4K t²`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section IidA

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

lemma int_of_ae_bdd {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ᵐ x ∂F, |g x| ≤ C) :
    Integrable g F :=
  Integrable.of_bound hg.aestronglyMeasurable C (h.mono fun x hx => by rwa [Real.norm_eq_abs])

lemma tx_le (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) : ∀ᵐ x ∂F, |t * x| ≤ |t| * K :=
  hsupp.mono fun x hx => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)

lemma iexp (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) : Integrable (fun x : ℝ => exp (t * x)) F :=
  int_of_ae_bdd (by fun_prop) (exp (|t| * K)) ((tx_le hsupp t).mono fun x hx => by
    rw [abs_exp]; exact exp_le_exp.2 ((le_abs_self _).trans hx))

lemma mgf_le (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) :
    mgf (fun x : ℝ => x) F t ≤ exp (|t| * K) := by
  have h := integral_mono_ae (iexp hsupp t) (integrable_const (exp (|t| * K)))
    ((tx_le hsupp t).mono fun x hx => exp_le_exp.2 ((le_abs_self _).trans hx))
  simpa [mgf] using h

end IidA

end P99bcb804

end X60_IidA

section X64_IidD

/-! E (iid Cramér) part D: left tail by reflection, Berry–Esseen for the sum, and the root
quantile coupling bound (KMT 1975 I (2.6) / 1976 II Thm 1B, root of the dyadic scheme). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section IidD

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

/-- Law of the sum of an iid block. -/
noncomputable def sLaw (F : Measure ℝ) (ι : Type) [Fintype ι] : Measure ℝ :=
  (Measure.pi fun _ : ι => F).map (fun x => ∑ i, x i)

lemma measurable_sum' (ι : Type) [Fintype ι] : Measurable (fun x : ι → ℝ => ∑ i, x i) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

instance sLaw_prob (F : Measure ℝ) [IsProbabilityMeasure F] (ι : Type) [Fintype ι] :
    IsProbabilityMeasure (sLaw F ι) :=
  Measure.isProbabilityMeasure_map (measurable_sum' ι).aemeasurable

end IidD

end P99bcb804

end X64_IidD

section X65_Root

/-! P4: the root quantile coupling bound holds for every `w` (off the moderate range the
quantile is bounded by the support of the sum). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section Root

lemma qnt_abs_le (L : Measure ℝ) [IsProbabilityMeasure L] {B u : ℝ} (hB : ∀ᵐ s ∂L, |s| ≤ B)
    (hu0 : 0 < u) (hu1 : u < 1) : |qnt L u| ≤ B := by
  have hnull : ∀ A : Set ℝ, A ⊆ {s | ¬ |s| ≤ B} → L A = 0 :=
    fun A hA => measure_mono_null hA (ae_iff.1 hB)
  rw [abs_le]; constructor
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := (qnt_le_iff L hu0 hu1 (qnt L u)).1 le_rfl
    have h2 : cdf L (qnt L u) = 0 := by
      rw [cdf_eq_real, measureReal_def, hnull _ (fun s hs => by
        simp only [Set.mem_Iic] at hs
        show ¬ |s| ≤ B
        exact not_le.2 (lt_of_lt_of_le (by linarith) (neg_le_abs s)))]
      simp
    linarith
  · rw [qnt_le_iff L hu0 hu1]
    have h0 : L (Iic B)ᶜ = 0 := hnull _ (fun s hs => by
      simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hs
      show ¬ |s| ≤ B
      exact not_le.2 (lt_of_lt_of_le hs (le_abs_self s)))
    rw [prob_compl_eq_zero_iff measurableSet_Iic] at h0
    rw [cdf_eq_real, measureReal_def, h0, ENNReal.toReal_one]
    exact hu1.le

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

lemma sLaw_supp (hK : 0 ≤ K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (ι : Type) [Fintype ι] :
    ∀ᵐ s ∂(sLaw F ι), |s| ≤ Fintype.card ι * K := by
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : ι => F), ∀ i, |x i| ≤ K :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => F)
      (i := i)).eventually (p := fun y : ℝ => |y| ≤ K) hsupp
  refine (ae_map_iff (measurable_sum' ι).aemeasurable
    (measurableSet_le continuous_abs.measurable measurable_const)).2 (hae.mono fun x hx => ?_)
  calc |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, K := Finset.sum_le_sum fun i _ => hx i
    _ = Fintype.card ι * K := by simp

/-- Root coupling bound for every `w`. -/
theorem root_global (hK : 0 < K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ C : ℝ, ∃ m₀ : ℕ, 0 < C ∧ 1 ≤ m₀ ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      m₀ ≤ Fintype.card ι → ∀ w : ℝ,
        |qnt (sLaw F ι) (Phi (w / √(Fintype.card ι : ℝ))) - w| ≤
          C * (1 + w ^ 2 / Fintype.card ι) := by
  have hfact := @EthierKurtz.kmt_iid_sum_quantile_coupling_bound
  apply hfact <;> assumption

end Root

end P99bcb804

end X65_Root

section X66_RLaw

/-! P3: the X side `R n x z` of the tree, with `x ~ F^M` and node Gaussians iid `N(0,1)`,
is again distributed as `F^M` (uniform rearrangements preserve a product law). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- A product law is invariant under a fixed permutation of coordinates. -/
lemma perm_inv (F : Measure ℝ) [IsProbabilityMeasure F] {α : Type} [Fintype α]
    (τ : Equiv.Perm α) :
    MeasurePreserving (fun x : α → ℝ => x ∘ τ) (Measure.pi fun _ => F)
      (Measure.pi fun _ => F) := by
  have h := measurePreserving_arrowCongr' (fun _ : α => F) (fun _ : α => F) τ.symm
    (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id F)
  convert h using 1
  funext x a
  first
    | rfl
    | simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]

/-- Rearranging a product-law vector by a uniformly random (given the vector) permutation
keeps the product law. -/
theorem perm_mp (F : Measure ℝ) [IsProbabilityMeasure F] {α : Type} [Fintype α] [DecidableEq α]
    (s : (α → ℝ) × ℝ → Equiv.Perm α) (hs : ∀ τ, MeasurableSet {p | s p = τ})
    (hp : ∀ x τ, (gaussianReal 0 1) {z | s (x, z) = τ} =
      (Fintype.card (Equiv.Perm α) : ℝ≥0∞)⁻¹) :
    MeasurePreserving (fun p : (α → ℝ) × ℝ => p.1 ∘ s p)
      ((Measure.pi fun _ : α => F).prod (gaussianReal 0 1)) (Measure.pi fun _ : α => F) := by
  set ν := Measure.pi fun _ : α => F with hν
  set γ := gaussianReal 0 1 with hγ
  set c : ℝ≥0∞ := (Fintype.card (Equiv.Perm α) : ℝ≥0∞)⁻¹ with hc
  have hmeas : Measurable fun p : (α → ℝ) × ℝ => p.1 ∘ s p := by
    let _ : MeasurableSpace (Equiv.Perm α) := ⊤
    have hsm : Measurable s := measurable_to_countable' (fun τ => by
      have e : s ⁻¹' {τ} = {p | s p = τ} := rfl
      rw [e]; exact hs τ)
    have : MeasurableSingletonClass (Equiv.Perm α) :=
      ⟨fun _ => MeasurableSpace.measurableSet_top⟩
    have hg : Measurable fun q : ((α → ℝ) × ℝ) × Equiv.Perm α => q.1.1 ∘ q.2 := by
      apply measurable_from_prod_countable_left
      intro τ
      exact measurable_pi_lambda _ fun a => (measurable_pi_apply (τ a)).comp measurable_fst
    exact hg.comp (measurable_id.prodMk hsm)
  have hτm : ∀ τ : Equiv.Perm α, Measurable fun x : α → ℝ => x ∘ τ := fun τ =>
    measurable_pi_lambda _ fun a => measurable_pi_apply (τ a)
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.prod_apply (hmeas hA)]
  have hin : ∀ x : α → ℝ, γ (Prod.mk x ⁻¹' ((fun p : (α → ℝ) × ℝ => p.1 ∘ s p) ⁻¹' A)) =
      ∑ τ : Equiv.Perm α, ((fun y : α → ℝ => y ∘ τ) ⁻¹' A).indicator (fun _ => c) x := by
    intro x
    classical
    have e : Prod.mk x ⁻¹' ((fun p : (α → ℝ) × ℝ => p.1 ∘ s p) ⁻¹' A) =
        ⋃ τ ∈ (Finset.univ.filter fun τ : Equiv.Perm α => x ∘ τ ∈ A), {z | s (x, z) = τ} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro h; exact ⟨s (x, z), h, rfl⟩
      · rintro ⟨τ, h1, h2⟩; rw [h2]; exact h1
    rw [e, measure_biUnion_finset]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hp x τ]
      by_cases h : x ∘ τ ∈ A
      · rw [if_pos h, Set.indicator_of_mem (show x ∈ (fun y : α → ℝ => y ∘ τ) ⁻¹' A from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show x ∉ (fun y : α → ℝ => y ∘ τ) ⁻¹' A from h)]
    · intro τ _ τ' _ hne
      exact Set.disjoint_left.mpr fun z h1 h2 => hne ((show s (x, z) = τ from h1).symm.trans h2)
    · intro τ _
      exact measurable_prodMk_left (hs τ)
  simp_rw [hin]
  rw [lintegral_finsetSum _ (fun τ _ => measurable_const.indicator (hτm τ hA))]
  simp_rw [lintegral_indicator_const (hτm _ hA) c]
  have hinv : ∀ τ : Equiv.Perm α, ν ((fun y : α → ℝ => y ∘ τ) ⁻¹' A) = ν A := fun τ =>
    (perm_inv F τ).measure_preimage hA.nullMeasurableSet
  simp_rw [hinv]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

lemma measurable_hdG (n : ℕ) (σ : Equiv.Perm (Idx n ⊕ Idx n)) :
    Measurable fun x : Idx n ⊕ Idx n → ℝ => hdG (ι := Idx n) x σ := by
  unfold hdG
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- P3: the X side of the tree preserves the product law. -/
theorem rLaw (F : Measure ℝ) [IsProbabilityMeasure F] : ∀ n : ℕ,
    MeasurePreserving (fun p : (Idx n → ℝ) × Zn n => R n p.1 p.2)
      ((Measure.pi fun _ : Idx n => F).prod (γZ n)) (Measure.pi fun _ : Idx n => F)
  | 0 => by
      have := instProbγZ 0
      refine ⟨measurable_fst, ?_⟩
      show Measure.map Prod.fst _ = _
      rw [Measure.map_fst_prod]; simp
  | n + 1 => by
      have ih := rLaw F n
      have := instProbγZ n
      have hpm := perm_mp F (α := Idx n ⊕ Idx n)
        (fun p => pick (hdG (ι := Idx n) p.1) (Phi p.2))
        (fun τ => measurableSet_pick (hdG (ι := Idx n)) (measurable_hdG n) τ)
        (fun x τ => pick_prob (hdG (ι := Idx n) x) τ)
      have h1 := (measurePreserving_prodAssoc (Measure.pi fun _ : Idx n ⊕ Idx n => F)
        (gaussianReal 0 1) ((γZ n).prod (γZ n))).symm
      have h2 := hpm.prod (MeasurePreserving.id ((γZ n).prod (γZ n)))
      have h2b := (measurePreserving_sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => F)).prod
        (MeasurePreserving.id ((γZ n).prod (γZ n)))
      have h3 := shuffle_mp (Measure.pi fun _ : Idx n => F) (Measure.pi fun _ : Idx n => F)
        (γZ n) (γZ n)
      have h4 := ih.prod ih
      have h5 := measurePreserving_sumPiEquivProdPi_symm (fun _ : Idx n ⊕ Idx n => F)
      have h := h5.comp (h4.comp (h3.comp (h2b.comp (h2.comp h1))))
      convert h using 1
      · funext ⟨x, z0, zL, zR⟩ i
        rcases i with i | i <;> rfl
      · rfl

end P99bcb804

end X66_RLaw

section X67_Mom

/-! P6 (part 1): exponential moments of squared sub-Gaussian sums via the Gaussian trick. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- `E exp(g²/4) = √2 ≤ 2` for a standard Gaussian. -/
lemma gauss_sq : ∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂(gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (by fun_prop)]
  have hfun : ∀ x : ℝ, (gaussianPDF 0 1 * fun x => ENNReal.ofReal (exp (x ^ 2 / 4))) x =
      ENNReal.ofReal ((√(2 * π))⁻¹ * exp (-(1 / 4) * x ^ 2)) := by
    intro x
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, integral_gaussian]
    have h1 : (√(2 * π))⁻¹ * √(π / (1 / 4)) = √2 := by
      have e1 : √(π / (1 / 4)) = √2 * √(2 * π) := by
        rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
      rw [e1, mul_comm (√2), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [h1]
    have : √2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc ENNReal.ofReal √2 ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  · exact (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  · exact Filter.Eventually.of_forall fun x => by positivity

/-- Gaussian trick: a sub-Gaussian `S` with parameter `v` has `E exp(s S²) ≤ 2` when `s v ≤ 1/4`. -/
lemma subG_sq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → ℝ} (hSm : Measurable S) {v : ℝ≥0} (h : HasSubgaussianMGF S v P) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s * v ≤ 1 / 4) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * S ω ^ 2)) ∂P ≤ 2 := by
  have hrep : ∀ ω, ENNReal.ofReal (exp (s * S ω ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (exp (√(2 * s) * S ω * g)) ∂(gaussianReal 0 1) := by
    intro ω
    have hm := mgf_gaussianReal (p := gaussianReal 0 1) (X := id) (μ := 0) (v := 1)
      (by simp) (√(2 * s) * S ω)
    rw [mgf] at hm
    have hint : Integrable (fun g => exp (√(2 * s) * S ω * g)) (gaussianReal 0 1) := by
      have := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (√(2 * s) * S ω)
      simpa using this
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)]
    congr 1
    simp only [id] at hm
    rw [hm, mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    push_cast
    ring
  simp_rw [hrep]
  rw [lintegral_lintegral_swap (by
    exact (Measurable.ennreal_ofReal (Real.measurable_exp.comp
      ((measurable_const.mul (hSm.comp measurable_fst)).mul measurable_snd))).aemeasurable)]
  refine le_trans (lintegral_mono fun g => ?_) gauss_sq
  have hint : Integrable (fun ω => exp (√(2 * s) * g * S ω)) P := h.integrable_exp_mul _
  have hmg := h.mgf_le (√(2 * s) * g)
  rw [mgf] at hmg
  calc ∫⁻ ω, ENNReal.ofReal (exp (√(2 * s) * S ω * g)) ∂P
      = ENNReal.ofReal (∫ ω, exp (√(2 * s) * g * S ω) ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)]
        congr 1; ext ω; congr 2; ring
    _ ≤ ENNReal.ofReal (exp (g ^ 2 / 4)) := by
        apply ENNReal.ofReal_le_ofReal
        refine hmg.trans (Real.exp_le_exp.2 ?_)
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hg := sq_nonneg g
        nlinarith [mul_le_mul_of_nonneg_right hs hg]

end P99bcb804

end X67_Mom

section X68_Mom2

/-! P6 (part 2): exponential moments of the X-side path sums `Σ_d (U_d² + W_d²)/m_d` and of the
Gaussian path sums `Σ_d z_d²`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma card_Idx : ∀ n : ℕ, Fintype.card (Idx n) = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      rw [show Fintype.card (Idx (n + 1)) = Fintype.card (Idx n ⊕ Idx n) from rfl,
        Fintype.card_sum, card_Idx n]
      ring

lemma ae_pi_bdd (F : Measure ℝ) [IsProbabilityMeasure F] {φ : ℝ → ℝ} {K : ℝ}
    (h : ∀ᵐ x ∂F, |φ x| ≤ K) (ι : Type) [Fintype ι] :
    ∀ᵐ r ∂(Measure.pi fun _ : ι => F), ∀ i, |φ (r i)| ≤ K := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : ι => F) i).quasiMeasurePreserving.ae h

lemma blk_subG (F : Measure ℝ) [IsProbabilityMeasure F] {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ᵐ x ∂F, |φ x| ≤ B) (h0 : ∫ x, φ x ∂F = 0) (ι : Type) [Fintype ι] :
    HasSubgaussianMGF (fun r : ι → ℝ => ∑ i, φ (r i)) (∑ _i : ι, (‖B - -B‖₊ / 2) ^ 2)
      (Measure.pi fun _ : ι => F) := by
  have hF : HasSubgaussianMGF φ ((‖B - -B‖₊ / 2) ^ 2) F :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hφ.aemeasurable
      (hB.mono fun x hx => ⟨(abs_le.1 hx).1, (abs_le.1 hx).2⟩) h0
  have hi : ∀ i, HasSubgaussianMGF (fun r : ι → ℝ => φ (r i)) ((‖B - -B‖₊ / 2) ^ 2)
      (Measure.pi fun _ : ι => F) := fun i => by
    have hmp := measurePreserving_eval (fun _ : ι => F) i
    exact HasSubgaussianMGF.of_map (X := φ) (Y := fun r : ι → ℝ => r i)
      hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF)
  have hind := iIndepFun_pi (μ := fun _ : ι => F) (X := fun _ => φ) (fun _ => hφ.aemeasurable)
  exact HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hi i)

lemma subG_param (ι : Type) [Fintype ι] (B : ℝ) :
    (((∑ _i : ι, (‖B - -B‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ) = Fintype.card ι * B ^ 2 := by
  push_cast
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs,
    sub_neg_eq_add, ← two_mul, abs_mul, abs_two, mul_div_cancel_left₀ _ two_ne_zero, sq_abs]

/-- Normalised squared block sums `((Σ r)² + (Σ (r² - 1))²) / 2^n`. -/
noncomputable def Qn (n : ℕ) (r : Idx n → ℝ) : ℝ :=
  ((∑ i, r i) ^ 2 + (∑ i, (r i ^ 2 - 1)) ^ 2) / 2 ^ n

lemma measurable_Qn (n : ℕ) : Measurable (Qn n) := by
  unfold Qn
  refine Measurable.div_const (Measurable.add ?_ ?_) _
  · exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).pow_const 2
  · exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).pow_const 2).sub measurable_const).pow_const 2

/-- `E exp(c Qn) ≤ 4` for `c B² ≤ 1/8`, when `|x| ≤ B`, `|x² - 1| ≤ B`, mean 0, `E x² = 1`. -/
lemma mom_Qn (F : Measure ℝ) [IsProbabilityMeasure F] {B : ℝ} (hB1 : ∀ᵐ x ∂F, |x| ≤ B)
    (hB2 : ∀ᵐ x ∂F, |x ^ 2 - 1| ≤ B) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (hint2 : Integrable (fun x => x ^ 2) F)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c * B ^ 2 ≤ 1 / 8) (n : ℕ) :
    ∫⁻ r, ENNReal.ofReal (exp (c * Qn n r)) ∂(Measure.pi fun _ : Idx n => F) ≤ 4 := by
  have hm0 : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := blk_subG F (φ := fun x => x) measurable_id hB1 hm (Idx n)
  have h2 := blk_subG F (φ := fun x => x ^ 2 - 1) ((measurable_id.pow_const 2).sub measurable_const)
    hB2 (by rw [integral_sub hint2 (integrable_const 1), hv]; simp) (Idx n)
  have hs : ∀ (v : ℝ≥0), (v : ℝ) = Fintype.card (Idx n) * B ^ 2 →
      2 * c / 2 ^ n * v ≤ 1 / 4 := by
    intro v hv'
    rw [hv', card_Idx]; push_cast
    rw [show 2 * c / 2 ^ n * (2 ^ n * B ^ 2) = 2 * (c * B ^ 2) by field_simp]
    linarith
  have e1 := subG_sq (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) h1
    (s := 2 * c / 2 ^ n) (by positivity) (hs _ (subG_param _ _))
  have e2 := subG_sq (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).pow_const 2).sub measurable_const) h2
    (s := 2 * c / 2 ^ n) (by positivity) (hs _ (subG_param _ _))
  have hpt : ∀ r : Idx n → ℝ, ENNReal.ofReal (exp (c * Qn n r)) ≤
      ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, r i) ^ 2)) +
        ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, (r i ^ 2 - 1)) ^ 2)) := by
    intro r
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set a := c / 2 ^ n * (∑ i, r i) ^ 2
    set b := c / 2 ^ n * (∑ i, (r i ^ 2 - 1)) ^ 2
    have hq : c * Qn n r = a + b := by simp only [Qn, a, b]; ring
    have ha : 2 * c / 2 ^ n * (∑ i, r i) ^ 2 = 2 * a := by simp only [a]; ring
    have hb : 2 * c / 2 ^ n * (∑ i, (r i ^ 2 - 1)) ^ 2 = 2 * b := by simp only [b]; ring
    rw [hq, ha, hb, Real.exp_add, show 2 * a = a + a by ring, show 2 * b = b + b by ring,
      Real.exp_add, Real.exp_add]
    nlinarith [sq_nonneg (exp a - exp b), Real.exp_pos a, Real.exp_pos b]
  calc ∫⁻ r, ENNReal.ofReal (exp (c * Qn n r)) ∂(Measure.pi fun _ : Idx n => F)
      ≤ ∫⁻ r, (ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, r i) ^ 2)) +
        ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, (r i ^ 2 - 1)) ^ 2)))
          ∂(Measure.pi fun _ : Idx n => F) := lintegral_mono hpt
    _ = (∫⁻ r, ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, r i) ^ 2))
          ∂(Measure.pi fun _ : Idx n => F)) +
        ∫⁻ r, ENNReal.ofReal (exp (2 * c / 2 ^ n * (∑ i, (r i ^ 2 - 1)) ^ 2))
          ∂(Measure.pi fun _ : Idx n => F) := by
        apply lintegral_add_left
        exact (Real.measurable_exp.comp (measurable_const.mul
          ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).pow_const 2))).ennreal_ofReal
    _ ≤ 2 + 2 := add_le_add e1 e2
    _ = 4 := by norm_num

end P99bcb804

end X68_Mom2

section X69_Mom3

/-! P6 (part 3): path sums along the dyadic tree and their exponential moments. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- X-side path sum: `Σ_d Qn` over the dyadic blocks (of size ≥ 2) containing leaf `i`. -/
noncomputable def PBX : (n : ℕ) → (Idx n → ℝ) → Idx n → ℝ
  | 0, _, _ => 0
  | n + 1, r, Sum.inl i => Qn (n + 1) r + PBX n (fun j => r (Sum.inl j)) i
  | n + 1, r, Sum.inr i => Qn (n + 1) r + PBX n (fun j => r (Sum.inr j)) i

/-- Gaussian path sum: `Σ z_node²` along the path to leaf `i`. -/
noncomputable def PZ : (n : ℕ) → Zn n → Idx n → ℝ
  | 0, _, _ => 0
  | n + 1, z, Sum.inl i => z.1 ^ 2 + PZ n z.2.1 i
  | n + 1, z, Sum.inr i => z.1 ^ 2 + PZ n z.2.2 i

lemma measurable_PBX : ∀ (n : ℕ) (i : Idx n), Measurable fun r : Idx n → ℝ => PBX n r i
  | 0, _ => measurable_const
  | n + 1, Sum.inl i => (measurable_Qn (n + 1)).add ((measurable_PBX n i).comp
      (measurable_pi_lambda _ fun j => measurable_pi_apply (Sum.inl j)))
  | n + 1, Sum.inr i => (measurable_Qn (n + 1)).add ((measurable_PBX n i).comp
      (measurable_pi_lambda _ fun j => measurable_pi_apply (Sum.inr j)))

lemma measurable_PZ : ∀ (n : ℕ) (i : Idx n), Measurable fun z : Zn n => PZ n z i
  | 0, _ => measurable_const
  | n + 1, Sum.inl i => by
      have := instMeasZn n
      exact (measurable_fst.pow_const 2).add ((measurable_PZ n i).comp
        (measurable_fst.comp measurable_snd))
  | n + 1, Sum.inr i => by
      have := instMeasZn n
      exact (measurable_fst.pow_const 2).add ((measurable_PZ n i).comp
        (measurable_snd.comp measurable_snd))

lemma Qn_split (n : ℕ) (r : Idx (n + 1) → ℝ) :
    Qn (n + 1) r ≤ 3 / 4 * Qn n (fun j => r (Sum.inl j)) + 3 / 2 * Qn n (fun j => r (Sum.inr j)) ∧
    Qn (n + 1) r ≤ 3 / 2 * Qn n (fun j => r (Sum.inl j)) + 3 / 4 * Qn n (fun j => r (Sum.inr j)) := by
  unfold Qn
  have e1 : ∑ i : Idx (n + 1), r i = ∑ j : Idx n, r (Sum.inl j) + ∑ j : Idx n, r (Sum.inr j) :=
    Fintype.sum_sum_type (f := r)
  have e2 : ∑ i : Idx (n + 1), (r i ^ 2 - 1) =
      ∑ j : Idx n, (r (Sum.inl j) ^ 2 - 1) + ∑ j : Idx n, (r (Sum.inr j) ^ 2 - 1) :=
    Fintype.sum_sum_type (f := fun i => r i ^ 2 - 1)
  rw [e1, e2]
  set a1 := ∑ j : Idx n, r (Sum.inl j)
  set b1 := ∑ j : Idx n, r (Sum.inr j)
  set a2 := ∑ j : Idx n, (r (Sum.inl j) ^ 2 - 1)
  set b2 := ∑ j : Idx n, (r (Sum.inr j) ^ 2 - 1)
  have hm : (0 : ℝ) < 2 ^ n := by positivity
  have key : (a1 + b1) ^ 2 + (a2 + b2) ^ 2 ≤ 3 / 2 * (a1 ^ 2 + a2 ^ 2) + 3 * (b1 ^ 2 + b2 ^ 2) := by
    nlinarith [sq_nonneg (a1 - 2 * b1), sq_nonneg (a2 - 2 * b2)]
  have key2 : (a1 + b1) ^ 2 + (a2 + b2) ^ 2 ≤ 3 * (a1 ^ 2 + a2 ^ 2) + 3 / 2 * (b1 ^ 2 + b2 ^ 2) := by
    nlinarith [sq_nonneg (b1 - 2 * a1), sq_nonneg (b2 - 2 * a2)]
  constructor
  · calc ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) / 2 ^ (n + 1)
        ≤ (3 / 2 * (a1 ^ 2 + a2 ^ 2) + 3 * (b1 ^ 2 + b2 ^ 2)) / 2 ^ (n + 1) := by gcongr
      _ = 3 / 4 * ((a1 ^ 2 + a2 ^ 2) / 2 ^ n) + 3 / 2 * ((b1 ^ 2 + b2 ^ 2) / 2 ^ n) := by
        rw [pow_succ]; field_simp; ring
  · calc ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) / 2 ^ (n + 1)
        ≤ (3 * (a1 ^ 2 + a2 ^ 2) + 3 / 2 * (b1 ^ 2 + b2 ^ 2)) / 2 ^ (n + 1) := by gcongr
      _ = 3 / 2 * ((a1 ^ 2 + a2 ^ 2) / 2 ^ n) + 3 / 4 * ((b1 ^ 2 + b2 ^ 2) / 2 ^ n) := by
        rw [pow_succ]; field_simp; ring

lemma Qn_nonneg (n : ℕ) (r : Idx n → ℝ) : 0 ≤ Qn n r := by
  unfold Qn; positivity

/-- Exponential moment of the X-side path sum. -/
theorem momX (F : Measure ℝ) [IsProbabilityMeasure F] {B : ℝ} (hB1 : ∀ᵐ x ∂F, |x| ≤ B)
    (hB2 : ∀ᵐ x ∂F, |x ^ 2 - 1| ≤ B) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (hint2 : Integrable (fun x => x ^ 2) F) {l : ℝ} (hl0 : 0 ≤ l) (hl : 48 * l * B ^ 2 ≤ 1) :
    ∀ (n : ℕ) (i : Idx n), ∫⁻ r, ENNReal.ofReal (exp (l * PBX n r i + 3 * l * Qn n r))
      ∂(Measure.pi fun _ : Idx n => F) ≤ ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ n := by
  have hg : ∀ n : ℕ, ∫⁻ r, ENNReal.ofReal (exp (6 * l * Qn n r))
      ∂(Measure.pi fun _ : Idx n => F) ≤ 4 :=
    fun n => mom_Qn F hB1 hB2 hm hv hint2 (by positivity) (by nlinarith) n
  have hgm : ∀ n : ℕ, Measurable fun r : Idx n → ℝ => ENNReal.ofReal (exp (6 * l * Qn n r)) :=
    fun n => (Real.measurable_exp.comp (measurable_const.mul (measurable_Qn n))).ennreal_ofReal
  have hfm : ∀ (n : ℕ) (i : Idx n), Measurable fun r : Idx n → ℝ =>
      ENNReal.ofReal (exp (l * PBX n r i + 3 * l * Qn n r)) := fun n i =>
    (Real.measurable_exp.comp ((measurable_const.mul (measurable_PBX n i)).add
      (measurable_const.mul (measurable_Qn n)))).ennreal_ofReal
  intro n
  induction n with
  | zero =>
    intro i
    have hae := ae_pi_bdd F (φ := fun x => x) hB1 (Idx 0)
    have hae2 := ae_pi_bdd F (φ := fun x => x ^ 2 - 1) hB2 (Idx 0)
    calc ∫⁻ r, ENNReal.ofReal (exp (l * PBX 0 r i + 3 * l * Qn 0 r))
          ∂(Measure.pi fun _ : Idx 0 => F)
        ≤ ∫⁻ _r, ENNReal.ofReal (exp (6 * l * B ^ 2)) ∂(Measure.pi fun _ : Idx 0 => F) := by
          apply lintegral_mono_ae
          filter_upwards [hae, hae2] with r h1 h2
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have hq : Qn 0 r = r () ^ 2 + (r () ^ 2 - 1) ^ 2 := by
            simp [Qn]
          have e1 := h1 (); have e2 := h2 ()
          have s1 : r () ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e1 2
          have s2 : (r () ^ 2 - 1) ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e2 2
          simp only [PBX, mul_zero, zero_add, hq]
          nlinarith
      _ = ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ 0 := by simp
  | succ n ih =>
    have hmp := measurePreserving_sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => F)
    have hpt : ∀ (r : Idx (n + 1) → ℝ) (a b : ℝ), a = Qn (n + 1) r →
        exp (l * (a + b) + 3 * l * a) ≤
          exp (l * b + 3 * l * Qn n (fun j => r (Sum.inl j))) *
            exp (6 * l * Qn n (fun j => r (Sum.inr j))) ∧
        exp (l * (a + b) + 3 * l * a) ≤
          exp (6 * l * Qn n (fun j => r (Sum.inl j))) *
            exp (l * b + 3 * l * Qn n (fun j => r (Sum.inr j))) := by
      intro r a b ha
      obtain ⟨hs, hs'⟩ := Qn_split n r
      have hq1 := Qn_nonneg n (fun j => r (Sum.inl j))
      have hq2 := Qn_nonneg n (fun j => r (Sum.inr j))
      rw [← Real.exp_add, ← Real.exp_add]
      constructor
      · apply Real.exp_le_exp.2; rw [ha]; nlinarith
      · apply Real.exp_le_exp.2; rw [ha]; nlinarith
    intro i
    rcases i with i | i
    · calc ∫⁻ r, ENNReal.ofReal (exp (l * PBX (n + 1) r (Sum.inl i) + 3 * l * Qn (n + 1) r))
            ∂(Measure.pi fun _ : Idx (n + 1) => F)
          ≤ ∫⁻ r, (fun p : (Idx n → ℝ) × (Idx n → ℝ) =>
              ENNReal.ofReal (exp (l * PBX n p.1 i + 3 * l * Qn n p.1)) *
                ENNReal.ofReal (exp (6 * l * Qn n p.2))) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)) r)
            ∂(Measure.pi fun _ : Idx n ⊕ Idx n => F) := by
            apply lintegral_mono; intro r
            show ENNReal.ofReal (exp (l * (Qn (n + 1) r + PBX n (fun j => r (Sum.inl j)) i) +
                3 * l * Qn (n + 1) r)) ≤
              ENNReal.ofReal (exp (l * PBX n (fun j => r (Sum.inl j)) i +
                3 * l * Qn n (fun j => r (Sum.inl j)))) *
              ENNReal.ofReal (exp (6 * l * Qn n (fun j => r (Sum.inr j))))
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hpt r _ _ rfl).1
        _ = ∫⁻ p, ENNReal.ofReal (exp (l * PBX n p.1 i + 3 * l * Qn n p.1)) *
                ENNReal.ofReal (exp (6 * l * Qn n p.2))
              ∂((Measure.pi fun _ : Idx n => F).prod (Measure.pi fun _ : Idx n => F)) :=
            hmp.lintegral_comp_emb (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)).measurableEmbedding
              (fun p : (Idx n → ℝ) × (Idx n → ℝ) => ENNReal.ofReal (exp (l * PBX n p.1 i + 3 * l * Qn n p.1)) * ENNReal.ofReal (exp (6 * l * Qn n p.2)))
        _ = (∫⁻ r, ENNReal.ofReal (exp (l * PBX n r i + 3 * l * Qn n r))
                ∂(Measure.pi fun _ : Idx n => F)) *
              ∫⁻ r, ENNReal.ofReal (exp (6 * l * Qn n r)) ∂(Measure.pi fun _ : Idx n => F) :=
            lintegral_prod_mul (hfm n i).aemeasurable (hgm n).aemeasurable
        _ ≤ (ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ n) * 4 := mul_le_mul' (ih i) (hg n)
        _ = ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ (n + 1) := by ring
    · calc ∫⁻ r, ENNReal.ofReal (exp (l * PBX (n + 1) r (Sum.inr i) + 3 * l * Qn (n + 1) r))
            ∂(Measure.pi fun _ : Idx (n + 1) => F)
          ≤ ∫⁻ r, (fun p : (Idx n → ℝ) × (Idx n → ℝ) =>
              ENNReal.ofReal (exp (6 * l * Qn n p.1)) *
                ENNReal.ofReal (exp (l * PBX n p.2 i + 3 * l * Qn n p.2))) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)) r)
            ∂(Measure.pi fun _ : Idx n ⊕ Idx n => F) := by
            apply lintegral_mono; intro r
            show ENNReal.ofReal (exp (l * (Qn (n + 1) r + PBX n (fun j => r (Sum.inr j)) i) +
                3 * l * Qn (n + 1) r)) ≤
              ENNReal.ofReal (exp (6 * l * Qn n (fun j => r (Sum.inl j)))) *
              ENNReal.ofReal (exp (l * PBX n (fun j => r (Sum.inr j)) i +
                3 * l * Qn n (fun j => r (Sum.inr j))))
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hpt r _ _ rfl).2
        _ = ∫⁻ p, ENNReal.ofReal (exp (6 * l * Qn n p.1)) *
                ENNReal.ofReal (exp (l * PBX n p.2 i + 3 * l * Qn n p.2))
              ∂((Measure.pi fun _ : Idx n => F).prod (Measure.pi fun _ : Idx n => F)) :=
            hmp.lintegral_comp_emb (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)).measurableEmbedding
              (fun p : (Idx n → ℝ) × (Idx n → ℝ) => ENNReal.ofReal (exp (6 * l * Qn n p.1)) * ENNReal.ofReal (exp (l * PBX n p.2 i + 3 * l * Qn n p.2)))
        _ = (∫⁻ r, ENNReal.ofReal (exp (6 * l * Qn n r)) ∂(Measure.pi fun _ : Idx n => F)) *
              ∫⁻ r, ENNReal.ofReal (exp (l * PBX n r i + 3 * l * Qn n r))
                ∂(Measure.pi fun _ : Idx n => F) :=
            lintegral_prod_mul (hgm n).aemeasurable (hfm n i).aemeasurable
        _ ≤ 4 * (ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ n) := mul_le_mul' (hg n) (ih i)
        _ = ENNReal.ofReal (exp (6 * l * B ^ 2)) * 4 ^ (n + 1) := by ring

/-- Exponential moment of the Gaussian path sum. -/
theorem momZ : ∀ (n : ℕ) (i : Idx n), ∫⁻ z, ENNReal.ofReal (exp (PZ n z i / 4)) ∂(γZ n) ≤ 2 ^ n
  | 0, i => by
      have := instProbγZ 0
      simp [PZ]
  | n + 1, Sum.inl i => by
      have := instProbγZ n
      have ih := momZ n i
      show ∫⁻ z, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.1 i) / 4))
        ∂((gaussianReal 0 1).prod ((γZ n).prod (γZ n))) ≤ 2 ^ (n + 1)
      have hfun : ∀ z : ℝ × Zn n × Zn n, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.1 i) / 4)) =
          ENNReal.ofReal (exp (z.1 ^ 2 / 4)) * (ENNReal.ofReal (exp (PZ n z.2.1 i / 4)) * 1) := by
        intro z
        rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, add_div]
      simp_rw [hfun]
      have hm1 : Measurable fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)) :=
        (Real.measurable_exp.comp ((measurable_PZ n i).div_const 4)).ennreal_ofReal
      rw [lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (exp (x ^ 2 / 4)))
          (g := fun p : Zn n × Zn n => ENNReal.ofReal (exp (PZ n p.1 i / 4)) * 1) (by fun_prop)
          ((hm1.comp measurable_fst).mul measurable_const).aemeasurable,
        lintegral_prod_mul (f := fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)))
          (g := fun _ : Zn n => (1 : ℝ≥0∞)) hm1.aemeasurable aemeasurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
      calc (∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂gaussianReal 0 1) *
            ∫⁻ x, ENNReal.ofReal (exp (PZ n x i / 4)) ∂γZ n ≤ 2 * 2 ^ n := mul_le_mul' gauss_sq ih
        _ = 2 ^ (n + 1) := by ring
  | n + 1, Sum.inr i => by
      have := instProbγZ n
      have ih := momZ n i
      show ∫⁻ z, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.2 i) / 4))
        ∂((gaussianReal 0 1).prod ((γZ n).prod (γZ n))) ≤ 2 ^ (n + 1)
      have hfun : ∀ z : ℝ × Zn n × Zn n, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.2 i) / 4)) =
          ENNReal.ofReal (exp (z.1 ^ 2 / 4)) * (1 * ENNReal.ofReal (exp (PZ n z.2.2 i / 4))) := by
        intro z
        rw [one_mul, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, add_div]
      simp_rw [hfun]
      have hm1 : Measurable fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)) :=
        (Real.measurable_exp.comp ((measurable_PZ n i).div_const 4)).ennreal_ofReal
      rw [lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (exp (x ^ 2 / 4)))
          (g := fun p : Zn n × Zn n => 1 * ENNReal.ofReal (exp (PZ n p.2 i / 4))) (by fun_prop)
          (measurable_const.mul (hm1.comp measurable_snd)).aemeasurable,
        lintegral_prod_mul (f := fun _ : Zn n => (1 : ℝ≥0∞))
          (g := fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4))) aemeasurable_const hm1.aemeasurable]
      simp only [lintegral_const, measure_univ, one_mul]
      calc (∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂gaussianReal 0 1) *
            ∫⁻ x, ENNReal.ofReal (exp (PZ n x i / 4)) ∂γZ n ≤ 2 * 2 ^ n := mul_le_mul' gauss_sq ih
        _ = 2 ^ (n + 1) := by ring

end P99bcb804

end X69_Mom3

section X70_Path

/-! P6/P7 (part 4): the node bound in global form on the tree, and the path bound for `D`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Transport a split arrangement on `Idx n ⊕ Idx n` to `Fin (2^n) ⊕ Fin (2^n)`. -/
lemma hdG_transfer (n : ℕ) (x : Idx n ⊕ Idx n → ℝ) :
    ∃ y : Fin (2 ^ n) ⊕ Fin (2 ^ n) → ℝ, (∀ φ : ℝ → ℝ, ∑ i, φ (y i) = ∑ j, φ (x j)) ∧
      (∀ i, ∃ j, y i = x j) ∧ pLaw (hdS y) = uLaw (hdG (ι := Idx n) x) := by
  let eq : Idx n ≃ Fin (2 ^ n) := (Fintype.equivFin (Idx n)).trans (finCongr (card_Idx n))
  let E : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Idx n ⊕ Idx n := Equiv.sumCongr eq.symm eq.symm
  refine ⟨fun i => x (E i), fun φ => Equiv.sum_comp E (fun j => φ (x j)), fun i => ⟨E i, rfl⟩, ?_⟩
  have h : hdS (fun i => x (E i)) = hdG (ι := Idx n) x ∘ E.permCongr := by
    funext σ
    simp only [hdS, hdG, Function.comp, Equiv.permCongr_apply]
    rw [← Equiv.sum_comp eq (fun j : Fin (2 ^ n) =>
      x (E (σ (Sum.inl j))) - x (E (σ (Sum.inr j))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [E]
  rw [pLaw_eq_uLaw, h, uLaw_equiv]

/-- Generalised `sum_R`: `R` rearranges the block. -/
lemma sumφ_R (φ : ℝ → ℝ) : ∀ (n : ℕ) (x : Idx n → ℝ) (z : Zn n),
    ∑ i, φ (R n x z i) = ∑ i, φ (x i)
  | 0, x, _ => rfl
  | n + 1, x, (z0, zL, zR) => by
      show ∑ i : Idx n ⊕ Idx n, φ (R (n + 1) x (Zn.mk z0 zL zR) i) = ∑ i : Idx n ⊕ Idx n, φ (x i)
      rw [Fintype.sum_sum_type]
      simp only [R, Sum.elim_inl, Sum.elim_inr]
      rw [sumφ_R φ n, sumφ_R φ n]
      exact halves_sum (ι := Idx n) (fun j => φ (x j)) _

lemma Qn_R (n : ℕ) (x : Idx n → ℝ) (z : Zn n) : Qn n (R n x z) = Qn n x := by
  unfold Qn
  rw [sumφ_R (fun t => t) n x z, sumφ_R (fun t => t ^ 2 - 1) n x z]

lemma abs_hdG_le {ι : Type} [Fintype ι] {K : ℝ} (x : ι ⊕ ι → ℝ) (hx : ∀ i, |x i| ≤ K)
    (σ : Equiv.Perm (ι ⊕ ι)) : |hdG x σ| ≤ Fintype.card ι * (2 * K) := by
  unfold hdG
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset ι), |x (σ (Sum.inl i)) - x (σ (Sum.inr i))| ≤ 2 * K := by
    intro i _
    have h1 := hx (σ (Sum.inl i)); have h2 := hx (σ (Sum.inr i))
    calc _ ≤ |x (σ (Sum.inl i))| + |x (σ (Sum.inr i))| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma m_le_of_sq {m ε t s : ℝ} (hm : 0 < m) (hε : 0 < ε) (h : (ε * m) ^ 2 ≤ t * m) (hts : t ≤ s) :
    m ≤ s / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [le_div_iff₀ hε2]
  have : ε ^ 2 * m ≤ t := by
    have h' : (ε ^ 2 * m) * m ≤ t * m := by nlinarith
    exact le_of_mul_le_mul_right h' hm
  linarith

lemma fin_comb {K C ε N1 m z2 Q E : ℝ} (hK : 0 < K) (hC : 0 < C) (hε : 0 < ε) (hN : 0 ≤ N1)
    (hz : 0 ≤ z2) (hQ : 0 ≤ Q) (hE : E ≤ K * m + (m + z2) / 2)
    (hmb : m ≤ 2 * N1 + (z2 + Q) / ε ^ 2) :
    E ≤ (C + (K + 1) * (2 * N1 + 2 / ε ^ 2) + 1) * (1 + z2 + Q) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have e : (z2 + Q) / ε ^ 2 ≤ 2 / ε ^ 2 * (1 + z2 + Q) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε2]; nlinarith
  have hA : 0 ≤ 2 / ε ^ 2 := by positivity
  have hm' : m ≤ (2 * N1 + 2 / ε ^ 2) * (1 + z2 + Q) := by nlinarith
  have hB : 0 ≤ (2 * N1 + 2 / ε ^ 2) * (1 + z2 + Q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hm' (by linarith : (0 : ℝ) ≤ K + 1)]

/-- KMT (4.12) in global form on the tree: for a bounded block of size `m = 2^(n+1)`, the node
error is at most `C (1 + z0² + Qn)` for every Gaussian `z0`. -/
theorem nodeG (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Idx (n + 1) → ℝ), (∀ i, |x i| ≤ K) → ∀ z0 : ℝ,
      |hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) - √((2 : ℝ) ^ (n + 1)) * z0| ≤
        C * (1 + z0 ^ 2 + Qn (n + 1) x) := by
  obtain ⟨C, ε, N1, hC, hε, hε4, hN1, H⟩ := node_bound K hK
  refine ⟨C + (K + 1) * (2 * N1 + 2 / ε ^ 2) + 1, by positivity, ?_⟩
  intro n x hx z0
  obtain ⟨y, hsum, hyx, hlaw⟩ := hdG_transfer n x
  have hy : ∀ i, |y i| ≤ K := fun i => by obtain ⟨j, hj⟩ := hyx i; rw [hj]; exact hx j
  set m : ℝ := (2 : ℝ) ^ (n + 1) with hm
  have hm0 : 0 < m := by positivity
  have hmc : ((2 * 2 ^ n : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have hsq : √m ^ 2 = m := Real.sq_sqrt hm0.le
  have hsqp : 0 < √m := Real.sqrt_pos.2 hm0
  set U := ∑ i, x i with hU
  set W := ∑ i, (x i ^ 2 - 1) with hW
  have hUy : ∑ i, y i = U := hsum (fun t => t)
  have hWy : ∑ i, (y i ^ 2 - 1) = W := hsum (fun t => t ^ 2 - 1)
  have hQ : Qn (n + 1) x = U ^ 2 / m + W ^ 2 / m := by
    simp only [Qn, hU, hW, hm]; ring
  have hpick : hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) =
      qnt (pLaw (hdS y)) (Phi z0) := by
    rw [hlaw, qnt_pick _ (Phi_pos' z0) (Phi_lt_one z0)]
  have hz2 : (√m * z0) ^ 2 / m = z0 ^ 2 := by
    rw [mul_pow, hsq]; field_simp
  have hU2 : 0 ≤ U ^ 2 / m := by positivity
  have hW2 : 0 ≤ W ^ 2 / m := by positivity
  have hz := sq_nonneg z0
  have hQ0 : 0 ≤ Qn (n + 1) x := Qn_nonneg _ _
  by_cases hgood : N1 ≤ 2 ^ n ∧ |U| ≤ ε * m ∧ |W| ≤ ε * m ∧ |√m * z0| < ε * m
  · obtain ⟨g1, g2, g3, g4⟩ := hgood
    have := H (2 ^ n) g1 y hy (by rw [hUy, hmc]; exact g2) (by rw [hWy, hmc]; exact g3) (√m * z0)
      (by rw [hmc]; exact g4)
    rw [hmc, hUy, hWy, hz2, show √m * z0 / √m = z0 by field_simp] at this
    rw [hpick]
    refine this.trans ?_
    rw [hQ]
    have : 0 ≤ (K + 1) * (2 * N1 + 2 / ε ^ 2) := by positivity
    nlinarith
  · have hcrude : |hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) - √m * z0| ≤
        K * m + (m + z0 ^ 2) / 2 := by
      have h1 := abs_hdG_le (ι := Idx n) x hx (pick (hdG (ι := Idx n) x) (Phi z0))
      rw [card_Idx] at h1
      push_cast at h1
      have h2 : |√m * z0| ≤ (m + z0 ^ 2) / 2 := by
        rw [abs_mul, abs_of_pos hsqp]
        nlinarith [sq_nonneg (√m - |z0|), sq_abs z0]
      have h3 := abs_sub (hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0))) (√m * z0)
      have : (2 : ℝ) ^ n * (2 * K) = K * m := by rw [hm, pow_succ]; ring
      linarith
    have hmb : m ≤ 2 * N1 + (z0 ^ 2 + Qn (n + 1) x) / ε ^ 2 := by
      have hdiv : 0 ≤ (z0 ^ 2 + Qn (n + 1) x) / ε ^ 2 := by positivity
      rcases not_and_or.1 hgood with h | h
      · have : (2 : ℝ) ^ n < N1 := by exact_mod_cast not_le.1 h
        have : m < 2 * N1 := by rw [hm, pow_succ]; linarith
        linarith
      rcases not_and_or.1 h with h | h
      · have hlt : ε * m < |U| := not_le.1 h
        have h5 : (ε * m) ^ 2 ≤ U ^ 2 := by
          rw [← sq_abs U]; exact pow_le_pow_left₀ (by positivity) hlt.le 2
        have h6 : U ^ 2 = U ^ 2 / m * m := by field_simp
        have := m_le_of_sq hm0 hε (t := U ^ 2 / m) (h5.trans h6.le)
          (show U ^ 2 / m ≤ z0 ^ 2 + Qn (n + 1) x by rw [hQ]; linarith)
        linarith
      rcases not_and_or.1 h with h | h
      · have hlt : ε * m < |W| := not_le.1 h
        have h5 : (ε * m) ^ 2 ≤ W ^ 2 := by
          rw [← sq_abs W]; exact pow_le_pow_left₀ (by positivity) hlt.le 2
        have h6 : W ^ 2 = W ^ 2 / m * m := by field_simp
        have := m_le_of_sq hm0 hε (t := W ^ 2 / m) (h5.trans h6.le)
          (show W ^ 2 / m ≤ z0 ^ 2 + Qn (n + 1) x by rw [hQ]; linarith)
        linarith
      · have hle : ε * m ≤ |√m * z0| := not_lt.1 h
        have h5 : (ε * m) ^ 2 ≤ (√m * z0) ^ 2 := by
          rw [← sq_abs (√m * z0)]; exact pow_le_pow_left₀ (by positivity) hle 2
        have h6 : (√m * z0) ^ 2 = z0 ^ 2 * m := by rw [mul_pow, hsq]; ring
        have := m_le_of_sq hm0 hε (t := z0 ^ 2) (h5.trans h6.le)
          (show z0 ^ 2 ≤ z0 ^ 2 + Qn (n + 1) x by linarith)
        linarith
    exact fin_comb hK hC hε (by positivity) hz hQ0 hcrude hmb

end P99bcb804

end X70_Path

section X71_Tail

/-! P6/P7 (part 5): `D ≤ C (n + PZ + PBX ∘ R)` along some leaf, and the exponential tail of `D`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

theorem D_le {K C : ℝ} (hC : 0 < C)
    (hnode : ∀ (n : ℕ) (x : Idx (n + 1) → ℝ), (∀ i, |x i| ≤ K) → ∀ z0 : ℝ,
      |hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) - √((2 : ℝ) ^ (n + 1)) * z0| ≤
        C * (1 + z0 ^ 2 + Qn (n + 1) x)) :
    ∀ (n : ℕ) (x : Idx n → ℝ) (z : Zn n), (∀ i, |x i| ≤ K) →
      ∃ i, D n x z ≤ C * (n + PZ n z i + PBX n (R n x z) i)
  | 0, x, z, _ => ⟨(), by simp [D, PZ, PBX]⟩
  | n + 1, x, (z0, zL, zR), hx => by
      set σ := pick (hdG (ι := Idx n) x) (Phi z0) with hσ
      set xL : Idx n → ℝ := fun i => x (σ (Sum.inl i)) with hxL
      set xR : Idx n → ℝ := fun i => x (σ (Sum.inr i)) with hxR
      obtain ⟨iL, hL⟩ := D_le hC hnode n xL zL (fun i => hx _)
      obtain ⟨iR, hR⟩ := D_le hC hnode n xR zR (fun i => hx _)
      have hN := hnode n x hx z0
      have eD : D (n + 1) x (z0, zL, zR) =
          |hdG (ι := Idx n) x σ - √((2 : ℝ) ^ (n + 1)) * z0| + max (D n xL zL) (D n xR zR) := rfl
      have eQ : Qn (n + 1) (R (n + 1) x (z0, zL, zR)) = Qn (n + 1) x := Qn_R _ _ _
      have ePL : PBX (n + 1) (R (n + 1) x (z0, zL, zR)) (Sum.inl iL) =
          Qn (n + 1) (R (n + 1) x (z0, zL, zR)) + PBX n (R n xL zL) iL := rfl
      have ePR : PBX (n + 1) (R (n + 1) x (z0, zL, zR)) (Sum.inr iR) =
          Qn (n + 1) (R (n + 1) x (z0, zL, zR)) + PBX n (R n xR zR) iR := rfl
      have eZL : PZ (n + 1) (z0, zL, zR) (Sum.inl iL) = z0 ^ 2 + PZ n zL iL := rfl
      have eZR : PZ (n + 1) (z0, zL, zR) (Sum.inr iR) = z0 ^ 2 + PZ n zR iR := rfl
      have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rcases le_total (D n xR zR) (D n xL zL) with h | h
      · refine ⟨Sum.inl iL, ?_⟩
        rw [eD, max_eq_left h, ePL, eQ, eZL, hcast]
        nlinarith
      · refine ⟨Sum.inr iR, ?_⟩
        rw [eD, max_eq_right h, ePR, eQ, eZR, hcast]
        nlinarith

/-- Markov with an exponential. -/
lemma markov_exp {α : Type} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : 0 < c) {M : ℝ≥0∞} (hM : ∫⁻ a, ENNReal.ofReal (exp (c * g a)) ∂μ ≤ M) (s : ℝ) :
    μ {a | s < g a} ≤ M * ENNReal.ofReal (exp (-(c * s))) := by
  have hsub : {a | s < g a} ⊆ {a | ENNReal.ofReal (exp (c * s)) ≤ ENNReal.ofReal (exp (c * g a))} := by
    intro a ha
    have ha' : s < g a := ha
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div ((Real.measurable_exp.comp
    (measurable_const.mul hg)).ennreal_ofReal.aemeasurable)
    (by simpa using Real.exp_pos (c * s)) ENNReal.ofReal_ne_top).trans ?_
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_right hM zero_le

end P99bcb804

end X71_Tail

section X72_Tail2

/-! P7: exponential tail of the path error `D` under `(pi F) ⊗ γZ n`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

theorem D_tail (F : Measure ℝ) [IsProbabilityMeasure F] {K : ℝ} (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (hint2 : Integrable (fun x => x ^ 2) F) :
    ∃ C c A : ℝ, 0 < C ∧ 0 < c ∧ 0 < A ∧ ∀ (n : ℕ) (s : ℝ), 0 ≤ s →
      ((Measure.pi fun _ : Idx n => F).prod (γZ n)) {p | C * (n + 2 * s) < D n p.1 p.2} ≤
        ENNReal.ofReal (A * 8 ^ n * exp (-(c * s))) := by
  obtain ⟨C, hC, hnode⟩ := nodeG K hK
  set B : ℝ := K ^ 2 + K + 1 with hBdef
  have hB0 : 0 < B := by positivity
  have hB1 : ∀ᵐ x ∂F, |x| ≤ B := hsupp.mono fun x hx => by nlinarith [sq_nonneg K]
  have hB2 : ∀ᵐ x ∂F, |x ^ 2 - 1| ≤ B := hsupp.mono fun x hx => by
    have : x ^ 2 ≤ K ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]
  set l : ℝ := 1 / (48 * B ^ 2) with hldef
  have hl0 : 0 < l := by positivity
  have hl : 48 * l * B ^ 2 ≤ 1 := by rw [hldef]; field_simp; rfl
  set E0 : ℝ := exp (6 * l * B ^ 2) with hE0
  set c : ℝ := min (1 / 4) l with hcdef
  have hc0 : 0 < c := lt_min (by norm_num) hl0
  refine ⟨C, c, 1 + E0, hC, hc0, by positivity, ?_⟩
  intro n s hs
  have := instProbγZ n
  set μ := (Measure.pi fun _ : Idx n => F).prod (γZ n) with hμ
  have hbad : μ {p | ¬ ∀ i, |p.1 i| ≤ K} = 0 := by
    have h := (measurePreserving_fst (μ := Measure.pi fun _ : Idx n => F)
      (ν := γZ n)).quasiMeasurePreserving.ae (ae_pi_bdd F (φ := fun x => x) hsupp (Idx n))
    exact ae_iff.1 h
  have hsub : {p : (Idx n → ℝ) × Zn n | C * (n + 2 * s) < D n p.1 p.2} ⊆
      {p | ¬ ∀ i, |p.1 i| ≤ K} ∪
        ⋃ i, ({p | s < PZ n p.2 i} ∪ {p | s < PBX n (R n p.1 p.2) i}) := by
    intro p hp
    have hp' : C * (n + 2 * s) < D n p.1 p.2 := hp
    by_cases hb : ∀ i, |p.1 i| ≤ K
    · right
      obtain ⟨i, hi⟩ := D_le hC hnode n p.1 p.2 hb
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
      have := lt_of_lt_of_le hp' hi
      nlinarith [hcon.1, hcon.2]
    · left; exact hb
  have hz : ∀ i, μ {p | s < PZ n p.2 i} ≤ ENNReal.ofReal (2 ^ n * exp (-(1 / 4 * s))) := by
    intro i
    have e : μ {p | s < PZ n p.2 i} = γZ n {z | s < PZ n z i} :=
      (measurePreserving_snd (μ := Measure.pi fun _ : Idx n => F) (ν := γZ n)).measure_preimage
        (measurableSet_lt measurable_const (measurable_PZ n i)).nullMeasurableSet
    have hmz := momZ n i
    simp_rw [show ∀ z, PZ n z i / 4 = 1 / 4 * PZ n z i from fun z => by ring] at hmz
    rw [e]
    refine (markov_exp (γZ n) (measurable_PZ n i) (by norm_num) hmz s).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hx : ∀ i, μ {p | s < PBX n (R n p.1 p.2) i} ≤
      ENNReal.ofReal (E0 * 4 ^ n * exp (-(l * s))) := by
    intro i
    have e : μ {p | s < PBX n (R n p.1 p.2) i} = (Measure.pi fun _ : Idx n => F) {r | s < PBX n r i} :=
      (rLaw F n).measure_preimage
        (measurableSet_lt measurable_const (measurable_PBX n i)).nullMeasurableSet
    have hmx := momX F hB1 hB2 hm hv hint2 hl0.le hl n i
    have hmx' : ∫⁻ r, ENNReal.ofReal (exp (l * PBX n r i)) ∂(Measure.pi fun _ : Idx n => F) ≤
        ENNReal.ofReal E0 * 4 ^ n := by
      refine le_trans (lintegral_mono fun r => ?_) hmx
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have := Qn_nonneg n r
      nlinarith
    rw [e]
    refine (markov_exp _ (measurable_PBX n i) hl0 hmx' s).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hleaf : ∀ i, μ {p | s < PZ n p.2 i} + μ {p | s < PBX n (R n p.1 p.2) i} ≤
      ENNReal.ofReal ((1 + E0) * 4 ^ n * exp (-(c * s))) := by
    intro i
    refine (add_le_add (hz i) (hx i)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e1 : exp (-(1 / 4 * s)) ≤ exp (-(c * s)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (1 / 4 : ℝ) l])
    have e2 : exp (-(l * s)) ≤ exp (-(c * s)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (1 / 4 : ℝ) l])
    have p24 : (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have hE : 0 < E0 := Real.exp_pos _
    have := mul_le_mul p24 e1 (Real.exp_pos _).le h4.le
    have := mul_le_mul_of_nonneg_left e2 (mul_pos hE h4).le
    nlinarith
  calc μ {p | C * (n + 2 * s) < D n p.1 p.2}
      ≤ μ ({p | ¬ ∀ i, |p.1 i| ≤ K} ∪
          ⋃ i, ({p | s < PZ n p.2 i} ∪ {p | s < PBX n (R n p.1 p.2) i})) := measure_mono hsub
    _ ≤ μ {p | ¬ ∀ i, |p.1 i| ≤ K} +
          μ (⋃ i, ({p | s < PZ n p.2 i} ∪ {p | s < PBX n (R n p.1 p.2) i})) := measure_union_le _ _
    _ ≤ 0 + ∑ i, (μ {p | s < PZ n p.2 i} + μ {p | s < PBX n (R n p.1 p.2) i}) := by
        rw [hbad]
        gcongr
        refine (measure_iUnion_fintype_le μ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact measure_union_le _ _
    _ ≤ 0 + ∑ _i : Idx n, ENNReal.ofReal ((1 + E0) * 4 ^ n * exp (-(c * s))) := by
        gcongr with i; exact hleaf i
    _ = ENNReal.ofReal ((1 + E0) * 8 ^ n * exp (-(c * s))) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, card_Idx, nsmul_eq_mul]
        rw [show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]; push_cast; rfl]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (8 : ℝ) ^ n = 2 ^ n * 4 ^ n by rw [← mul_pow]; norm_num]
        ring

end P99bcb804

end X72_Tail2

section X73_RootJ

/-! P4 (joint form): a law of `(w, x)` with `w ~ N(0,1)`, `x ~ F^{2^n}` and
`Σ x = qnt (sLaw F) (Φ w)` almost surely (KMT (2.6) root coupling, via the conditional law of the
block given its sum). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

theorem root_joint (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    ∃ J : Measure (ℝ × (Idx n → ℝ)), IsProbabilityMeasure J ∧
      J.map Prod.fst = gaussianReal 0 1 ∧ J.map Prod.snd = Measure.pi (fun _ : Idx n => F) ∧
      ∀ᵐ p ∂J, ∑ i, p.2 i = qnt (sLaw F (Idx n)) (Phi p.1) := by
  set P := Measure.pi fun _ : Idx n => F with hP
  set S : (Idx n → ℝ) → ℝ := fun x => ∑ i, x i with hS
  have hSm : Measurable S := measurable_sum' (Idx n)
  set κ := condDistrib (fun x : Idx n → ℝ => x) S P with hκ
  have hdis : (P.map S) ⊗ₘ κ = P.map fun x => (S x, x) :=
    compProd_map_condDistrib (μ := P) (X := S) measurable_id.aemeasurable
  set L := sLaw F (Idx n) with hL
  have hPS : P.map S = L := rfl
  set g : ℝ → ℝ := fun w => qnt L (Phi w) with hg
  have hgm : Measurable g :=
    (measurable_qnt_kernel (Kernel.const ℝ L)).comp (measurable_id.prodMk measurable_id)
  set J := (gaussianReal 0 1) ⊗ₘ (κ.comap g hgm) with hJ
  have hgmap : (gaussianReal 0 1).map g = L := map_qnt_Phi' L
  have hpm : Measurable (Prod.map g (id : (Idx n → ℝ) → (Idx n → ℝ))) := hgm.prodMap measurable_id
  have key : J.map (Prod.map g id) = P.map fun x => (S x, x) := by
    rw [← hdis, hPS]
    ext t ht
    rw [Measure.map_apply hpm ht, Measure.compProd_apply (hpm ht), Measure.compProd_apply ht,
      ← hgmap, lintegral_map (Kernel.measurable_kernel_prodMk_left ht) hgm]
    refine lintegral_congr fun w => ?_
    rw [Kernel.comap_apply]
    rfl
  refine ⟨J, inferInstance, by exact Measure.fst_compProd _ _, ?_, ?_⟩
  · have h1 : J.map Prod.snd = (J.map (Prod.map g id)).map Prod.snd := by
      rw [Measure.map_map measurable_snd hpm]; rfl
    have hm2 : Measurable fun x : Idx n → ℝ => (S x, x) := hSm.prodMk measurable_id
    rw [h1, key, Measure.map_map measurable_snd hm2]
    exact Measure.map_id
  · rw [ae_iff]
    have hset : MeasurableSet {q : ℝ × (Idx n → ℝ) | S q.2 ≠ q.1} :=
      (measurableSet_eq_fun (hSm.comp measurable_snd) measurable_fst).compl
    have e : {p : ℝ × (Idx n → ℝ) | ¬ ∑ i, p.2 i = qnt L (Phi p.1)} =
        Prod.map g id ⁻¹' {q : ℝ × (Idx n → ℝ) | S q.2 ≠ q.1} := rfl
    have hm2 : Measurable fun x : Idx n → ℝ => (S x, x) := hSm.prodMk measurable_id
    rw [e, ← Measure.map_apply hpm hset, key, Measure.map_apply hm2 hset]
    simp

end P99bcb804

end X73_RootJ

section X74_Block

/-! P4 + P7 assembled for one dyadic block (in progress): the root bound for every block size. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Root bound in Gaussian units, for every `n`: `|qnt (sLaw) (Φ w) - √(2^n) w| ≤ C (1 + w²)`. -/
theorem root_all (F : Measure ℝ) [IsProbabilityMeasure F] {K : ℝ} (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (w : ℝ),
      |qnt (sLaw F (Idx n)) (Phi w) - √((2 : ℝ) ^ n) * w| ≤ C * (1 + w ^ 2) := by
  obtain ⟨C0, m0, hC0, hm0, H0⟩ := root_global hK hsupp hm hv
  refine ⟨C0 + K * m0 + m0 + 1, by positivity, ?_⟩
  intro n w
  set M : ℝ := (2 : ℝ) ^ n with hM
  have hM0 : 0 < M := by positivity
  have hsq : √M ^ 2 = M := Real.sq_sqrt hM0.le
  have hsqp : 0 < √M := Real.sqrt_pos.2 hM0
  have hcard : ((Fintype.card (Idx n) : ℕ) : ℝ) = M := by rw [card_Idx]; push_cast; rfl
  have hw2 := sq_nonneg w
  by_cases hbig : m0 ≤ Fintype.card (Idx n)
  · have h := H0 (Idx n) hbig (√M * w)
    rw [hcard, show √M * w / √M = w by field_simp, mul_pow, hsq,
      show M * w ^ 2 / M = w ^ 2 by field_simp] at h
    refine h.trans ?_
    have : 0 ≤ (K * m0 + m0 + 1) * (1 + w ^ 2) := by positivity
    nlinarith
  · have hlt : M < m0 := by
      rw [← hcard]; exact_mod_cast not_le.1 hbig
    have hq := qnt_abs_le (sLaw F (Idx n)) (sLaw_supp hK.le hsupp (Idx n)) (Phi_pos' w)
      (Phi_lt_one w)
    rw [hcard] at hq
    have h2 : |√M * w| ≤ (M + w ^ 2) / 2 := by
      rw [abs_mul, abs_of_pos hsqp]
      nlinarith [sq_nonneg (√M - |w|), sq_abs w]
    have h3 := abs_sub (qnt (sLaw F (Idx n)) (Phi w)) (√M * w)
    have hKM : M * K ≤ m0 * K := mul_le_mul_of_nonneg_right hlt.le hK.le
    have : (0 : ℝ) ≤ C0 * (1 + w ^ 2) := by positivity
    have : (m0 : ℝ) * K ≤ K * m0 * (1 + w ^ 2) := by nlinarith [mul_nonneg hK.le (Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)]
    have : (M + w ^ 2) / 2 ≤ (m0 + 1) * (1 + w ^ 2) := by nlinarith
    nlinarith

lemma gauss_tail (s : ℝ) :
    (gaussianReal 0 1) {w : ℝ | s < w ^ 2} ≤ 2 * ENNReal.ofReal (exp (-(1 / 4 * s))) := by
  refine markov_exp (gaussianReal 0 1) (g := fun w : ℝ => w ^ 2) (by fun_prop) (by norm_num) ?_ s
  refine le_trans (le_of_eq ?_) gauss_sq
  refine lintegral_congr fun w => ?_
  congr 2; ring

lemma measurable_ps (n k : ℕ) : Measurable fun f : Idx n → ℝ => ps n f k := by
  unfold ps; exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- One dyadic block of size `2^n`: a coupling of `pi F` with iid `N(0,1)` whose partial sums
stay within `C (n + s)` except with probability `A 8^n e^{-c s}` (KMT II, Thm 1B per block). -/
theorem block (F : Measure ℝ) [IsProbabilityMeasure F] {K : ℝ} (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (hint2 : Integrable (fun x => x ^ 2) F) :
    ∃ C c A : ℝ, 0 < C ∧ 0 < c ∧ 0 < A ∧ ∀ n : ℕ,
      ∃ Q : Measure ((Idx n → ℝ) × (Idx n → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Idx n => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Idx n => gaussianReal 0 1) ∧
        ∀ s : ℝ, 0 ≤ s → Q {p | ∃ k : ℕ, C * (n + s) < |ps n p.1 k - ps n p.2 k|} ≤
          ENNReal.ofReal (A * 8 ^ n * exp (-(c * s))) := by
  obtain ⟨C0, hC0, H0⟩ := root_all F hK hsupp hm hv
  obtain ⟨C1, c1, A1, hC1, hc1, hA1, H1⟩ := D_tail F hK hsupp hm hv hint2
  refine ⟨8 * C1 + 4 * C0, min c1 (1 / 4), A1 + 2 * exp (1 / 4), by positivity,
    lt_min hc1 (by norm_num), by positivity, ?_⟩
  intro n
  obtain ⟨J, hJp, hJ1, hJ2, hJ3⟩ := root_joint F n
  have := hJp
  set ν : Measure ((ℝ × (Idx n → ℝ)) × Zn n) := J.prod (γZ n) with hν
  set Φm : (ℝ × (Idx n → ℝ)) × Zn n → (Idx n → ℝ) × (Idx n → ℝ) :=
    fun q => (R n q.1.2 q.2, G n (√((2 : ℝ) ^ n) * q.1.1) q.2) with hΦm
  have hR := rLaw F n
  have hG := gLaw n
  have hPS : Measurable (Prod.map Prod.snd id : (ℝ × (Idx n → ℝ)) × Zn n → (Idx n → ℝ) × Zn n) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hPW : Measurable (Prod.map (fun p : ℝ × (Idx n → ℝ) => √((2 : ℝ) ^ n) * p.1) id :
      (ℝ × (Idx n → ℝ)) × Zn n → ℝ × Zn n) :=
    (measurable_const.mul (measurable_fst.comp measurable_fst)).prodMk measurable_snd
  have hmR : Measurable fun q : (ℝ × (Idx n → ℝ)) × Zn n => R n q.1.2 q.2 :=
    hR.measurable.comp hPS
  have hmG : Measurable fun q : (ℝ × (Idx n → ℝ)) × Zn n => G n (√((2 : ℝ) ^ n) * q.1.1) q.2 :=
    (measurable_G n).comp hPW
  have hmΦ : Measurable Φm := hmR.prodMk hmG
  have hXZ : ν.map (Prod.map Prod.snd id) = (Measure.pi fun _ : Idx n => F).prod (γZ n) := by
    have h := Measure.map_prod_map J (γZ n) (f := Prod.snd) (g := id) measurable_snd measurable_id
    rw [Measure.map_id, hJ2] at h; exact h.symm
  have hWZ : ν.map (Prod.map (fun p : ℝ × (Idx n → ℝ) => √((2 : ℝ) ^ n) * p.1) id) =
      (gaussianReal 0 (2 ^ n)).prod (γZ n) := by
    have h := Measure.map_prod_map J (γZ n)
      (f := fun p : ℝ × (Idx n → ℝ) => √((2 : ℝ) ^ n) * p.1) (g := id)
      (measurable_const.mul measurable_fst) measurable_id
    rw [Measure.map_id] at h; rw [← h]; congr 1
    have h2 : J.map (fun p : ℝ × (Idx n → ℝ) => √((2 : ℝ) ^ n) * p.1) =
        (J.map Prod.fst).map (fun w => √((2 : ℝ) ^ n) * w) := by
      rw [Measure.map_map (show Measurable fun w : ℝ => √((2 : ℝ) ^ n) * w by fun_prop) measurable_fst]; rfl
    rw [h2, hJ1, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  have hJν : ν.map Prod.fst = J := by
    rw [hν, Measure.map_fst_prod]; simp
  refine ⟨ν.map Φm, Measure.isProbabilityMeasure_map hmΦ.aemeasurable, ?_, ?_, ?_⟩
  · have e : (ν.map Φm).map Prod.fst =
        (ν.map (Prod.map Prod.snd id)).map (fun p : (Idx n → ℝ) × Zn n => R n p.1 p.2) := by
      rw [Measure.map_map hR.measurable hPS, Measure.map_map measurable_fst hmΦ]; rfl
    rw [e, hXZ, hR.map_eq]
  · have e : (ν.map Φm).map Prod.snd =
        (ν.map (Prod.map (fun p : ℝ × (Idx n → ℝ) => √((2 : ℝ) ^ n) * p.1) id)).map
          (fun p : ℝ × Zn n => G n p.1 p.2) := by
      rw [Measure.map_map (measurable_G n) hPW, Measure.map_map measurable_snd hmΦ]; rfl
    rw [e, hWZ, hG.map_eq]
  intro s hs
  set C := 8 * C1 + 4 * C0 with hC
  set c := min c1 (1 / 4) with hc
  have hbadm : MeasurableSet {p : (Idx n → ℝ) × (Idx n → ℝ) |
      ∃ k : ℕ, C * (n + s) < |ps n p.1 k - ps n p.2 k|} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_lt measurable_const
      (((measurable_ps n k).comp measurable_fst).sub ((measurable_ps n k).comp measurable_snd)).abs
  rw [Measure.map_apply hmΦ hbadm]
  set S1 : Set ((ℝ × (Idx n → ℝ)) × Zn n) := (fun q => q.1.1) ⁻¹' {w : ℝ | s - 1 < w ^ 2} with hS1
  set S2 : Set ((ℝ × (Idx n → ℝ)) × Zn n) :=
    Prod.map Prod.snd id ⁻¹' {p : (Idx n → ℝ) × Zn n | C1 * (n + 2 * s) < D n p.1 p.2} with hS2
  have hae : ∀ᵐ q ∂ν, ∑ i, q.1.2 i = qnt (sLaw F (Idx n)) (Phi q.1.1) := by
    refine ae_of_ae_map (p := fun p : ℝ × (Idx n → ℝ) => ∑ i, p.2 i = qnt (sLaw F (Idx n)) (Phi p.1))
      measurable_fst.aemeasurable ?_
    rw [hJν]; exact hJ3
  have hsub : Φm ⁻¹' {p : (Idx n → ℝ) × (Idx n → ℝ) |
      ∃ k : ℕ, C * (n + s) < |ps n p.1 k - ps n p.2 k|} ≤ᵐ[ν] (S1 ∪ S2 : Set _) := by
    refine hae.mono fun q hq hbad => ?_
    obtain ⟨⟨w, x⟩, z⟩ := q
    obtain ⟨k, hk⟩ := hbad
    have hp := path_bound n x (√((2 : ℝ) ^ n) * w) z k
    have hr := H0 n w
    simp only at hq
    rw [← hq] at hr
    by_cases hw : s - 1 < w ^ 2
    · exact Or.inl hw
    · refine Or.inr ?_
      show C1 * (n + 2 * s) < D n x z
      push Not at hw
      have hk' : C * (n + s) < |ps n (R n x z) k - ps n (G n (√((2 : ℝ) ^ n) * w) z) k| := hk
      have h1 : C0 * (1 + w ^ 2) ≤ C0 * s := mul_le_mul_of_nonneg_left (by linarith) hC0.le
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := mul_nonneg hC1.le hn
      have := mul_nonneg hC1.le hs
      have := mul_nonneg hC0.le hn
      have := mul_nonneg hC0.le hs
      rw [hC] at hk'
      linarith
  have hν1 : ν S1 ≤ 2 * ENNReal.ofReal (exp (-(1 / 4 * (s - 1)))) := by
    have h1 : ν.map (fun q => q.1.1) = gaussianReal 0 1 := by
      have : (fun q : (ℝ × (Idx n → ℝ)) × Zn n => q.1.1) = Prod.fst ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map measurable_fst measurable_fst, hJν, hJ1]
    calc ν S1 ≤ ν.map (fun q => q.1.1) {w : ℝ | s - 1 < w ^ 2} :=
          Measure.le_map_apply (by fun_prop) _
      _ = _ := by rw [h1]
      _ ≤ _ := gauss_tail (s - 1)
  have hν2 : ν S2 ≤ ENNReal.ofReal (A1 * 8 ^ n * exp (-(c1 * s))) := by
    calc ν S2 ≤ ν.map (Prod.map Prod.snd id)
          {p : (Idx n → ℝ) × Zn n | C1 * (n + 2 * s) < D n p.1 p.2} :=
          Measure.le_map_apply hPS.aemeasurable _
      _ = _ := by rw [hXZ]
      _ ≤ _ := H1 n s hs
  calc ν (Φm ⁻¹' _) ≤ ν (S1 ∪ S2) := measure_mono_ae hsub
    _ ≤ ν S1 + ν S2 := measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (exp (-(1 / 4 * (s - 1)))) +
          ENNReal.ofReal (A1 * 8 ^ n * exp (-(c1 * s))) := add_le_add hν1 hν2
    _ ≤ ENNReal.ofReal ((A1 + 2 * exp (1 / 4)) * 8 ^ n * exp (-(c * s))) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have e1 : exp (-(c1 * s)) ≤ exp (-(c * s)) :=
        exp_le_exp.2 (by nlinarith [min_le_left c1 (1 / 4)])
      have e2 : exp (-(1 / 4 * (s - 1))) = exp (1 / 4) * exp (-(1 / 4 * s)) := by
        rw [← exp_add]; ring_nf
      have e3 : exp (-(1 / 4 * s)) ≤ exp (-(c * s)) :=
        exp_le_exp.2 (by nlinarith [min_le_right c1 (1 / 4)])
      have h8 : (1 : ℝ) ≤ 8 ^ n := one_le_pow₀ (by norm_num)
      have hE := exp_pos (-(c * s))
      have hE4 := exp_pos (1 / 4 : ℝ)
      have f1 : A1 * 8 ^ n * exp (-(c1 * s)) ≤ A1 * 8 ^ n * exp (-(c * s)) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      have f2 : 2 * exp (-(1 / 4 * (s - 1))) ≤ 2 * exp (1 / 4) * 8 ^ n * exp (-(c * s)) := by
        rw [e2]
        have : exp (1 / 4) * exp (-(1 / 4 * s)) ≤ exp (1 / 4) * exp (-(c * s)) :=
          mul_le_mul_of_nonneg_left e3 hE4.le
        have : exp (1 / 4) * exp (-(c * s)) ≤ exp (1 / 4) * 8 ^ n * exp (-(c * s)) := by
          have := mul_le_mul_of_nonneg_left h8 (mul_pos hE4 hE).le
          nlinarith
        nlinarith
      nlinarith

end P99bcb804

end X74_Block

section X81_Kr2

/-! R4 / Kr2 (root density): the standardised root density `hR x = sR · fS(sR x)`,
`sR = √(N L2s 0)`: integrability and total mass, its law maps to `sL` (`hR_map`), the far tail
via `xLaw` + `tail_abs` (`hR_far`), and the scalar near conversion `root_near`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sR (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : ℝ :=
  √(Fintype.card ι * L2s G σ 0)

noncomputable def hR (G : Measure ℝ) (ι : Type) [Fintype ι] (σ x : ℝ) : ℝ :=
  sR G ι σ * fS G ι σ (sR G ι σ * x)

section Kr2

variable {G : Measure ℝ} [IsProbabilityMeasure G]

end Kr2

end P99bcb804

end X81_Kr2

section X95_Glue2

/-! P8 part 2: block exponential moment of `Dl`; leaf-order facts for `toNat` and `ps`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma toNat_inj : ∀ (n : ℕ) (i j : Idx n), toNat n i = toNat n j → i = j
  | 0, i, j, _ => Subsingleton.elim i j
  | n + 1, Sum.inl i, Sum.inl j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j h]
  | n + 1, Sum.inl i, Sum.inr j, h => by
      simp only [toNat] at h; have := toNat_lt n i; omega
  | n + 1, Sum.inr i, Sum.inl j, h => by
      simp only [toNat] at h; have := toNat_lt n j; omega
  | n + 1, Sum.inr i, Sum.inr j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j (by omega)]

lemma toNat_surj : ∀ (n r : ℕ), r < 2 ^ n → ∃ i : Idx n, toNat n i = r
  | 0, r, hr => ⟨(), by simp [toNat]; omega⟩
  | n + 1, r, hr => by
      by_cases h : r < 2 ^ n
      · obtain ⟨i, hi⟩ := toNat_surj n r h
        exact ⟨Sum.inl i, by simp [toNat, hi]⟩
      · obtain ⟨i, hi⟩ := toNat_surj n (r - 2 ^ n) (by rw [pow_succ] at hr; omega)
        exact ⟨Sum.inr i, by simp only [toNat, hi]; omega⟩

end P99bcb804

end X95_Glue2

section Tail
open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- In-order positions identify the dyadic index type with `Fin (2^n)`. -/
noncomputable def eFin (n : ℕ) : Idx n ≃ Fin (2 ^ n) :=
  Equiv.ofBijective (fun i => ⟨toNat n i, toNat_lt n i⟩)
    ⟨fun i j h => toNat_inj n i j (congrArg Fin.val h),
     fun r => by
       obtain ⟨i, hi⟩ := toNat_surj n r.1 r.2
       exact ⟨i, Fin.ext hi⟩⟩

lemma eFin_val (n : ℕ) (i : Idx n) : ((eFin n i : Fin (2 ^ n)) : ℕ) = toNat n i := rfl

lemma ps_eFin (n : ℕ) (g : Fin (2 ^ n) → ℝ) (k : ℕ) :
    ps n (fun i => g (eFin n i)) k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) < k), g i := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp (eFin n) (fun j : Fin (2 ^ n) => if (j : ℕ) < k then g j else 0)

lemma pi_eFin (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (Measure.pi (fun _ : Fin (2 ^ n) => F)).map (fun g : Fin (2 ^ n) → ℝ => fun i => g (eFin n i)) =
      Measure.pi (fun _ : Idx n => F) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Idx n => F) (eFin n).symm).map_eq
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Idx n => ℝ) (eFin n).symm) :
      (Fin (2 ^ n) → ℝ) → (Idx n → ℝ)) = fun g i => g (eFin n i) := by
    funext g i
    have := Equiv.piCongrLeft_apply_apply (fun _ : Idx n => ℝ) (eFin n).symm g (eFin n i)
    simp only [Equiv.symm_apply_apply] at this
    rw [← this]; rfl
  rw [hf] at h
  exact h

end P99bcb804

namespace P99bcb804

lemma pi_eFin_symm (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (Measure.pi (fun _ : Idx n => F)).map (fun g : Idx n → ℝ => fun j => g ((eFin n).symm j)) =
      Measure.pi (fun _ : Fin (2 ^ n) => F) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin (2 ^ n) => F) (eFin n)).map_eq
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (2 ^ n) => ℝ) (eFin n)) :
      (Idx n → ℝ) → (Fin (2 ^ n) → ℝ)) = fun g j => g ((eFin n).symm j) := by
    funext g j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (2 ^ n) => ℝ) (eFin n) g ((eFin n).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]; rfl
  rw [hf] at h
  exact h

/-- Export of a dyadic block tail bound from `Idx n` to `Fin (2^n)` in KMT (1.1) form. -/
theorem dy_of_idx (F : Measure ℝ) [IsProbabilityMeasure F] {C c A R b : ℝ} (hC : 0 < C)
    (hc : 0 < c) (hA : 0 < A) (hR : 1 ≤ R) (hb : 0 ≤ b)
    (H : ∀ n : ℕ, ∃ Q : Measure ((Idx n → ℝ) × (Idx n → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.pi (fun _ : Idx n => F) ∧
      Q.map Prod.snd = Measure.pi (fun _ : Idx n => gaussianReal 0 1) ∧
      ∀ s : ℝ, 0 ≤ s → Q {q | ∃ k : ℕ, C * (n + b + s) < |ps n q.1 k - ps n q.2 k|} ≤
        ENNReal.ofReal (A * R ^ n * Real.exp (-(c * s)))) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  set C' : ℝ := C * (2 + Real.log R / c) / Real.log 2 with hC'
  set K : ℝ := 2 * (A * Real.exp (c * b) + Real.exp (c * b)) with hKdef
  refine ⟨C', K, c / C, by positivity, by positivity, by positivity, ?_⟩
  intro N
  obtain ⟨Q, hQp, hQ1, hQ2, hQ3⟩ := H N
  set T : (Idx N → ℝ) × (Idx N → ℝ) → (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) :=
    fun q => (fun j => q.1 ((eFin N).symm j), fun j => q.2 ((eFin N).symm j)) with hT
  have hTm : Measurable T := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd
  refine ⟨Q.map T, Measure.isProbabilityMeasure_map hTm.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hTm]
    have : (Prod.fst ∘ T) = (fun g : Idx N → ℝ => fun j => g ((eFin N).symm j)) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_fst,
      hQ1, pi_eFin_symm]
  · rw [Measure.map_map measurable_snd hTm]
    have : (Prod.snd ∘ T) = (fun g : Idx N → ℝ => fun j => g ((eFin N).symm j)) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_snd,
      hQ2, pi_eFin_symm]
  intro x hx
  have hps : ∀ (g : Idx N → ℝ) (k : ℕ),
      (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), g ((eFin N).symm i)) =
        ps N g k := by
    intro g k
    have := ps_eFin N (fun j => g ((eFin N).symm j)) k
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hmeasF : MeasurableSet {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
          (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} := by
    have : {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
          (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} =
        ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ k ≤ 2 ^ N), {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
          C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
          |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
            (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} := by
      ext q; simp [and_assoc]
    rw [this]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const (by fun_prop)
  rw [Measure.map_apply hTm hmeasF]
  have hQ1' : (Q : Measure _) Set.univ = 1 := measure_univ
  by_cases hxb : x < C * b
  · -- small x: the bound exceeds 1
    refine lt_of_le_of_lt (prob_le_one) ?_
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    have h1 : Real.exp (-(c * b)) ≤ Real.exp (-(c / C) * x) := by
      refine Real.exp_le_exp.2 ?_
      have : c / C * x ≤ c / C * (C * b) := mul_le_mul_of_nonneg_left hxb.le (by positivity)
      rw [show c / C * (C * b) = c * b by field_simp] at this
      linarith
    have h2 : Real.exp (c * b) * Real.exp (-(c * b)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < A * Real.exp (c * b) * Real.exp (-(c / C) * x) := by positivity
    have h4 : Real.exp (c * b) * Real.exp (-(c * b)) ≤ Real.exp (c * b) * Real.exp (-(c / C) * x) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hKdef]
    nlinarith
  · push_neg at hxb
    set s : ℝ := N * (1 + Real.log R / c) + (x - C * b) / C with hs
    have hs0 : 0 ≤ s := by
      have : 0 ≤ (x - C * b) / C := div_nonneg (by linarith) hC.le
      positivity
    have hthr : C * (N + b + s) = C' * Real.log ((2 ^ N : ℕ) : ℝ) + x := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hC', hs]
      field_simp
      ring
    refine lt_of_le_of_lt (measure_mono ?_) (lt_of_le_of_lt (hQ3 s hs0) ?_)
    · intro q hq
      obtain ⟨k, -, -, hk⟩ := hq
      refine ⟨k, ?_⟩
      rw [hthr]
      simpa only [hT, hps] using hk
    · refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
      have hRn : R ^ N = Real.exp (N * Real.log R) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
      have he : R ^ N * Real.exp (-(c * s)) ≤ Real.exp (c * b) * Real.exp (-(c / C) * x) := by
        rw [hRn, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have key : (N : ℝ) * Real.log R + -(c * s) = -(c * N) + (c * b + -(c / C) * x) := by
          rw [hs]; field_simp; ring
        rw [key]
        have : 0 ≤ c * N := by positivity
        linarith
      have h5 : 0 < A * Real.exp (c * b) * Real.exp (-(c / C) * x) := by positivity
      rw [mul_assoc, hKdef]
      have h6 := mul_le_mul_of_nonneg_left he hA.le
      nlinarith [Real.exp_pos (c * b), Real.exp_pos (-(c / C) * x)]

end P99bcb804

end Tail

section BddMain
open MeasureTheory ProbabilityTheory Real Set Filter Topology
namespace P99bcb804
theorem bdd_main (F : Measure ℝ) [IsProbabilityMeasure F] (K : ℝ) (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  have hint2 : Integrable (fun x : ℝ => x ^ 2) F := by
    refine Integrable.of_bound (by fun_prop) (K ^ 2) (hsupp.mono fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  obtain ⟨C, c, A, hC, hc, hA, H⟩ := P99bcb804.block F hK hsupp hm hv hint2
  refine P99bcb804.dy_of_idx F (R := 8) (b := 0) hC hc hA (by norm_num) le_rfl fun n => ?_
  obtain ⟨Q, hQp, hQ1, hQ2, hQ3⟩ := H n
  refine ⟨Q, hQp, hQ1, hQ2, fun s hs => ?_⟩
  simpa only [add_zero] using hQ3 s hs
end P99bcb804
end BddMain

end P99Hyps

open MeasureTheory ProbabilityTheory in

open MeasureTheory ProbabilityTheory in
theorem solution (F : Measure ℝ) [IsProbabilityMeasure F] (K : ℝ) (hK : 0 < K)
    (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  first
  | exact P99bcb804.bdd_main
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.bdd_main <;> assumption)
