-- Prove2me | solution 1 for ConnesRZ.quartet_coefficient_energy_separation
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T22:25:48.466069+00:00
-- url     : https://prove2.me/submissions/5a22f0f7-9689-45d2-a24f-d9082ae9ed08

import Theorems.Thm_ConnesRZ_coefficient_energy_localization
import Theorems.Thm_ConnesRZ_spectral_star_square
import Theorems.Thm_ConnesRZ_explicit_formula

set_option autoImplicit false
open Complex MeasureTheory ConnesRZ
open scoped BigOperators
noncomputable section
/-
Adapted actual-zeta reflection proof bodies retain their original attribution:
Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
Source: anthropics/formal-math e1a4e6508154ea59f030480661590a9fe3018011,
zeta23/Zeta23/ZetaReflect.lean and Statement/Seam.lean.
Original checkpoint port: namespace and exact Connes zero predicate/multiplicity.
The packet and coefficient-energy bodies are the independently checked Connes
repository construction. Platform adaptation expands the public packet/energy
notation and imports accepted analytic dependencies; no goal stub is imported.
-/
namespace ConnesRZFrontier
abbrev CriticalZeros := {s : ℂ // IsCriticalZero s}
def ExplicitFormula : Prop :=
  ∀ g : ℝ → ℂ, IsTest g →
    HasSum (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1)
      (weilDistribution g)
def quadraticTerm (g : ℝ → ℂ) (ρ : CriticalZeros) : ℂ :=
  (zeroMult ρ.1 : ℂ) *
    (mellinHat g ρ.1 * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))
theorem quadratic_hasSum (_hEF : ExplicitFormula) (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (quadraticTerm g) (weilDistribution (conv g (starInv g))) :=
  ConnesRZ.spectral_star_square g hg
def mirror (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z

@[simp] theorem mirror_mirror (z : ℂ) : mirror (mirror z) = z := by
  simp [mirror] <;> ring


end ConnesRZFrontier
open ConnesRZFrontier
open scoped Topology

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZetaReflect.lean — the two reflection seam obligations of ZetaSeam.

Paper [subsec:weil], verbatim: "The multiset {(γ_ρ, m_ρ)} is invariant under
γ ↦ γ̄ (i.e. ρ ↦ 1 − ρ̄; multiplicities agree because conj ξ(conj s) = ξ(s) =
ξ(1−s))".  These are CLASSICAL facts about ζ, not paper inputs.

Contents:
  • riemannZeta_conj : ζ(s̄) = ζ(s)̄ for s ≠ 1 (Schwarz reflection: Dirichlet
    series on Re s > 1 + the identity theorem on ℂ∖{1});
  • analyticOrderAt_conj_conj : vanishing order is invariant under z ↦ z̄
    conjugation of a function (general lemma);
  • analyticOrderAt_zeta_one_sub : order transport through the functional
    equation ζ(1−s) = 2(2π)^{−s}Γ(s)cos(πs/2)·ζ(s) (prefactor nonvanishing in
    the strip);
  • zeta_reflect_zero, zeta_mult_reflect : the ZetaSeam field shapes.
-/

open Complex
open scoped ComplexConjugate

namespace ConnesRZReflection

/-! ### 1. Schwarz reflection for ζ -/

private lemma zeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  have hs' : (1 : ℝ) < (conj s).re := by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar : star (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := tsum_star
  calc conj (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := hstar
    _ = ∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ s := by
        congr 1
        funext n
        have harg : ((n : ℂ)).arg ≠ Real.pi := by
          rw [Complex.natCast_arg]
          exact Ne.symm Real.pi_ne_zero
        have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
          have h := Complex.cpow_conj (n : ℂ) s harg
          rwa [Complex.conj_natCast] at h
        show star ((1 : ℂ) / (n : ℂ) ^ (conj s)) = 1 / (n : ℂ) ^ s
        rw [star_div₀, star_one, hpow]
        simp

/-- **Schwarz reflection for ζ**: ζ(s̄) = ζ(s)̄ away from the pole. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hU_conn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have hζt : AnalyticOnNhd ℂ (fun z => conj (riemannZeta (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have hd : DifferentiableAt ℂ riemannZeta (conj z) := differentiableAt_riemannZeta hz1
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hagree : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zeta_conj_of_one_lt_re hz
  have heq := hζt.eqOn_of_preconnected_of_eventuallyEq hζ hU_conn h2mem hagree
  have h3 : conj (riemannZeta (conj s)) = riemannZeta s := heq (by simpa using hs)
  calc riemannZeta (conj s) = conj (conj (riemannZeta (conj s))) := (Complex.conj_conj _).symm
    _ = conj (riemannZeta s) := by rw [h3]

/-! ### 2. Vanishing order under conjugation -/

private lemma tendsto_conj_nhds (w : ℂ) :
    Filter.Tendsto (fun z => conj z) (nhds (conj w)) (nhds w) := by
  have h := (Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h

private lemma analyticAt_conj_conj {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(tendsto_conj_nhds w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

/-- The vanishing order of z ↦ conj (f (conj z)) at conj w equals that of f at w. -/
theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(tendsto_conj_nhds w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hgne, ?_⟩
      filter_upwards [(tendsto_conj_nhds w).eventually hfg] with z hz
      have : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by rw [hz]; rfl
      rw [this]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := analyticAt_conj_conj hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']

/-- Order of ζ is conjugation-symmetric away from the pole. -/
theorem analyticOrderAt_zeta_conj {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hne : conj w ≠ 1 := by
    intro h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_one] at h2
    exact hw h2
  have hcong : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne :
      conj w ∈ ({(1 : ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz), Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      = analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := analyticOrderAt_conj_conj _ _

/-! ### 3. Order transport through the functional equation -/

/-- The prefactor of [riemannZeta_one_sub]: E(s) = 2(2π)^{−s} Γ(s) cos(πs/2). -/
private noncomputable def Efac (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

private lemma two_pi_ne_zero' : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩

private lemma Efac_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : Efac s ≠ 0 := by
  have hsne : ∀ m : ℕ, s ≠ -m := by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_pi_ne_zero']
    exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination (2 : ℂ) * hk
    have hs_eq : s = ((2 * k + 1 : ℤ) : ℂ) := by
      have h3 := mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq, Complex.intCast_re] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
    have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
    omega
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsne
  unfold Efac
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hΓ) hcos

private lemma analyticAt_Efac {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ Efac s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl two_pi_ne_zero')
  have h2 : AnalyticAt ℂ Complex.Gamma s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3 : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4 : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3

/-- Order transport through the functional equation: for w in the open strip,
ord_{1−w} ζ = ord_w ζ. -/
theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[nhds w]
      (Efac * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    have hzne : ∀ n : ℕ, z ≠ -n := by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have hzne1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    show riemannZeta (1 - z) = Efac z * riemannZeta z
    rw [riemannZeta_one_sub hzne hzne1]
    unfold Efac
    ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have hEfac := analyticAt_Efac h0
  have hEord : analyticOrderAt Efac w = 0 :=
    hEfac.analyticOrderAt_eq_zero.mpr (Efac_ne_zero h0 h1)
  calc analyticOrderAt riemannZeta (1 - w)
      = analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (Efac * riemannZeta) w := analyticOrderAt_congr hev
    _ = analyticOrderAt Efac w + analyticOrderAt riemannZeta w := by
        by_cases hζw : AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul hEfac hζw
        · exfalso
          exact hζw (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1 : w ≠ 1 := by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1 : w ∈ ({(1 : ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _ = analyticOrderAt riemannZeta w := by rw [hEord, zero_add]

/-! ### 4. The ZetaSeam reflection fields -/

/-- H-symm (set): ρ ↦ 1 − ρ̄ maps nontrivial zeros to nontrivial zeros. -/
theorem zeta_reflect_zero : ∀ ρ, ConnesRZ.IsCriticalZero ρ → ConnesRZ.IsCriticalZero (ConnesRZFrontier.mirror ρ) := by
  rintro ρ ⟨hzero, h0, h1⟩
  have hρne : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [this] at h0
    simp at h0
  have hrefl_eq : ConnesRZFrontier.mirror ρ = conj (1 - ρ) := by
    unfold ConnesRZFrontier.mirror
    rw [map_sub, map_one]
  constructor
  · -- ζ(ConnesRZFrontier.mirror ρ) = 0
    rw [hrefl_eq, riemannZeta_conj h1subne, riemannZeta_one_sub hρne hρne1, hzero]
    simp
  constructor
  · -- 0 < re
    unfold ConnesRZFrontier.mirror
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · -- re < 1
    unfold ConnesRZFrontier.mirror
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- H-symm (multiplicity): m_{1−ρ̄} = m_ρ. -/
theorem zeta_mult_reflect : ∀ ρ, ConnesRZ.IsCriticalZero ρ → ConnesRZ.zeroMult (ConnesRZFrontier.mirror ρ) = ConnesRZ.zeroMult ρ := by
  rintro ρ ⟨_, h0, h1⟩
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have hρ0 : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [hρ0] at h0
    simp at h0
  have hrefl_eq : ConnesRZFrontier.mirror ρ = conj (1 - ρ) := by
    unfold ConnesRZFrontier.mirror
    rw [map_sub, map_one]
  unfold ConnesRZ.zeroMult analyticOrderNatAt
  rw [hrefl_eq, analyticOrderAt_zeta_conj h1subne, analyticOrderAt_zeta_one_sub h0 h1]

end ConnesRZReflection



open Complex Set Filter Topology ConnesRZ

noncomputable section
namespace ConnesRZReflection

/-- ζ is analytic on ℂ ∖ {1}. -/
lemma riemannZeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- ℂ ∖ {1} is connected. -/
lemma isConnected_compl_one : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1

/-- ζ is not locally identically zero anywhere on ℂ ∖ {1}. -/
lemma analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine riemannZeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    isConnected_compl_one.isPreconnected h2 hs ?_
  rw [(riemannZeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

/-- Seam obligation H-fin. -/
theorem one_le_zeroMult : ∀ ρ, ConnesRZ.IsCriticalZero ρ → 1 ≤ ConnesRZ.zeroMult ρ := by
  intro ρ h
  have hρ1 : ρ ≠ 1 := by
    intro hρ
    have hlt := h.2.2
    rw [hρ] at hlt
    norm_num at hlt
  have han : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop := analyticOrderAt_riemannZeta_ne_top hρ1
  unfold ConnesRZ.zeroMult analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega


end ConnesRZReflection

namespace ConnesRZFrontier

/-- The canonical reflected critical zero, using the recovered analytic proof. -/
def reflectedZero (ρ : CriticalZeros) : CriticalZeros :=
  ⟨mirror ρ.1, ConnesRZReflection.zeta_reflect_zero ρ.1 ρ.2⟩

@[simp] theorem reflectedZero_val (ρ : CriticalZeros) :
    (reflectedZero ρ).1 = mirror ρ.1 := rfl

@[simp] theorem reflectedZero_involutive (ρ : CriticalZeros) :
    reflectedZero (reflectedZero ρ) = ρ := by
  apply Subtype.ext
  exact mirror_mirror ρ.1

@[simp] theorem zeroMult_reflectedZero (ρ : CriticalZeros) :
    zeroMult (reflectedZero ρ).1 = zeroMult ρ.1 :=
  ConnesRZReflection.zeta_mult_reflect ρ.1 ρ.2


end ConnesRZFrontier
namespace ConnesRZQuartet

lemma critical_conj (s : ℂ) (hs : IsCriticalZero s) : IsCriticalZero ((starRingEnd ℂ) s) := by
  have hne : s ≠ 1 := by
    intro h
    have hh := hs.2.2
    simp [h] at hh
  refine ⟨?_, ?_, ?_⟩
  · rw [ConnesRZReflection.riemannZeta_conj hne, hs.1]
    simp
  · simpa using hs.2.1
  · simpa using hs.2.2

def conjugateZero (ρ : CriticalZeros) : CriticalZeros :=
  ⟨(starRingEnd ℂ) ρ.1, critical_conj ρ.1 ρ.2⟩

@[simp] lemma conjugateZero_val (ρ : CriticalZeros) :
    (conjugateZero ρ).1 = (starRingEnd ℂ) ρ.1 := rfl

@[simp] lemma conjugateZero_involutive (ρ : CriticalZeros) :
    conjugateZero (conjugateZero ρ) = ρ := by
  apply Subtype.ext
  simp

lemma reflection_conjugation (ρ : CriticalZeros) :
    reflectedZero (conjugateZero ρ) = conjugateZero (reflectedZero ρ) := by
  apply Subtype.ext
  simp [mirror]

/-- The selected actor is exactly the reflection/conjugation orbit of the actual
zeta zero. It is fixed throughout interpolation and convolution amplification. -/
def quartet (ρ : CriticalZeros) : Finset CriticalZeros :=
  {ρ, conjugateZero ρ, reflectedZero ρ, conjugateZero (reflectedZero ρ)}

lemma mem_quartet (ρ : CriticalZeros) : ρ ∈ quartet ρ := by simp [quartet]

lemma quartet_reflection_closed (ρ : CriticalZeros) :
    ∀ τ ∈ quartet ρ, reflectedZero τ ∈ quartet ρ := by
  intro τ hτ
  simp only [quartet, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl
  · simp [quartet]
  · simp [quartet, reflection_conjugation]
  · simp [quartet]
  · simp [quartet, reflection_conjugation]

/-- Real prescribed values, conjugation compatible and opposite on reflected pairs. -/
def packetValues (s z : ℂ) : ℂ := if z.re = s.re then 1 else -1

lemma negative_pair_values (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∀ τ ∈ quartet ρ, packetValues ρ.1 τ.1 *
      (starRingEnd ℂ) (packetValues ρ.1 (mirror τ.1)) = -1 := by
  have hr : 1 - ρ.1.re ≠ ρ.1.re := by intro h; apply hoff; linarith
  intro τ hτ
  simp only [quartet, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;>
    simp [packetValues, mirror, hr]


end ConnesRZQuartet
namespace ConnesRZEnergy

/-- The actual multiplicity-weighted raw coefficient energy, before any native
Green weighting or Hilbert realization. -/
def coefficientEnergy (g : ℝ → ℂ) (ρ : CriticalZeros) : ℝ :=
  (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2

lemma coefficientEnergy_nonneg (g : ℝ → ℂ) (ρ : CriticalZeros) :
    0 ≤ coefficientEnergy g ρ := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem coefficient_energy_localization (_hEF : ExplicitFormula)
    (S : Finset CriticalZeros) (a : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, IsTest g ∧ (∀ ρ ∈ S, mellinHat g ρ.1 = a ρ.1) ∧
      Summable (fun ρ : CriticalZeros => if ρ ∈ S then 0 else coefficientEnergy g ρ) ∧
      (∑' ρ : CriticalZeros, if ρ ∈ S then 0 else coefficientEnergy g ρ) < ε := by
  simpa only [coefficientEnergy] using ConnesRZ.coefficient_energy_localization S a ε hε

/-- Reflection permutes exactly the same actual zero set. -/
def reflectionEquiv : CriticalZeros ≃ CriticalZeros :=
  Function.Involutive.toPerm reflectedZero reflectedZero_involutive

/-- A complementary product is bounded by the corresponding two individual
energies, with the ACTUAL multiplicities carried through reflection. -/
lemma quadratic_norm_le_half_energy (g : ℝ → ℂ) (ρ : CriticalZeros) :
    ‖quadraticTerm g ρ‖ ≤
      (coefficientEnergy g ρ + coefficientEnergy g (reflectedZero ρ)) / 2 := by
  have hm : (0 : ℝ) ≤ zeroMult ρ.1 := Nat.cast_nonneg _
  have hs := sq_nonneg (‖mellinHat g ρ.1‖ - ‖mellinHat g (mirror ρ.1)‖)
  have hmult := ConnesRZReflection.zeta_mult_reflect ρ.1 ρ.2
  simp only [quadraticTerm, coefficientEnergy, norm_mul, Complex.norm_natCast,
    Complex.norm_conj, reflectedZero_val, hmult]
  change (zeroMult ρ.1 : ℝ) * (‖mellinHat g ρ.1‖ * ‖mellinHat g (mirror ρ.1)‖) ≤ _
  have hh : ‖mellinHat g ρ.1‖ * ‖mellinHat g (mirror ρ.1)‖ ≤
      (‖mellinHat g ρ.1‖ ^ 2 + ‖mellinHat g (mirror ρ.1)‖ ^ 2) / 2 := by nlinarith [hs]
  calc
    _ ≤ (zeroMult ρ.1 : ℝ) *
        ((‖mellinHat g ρ.1‖ ^ 2 + ‖mellinHat g (mirror ρ.1)‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hh hm
    _ = _ := by ring

/-- The entire complementary absolute quadratic sum is at most the
complementary raw coefficient energy. This closes the coefficient/product gap
without dropping any positive or negative background actor. -/
theorem full_tail_le_coefficient_energy (g : ℝ → ℂ) (S : Finset CriticalZeros)
    (hS : ∀ ρ ∈ S, reflectedZero ρ ∈ S)
    (he : Summable (fun ρ : CriticalZeros => if ρ ∈ S then 0 else coefficientEnergy g ρ)) :
    Summable (fun ρ : CriticalZeros => ‖if ρ ∈ S then 0 else quadraticTerm g ρ‖) ∧
      (∑' ρ : CriticalZeros, ‖if ρ ∈ S then 0 else quadraticTerm g ρ‖) ≤
        ∑' ρ : CriticalZeros, if ρ ∈ S then 0 else coefficientEnergy g ρ := by
  classical
  let e : CriticalZeros → ℝ := fun ρ => if ρ ∈ S then 0 else coefficientEnergy g ρ
  have hmem : ∀ ρ, reflectedZero ρ ∈ S ↔ ρ ∈ S := by
    intro ρ
    constructor
    · intro h
      simpa using hS (reflectedZero ρ) h
    · exact hS ρ
  have he' : Summable e := he
  have her : Summable (fun ρ => e (reflectedZero ρ)) :=
    he'.comp_injective (fun a b h => by
      have hh := congrArg reflectedZero h
      simpa only [reflectedZero_involutive] using hh)
  have hd : Summable (fun ρ => (e ρ + e (reflectedZero ρ)) / 2) :=
    (he.add her).div_const 2
  have hb : ∀ ρ : CriticalZeros, ‖if ρ ∈ S then 0 else quadraticTerm g ρ‖ ≤
      (e ρ + e (reflectedZero ρ)) / 2 := by
    intro ρ
    by_cases hp : ρ ∈ S
    · simp [e, hp, (hmem ρ).mpr hp]
    · have hr : reflectedZero ρ ∉ S := fun h => hp ((hmem ρ).mp h)
      simpa only [e, if_neg hp, if_neg hr] using quadratic_norm_le_half_energy g ρ
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hd
  refine ⟨hs, (hs.tsum_le_tsum hb hd).trans_eq ?_⟩
  rw [tsum_div_const]
  rw [Summable.tsum_add he her]
  have hr : (∑' ρ, e (reflectedZero ρ)) = ∑' ρ, e ρ :=
    reflectionEquiv.tsum_eq e
  rw [hr]
  ring

/-- One witness controls individual complementary coefficient energy and the
full arithmetic negative margin simultaneously. This is a global support
statement, not an endpoint localization or a native Green-weight attachment. -/
theorem quartet_coefficient_energy_separation (hEF : ExplicitFormula)
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ, IsTest g ∧
      (∀ τ ∈ ConnesRZQuartet.quartet ρ,
        mellinHat g τ.1 = ConnesRZQuartet.packetValues ρ.1 τ.1) ∧
      Summable (fun τ : CriticalZeros =>
        if τ ∈ ConnesRZQuartet.quartet ρ then 0 else coefficientEnergy g τ) ∧
      (∑' τ : CriticalZeros,
        if τ ∈ ConnesRZQuartet.quartet ρ then 0 else coefficientEnergy g τ) < 1 / 2 ∧
      (∑' τ : CriticalZeros,
        ‖if τ ∈ ConnesRZQuartet.quartet ρ then 0 else quadraticTerm g τ‖) < 1 / 2 ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) := by
  classical
  let S := ConnesRZQuartet.quartet ρ
  have hS := ConnesRZQuartet.quartet_reflection_closed ρ
  obtain ⟨g, hg, he, hsum, hsmall⟩ := coefficient_energy_localization hEF S
    (ConnesRZQuartet.packetValues ρ.1) (1 / 2) (by norm_num)
  obtain ⟨hsumQ, hbound⟩ := full_tail_le_coefficient_energy g S hS hsum
  have hsmallQ := hbound.trans_lt hsmall
  have hterm : ∀ τ ∈ S, quadraticTerm g τ = -(zeroMult τ.1 : ℂ) := by
    intro τ hτ
    have hem := he (reflectedZero τ) (hS τ hτ)
    change mellinHat g (mirror τ.1) = ConnesRZQuartet.packetValues ρ.1 (mirror τ.1) at hem
    change (zeroMult τ.1 : ℂ) *
      (mellinHat g τ.1 * (starRingEnd ℂ) (mellinHat g (mirror τ.1))) = _
    rw [he τ hτ, hem, ConnesRZQuartet.negative_pair_values ρ hoff τ hτ]
    ring
  have hpacket : (∑ τ ∈ S, quadraticTerm g τ).re =
      -(∑ τ ∈ S, (zeroMult τ.1 : ℝ)) := by
    rw [Complex.re_sum]
    calc
      _ = ∑ τ ∈ S, -(zeroMult τ.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro τ hτ
        rw [hterm τ hτ]
        simp
      _ = _ := Finset.sum_neg_distrib _
  have hmass : (1 : ℝ) ≤ ∑ τ ∈ S, (zeroMult τ.1 : ℝ) := by
    have hm : (1 : ℝ) ≤ zeroMult ρ.1 := by
      exact_mod_cast ConnesRZReflection.one_le_zeroMult ρ.1 ρ.2
    exact hm.trans (Finset.single_le_sum (fun τ _ => Nat.cast_nonneg (zeroMult τ.1))
      (ConnesRZQuartet.mem_quartet ρ))
  let q : CriticalZeros → ℂ := fun τ => if τ ∈ S then 0 else quadraticTerm g τ
  have hhead : HasSum (fun τ : CriticalZeros => if τ ∈ S then quadraticTerm g τ else 0)
      (∑ τ ∈ S, quadraticTerm g τ) := by
    convert hasSum_sum_of_ne_finset_zero (L := .unconditional CriticalZeros) (s := S)
      (f := fun τ : CriticalZeros => if τ ∈ S then quadraticTerm g τ else 0)
      (fun τ hτ => by simp [hτ]) using 1
    simp
  have htail : Summable q := hsumQ.of_norm
  have hfull : HasSum (quadraticTerm g) ((∑ τ ∈ S, quadraticTerm g τ) + ∑' τ, q τ) := by
    convert hhead.add htail.hasSum using 1
    funext τ
    dsimp [q]
    split_ifs <;> simp
  have hW := hfull.unique (quadratic_hasSum hEF g hg)
  have hreal := congrArg Complex.re hW
  simp only [Complex.add_re] at hreal
  rw [hpacket] at hreal
  have htailre : (∑' τ, q τ).re < 1 / 2 :=
    (Complex.re_le_norm _).trans_lt ((norm_tsum_le_tsum_norm hsumQ).trans_lt hsmallQ)
  refine ⟨g, hg, he, hsum, hsmall, hsmallQ, ?_⟩
  linarith

end ConnesRZEnergy

theorem solution (s : ℂ) (hs : IsCriticalZero s) (hoff : s.re ≠ 1 / 2) :
    let Q : Finset ℂ := {s, (starRingEnd ℂ) s, 1 - (starRingEnd ℂ) s, 1 - s}
    ∃ g : ℝ → ℂ, IsTest g ∧
      (∀ z ∈ Q, mellinHat g z = if z.re = s.re then 1 else -1) ∧
      Summable (fun ρ : {z : ℂ // IsCriticalZero z} =>
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < 1 / 2 ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        ‖if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℂ) *
          (mellinHat g ρ.1 * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))‖) < 1 / 2 ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) := by
  classical
  let ρ : CriticalZeros := ⟨s, hs⟩
  let S := ConnesRZQuartet.quartet ρ
  let Q : Finset ℂ := {s, (starRingEnd ℂ) s, 1 - (starRingEnd ℂ) s, 1 - s}
  change ∃ g : ℝ → ℂ, IsTest g ∧
      (∀ z ∈ Q, mellinHat g z = if z.re = s.re then 1 else -1) ∧
      Summable (fun ρ : {z : ℂ // IsCriticalZero z} =>
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < 1 / 2 ∧
      (∑' ρ : {z : ℂ // IsCriticalZero z},
        ‖if ρ.1 ∈ Q then 0 else (zeroMult ρ.1 : ℂ) *
          (mellinHat g ρ.1 * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))‖) < 1 / 2 ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2)
  have hQ : Q = S.image Subtype.val := by
    simp [Q, S, ConnesRZQuartet.quartet, ρ, ConnesRZQuartet.conjugateZero,
      reflectedZero, mirror]
  have hmem : ∀ τ : CriticalZeros, τ.1 ∈ Q ↔ τ ∈ S := by
    intro τ
    rw [hQ]
    constructor
    · intro h
      obtain ⟨ξ, hξ, he⟩ := Finset.mem_image.mp h
      exact Subtype.ext he ▸ hξ
    · intro h
      exact Finset.mem_image.mpr ⟨τ, h, rfl⟩
  obtain ⟨g, hg, he, hsum, hsmall, hsmallQ, hnegative⟩ :=
    ConnesRZEnergy.quartet_coefficient_energy_separation ConnesRZ.explicit_formula ρ hoff
  refine ⟨g, hg, ?_, ?_, ?_, ?_, hnegative⟩
  · intro z hz
    rw [hQ] at hz
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hz
    exact he τ hτ
  · simpa only [hmem, ConnesRZEnergy.coefficientEnergy] using hsum
  · simpa only [hmem, ConnesRZEnergy.coefficientEnergy] using hsmall
  · simpa only [hmem, quadraticTerm] using hsmallQ
