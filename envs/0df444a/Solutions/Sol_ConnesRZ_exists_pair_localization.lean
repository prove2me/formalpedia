-- Prove2me | solution 1 for ConnesRZ.exists_pair_localization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T21:17:09.785964+00:00
-- url     : https://prove2.me/submissions/88570564-1d9a-4a44-80d8-44ad78ab96fe

import Theorems.Thm_ConnesRZ_finite_mellin_interpolation
import Theorems.Thm_ConnesRZ_finite_mellin_exceptional
import Theorems.Thm_ConnesRZ_spectral_star_square
import Theorems.Thm_ConnesRZ_explicit_formula

-- Burnol localization; upstream reflection proof-body attribution is preserved below.

namespace ConnesRZFrontier
noncomputable def mirror (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z
end ConnesRZFrontier

/-!
Adapted by proof body from Zeta23/ZetaReflect.lean (Anthropic, Apache-2.0).
Source: Formalpedia commit ae3af9184af2e274c721b1cf3b0dffa09af02c6c,
Definitions.Def_Zeta23_ZetaReflect; original source commit
182afbf851aa42a8ae78507be83f2356d3a33260 in anthropics/zeta-23-lean.
Changes: namespace; ConnesRZ zero predicate/multiplicity; mirror name;
explicit unfolding of analyticOrderNatAt. No exported theorem-stub imports.
Standalone mission adaptation; validated locally against the pinned environment.
-/

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

open ConnesRZ Complex

/-- Classical zero-pair metadata, with analytic multiplicities. -/
theorem ConnesRZ.critical_zero_pair_facts (s : ℂ) (hs : IsCriticalZero s) :
    IsCriticalZero (1 - (starRingEnd ℂ) s) ∧
      zeroMult (1 - (starRingEnd ℂ) s) = zeroMult s ∧ 0 < zeroMult s := by
  refine ⟨ConnesRZReflection.zeta_reflect_zero s hs,
    ConnesRZReflection.zeta_mult_reflect s hs, ?_⟩
  exact lt_of_lt_of_le Nat.zero_lt_one (ConnesRZReflection.one_le_zeroMult s hs)

namespace ConnesRZPos
open MeasureTheory ConnesRZ
lemma isTest_conv {g₁ g₂ : ℝ → ℂ} (h₁ : IsTest g₁) (h₂ : IsTest g₂) :
    IsTest (conv g₁ g₂) := by
  change IsTest (convolution g₁ g₂ (ContinuousLinearMap.mul ℝ ℂ) volume)
  refine ⟨?_, HasCompactSupport.convolution _ h₁.2 h₂.2⟩
  exact HasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞)) _ h₂.2
    (h₁.1.continuous.locallyIntegrable) h₂.1
end ConnesRZPos

open Complex MeasureTheory ConnesRZ ConnesRZPos

noncomputable section
namespace ConnesRZConvolution

lemma integrable_pair (f h : ℝ → ℂ) (hf : IsTest f) (hh : IsTest h) (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => f p.2 * h (p.1 - p.2) *
      Complex.exp ((z - 1 / 2) * p.1)) := by
  have hc : Continuous (fun p : ℝ × ℝ => f p.2 * h (p.1 - p.2) *
      Complex.exp ((z - 1 / 2) * p.1)) := by
    have hfcont := hf.1.continuous
    have hhcont := hh.1.continuous
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro
    (K := (fun q : ℝ × ℝ => (q.1 + q.2, q.1)) '' (tsupport f ×ˢ tsupport h))
    ((hf.2.prod hh.2).image (by fun_prop)) ?_
  rintro ⟨t, s⟩ hts
  by_contra hn
  have hf' : f s ≠ 0 := by intro he; apply hn; simp [he]
  have hh' : h (t - s) ≠ 0 := by intro he; apply hn; simp [he]
  exact hts ⟨(s, t-s), ⟨subset_tsupport _ hf', subset_tsupport _ hh'⟩, by simp⟩

lemma mellin_conv (f h : ℝ → ℂ) (hf : IsTest f) (hh : IsTest h) (z : ℂ) :
    mellinHat (conv f h) z = mellinHat f z * mellinHat h z := by
  unfold mellinHat
  have h1 : ∀ t : ℝ, conv f h t * Complex.exp ((z - 1 / 2) * t) =
      ∫ s : ℝ, f s * h (t-s) * Complex.exp ((z - 1 / 2) * t) := by
    intro t
    unfold conv
    rw [← integral_mul_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
  rw [integral_integral_swap (integrable_pair f h hf hh z)]
  have h2 : ∀ s : ℝ, (∫ t : ℝ, f s * h (t-s) * Complex.exp ((z - 1 / 2) * t)) =
      (f s * Complex.exp ((z - 1 / 2) * s)) *
        ∫ u : ℝ, h u * Complex.exp ((z - 1 / 2) * u) := by
    intro s
    rw [← integral_const_mul]
    have ht := integral_sub_right_eq_self
      (fun u : ℝ => (f s * Complex.exp ((z - 1 / 2) * s)) *
        (h u * Complex.exp ((z - 1 / 2) * u))) s (μ := volume)
    rw [← ht]
    apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have he : Complex.exp ((z - 1 / 2) * s) *
        Complex.exp ((z - 1 / 2) * ((t-s : ℝ) : ℂ)) =
        Complex.exp ((z - 1 / 2) * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (-(f s * h (t-s))) * he
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_mul_const]

def amplify (φ κ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => κ
  | N+1 => conv φ (amplify φ κ N)

lemma isTest_amplify (φ κ : ℝ → ℂ) (hφ : IsTest φ) (hκ : IsTest κ) (N : ℕ) :
    IsTest (amplify φ κ N) := by
  induction N with
  | zero => exact hκ
  | succ N ih => exact isTest_conv hφ ih

lemma mellin_amplify (φ κ : ℝ → ℂ) (hφ : IsTest φ) (hκ : IsTest κ) (N : ℕ) (z : ℂ) :
    mellinHat (amplify φ κ N) z = mellinHat κ z * mellinHat φ z ^ N := by
  induction N with
  | zero => simp [amplify]
  | succ N ih =>
    rw [amplify, mellin_conv φ _ hφ (isTest_amplify φ κ hφ hκ N), ih, pow_succ]
    ring

end ConnesRZConvolution

open scoped BigOperators

namespace ConnesRZAmplification

/-- Burnol's geometric complementary-tail estimate, as an abstract summable family. -/
theorem amplified_tail_bound {ι : Type*} (c b : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖))
    (hb : ∀ i, ‖b i‖ ≤ (1 / 4 : ℝ)) (N : ℕ) :
    Summable (fun i => c i * b i ^ N) ∧
      ‖∑' i, c i * b i ^ N‖ ≤ (1 / 4 : ℝ) ^ N * ∑' i, ‖c i‖ := by
  have hbound : ∀ i, ‖c i * b i ^ N‖ ≤ (1 / 4 : ℝ) ^ N * ‖c i‖ := by
    intro i
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb i) _) (norm_nonneg _)
  have hd : Summable (fun i => (1 / 4 : ℝ) ^ N * ‖c i‖) := hc.mul_left _
  have hf : Summable (fun i => c i * b i ^ N) :=
    Summable.of_norm_bounded hd hbound
  refine ⟨hf, (norm_tsum_le_tsum_norm ?_).trans ?_⟩
  · exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hd
  · calc
      ∑' i, ‖c i * b i ^ N‖ ≤ ∑' i, (1 / 4 : ℝ) ^ N * ‖c i‖ :=
        Summable.tsum_le_tsum hbound
          (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hd) hd
      _ = (1 / 4 : ℝ) ^ N * ∑' i, ‖c i‖ := tsum_mul_left

end ConnesRZAmplification

namespace ConnesRZFrontier
open ConnesRZ Complex MeasureTheory
abbrev CriticalZeros := {s : ℂ // IsCriticalZero s}

def RH : Prop := ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2

def WeilPositive : Prop :=
  ∀ g : ℝ → ℂ, IsTest g → 0 ≤ (weilDistribution (conv g (starInv g))).re

/-- A proved classical dependency, supplied explicitly until its accepted proof
and all transitive imports have been rebuilt without declaration stubs. -/
def ExplicitFormula : Prop :=
  ∀ g : ℝ → ℂ, IsTest g →
    HasSum (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1)
      (weilDistribution g)

def quadraticTerm (g : ℝ → ℂ) (ρ : CriticalZeros) : ℂ :=
  (zeroMult ρ.1 : ℂ) *
    (mellinHat g ρ.1 *
      (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))

lemma quadratic_summable (_hEF : ExplicitFormula) (g : ℝ → ℂ) (hg : IsTest g) :
    Summable (quadraticTerm g) := (ConnesRZ.spectral_star_square g hg).summable
end ConnesRZFrontier

open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZConvolution
open scoped BigOperators

noncomputable section
namespace ConnesRZLocalization

lemma pair_distinct (s : ℂ) (hoff : s.re ≠ 1 / 2) : 1 - (starRingEnd ℂ) s ≠ s := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  exact hoff (by linarith)

lemma choose_base (s : ℂ) : ∃ φ : ℝ → ℂ, IsTest φ ∧
    mellinHat φ s = 1 ∧ mellinHat φ (1 - (starRingEnd ℂ) s) = 1 := by
  classical
  let S : Finset ℂ := {s, 1 - (starRingEnd ℂ) s}
  obtain ⟨φ, hφ, he⟩ := finite_mellin_interpolation
    (fun z : S => (z : ℂ)) Subtype.val_injective (fun _ => (1 : ℂ))
  exact ⟨φ, hφ, he ⟨s, by simp [S]⟩, he ⟨1 - (starRingEnd ℂ) s, by simp [S]⟩⟩

lemma choose_corrector (s : ℂ) (hoff : s.re ≠ 1 / 2) (φ : ℝ → ℂ) (hφ : IsTest φ) :
    ∃ κ : ℝ → ℂ, IsTest κ ∧ mellinHat κ s = 1 ∧
      mellinHat κ (1 - (starRingEnd ℂ) s) = -1 ∧
      ∀ z : ℂ, IsCriticalZero z → (1 / 2 : ℝ) ≤ ‖mellinHat φ z‖ →
        z ≠ s → z ≠ 1 - (starRingEnd ℂ) s → mellinHat κ z = 0 := by
  classical
  let E := {z : ℂ | IsCriticalZero z ∧ (1 / 2 : ℝ) ≤ ‖mellinHat φ z‖}
  have hE : E.Finite := finite_mellin_exceptional φ hφ _ (by norm_num)
  let S : Finset ℂ := insert s (insert (1 - (starRingEnd ℂ) s) hE.toFinset)
  obtain ⟨κ, hκ, he⟩ := finite_mellin_interpolation (fun z : S => (z : ℂ))
    Subtype.val_injective (fun z => if (z : ℂ) = s then (1 : ℂ)
      else if (z : ℂ) = 1 - (starRingEnd ℂ) s then -1 else 0)
  refine ⟨κ, hκ, ?_, ?_, ?_⟩
  · simpa using he ⟨s, by simp [S]⟩
  · simpa [pair_distinct s hoff] using he ⟨1 - (starRingEnd ℂ) s, by simp [S]⟩
  · intro z hz hbound hzs hzσ
    have hm : z ∈ S := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact hE.mem_toFinset.mpr ⟨hz, hbound⟩
    simpa [hzs, hzσ] using he ⟨z, hm⟩

lemma quadratic_amplify (φ κ : ℝ → ℂ) (hφ : IsTest φ) (hκ : IsTest κ)
    (N : ℕ) (ρ : CriticalZeros) :
    quadraticTerm (amplify φ κ N) ρ = quadraticTerm κ ρ *
      (mellinHat φ ρ.1 * (starRingEnd ℂ) (mellinHat φ (1 - (starRingEnd ℂ) ρ.1))) ^ N := by
  simp only [quadraticTerm, mellin_amplify φ κ hφ hκ N, map_mul, map_pow, mul_pow]
  ring

/-- Burnol's pair localization, with the classical explicit formula supplied
as a visible dependency. The infinite complement is controlled for the test
constructed by convolution powers, not for a separately chosen test. -/
theorem pair_localization (hEF : ExplicitFormula) (s : ℂ) (hs : IsCriticalZero s)
    (hoff : s.re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ, IsTest g ∧ IsCriticalZero (1 - (starRingEnd ℂ) s) ∧
      0 < zeroMult s ∧ 0 < zeroMult (1 - (starRingEnd ℂ) s) ∧
      mellinHat g s = 1 ∧ mellinHat g (1 - (starRingEnd ℂ) s) = -1 ∧
      ∃ r : ℝ, r < 1 ∧ HasSum
        (fun ρ : CriticalZeros => if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0
          else (quadraticTerm g ρ).re) r := by
  classical
  obtain ⟨φ, hφ, hφs, hφσ⟩ := choose_base s
  obtain ⟨κ, hκ, hκs, hκσ, hkill⟩ := choose_corrector s hoff φ hφ
  let c : CriticalZeros → ℂ := fun ρ =>
    if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0 else quadraticTerm κ ρ
  let b : CriticalZeros → ℂ := fun ρ =>
    if ‖mellinHat φ ρ.1‖ ≤ (1 / 2 : ℝ) ∧
      ‖mellinHat φ (1 - (starRingEnd ℂ) ρ.1)‖ ≤ (1 / 2 : ℝ) then
      mellinHat φ ρ.1 * (starRingEnd ℂ) (mellinHat φ (1 - (starRingEnd ℂ) ρ.1)) else 0
  have hc : Summable (fun ρ => ‖c ρ‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      (quadratic_summable hEF κ hκ).norm
    intro ρ
    dsimp [c]
    split_ifs <;> simp
  have hb : ∀ ρ, ‖b ρ‖ ≤ (1 / 4 : ℝ) := by
    intro ρ
    dsimp [b]
    split_ifs with h
    · rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg (mellinHat φ ρ.1),
        norm_nonneg (mellinHat φ (1 - (starRingEnd ℂ) ρ.1))]
    · simp
  have hc0 : ∀ ρ : CriticalZeros,
      ¬ (ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s) →
      ¬ (‖mellinHat φ ρ.1‖ ≤ (1 / 2 : ℝ) ∧
        ‖mellinHat φ (1 - (starRingEnd ℂ) ρ.1)‖ ≤ (1 / 2 : ℝ)) →
      quadraticTerm κ ρ = 0 := by
    intro ρ hpair hlarge
    have hρs : ρ.1 ≠ s := fun h => hpair (Or.inl h)
    have hρσ : ρ.1 ≠ 1 - (starRingEnd ℂ) s := fun h => hpair (Or.inr h)
    by_cases ha : ‖mellinHat φ ρ.1‖ ≤ (1 / 2 : ℝ)
    · have hnot : ¬ ‖mellinHat φ (1 - (starRingEnd ℂ) ρ.1)‖ ≤ (1 / 2 : ℝ) :=
        fun h => hlarge ⟨ha, h⟩
      have hmirror := ConnesRZReflection.zeta_reflect_zero ρ.1 ρ.2
      have hms : 1 - (starRingEnd ℂ) ρ.1 ≠ s := by
        intro h
        have hh := congrArg mirror h
        exact hρσ (by simpa [mirror] using hh)
      have hmσ : 1 - (starRingEnd ℂ) ρ.1 ≠ 1 - (starRingEnd ℂ) s := by
        intro h
        have hh := congrArg mirror h
        exact hρs (by simpa [mirror] using hh)
      have hk := hkill _ hmirror (le_of_not_ge hnot) hms hmσ
      change mellinHat κ (1 - (starRingEnd ℂ) ρ.1) = 0 at hk
      simp [quadraticTerm, hk]
    · have hk := hkill ρ.1 ρ.2 (le_of_not_ge ha) hρs hρσ
      simp [quadraticTerm, hk]
  have heq : ∀ N : ℕ, (fun ρ : CriticalZeros =>
      if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then (0 : ℂ)
      else quadraticTerm (amplify φ κ N) ρ) = fun ρ => c ρ * b ρ ^ N := by
    intro N
    funext ρ
    by_cases hp : ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s
    · simp [c, hp]
    · by_cases ht : ‖mellinHat φ ρ.1‖ ≤ (1 / 2 : ℝ) ∧
          ‖mellinHat φ (1 - (starRingEnd ℂ) ρ.1)‖ ≤ (1 / 2 : ℝ)
      · simp only [c, b, if_neg hp, if_pos ht, quadratic_amplify φ κ hφ hκ N]
      · simp only [c, b, if_neg hp, if_neg ht, quadratic_amplify φ κ hφ hκ N, hc0 ρ hp ht, zero_mul]
  have ht : Filter.Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N * ∑' ρ, ‖c ρ‖)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hp.mul_const (∑' ρ, ‖c ρ‖)
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  obtain ⟨hsum, hbound⟩ := ConnesRZAmplification.amplified_tail_bound c b hc hb N
  let g := amplify φ κ N
  let Z : ℂ := ∑' ρ, c ρ * b ρ ^ N
  have hsumg : HasSum (fun ρ : CriticalZeros =>
      if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then (0 : ℂ)
      else quadraticTerm g ρ) Z := by
    rw [heq]
    exact hsum.hasSum
  have hreal : HasSum (fun ρ : CriticalZeros =>
      if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then (0 : ℝ)
      else (quadraticTerm g ρ).re) Z.re := by
    have hr := Complex.reCLM.hasSum hsumg
    change HasSum (fun ρ : CriticalZeros =>
      (if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then (0 : ℂ)
        else quadraticTerm g ρ).re) Z.re at hr
    simpa only [apply_ite, Complex.zero_re] using hr
  have hsσ := ConnesRZReflection.zeta_reflect_zero s hs
  refine ⟨g, isTest_amplify φ κ hφ hκ N, hsσ,
    lt_of_lt_of_le Nat.zero_lt_one (ConnesRZReflection.one_le_zeroMult s hs),
    lt_of_lt_of_le Nat.zero_lt_one (ConnesRZReflection.one_le_zeroMult _ hsσ), ?_, ?_,
    Z.re, (Complex.re_le_norm Z).trans_lt (hbound.trans_lt hN), hreal⟩
  · simp [g, mellin_amplify φ κ hφ hκ N, hκs, hφs]
  · simp [g, mellin_amplify φ κ hφ hκ N, hκσ, hφσ]

end ConnesRZLocalization

open ConnesRZ Complex MeasureTheory

theorem solution (s : ℂ) (hs : IsCriticalZero s) (hoff : s.re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ, IsTest g ∧ IsCriticalZero (1 - (starRingEnd ℂ) s) ∧
      0 < zeroMult s ∧ 0 < zeroMult (1 - (starRingEnd ℂ) s) ∧
      mellinHat g s = 1 ∧ mellinHat g (1 - (starRingEnd ℂ) s) = -1 ∧
      ∃ r : ℝ, r < 1 ∧ HasSum
        (fun ρ : {z : ℂ // IsCriticalZero z} =>
          if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0
          else ((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
            (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))).re) r := by
  exact ConnesRZLocalization.pair_localization ConnesRZ.explicit_formula s hs hoff
