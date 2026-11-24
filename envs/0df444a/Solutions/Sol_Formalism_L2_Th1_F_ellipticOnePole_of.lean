-- Prove2me | solution 1 for Formalism.L2.Th1.F.ellipticOnePole_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:44.202631+00:00
-- url     : https://prove2.me/submissions/e4153411-64f5-4af3-8bcb-92ecacbad568

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eq_of_eventuallyEq_nhdsNE
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_tendsto_add_nhdsNE
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_analyticAt_wZeta
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_analyticAt_zetaExcept
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_zeta_local
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_simple_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open OnePole AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F
theorem _root_.solution (hN : EllipticNoPole) (hE : EllipticEntire) (hq : ZetaQuasi)
    (hL : Legendre) : EllipticOnePole := by
  intro L f p hmer hper hord hp
  obtain ⟨r, k, hk, hfk⟩ := simple_local (hmer p) hp
  set g : ℂ → ℂ := fun w => f w - r * wZeta L (w - p) with hg

  have hB : ∀ z, 0 ≤ meromorphicOrderAt f z →
      ∃ B : ℂ → ℂ, AnalyticAt ℂ B z ∧ f =ᶠ[𝓝[≠] z] B := by
    intro z hz
    cases h : meromorphicOrderAt f z with
    | top =>
      exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.1 h⟩
    | coe n =>
      obtain ⟨B, hBa, -, hfB⟩ := (meromorphicOrderAt_eq_int_iff (hmer z)).1 h
      have hn : 0 ≤ n := by rw [h] at hz; exact_mod_cast hz
      lift n to ℕ using hn
      refine ⟨fun w => (w - z) ^ n * B w, by fun_prop, ?_⟩
      filter_upwards [hfB] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]

  have hloc : ∀ z, ∃ A : ℂ → ℂ, AnalyticAt ℂ A z ∧ g =ᶠ[𝓝[≠] z] A := by
    intro z
    by_cases hz : z - p ∈ L.lattice
    · refine ⟨fun w => k (w - (z - p)) - r * zetaExcept L 0 (w - z) - r * wEta L (z - p), ?_, ?_⟩
      · have h1 : AnalyticAt ℂ (fun w => k (w - (z - p))) z := by
          have hk' : AnalyticAt ℂ k (z - (z - p)) := by simpa using hk
          exact AnalyticAt.comp (f := fun w : ℂ => w - (z - p)) (g := k) hk' (by fun_prop)
        have h2 : AnalyticAt ℂ (fun w => zetaExcept L 0 (w - z)) z := by
          have hz' : AnalyticAt ℂ (zetaExcept L 0) (z - z) := by simpa using analyticAt_zetaExcept L
          exact AnalyticAt.comp (f := fun w : ℂ => w - z) (g := zetaExcept L 0) hz' (by fun_prop)
        exact (h1.sub (analyticAt_const.mul h2)).sub analyticAt_const
      · have hshift : Tendsto (fun w : ℂ => w - (z - p)) (𝓝[≠] z) (𝓝[≠] p) := by
          have h' := tendsto_add_nhdsNE z (-(z - p))
          rw [show z + -(z - p) = p by ring] at h'
          simpa only [← sub_eq_add_neg] using h'
        filter_upwards [hshift.eventually hfk, zeta_local hq L p z hz] with w hw1 hw2
        have hfw : f w = f (w - (z - p)) := by
          have := hper (z - p) hz (w - (z - p))
          rw [sub_add_cancel] at this
          exact this
        show f w - r * wZeta L (w - p) = _
        rw [hfw, hw1, hw2, show w - (z - p) - p = w - z by ring]
        ring
    · obtain ⟨B, hBa, hfB⟩ := hB z (hord z hz)
      refine ⟨fun w => B w - r * wZeta L (w - p), ?_, ?_⟩
      · have : AnalyticAt ℂ (wZeta L) (z - p) := analyticAt_wZeta L _ hz
        exact hBa.sub (analyticAt_const.mul
          (AnalyticAt.comp (f := fun w : ℂ => w - p) (g := wZeta L) this (by fun_prop)))
      · filter_upwards [hfB] with w hw
        show f w - r * wZeta L (w - p) = _
        rw [hw]

  set G : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) g with hG
  have hGA : ∀ z, ∀ A : ℂ → ℂ, AnalyticAt ℂ A z → g =ᶠ[𝓝[≠] z] A → G =ᶠ[𝓝 z] A := by
    intro z A hA hgA
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ ({z}ᶜ : Set ℂ) → g y = A y := eventually_nhdsWithin_iff.1 hgA
    filter_upwards [eventually_eventually_nhds.2 h1, hA.eventually_analyticAt] with w hw hAw
    show limUnder (𝓝[≠] w) g = A w
    apply Tendsto.limUnder_eq
    by_cases hwz : w = z
    · subst hwz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgA.symm
    · have hgw : g =ᶠ[𝓝[≠] w] A := by
        apply eventually_nhdsWithin_of_eventually_nhds
        filter_upwards [hw, isOpen_ne.mem_nhds hwz] with y hy hyz
        exact hy hyz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgw.symm
  have hGd : Differentiable ℂ G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    exact hA.differentiableAt.congr_of_eventuallyEq (hGA z A hA hgA)
  have hgG : ∀ z, g =ᶠ[𝓝[≠] z] G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    filter_upwards [hgA, nhdsWithin_le_nhds (hGA z A hA hgA)] with w h1 h2
    rw [h1, h2]

  have hGq : ∀ ω ∈ L.lattice, ∀ w, G (w + ω) = G w - r * wEta L ω := by
    intro ω hω w
    refine eq_of_eventuallyEq_nhdsNE (g₁ := fun y => G (y + ω)) (g₂ := fun y => G y - r * wEta L ω)
      (hGd.continuous.comp (continuous_add_right ω)).continuousAt
      (hGd.continuous.sub continuous_const).continuousAt ?_
    filter_upwards [(tendsto_add_nhdsNE w ω).eventually (hgG (w + ω)), hgG w,
      eventually_notMem L p w] with y h1 h2 h3
    show G (y + ω) = G y - r * wEta L ω
    rw [← h1, ← h2]
    show f (y + ω) - r * wZeta L (y + ω - p) = f y - r * wZeta L (y - p) - r * wEta L ω
    rw [hper ω hω y, show y + ω - p = (y - p) + ω by ring, hq L ω (y - p) hω h3]
    ring

  have hDd : Differentiable ℂ (deriv G) := fun z => ((hGd.analyticAt z).deriv).differentiableAt
  have hDp : IsPeriodic L (deriv G) := by
    intro ω hω z
    have hfun : (fun y => G (y + ω)) = fun y => G y - r * wEta L ω := funext fun y => hGq ω hω y
    rw [← deriv_comp_add_const, hfun, deriv_sub_const]
  have hDc := hE L (deriv G) hDd hDp
  set a := deriv G 0 with ha
  have hlin : ∀ w, G w = a * w + G 0 := by
    have hH : Differentiable ℂ (fun w => G w - a * w) := hGd.sub (differentiable_id.const_mul a)
    have hH' : ∀ x, deriv (fun w => G w - a * w) x = 0 := by
      intro x
      have h1 : HasDerivAt G a x := by rw [← hDc x]; exact (hGd x).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => a * w) (a * 1) x := (hasDerivAt_id' x).const_mul a
      have h3 : HasDerivAt (fun w => G w - a * w) (a - a * 1) x := h1.sub h2
      rw [h3.deriv]
      ring
    intro w
    have := is_const_of_deriv_eq_zero hH hH' w 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this

  have hr : r = 0 := by
    have e1 := hGq L.ω₁ L.ω₁_mem_lattice 0
    have e2 := hGq L.ω₂ L.ω₂_mem_lattice 0
    rw [zero_add, hlin L.ω₁] at e1
    rw [zero_add, hlin L.ω₂] at e2
    have hs : (if 0 < (L.ω₂ / L.ω₁).im then (1 : ℂ) else -1) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · split_ifs <;> norm_num
      · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have key : r * (wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * e1 - L.ω₁ * e2
    rw [hL L] at key
    exact (mul_eq_zero.1 key).resolve_right hs

  have hGp : IsPeriodic L G := fun ω hω w => by rw [hGq ω hω w, hr]; ring
  refine ⟨G 0, fun z hz => ?_⟩
  have hfG : f =ᶠ[𝓝[≠] z] G := by
    filter_upwards [hgG z] with w hw
    rw [← hw]
    show f w = f w - r * wZeta L (w - p)
    rw [hr]
    ring
  rw [eq_of_eventuallyEq_nhdsNE hz (hGd z).continuousAt hfG]
  exact hE L G hGd hGp z
end Formalism.L2.Th1.F
