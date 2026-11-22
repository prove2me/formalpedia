-- Prove2me | solution 1 for FiniteEnergyPlane.isEmbeddedPlane_of_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:16:27.426416+00:00
-- url     : https://prove2.me/submissions/c91c3523-f716-4ff4-9d8a-590189c0dd0f

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_forall_isolated_of_isBounded_of_isClosed
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_continuous_aCoord_proj_comp
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj



/-! Hryniewicz (2012) § 4.7: `C^∞_loc` limits of embedded fast planes are embedded. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isEmbeddedPlane_of_tendstoCInftyLocOn_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℕ → ℂ → V 1) (v : ℂ → V 1) (hu : ∀ k, IsFastPlane H J (u k))
    (hue : ∀ k, IsEmbeddedPlane (u k)) (hv : IsFastPlane H J v)
    (hconv : JHolomorphic.TendstoCInftyLocOn u v Set.univ) :
    IsEmbeddedPlane v := by
  have hfe := hv.1
  have hsm : ContDiff ℝ ∞ v := contDiffOn_univ.1 hfe.1
  have hv0 : ∀ z, v z ≠ 0 := fun z => hfe.2.1 z trivial
  have hvc : Continuous v := hsm.continuous
  -- `v` is an immersion
  have himm : ∀ z, Function.Injective (fderiv ℝ (proj H ∘ v) z) := by
    intro z a b hab
    by_contra hne
    have := isFastPlane_immersion_transverse H hH J hJ v hv z (a - b) (sub_ne_zero.2 hne) 0
    apply this
    rw [zero_smul, map_sub]
    exact sub_eq_zero.2 hab
  have hvi : ∀ z, Function.Injective (fderiv ℝ v z) := by
    intro z
    have hd : DifferentiableAt ℝ v z := hsm.differentiable (by simp) z
    have hpd : DifferentiableAt ℝ (proj H) (v z) :=
      (contDiffAt_aCoord_proj H hH (v z) (hv0 z)).2.differentiableAt (by simp)
    have hc : fderiv ℝ (proj H ∘ v) z = (fderiv ℝ (proj H) (v z)).comp (fderiv ℝ v z) :=
      fderiv_comp z hpd hd
    have := himm z
    rw [hc, ContinuousLinearMap.coe_comp'] at this
    exact this.of_comp
  -- local injectivity
  have hloc : ∀ a : ℂ, ∃ ε > 0, Set.InjOn v (ball a ε) := by
    intro a
    set D := fderiv ℝ v a with hD
    have hker : LinearMap.ker (D : ℂ →ₗ[ℝ] V 1) = ⊥ := LinearMap.ker_eq_bot.2 (hvi a)
    obtain ⟨Lₗ, hL⟩ := LinearMap.exists_leftInverse_of_injective (D : ℂ →ₗ[ℝ] V 1) hker
    set L : V 1 →L[ℝ] ℂ := LinearMap.toContinuousLinearMap Lₗ with hLdef
    have hLD : L.comp D = ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := by
      ext1 w
      have := congrArg (fun g : ℂ →ₗ[ℝ] ℂ => g w) hL
      simpa [hLdef] using this
    have hs : HasStrictFDerivAt v D a :=
      (hsm.contDiffAt (x := a)).hasStrictFDerivAt (by simp)
    have hg : HasStrictFDerivAt (fun z => L (v z))
        ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) a := by
      rw [← hLD]; exact L.hasStrictFDerivAt.comp a hs
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_left_inverse
    refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
    have h1 := hball x hx
    have h2 := hball y hy
    rw [← h1, ← h2, hxy]
  -- the asymptotic orbit
  obtain ⟨P, hP, hvP⟩ := hv.2.1
  obtain ⟨μ, e, he⟩ :=
    exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd H hH J hJ P v hfe hvP
  obtain ⟨S, hS⟩ := exists_eq_of_endW_eq_of_hasAsymptoticEigenvector H hH J hJ P hP v hvP μ e he
  obtain ⟨d, R0, hR0, hlog⟩ := exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd H P v hvP
  have hac : Continuous (fun z => aCoord H (v z)) :=
    (continuous_aCoord_proj_comp H hH v hv0 hvc).1
  set R1 : ℝ := max R0 (Real.exp (2 * π * S)) with hR1
  have hR1pos : 0 < R1 := lt_of_lt_of_le hR0 (le_max_left _ _)
  -- far points carry no double points
  have hfar : ∀ z w : ℂ, R1 ≤ ‖z‖ → R1 ≤ ‖w‖ → v z = v w → z = w := by
    have hrep : ∀ z : ℂ, R1 ≤ ‖z‖ →
        S ≤ Real.log ‖z‖ / (2 * π) ∧ cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR1pos hz
      have hexp : Real.exp (2 * π * S) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      constructor
      · rw [le_div_iff₀ (by positivity), mul_comm]
        exact (Real.le_log_iff_exp_le hzpos).2 hexp
      · unfold cylInf ccwLoop
        have h1 : 2 * π * (Real.log ‖z‖ / (2 * π)) = Real.log ‖z‖ := by
          field_simp
        have h2 : (2 * π * (Complex.arg z / (2 * π)) : ℝ) = Complex.arg z := by
          field_simp
        rw [h1, h2, Real.exp_log hzpos]
        exact Complex.norm_mul_exp_arg_mul_I z
    intro z w hz hw hzw
    obtain ⟨hsz, hz'⟩ := hrep z hz
    obtain ⟨hsw, hw'⟩ := hrep w hw
    have key := hS _ _ (Complex.arg z / (2 * π)) (Complex.arg w / (2 * π)) hsz hsw (by
      show proj H (v (cylInf _ _)) = proj H (v (cylInf _ _))
      rw [hz', hw', hzw])
    rw [hz', hw'] at key
    exact key
  -- bound for `aCoord ∘ v` on the closed ball of radius `R1`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ R1 → aCoord H (v z) ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R1).exists_bound_of_continuousOn
      hac.continuousOn
    exact ⟨M, fun z hz => le_trans (le_abs_self _)
      (by simpa [Real.norm_eq_abs] using hM z (mem_closedBall_zero_iff.2 hz))⟩
  set R2 : ℝ := max R1 (Real.exp (2 * π * (M + 2 - d) / P.T)) with hR2
  have hbig : ∀ z w : ℂ, z ≠ w → v z = v w → ‖z‖ < R2 := by
    intro z w hne hzw
    by_contra hcon
    push_neg at hcon
    have hz1 : R1 ≤ ‖z‖ := le_trans (le_max_left _ _) hcon
    have hz0 : R0 ≤ ‖z‖ := le_trans (le_max_left _ _) hz1
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR0 hz0
    by_cases hw : R1 ≤ ‖w‖
    · exact hne (hfar z w hz1 hw hzw)
    · push_neg at hw
      have haw : aCoord H (v w) ≤ M := hM w hw.le
      have hl := hlog z hz0
      have hexp : Real.exp (2 * π * (M + 2 - d) / P.T) ≤ ‖z‖ := le_trans (le_max_right _ _) hcon
      have hlogz : 2 * π * (M + 2 - d) / P.T ≤ Real.log ‖z‖ :=
        (Real.le_log_iff_exp_le hzpos).2 hexp
      have hT := P.T_pos
      have hpi : 0 < 2 * π := by positivity
      have hge : M + 2 - d ≤ P.T * Real.log ‖z‖ / (2 * π) := by
        rw [div_le_iff₀ hT] at hlogz
        rw [le_div_iff₀ hpi]
        linarith
      have := (abs_le.1 hl).1
      rw [hzw] at this
      linarith
  -- the set of off-diagonal double points
  set O : Set (ℂ × ℂ) := {p | p.1 ≠ p.2} with hOdef
  have hO : IsOpen O := isOpen_ne_fun continuous_fst continuous_snd
  have hbd : Bornology.IsBounded {p : ℂ × ℂ | p ∈ O ∧ v p.1 = v p.2} := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨R2, fun p hp => ?_⟩
    have h1 := hbig p.1 p.2 hp.1 hp.2
    have h2 := hbig p.2 p.1 (Ne.symm hp.1) hp.2.symm
    rw [Prod.norm_def]
    exact max_le h1.le h2.le
  have hcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ v p.1 = v p.2} := by
    choose ε hε hinj using hloc
    set N : Set (ℂ × ℂ) := ⋃ a : ℂ, ball a (ε a) ×ˢ ball a (ε a) with hN
    have hNo : IsOpen N := isOpen_iUnion fun a => isOpen_ball.prod isOpen_ball
    have hE : IsClosed {p : ℂ × ℂ | v p.1 = v p.2} :=
      isClosed_eq (hvc.comp continuous_fst) (hvc.comp continuous_snd)
    have heq : {p : ℂ × ℂ | p ∈ O ∧ v p.1 = v p.2} = {p : ℂ × ℂ | v p.1 = v p.2} ∩ Nᶜ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, hOdef]
      constructor
      · rintro ⟨hne, hpe⟩
        refine ⟨hpe, fun hpN => ?_⟩
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpN
        exact hne (hinj a ha.1 ha.2 hpe)
      · rintro ⟨hpe, hpN⟩
        refine ⟨fun hdiag => hpN (Set.mem_iUnion.2 ⟨p.1, ?_, ?_⟩), hpe⟩
        · exact mem_ball_self (hε p.1)
        · rw [← hdiag]; exact mem_ball_self (hε p.1)
    rw [heq]
    exact hE.inter hNo.isClosed_compl
  -- injectivity
  refine ⟨fun z₀ w₀ h => ?_, hvi⟩
  by_contra hne
  obtain ⟨ε, hε, hiso⟩ :=
    forall_isolated_of_isBounded_of_isClosed H hH J hJ v v hfe hfe hvi hvi O hO hcl hbd
      (z₀, w₀) hne h
  obtain ⟨z, w, hz, hw, hev⟩ :=
    exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ Set.univ isOpen_univ isOpen_univ
      v v u u hfe hfe (fun z _ => hvi z) (fun w _ => hvi w) (fun k => (hu k).1) (fun k => (hu k).1)
      hconv hconv z₀ w₀ trivial trivial h ⟨ε, hε, hiso⟩
  have hzw : ∀ᶠ k in atTop, w k = z k := hev.mono fun k hk => ((hue k).1 hk).symm
  exact hne (tendsto_nhds_unique hz (hw.congr' hzw))

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℕ → ℂ → V 1) (v : ℂ → V 1) (hu : ∀ k, IsFastPlane H J (u k))
    (hue : ∀ k, IsEmbeddedPlane (u k)) (hv : IsFastPlane H J v)
    (hconv : JHolomorphic.TendstoCInftyLocOn u v Set.univ) :
    IsEmbeddedPlane v :=
  isEmbeddedPlane_of_tendstoCInftyLocOn_aux H hH J hJ u v hu hue hv hconv
