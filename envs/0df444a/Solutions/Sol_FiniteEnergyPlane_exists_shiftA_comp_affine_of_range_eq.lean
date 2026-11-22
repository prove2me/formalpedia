-- Prove2me | solution 1 for FiniteEnergyPlane.exists_shiftA_comp_affine_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T10:05:20.253653+00:00
-- url     : https://prove2.me/submissions/4661d955-9985-4824-b63b-cbda272a0cd0

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA
import Theorems.Thm_FiniteEnergyPlane_forall_ne_shiftA_of_forall_norm_lt
import Theorems.Thm_FiniteEnergyPlane_exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_eq_of_aCoord_eq_of_proj_eq
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_exists_eq_mul_add_of_norm_le_mul_add
import Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd



/-!
# Hryniewicz Lemma 6.25 (`exists_shiftA_comp_affine_of_range_eq`): glue

* 6.24 gives that `proj ∘ u`, `proj ∘ v` miss `x(ℝ)`; the far bound and the sup argument of 6.23
  give a `τ₀` such that `u` meets no translate `τ · v` with `τ ≠ τ₀`;
* equal projected images then give `ψ` with `u (ψ w) = (τ₀ · v) w` for all `w`;
* every intersection of `τ₀ · v` and `u` is non-isolated (persistence), so McDuff 2.7 makes `ψ`
  locally a holomorphic map, hence entire (`u` injective);
* the `ℝ`-coordinates grow like `T log |z| / 2π` at `∞`, so `|ψ w| ≤ C |w| + K`, and `ψ` is affine.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem ei_shiftA_zero {n : ℕ} (u : ℂ → V n) : shiftA 0 u = u := by
  funext z; simp [shiftA]

theorem ei_fderiv_shiftA_inj {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (c : ℝ) (z : ℂ)
    (h : Function.Injective (fderiv ℝ u z)) : Function.Injective (fderiv ℝ (shiftA c u) z) := by
  have e : shiftA c u = Real.exp (2 * c) • u := rfl
  rw [e, fderiv_const_smul (hu.differentiable (by simp) z)]
  intro a b hab
  simp only [ContinuousLinearMap.smul_apply] at hab
  exact h ((smul_right_injective _ (Real.exp_pos _).ne') hab)

theorem ei_swap {n : ℕ} {f g : ℂ → V n} {τ : ℝ} {z w : ℂ} (h : f z = shiftA τ g w) :
    g w = shiftA (-τ) f z := by
  show g w = Real.exp (2 * -τ) • f z
  rw [h]
  simp only [shiftA]
  rw [smul_smul, ← Real.exp_add, show 2 * -τ + 2 * τ = 0 by ring, Real.exp_zero, one_smul]

theorem ei_lim (a : ℂ) (b : ℕ → ℂ) (hb : ∀ k : ℕ, b k ∈ ball a (1 / ((k : ℝ) + 1))) :
    Tendsto b atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun k hk => lt_of_lt_of_le (mem_ball.1 (hb k)) ?_⟩
  have : ((N : ℝ) + 1) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  exact le_trans (one_div_le_one_div_of_le (by positivity) this) hN.le

theorem exists_shiftA_comp_affine_of_range_eq_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (hrange : Set.range (proj H ∘ u) = Set.range (proj H ∘ v)) :
    ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧ ∀ z, u (A * z + B) = shiftA c v z := by
  have humiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz u hu huP hue
  have hvmiss := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz v hv hvP hve
  have hfu := hu.1
  have hfv := hv.1
  have hsu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfu.1
  have hsv : ContDiff ℝ ∞ v := contDiffOn_univ.1 hfv.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  have hv0 : ∀ z, v z ≠ 0 := fun z => hfv.2.1 z trivial
  have hui := hue.2
  have hvi := hve.2
  -- the distinguished translation `τ₀`
  obtain ⟨τ₀, hF⟩ :=
    exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane H hH J hJ P u v hu huP hv hvP humiss hvmiss
  have hpos := forall_ne_shiftA_of_forall_norm_lt H hH J hJ u v hu hv hui hvi τ₀ hF
  have hF' : ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (w z : ℂ), v w = shiftA τ u z → ε ≤ |τ - -τ₀| →
      ‖w‖ < R ∧ ‖z‖ < R := by
    intro ε hε
    obtain ⟨R, hR⟩ := hF ε hε
    refine ⟨R, fun τ w z h hτ => ?_⟩
    have h' : u z = shiftA (-τ) v w := ei_swap h
    have := hR (-τ) z w h' (by rwa [show -τ - τ₀ = -(τ - -τ₀) by ring, abs_neg])
    exact ⟨this.2, this.1⟩
  have hneg := forall_ne_shiftA_of_forall_norm_lt H hH J hJ v u hv hu hvi hui (-τ₀) hF'
  have hne : ∀ τ ≠ τ₀, ∀ z w, u z ≠ shiftA τ v w := by
    intro τ hτ z w h
    rcases lt_or_gt_of_ne hτ with hl | hl
    · exact hneg (-τ) (by linarith) w z (ei_swap h)
    · exact hpos τ hl z w h
  -- equal projections force the translation `τ₀`
  have hray : ∀ z w, proj H (u z) = proj H (v w) → u z = shiftA τ₀ v w := by
    intro z w h
    set τ := aCoord H (u z) - aCoord H (v w) with hτdef
    have hs := proj_aCoord_exp_smul H hH τ (v w) (hv0 w)
    have hτ : u z = shiftA τ v w :=
      eq_of_aCoord_eq_of_proj_eq H hH (hu0 z) (smul_ne_zero (Real.exp_pos _).ne' (hv0 w))
        (by show aCoord H (u z) = aCoord H (Real.exp (2 * τ) • v w); rw [hs.2]; ring)
        (by show proj H (u z) = proj H (Real.exp (2 * τ) • v w); rw [hs.1]; exact h)
    by_cases e : τ = τ₀
    · rw [← e]; exact hτ
    · exact absurd hτ (hne τ e z w)
  have hex : ∀ w, ∃ z, u z = shiftA τ₀ v w := by
    intro w
    have hm : proj H (v w) ∈ Set.range (proj H ∘ u) := hrange ▸ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, hray z w hz⟩
  choose ψ hψ using hex
  -- non-isolated intersections
  set V' : ℂ → V 1 := shiftA τ₀ v with hV'
  have hfV : IsFiniteEnergyCurve H J Set.univ V' := (isFastPlane_shiftA H hH J hJ v hv τ₀).1
  have hVi : ∀ w, Function.Injective (fderiv ℝ V' w) := fun w =>
    ei_fderiv_shiftA_inj v hsv τ₀ w (hvi w)
  have hnon : ∀ z w, u z = V' w → ∀ ε > 0, ∃ z' ∈ ball z ε, ∃ w' ∈ ball w ε,
      u z' = V' w' ∧ (z', w') ≠ (z, w) := by
    intro z w hzw ε hε
    by_contra hcon
    push_neg at hcon
    have hiso : ∃ ε > 0, ∀ z' ∈ ball z ε, ∀ w' ∈ ball w ε, u z' = V' w' → z' = z ∧ w' = w :=
      ⟨ε, hε, fun z' hz' w' hw' h => Prod.ext_iff.1 (hcon z' hz' w' hw' h)⟩
    have hcu' : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => shiftA 0 u) (shiftA 0 u)
        Set.univ :=
      tendstoCInftyLocOn_shiftA u hsu (fun _ => 0) 0 tendsto_const_nhds Set.univ
    rw [ei_shiftA_zero] at hcu'
    have hc : Tendsto (fun k : ℕ => τ₀ + 1 / ((k : ℝ) + 1)) atTop (𝓝 τ₀) := by
      have := (tendsto_const_nhds (x := τ₀)).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at this
    have hcv' := tendstoCInftyLocOn_shiftA v hsv (fun k : ℕ => τ₀ + 1 / ((k : ℝ) + 1)) τ₀ hc
      Set.univ
    obtain ⟨zs, ws, -, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ
      Set.univ isOpen_univ isOpen_univ u V' (fun _ => u)
      (fun k => shiftA (τ₀ + 1 / ((k : ℝ) + 1)) v) hfu hfV (fun z _ => hui z)
      (fun w _ => hVi w) (fun _ => hfu) (fun k => (isFastPlane_shiftA H hH J hJ v hv _).1)
      hcu' hcv' z w trivial trivial hzw hiso
    obtain ⟨k, hk⟩ := hev.exists
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact hne _ (by linarith : τ₀ < τ₀ + 1 / ((k : ℝ) + 1)).ne' _ _ hk
  -- `ψ` is entire
  have hdiff : Differentiable ℂ ψ := by
    intro w
    choose w' hw' z' hz' heq hne' using fun k : ℕ =>
      hnon (ψ w) w (hψ w) (1 / ((k : ℝ) + 1)) (by positivity)
    have hne'' : ∀ k, (z' k, w' k) ≠ (w, ψ w) := by
      intro k hh
      apply hne' k
      rw [Prod.mk.injEq] at hh ⊢
      exact ⟨hh.2, hh.1⟩
    obtain ⟨ε, hε, φ, hφd, -, -, -, hEq⟩ :=
      exists_holomorphic_eqOn_of_accPt_intersection H hH J hJ Set.univ Set.univ isOpen_univ
        isOpen_univ V' u hfV hfu (fun w _ => hVi w) (fun z _ => hui z) w (ψ w) trivial trivial
        z' w' (ei_lim w z' hz') (ei_lim (ψ w) w' hw') hne'' (fun k => (heq k).symm)
    have hev : ψ =ᶠ[𝓝 w] φ := by
      filter_upwards [ball_mem_nhds w hε] with y hy
      apply hue.1
      rw [hψ y]
      exact hEq hy
    exact (hφd.differentiableAt (ball_mem_nhds w hε)).congr_of_eventuallyEq hev
  -- growth of `ψ`
  have ha : ∀ w, aCoord H (u (ψ w)) = aCoord H (v w) + τ₀ := by
    intro w
    rw [hψ w]
    exact (proj_aCoord_exp_smul H hH τ₀ (v w) (hv0 w)).2
  obtain ⟨du, Ru, hRu, hgu⟩ := exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd H P u huP
  obtain ⟨dv, Rv, hRv, hgv⟩ := exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd H P v hvP
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) Rv).exists_bound_of_continuousOn
    hdiff.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hRv.le))
  have hT := P.T_pos
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set Q := dv + τ₀ - du + 2 with hQ
  set L := Q * (2 * π) / P.T with hL
  have hbound : ∀ w, ‖ψ w‖ ≤ Real.exp L * ‖w‖ + (M + Ru) := by
    intro w
    have hel : 0 ≤ Real.exp L * ‖w‖ := by positivity
    by_cases hw : ‖w‖ ≤ Rv
    · have := hM w (mem_closedBall_zero_iff.2 hw); linarith
    by_cases hp : ‖ψ w‖ < Ru
    · linarith
    push_neg at hw hp
    have h1 := abs_le.1 (hgu (ψ w) hp)
    have h2 := abs_le.1 (hgv w hw.le)
    have hw0 : 0 < ‖w‖ := hRv.trans hw
    have hp0 : 0 < ‖ψ w‖ := hRu.trans_le hp
    set X := Real.log ‖ψ w‖
    set Y := Real.log ‖w‖
    have h3 : P.T * X / (2 * π) ≤ P.T * Y / (2 * π) + Q := by
      have := ha w; rw [hQ]; linarith [h1.1, h2.2]
    have h4 : P.T * X ≤ P.T * Y + Q * (2 * π) := by
      have := (div_le_iff₀ hπ).1 h3
      rwa [add_mul, div_mul_cancel₀ _ hπ.ne'] at this
    have h5 : X - Y ≤ L := by
      rw [hL, le_div_iff₀ hT]; linarith
    have h6 : ‖ψ w‖ ≤ Real.exp L * ‖w‖ := by
      rw [← Real.exp_log hp0, ← Real.exp_log hw0, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    linarith
  obtain ⟨A, B, hAB⟩ := exists_eq_mul_add_of_norm_le_mul_add ψ hdiff _ _ hbound
  have hA : A ≠ 0 := by
    intro h0
    have e : ψ 0 = ψ 1 := by rw [hAB 0, hAB 1, h0]; ring
    have e2 : V' 0 = V' 1 := by rw [← hψ 0, ← hψ 1, e]
    have e3 : v 0 = v 1 := (smul_right_injective _ (Real.exp_pos (2 * τ₀)).ne') e2
    exact zero_ne_one (hve.1 e3)
  exact ⟨τ₀, A, B, hA, fun w => by rw [← hAB w]; exact hψ w⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (hrange : Set.range (proj H ∘ u) = Set.range (proj H ∘ v)) :
    ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧ ∀ z, u (A * z + B) = shiftA c v z :=
  exists_shiftA_comp_affine_of_range_eq_aux H hH J hJ P hcz u v hu huP hue hv hvP hve hrange
