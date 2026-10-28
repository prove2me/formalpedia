-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:02.922348+00:00
-- url     : https://prove2.me/submissions/6bfb726a-22a9-4462-bf63-70e50d4925fc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_unit_inner_le_infDist_frontier_readable
import Theorems.Thm_FunctionalInequalities_Analysis_mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11C5AlexandrovMaximumPrinciple
open MeasureTheory Set Metric
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.alexandrov_frontier_nonempty [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω : Set E} (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (frontier Ω).Nonempty := by
  by_contra hne
  have hfrontier_empty : frontier Ω = ∅ := by
    ext y
    constructor
    · intro hy
      exact (hne ⟨y, hy⟩).elim
    · intro hy
      simp at hy
  rw [frontier_eq_empty_iff] at hfrontier_empty
  rcases hfrontier_empty with hΩempty | hΩuniv
  · rw [hΩempty] at hx₀
    exact hx₀
  · obtain ⟨s, hs⟩ := hb.subset_closedBall x₀
    have hs_nonneg : 0 ≤ s := by
      have hsx : dist x₀ x₀ ≤ s := hs hx₀
      simpa only [dist_self] using hsx
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let e : E := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
      exact inv_mul_cancel₀ hvpos.ne'
    let y : E := x₀ + (s + 1) • e
    have hyΩ : y ∈ Ω := by
      rw [hΩuniv]
      exact mem_univ y
    have hyball : y ∈ closedBall x₀ s := hs hyΩ
    have hnorm : ‖y - x₀‖ = s + 1 := by
      dsimp [y]
      rw [add_sub_cancel_left, norm_smul, he, mul_one]
      exact abs_of_nonneg (by linarith)
    have hydist : dist y x₀ ≤ s := hyball
    rw [dist_eq_norm, hnorm] at hydist
    linarith
private lemma FunctionalInequalities.Analysis.alexandrov_diam_pos [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < diam Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
    exact inv_mul_cancel₀ hvpos.ne'
  let y : E := x₀ + (r / 2) • e
  have hy : y ∈ Ω := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  have hdist : dist x₀ y ≤ diam Ω :=
    Metric.dist_le_diam_of_mem hb hx₀ hy
  have hdist' : dist x₀ y = r / 2 := by
    rw [dist_eq_norm, norm_sub_rev]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
  rw [hdist'] at hdist
  linarith
section FiniteDimensional
variable [FiniteDimensional ℝ E] [Nontrivial E]
private lemma FunctionalInequalities.Analysis.alexandrov_infDist_frontier_pos
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < infDist x₀ (frontier Ω) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hne : (frontier Ω).Nonempty :=
    alexandrov_frontier_nonempty hb hx₀
  apply lt_of_lt_of_le hr
  apply (Metric.le_infDist hne).2
  intro y hy
  have hyn : y ∉ Ω := by
    intro hyΩ
    apply hy.2
    rw [hΩ.interior_eq]
    exact hyΩ
  have hnot : ¬ dist y x₀ < r := by
    intro hdist
    exact hyn (hball (mem_ball.mpr hdist))
  simpa [dist_comm] using (le_of_not_gt hnot)
private lemma FunctionalInequalities.Analysis.alexandrov_frontier_distance_le_diam
    {_Ω : Set E} (_hΩ : IsOpen _Ω) (hb : Bornology.IsBounded _Ω)
    {x₀ : E} (hx₀ : x₀ ∈ _Ω) :
    infDist x₀ (frontier _Ω) ≤ diam _Ω := by
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  have hcompact_ball : IsCompact (closedBall x₀ r) :=
    isCompact_closedBall x₀ r
  have hcompact_frontier : IsCompact (frontier _Ω) :=
    hcompact_ball.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hr isClosed_closedBall))
  obtain ⟨y, hy, hyeq⟩ :=
    hcompact_frontier.exists_infDist_eq_dist
      (alexandrov_frontier_nonempty hb hx₀) x₀
  have hdist : dist x₀ y ≤ diam _Ω := by
    have hdist' : dist x₀ y ≤ diam (closure _Ω) :=
      Metric.dist_le_diam_of_mem hb.closure
        (subset_closure hx₀) (frontier_subset_closure hy)
    simpa only [Metric.diam_closure] using hdist'
  exact hyeq.trans_le hdist
end FiniteDimensional
private lemma FunctionalInequalities.Analysis.alexandrov_affine_set_convex {u : E → ℝ} {x₀ : E}
    {Ω : Set E} :
    Convex ℝ {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0} := by
  intro p hp q hq a b ha hb hab x hx
  have hp' := hp x hx
  have hq' := hq x hx
  have hi :
      ⟪a • p + b • q, x - x₀⟫ =
        a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    u x₀ + ⟪a • p + b • q, x - x₀⟫ =
        u x₀ + (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hi]
    _ = (a + b) * u x₀ +
          (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hab]
          ring
    _ = a * (u x₀ + ⟪p, x - x₀⟫) +
          b * (u x₀ + ⟪q, x - x₀⟫) := by
          ring
    _ ≤ 0 := by
      simpa using add_le_add
        (mul_nonpos_of_nonneg_of_nonpos ha hp')
        (mul_nonpos_of_nonneg_of_nonpos hb hq')
/-- **Alexandrov maximum principle** (Gutiérrez, *The Monge–Ampère equation*, Theorem 1.4.2; weak
Letwin route, Caffarelli's argument): there is `c > 0` depending only on `E` such that for every
convex `u`, bounded open convex `Ω`, `u ≥ 0` on `∂Ω` and `x₀ ∈ Ω` with `u x₀ < 0`,
`c · (−u x₀)^n ≤ vol (∂u(Ω)) · diam(Ω)^(n−1) · dist(x₀, ∂Ω)`, `n = dim E`. -/
theorem solution [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ univ u → ∀ (Ω : Set E), IsOpen Ω → Convex ℝ Ω →
      Bornology.IsBounded Ω → (∀ x ∈ frontier Ω, 0 ≤ u x) → ∀ x₀ ∈ Ω, u x₀ < 0 →
      ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by
  obtain ⟨c, hc, hcone⟩ :=
    FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable (E := E)
  refine ⟨c, hc, ?_⟩
  intro u hconv Ω hΩ hΩconv hb hfr x₀ hx₀ hneg
  let m : ℝ := -u x₀
  let D : ℝ := diam Ω
  let d : ℝ := infDist x₀ (frontier Ω)
  have hm : 0 < m := by
    dsimp [m]
    linarith
  have hD : 0 < D := FunctionalInequalities.Analysis.alexandrov_diam_pos hΩ hb hx₀
  have hd : 0 < d := FunctionalInequalities.Analysis.alexandrov_infDist_frontier_pos hΩ hb hx₀
  have hdd : d ≤ D :=
    FunctionalInequalities.Analysis.alexandrov_frontier_distance_le_diam hΩ hb hx₀
  obtain ⟨e, he, heΩ⟩ :=
    FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_readable hΩ hΩconv hb hx₀
  let r : ℝ := m / D
  let q : E := (m / d) • e
  have hr : 0 < r := div_pos hm hD
  have hqnorm : ‖q‖ = m / d := by
    dsimp [q]
    rw [norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hd)]
  have hrq : r ≤ ‖q‖ := by
    rw [hqnorm]
    exact div_le_div_of_nonneg_left hm.le hd hdd
  let A : Set E := {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0}
  have hAconv : Convex ℝ A :=
    FunctionalInequalities.Analysis.alexandrov_affine_set_convex
  have hballA : closedBall (0 : E) r ⊆ A := by
    intro p hp x hx
    have hdist := Metric.dist_le_diam_of_mem hb.closure
      hx (subset_closure hx₀)
    have hxd : ‖x - x₀‖ ≤ D := by
      simpa only [dist_eq_norm, Metric.diam_closure] using hdist
    have hpnorm : ‖p‖ ≤ r := by
      simpa [mem_closedBall, dist_zero_right] using hp
    have hinner : ⟪p, x - x₀⟫ ≤ ‖p‖ * ‖x - x₀‖ :=
      le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    have hmul : ‖p‖ * ‖x - x₀‖ ≤ r * D :=
      mul_le_mul hpnorm hxd (norm_nonneg _) (by positivity)
    have hzero : u x₀ + r * D = 0 := by
      dsimp [r, m]
      rw [div_mul_cancel₀ _ hD.ne']
      ring
    calc
      u x₀ + ⟪p, x - x₀⟫ ≤ u x₀ + ‖p‖ * ‖x - x₀‖ := by
        exact add_le_add (le_refl _) hinner
      _ ≤ u x₀ + r * D := by
        exact add_le_add (le_refl _) hmul
      _ = 0 := hzero
  have hqA : q ∈ A := by
    intro x hx
    have hΩbound : ∀ y ∈ Ω, u x₀ + ⟪q, y - x₀⟫ ≤ 0 := by
      intro y hy
      have hey := heΩ y hy
      have hey' : ⟪e, y - x₀⟫ ≤ d := by
        simpa only [real_inner_comm] using hey
      have hi :
          ⟪q, y - x₀⟫ =
            (m / d) * ⟪e, y - x₀⟫ := by
        rw [real_inner_smul_left]
      have hmul :
          (m / d) * ⟪e, y - x₀⟫ ≤ (m / d) * d :=
        mul_le_mul_of_nonneg_left hey' (div_pos hm hd).le
      calc
        u x₀ + ⟪q, y - x₀⟫ =
            u x₀ + (m / d) * ⟪e, y - x₀⟫ := by rw [hi]
        _ ≤ u x₀ + (m / d) * d := by
          exact add_le_add (le_refl _) hmul
        _ = 0 := by
          dsimp [m]
          rw [div_mul_cancel₀ _ hd.ne']
          ring
    have hcont : Continuous (fun y : E =>
        u x₀ + ⟪q, y - x₀⟫) :=
      continuous_const.add
        ((continuous_const : Continuous (fun _ : E => q)).inner
          (continuous_id.sub continuous_const))
    have hclosed :
        IsClosed {y : E | u x₀ + ⟪q, y - x₀⟫ ≤ 0} :=
      isClosed_Iic.preimage hcont
    exact closure_minimal hΩbound hclosed hx
  have hHullA :
      convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆ A :=
    convexHull_min (by
      intro p hp
      rcases hp with hp | hp
      · exact hballA hp
      · rw [Set.mem_singleton_iff] at hp
        rw [hp]
        exact hqA) hAconv
  have hsub :
      convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆
        FunctionalInequalities.Analysis.subgradientImage u Ω := by
    exact hHullA.trans (by
      intro p hp
      exact FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable
        hconv hΩ hb hfr hx₀ hneg hp)
  have hvol :
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u Ω) :=
    (hcone r hr q hrq).trans (measure_mono hsub)
  have hn : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Module.finrank_pos (R := ℝ) (M := E)))
  have hcancel :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m := by
    rw [hqnorm]
    change
      (c * (m / D) ^ (Module.finrank ℝ E - 1) * (m / d)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m
    simp only [div_eq_mul_inv, mul_pow]
    have hpowD :
        D ^ (Module.finrank ℝ E - 1) *
            D⁻¹ ^ (Module.finrank ℝ E - 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hD.ne', one_pow]
    calc
      (c * (m ^ (Module.finrank ℝ E - 1) *
          D⁻¹ ^ (Module.finrank ℝ E - 1)) *
          (m * d⁻¹)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m *
            (D ^ (Module.finrank ℝ E - 1) *
              D⁻¹ ^ (Module.finrank ℝ E - 1)) *
            (d⁻¹ * d) := by ring
      _ = c * m ^ (Module.finrank ℝ E - 1) * m := by
        rw [hpowD, inv_mul_cancel₀ hd.ne']
        ring
  have hEq :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ Module.finrank ℝ E := by
    calc
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m := hcancel
      _ = c * (m ^ (Module.finrank ℝ E - 1) * m) := by ring
      _ = c * m ^ ((Module.finrank ℝ E - 1) + 1) := by
        rw [pow_succ]
      _ = c * m ^ Module.finrank ℝ E := by
        rw [Nat.sub_add_cancel hn]
  have hreal :
      c * m ^ Module.finrank ℝ E ≤
        (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [hEq]
  have hreal' :
      ENNReal.ofReal (c * m ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ c * r ^ (Module.finrank ℝ E - 1) * ‖q‖)]
    exact ENNReal.ofReal_mono hreal
  calc
    ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) =
        ENNReal.ofReal (c * m ^ Module.finrank ℝ E) := by
          rfl
    _ ≤ ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) := hreal'
    _ ≤ (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u Ω) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) :=
      mul_le_mul' hvol (le_refl _)
    _ = (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) *
            infDist x₀ (frontier Ω)) := by
      rfl
