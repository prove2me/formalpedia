-- Prove2me | solution 1 for DualityStability.WeakDuality.hull_lsc_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:44:06.943468+00:00
-- url     : https://prove2.me/submissions/0e5e5743-79bc-40da-8662-9acfb38ca0f9

import Definitions.Def_DualityStability_WeakDuality_Problem

open Filter Topology DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

lemma ds2_extract (P : Problem E E' F F') (x : E) (w : F) (t : ℝ)
    (h : P.f x - P.g w < t) : ∃ α γ : ℝ, P.f x = α ∧ P.g w = γ ∧ α - γ < t := by
  have hf1 : P.f x ≠ ⊥ := P.f_proper_convex.2.1 x
  have hg1 : P.g w ≠ ⊤ := P.g_proper_concave.2.1 w
  have hf2 : P.f x ≠ ⊤ := by
    intro hf; rw [hf, sub_eq_add_neg, EReal.top_add_of_ne_bot] at h
    · exact (not_top_lt h)
    · rwa [Ne, EReal.neg_eq_bot_iff]
  have hg2 : P.g w ≠ ⊥ := by
    intro hg; rw [hg, EReal.sub_bot hf1] at h; exact not_top_lt h
  refine ⟨(P.f x).toReal, (P.g w).toReal, (EReal.coe_toReal hf2 hf1).symm,
    (EReal.coe_toReal hg1 hg2).symm, ?_⟩
  rw [← EReal.coe_toReal hf2 hf1, ← EReal.coe_toReal hg1 hg2, ← EReal.coe_sub] at h
  exact_mod_cast h

lemma ds2_perturbation_convex (P : Problem E E' F F') : EpigraphConvex P.perturbation := by
  rintro ⟨z1, μ1⟩ h1 ⟨z2, μ2⟩ h2 a b ha hb hab
  simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h1 h2 ⊢
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have hr1' : a * μ1 + b * μ2 < r := by exact_mod_cast hr1
  set ε := r - (a * μ1 + b * μ2) with hε
  have hεpos : 0 < ε := by linarith
  have hlt1 : P.perturbation z1 < ((μ1 + ε : ℝ) : EReal) :=
    lt_of_le_of_lt h1 (by exact_mod_cast (by linarith : μ1 < μ1 + ε))
  have hlt2 : P.perturbation z2 < ((μ2 + ε : ℝ) : EReal) :=
    lt_of_le_of_lt h2 (by exact_mod_cast (by linarith : μ2 < μ2 + ε))
  obtain ⟨x1, hx1⟩ := iInf_lt_iff.mp hlt1
  obtain ⟨x2, hx2⟩ := iInf_lt_iff.mp hlt2
  obtain ⟨α1, γ1, hf1, hg1, hs1⟩ := ds2_extract P _ _ _ hx1
  obtain ⟨α2, γ2, hf2, hg2, hs2⟩ := ds2_extract P _ _ _ hx2
  have hfc := P.f_proper_convex.1 (x := (x1, α1)) (y := (x2, α2))
    (by simp [hf1]) (by simp [hf2]) ha hb hab
  have hgc := P.g_proper_concave.1 (x := (P.A x1 - z1, -γ1)) (y := (P.A x2 - z2, -γ2))
    (by simp [hg1]) (by simp [hg2]) ha hb hab
  simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hfc hgc
  have hw : P.A (a • x1 + b • x2) - (a • z1 + b • z2) =
      a • (P.A x1 - z1) + b • (P.A x2 - z2) := by
    simp only [map_add, map_smul, smul_sub]; abel
  have hle : P.perturbation (a • z1 + b • z2) ≤
      ((a * α1 + b * α2 : ℝ) : EReal) + ((a * -γ1 + b * -γ2 : ℝ) : EReal) := by
    calc P.perturbation (a • z1 + b • z2)
        ≤ P.f (a • x1 + b • x2) - P.g (P.A (a • x1 + b • x2) - (a • z1 + b • z2)) :=
          iInf_le (fun x : E => P.f x - P.g (P.A x - (a • z1 + b • z2))) _
      _ = P.f (a • x1 + b • x2) + -P.g (a • (P.A x1 - z1) + b • (P.A x2 - z2)) := by
          rw [hw, sub_eq_add_neg]
      _ ≤ _ := add_le_add hfc hgc
  rw [← EReal.coe_add] at hle
  have hfin : a * α1 + b * α2 + (a * -γ1 + b * -γ2) ≤ r := by
    have e1 : a * (α1 - γ1) ≤ a * (μ1 + ε) := mul_le_mul_of_nonneg_left hs1.le ha
    have e2 : b * (α2 - γ2) ≤ b * (μ2 + ε) := mul_le_mul_of_nonneg_left hs2.le hb
    have : a * (μ1 + ε) + b * (μ2 + ε) = r := by
      rw [hε]; have : b = 1 - a := by linarith
      subst this; ring
    nlinarith
  have := lt_of_lt_of_le hr2 hle
  have : (r : ℝ) < a * α1 + b * α2 + (a * -γ1 + b * -γ2) := by exact_mod_cast this
  linarith

lemma ds2_hull_le (P : Problem E E' F F') (z : F) : P.hull z ≤ P.perturbation z := by
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_iff]
  intro U hU
  exact ⟨z, mem_of_mem_nhds hU, le_rfl⟩

lemma ds2_epi_hull (P : Problem E E' F F') :
    {p : F × ℝ | P.hull p.1 ≤ (p.2 : EReal)} =
      closure {p : F × ℝ | P.perturbation p.1 ≤ (p.2 : EReal)} := by
  ext ⟨y, μ⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hy
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp ht
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hv
    have hν : P.hull y < ((μ + δ / 2 : ℝ) : EReal) :=
      lt_of_le_of_lt hy (by exact_mod_cast (by linarith : μ < μ + δ / 2))
    have hfreq : ∃ᶠ z in 𝓝 y, P.perturbation z < ((μ + δ / 2 : ℝ) : EReal) :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hν
    obtain ⟨z, hz1, hz2⟩ := (hfreq.and_eventually hu).exists
    refine ⟨(z, μ + δ / 2), huv ⟨hz2, hball ?_⟩, hz1.le⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith
  · intro hcl
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hev : ∀ᶠ z in 𝓝 y, (r : EReal) < P.perturbation z :=
      Filter.eventually_lt_of_lt_liminf hr2 (by isBoundedDefault)
    have hr1' : μ < r := by exact_mod_cast hr1
    have hn : {z | (r : EReal) < P.perturbation z} ×ˢ Set.Iio r ∈ 𝓝 (y, μ) :=
      prod_mem_nhds hev (Iio_mem_nhds hr1')
    obtain ⟨⟨z, ν⟩, ⟨hz, hνr⟩, hzν⟩ := mem_closure_iff_nhds.mp hcl _ hn
    simp only [Set.mem_setOf_eq, Set.mem_Iio] at hz hνr hzν
    have : (r : EReal) < ν := lt_of_lt_of_le hz hzν
    have : r < ν := by exact_mod_cast this
    linarith

theorem solution (P : Problem E E' F F') :
    LowerSemicontinuous P.hull ∧ EpigraphConvex P.hull := by
  refine ⟨?_, ?_⟩
  · intro y r hr
    obtain ⟨r', hr1, hr2⟩ := exists_between hr
    have hev : ∀ᶠ z in 𝓝 y, r' < P.perturbation z :=
      Filter.eventually_lt_of_lt_liminf hr2 (by isBoundedDefault)
    obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.mp hev
    filter_upwards [hto.mem_nhds hyt] with y'' hy''
    refine lt_of_lt_of_le hr1 ?_
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    filter_upwards [hto.mem_nhds hy''] with z hz using (ht z hz).le
  · unfold EpigraphConvex
    rw [ds2_epi_hull]
    exact (ds2_perturbation_convex P).closure
