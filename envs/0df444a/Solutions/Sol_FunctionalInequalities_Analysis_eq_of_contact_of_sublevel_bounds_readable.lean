-- Prove2me | solution 1 for FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:46.011873+00:00
-- url     : https://prove2.me/submissions/d4ca2aec-9dc1-4730-bc99-c11d644ad57c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_eq_of_two_contacts_below_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F5SublevelContactLemma
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
/-- **Caffarelli's contact-set lemma below a level** (weak Letwin route; KLS500
`supportContactSet_subsingleton_of_local_subgradient_bounds`): if `{u ≤ R}` is compact and the convex `u` has
two-sided Alexandrov bounds on compact subsets of `{u < R}`, then a supporting affine function at `x₀`
(`u x₀ < R`) touches the graph of `u` at no other point of `{u < R}`. No compactness of the full contact set
is assumed. -/
theorem solution {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {y | u y < R} → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E,
      IsOpen G → closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ∧
      (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
    {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hpy : ∀ w, u y + ⟪p, w - y⟫ ≤ u w := by
    intro w
    have hh := hp w
    have hy' := hy
    simp only [inner_sub_right] at hh hy' ⊢
    linarith
  have hxcontact : u x₀ = u y + ⟪p, x₀ - y⟫ := by
    have hy' := hy
    simp only [inner_sub_right] at hy' ⊢
    linarith
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let f : ℝ → E := AffineMap.lineMap y x₀
  have hf : Continuous f := AffineMap.lineMap_continuous
  have hf0 : f 0 = y := AffineMap.lineMap_apply_zero y x₀
  have htend : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u y)) := by
    have hh : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u (f 0))) :=
      (hu.comp hf).tendsto 0
    rw [hf0] at hh
    exact hh
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), u (f t) < R :=
    htend.eventually (eventually_lt_nhds hyR)
  obtain ⟨t, ht, htR, ht1⟩ :=
    (hnear.and (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one))).exists_gt
  have htcontact : u (f t) = u y + ⟪p, f t - y⟫ := by
    have hh := hconv.2 (mem_univ y) (mem_univ x₀)
      (sub_nonneg.mpr ht1.le) ht.le (by ring : 1 - t + t = 1)
    have hl := hpy (f t)
    have hx' := hxcontact
    have hft : f t = (1 - t) • y + t • x₀ :=
      AffineMap.lineMap_apply_module y x₀ t
    rw [hft] at hl ⊢
    simp only [smul_eq_mul] at hh
    simp only [inner_sub_right, inner_add_right, inner_smul_right] at hl hx' ⊢
    nlinarith
  have he : f t = y :=
    FunctionalInequalities.Analysis.eq_of_two_contacts_below_readable hconv hpy hK hB hyR htR htcontact
  have htzero : t = 0 :=
    (AffineMap.lineMap_injective ℝ hne) (he.trans hf0.symm)
  exact (ne_of_gt ht) htzero
