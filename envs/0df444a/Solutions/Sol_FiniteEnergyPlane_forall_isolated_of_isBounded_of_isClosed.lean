-- Prove2me | solution 1 for FiniteEnergyPlane.forall_isolated_of_isBounded_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T23:12:28.262933+00:00
-- url     : https://prove2.me/submissions/f945a28e-2ede-467e-b529-9b9b36405f4f

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib.Topology.DerivedSet
import Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection



/-!
# A bounded, closed intersection set has only isolated points

`u, v` are immersed finite-energy curves on `ℂ`. If the intersection pairs inside an open set `O`
form a bounded closed set `A`, then every pair in `A` is isolated: the first projection of the
derived set of `A` is open (McDuff, Lemma 2.7: near a non-isolated pair, `u = v ∘ φ`), closed
(compact), bounded, hence empty.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem forall_isolated_of_isBounded_of_isClosed_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hv : IsFiniteEnergyCurve H J Set.univ v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (O : Set (ℂ × ℂ)) (hO : IsOpen O)
    (hcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (hbd : Bornology.IsBounded {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (p : ℂ × ℂ) (hp : p ∈ O) (hpe : u p.1 = v p.2) :
    ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε, u z = v w → z = p.1 ∧ w = p.2 := by
  set A : Set (ℂ × ℂ) := {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2} with hAdef
  have hDsub : derivedSet A ⊆ A := (derivedSet_subset_closure A).trans hcl.closure_subset
  have hDc : IsCompact (derivedSet A) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_derivedSet A) (hbd.subset hDsub)
  set D : Set ℂ := Prod.fst '' derivedSet A with hDdef
  have hDcomp : IsCompact D := hDc.image continuous_fst
  -- `D` is open
  have hDopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨q, hq, rfl⟩
    have hqA : q ∈ A := hDsub hq
    -- a sequence of other intersection pairs converging to `q`
    have hcl' : q ∈ closure (A \ {q}) := by
      have := (accPt_principal_iff_clusterPt.1 hq)
      exact mem_closure_iff_clusterPt.2 this
    obtain ⟨s, hsA, hs⟩ := mem_closure_iff_seq_limit.1 hcl'
    have hs1 : Tendsto (fun k => (s k).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hs
    have hs2 : Tendsto (fun k => (s k).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hs
    have hne : ∀ k, ((s k).1, (s k).2) ≠ (q.1, q.2) := fun k h => (hsA k).2 (by
      simpa using h)
    have heq : ∀ k, u (s k).1 = v (s k).2 := fun k => (hsA k).1.2
    obtain ⟨ε, hε, φ, hφd, hφ0, -, -, hEq⟩ :=
      exists_holomorphic_eqOn_of_accPt_intersection H hH J hJ Set.univ Set.univ isOpen_univ
        isOpen_univ u v hu hv (fun z _ => hui z) (fun w _ => hvi w) q.1 q.2 trivial trivial
        (fun k => (s k).1) (fun k => (s k).2) hs1 hs2 hne heq
    set g : ℂ → ℂ × ℂ := fun z => (z, φ z) with hg
    have hφc : ∀ z ∈ ball q.1 ε, ContinuousAt φ z := fun z hz =>
      (hφd.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
    have hgc : ∀ z ∈ ball q.1 ε, ContinuousAt g z := fun z hz =>
      continuousAt_id.prodMk (hφc z hz)
    have hgq : g q.1 = q := by simp [hg, hφ0]
    have hev : ∀ᶠ z in 𝓝 q.1, z ∈ ball q.1 ε ∧ g z ∈ O := by
      refine Filter.Eventually.and (isOpen_ball.mem_nhds (mem_ball_self hε) :
        ∀ᶠ z in 𝓝 q.1, z ∈ ball q.1 ε) ?_
      have : O ∈ 𝓝 (g q.1) := by rw [hgq]; exact hO.mem_nhds hqA.1
      exact (hgc q.1 (mem_ball_self hε)) this
    have hev2 := eventually_eventually_nhds.2 hev
    filter_upwards [hev2, hev] with z hz hz0
    refine ⟨g z, ?_, rfl⟩
    rw [derivedSet, Set.mem_setOf_eq, accPt_iff_nhds]
    intro U hU
    have h1 : ∀ᶠ z' in 𝓝 z, g z' ∈ U := (hgc z hz0.1) hU
    obtain ⟨z', ⟨hz'U, hz'b, hz'O⟩, hz'ne⟩ :=
      (((h1.and hz).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
        (f := 𝓝[≠] z)
    refine ⟨g z', ⟨hz'U, hz'O, ?_⟩, ?_⟩
    · exact hEq hz'b
    · intro h
      exact hz'ne (congrArg Prod.fst h)
  have hDempty : D = ∅ := by
    rcases isClopen_iff.1 ⟨hDcomp.isClosed, hDopen⟩ with h | h
    · exact h
    · exact absurd (h ▸ hDcomp) (noncompact_univ ℂ)
  have hpA : p ∈ A := ⟨hp, hpe⟩
  have hnacc : ¬ AccPt p (𝓟 A) := fun h => by
    have : p.1 ∈ D := ⟨p, h, rfl⟩
    rw [hDempty] at this
    exact this
  rw [accPt_iff_nhds] at hnacc
  push_neg at hnacc
  obtain ⟨U, hU, hUA⟩ := hnacc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hO.mem_nhds hp))
  refine ⟨ε, hε, fun z hz w hw hzw => ?_⟩
  have hmem : (z, w) ∈ ball p ε := by
    rw [← ball_prod_same]; exact ⟨hz, hw⟩
  have h2 := hball hmem
  have := hUA (z, w) ⟨h2.1, h2.2, hzw⟩
  rw [← this]
  exact ⟨rfl, rfl⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hv : IsFiniteEnergyCurve H J Set.univ v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (O : Set (ℂ × ℂ)) (hO : IsOpen O)
    (hcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (hbd : Bornology.IsBounded {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (p : ℂ × ℂ) (hp : p ∈ O) (hpe : u p.1 = v p.2) :
    ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε, u z = v w → z = p.1 ∧ w = p.2 :=
  FiniteEnergyPlane.forall_isolated_of_isBounded_of_isClosed_aux H hH J hJ u v hu hv hui hvi O hO hcl hbd p hp hpe
