-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.limitStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:52.152004+00:00
-- url     : https://prove2.me/submissions/cb9bcca2-f5c2-47bb-87c6-5fab122bd470

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
import Theorems.Thm_Formalism_FourierDecayAlt_P_FinitePointSets_rows_le_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.LimitStep := by
  intro E W _ D jn H _ _ _ Vt c _ _ hE hC hA B hB R
  classical
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hsum : ∀ ρ, Summable (fun p : Pt E => c ρ p • Vt p) := by
    intro ρ
    refine Summable.of_norm ?_
    simpa [norm_smul] using hA3 ρ
  have hlim : Tendsto (fun F : Finset (Pt E) => ∑ ρ ∈ R, ‖∑ p ∈ F, c ρ p • Vt p‖ ^ 2) atTop
      (𝓝 (∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun ρ _ => ?_
    exact ((hsum ρ).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F

  set F0 : Finset (Pt E) := F.filter (fun p => IsPt p (D.r + 1)) with hF0
  set S : Finset E := F0.biUnion fun p => (p.map Prod.snd).toFinset with hS
  have hS0 : (0 : E) ∉ S := by
    intro h
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hp, b, hb, hb0⟩ := h
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
    exact ((Finset.mem_filter.1 hp).2.2 k hk).2 hb0
  set T : Tower E := FinitePointSets.tw S hS0 with hT
  set Y : Finset (Pt E) := T.X (D.r + 1) with hY
  have hYpt : ∀ p ∈ Y, IsPt p (D.r + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (T.isTower (D.r + 1) p).1 hp
    refine ⟨h1, fun k hk => ⟨(h2 k hk).1, fun h => ?_⟩⟩
    have := (h2 k hk).2
    rw [h] at this
    exact T.zero_not_mem _ _ this
  have hF0Y : ∀ p ∈ F0, p ∈ Y := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine (T.isTower (D.r + 1) p).2 ⟨hp'.1, fun k hk => ⟨(hp'.2 k hk).1, ?_⟩⟩
    change (p[k]'hk).2 ∈ S
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, p[k]'hk, List.getElem_mem hk, rfl⟩
  refine ⟨F ∪ Y, Finset.subset_union_left, ?_⟩
  have e : ∀ ρ, ∑ p ∈ F ∪ Y, c ρ p • Vt p = ∑ p ∈ Y, c ρ p • Vt p := by
    intro ρ
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p hp hnp => ?_
    have hc : c ρ p = 0 := by
      by_contra h
      have hpF : p ∈ F := by
        rcases Finset.mem_union.1 hp with h' | h'
        · exact h'
        · exact absurd h' hnp
      exact hnp (hF0Y p (Finset.mem_filter.2 ⟨hpF, hA1 ρ p h⟩))
    rw [hc, zero_smul]
  simp_rw [e]
  refine (FinitePointSets.rows_le_form Y (D.Kr (D.r + 1)) Vt c R (hA2 Y hYpt R)).trans ?_

  have key : ∀ δ : ℝ, 0 < δ →
      (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re ≤ B * (jn + δ) := by
    intro δ hδ
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ D.Wb D.Ntop,
        (D.gram ε 0 w [] []).re / D.wt w ≤ jn + δ :=
      (Filter.eventually_all_finset _).2 fun w hw =>
        (hE w hw).eventually_le_const (by linarith)
    obtain ⟨ε, h1ε, h2ε, hε⟩ := (h1.and ((hC Y hYpt).and self_mem_nhdsWithin)).exists
    have h3 := hB T ε hε (jn + δ) h1ε
    have e2 : D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1))
        = (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re := by
      unfold Data.Sf
      congr 1
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
      by_cases hK : D.Kr (D.r + 1) p q = 0
      · rw [hK, zero_mul, zero_mul]
      · rw [h2ε p hp q hq hK]
    rwa [e2] at h3
  have ht : Tendsto (fun δ : ℝ => B * (jn + δ)) (𝓝[>] 0) (𝓝 (B * (jn + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [add_zero] at ht
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with δ hδ using key δ hδ)
end Formalism.FourierDecayAlt.P
