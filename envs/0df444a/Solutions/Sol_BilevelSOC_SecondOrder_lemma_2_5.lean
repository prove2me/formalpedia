-- Prove2me | solution 1 for BilevelSOC.SecondOrder.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:03:23.758357+00:00
-- url     : https://prove2.me/submissions/1849ce4d-bc59-43f1-836a-eead93326a65

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

open BilevelSOC.SecondOrder in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (X : Set V)
    (hX : X.Nonempty) (hClosed : IsClosed X) (x : V) (hx : x ∈ X)
    (hmin : IsLocalMinOn θ X x) (θs : V → ℝ)
    (hDiff : ∀ d, HasHadamardDirDerivAt θ x d (θs d)) :
    ∀ d ∈ tangentCone X x, 0 ≤ θs d := by
  rintro d ⟨t, dk, ht, htl, hdk, hmem⟩
  have hT : Filter.Tendsto (fun k => (t k, dk k)) Filter.atTop ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 d) :=
    (tendsto_nhdsWithin_iff.mpr ⟨htl, Filter.Eventually.of_forall ht⟩).prodMk hdk
  have hlim := (hDiff d).comp hT
  have hx' : Filter.Tendsto (fun k => x + t k • dk k) Filter.atTop (𝓝 x) := by
    have := tendsto_const_nhds (x := x) |>.add (htl.smul hdk)
    simpa using this
  have hxX : Filter.Tendsto (fun k => x + t k • dk k) Filter.atTop (𝓝[X] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx', Filter.Eventually.of_forall hmem⟩
  refine ge_of_tendsto hlim ?_
  filter_upwards [hxX.eventually hmin] with k hk
  simp only [Function.comp_apply]
  exact div_nonneg (sub_nonneg.mpr hk) (ht k).le
