-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_expIterate_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:19.074676+00:00
-- url     : https://prove2.me/submissions/3637f47a-f907-4c0a-9365-7f8bfa9b62e7

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → Y) :
    ¬ TendstoLocallyUniformlyOn (fun n z => q (expIterate (φ n) z)) g atTop U := by
  intro hlim
  obtain ⟨x, hx⟩ := hUne
  have hg : ContinuousOn g U := hlim.continuousOn
    (Filter.Eventually.of_forall (fun n =>
      (hqcont.comp (continuous_expIterate (φ n))).continuousOn)).frequently
  -- Every nonzero target would have to equal the same limit value at x.
  have hvalue (w : ℂ) (hw : w ≠ 0) : g x = q w := by
    apply eq_of_uniformity
    intro E hE
    obtain ⟨V, hV, hVV⟩ := comp_mem_uniformity_sets hE
    obtain ⟨T, hT, hconv⟩ := hlim V hV x hx
    have hclose : ∀ᶠ z in 𝓝[U] x, (g x, g z) ∈ V :=
      Uniform.continuousWithinAt_iff'_right.mp (hg x hx) hV
    rw [hU.nhdsWithin_eq hx] at hT hclose
    obtain ⟨W, hWsub, hWopen, hxW⟩ :=
      _root_.mem_nhds_iff.mp (inter_mem hT hclose)
    obtain ⟨N, hN⟩ := eventually_hits_nonzero hWopen ⟨x, hxW⟩ hw
    obtain ⟨n, hnconv, hnlarge⟩ :=
      (hconv.and (hφ.tendsto_atTop.eventually (eventually_ge_atTop N))).exists
    obtain ⟨z, hz, hzw⟩ := hN (φ n) hnlarge
    apply hVV
    apply SetRel.prodMk_mem_comp (hWsub hz).2
    simpa only [hzw] using hnconv z (hWsub hz).1
  exact hq ((hvalue 1 one_ne_zero).symm.trans (hvalue 2 (by norm_num)))
end ExponentialJuliaSetMisiurewicz
