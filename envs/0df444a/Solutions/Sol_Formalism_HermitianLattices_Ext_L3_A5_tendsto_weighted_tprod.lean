-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.tendsto_weighted_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.067606+00:00
-- url     : https://prove2.me/submissions/aac1685c-4b66-4571-a996-4e5f9346d840

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_tendsto_weighted
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_euler_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (hρS : ∀ i ∈ S, ∀ j, ρ i j = 1)
    (hρb : ∀ i j, |ρ i (j + 1) - ρ i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c c0 C : ℝ) (E : ι → ℝ)
    (hc : c0 = 0 → c = 0)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v)
    (H3 : ∀ S' : Finset ι, S ⊆ S' →
      Tendsto (fun j => sc j * ∑ n ∈ B j, a n * ∏ i ∈ S', ρ i (val n i)) atTop
        (𝓝 (c0 * ∏ i ∈ S', E i))) :
    Tendsto (fun j => sc j * ∑ n ∈ B j, a n * (val n).prod ρ) atTop (𝓝 (c0 * ∏' i, E i)) := by
  have h := tendsto_weighted hq hsum S hρ0 hρS hρb val B a sc c C H1 H2
  rwa [euler_identity hq hsum S hρ0 hρS hρb val B a sc c c0 C E hc H1 H2 H3] at h
end Formalism.HermitianLattices.Ext.L3.A5
