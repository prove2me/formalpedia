-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.InJ.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:34.004157+00:00
-- url     : https://prove2.me/submissions/48099aa5-d3e4-4f1c-8c3b-40612e7d0c2e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_PIW_AdelClassFin_DictRing_algebraMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
namespace InJ
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a b : K} (ha : InJ p a) (hb : InJ p b) :
    InJ p (a + b) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  obtain ⟨r', s', hs', hr1', hr2', rfl⟩ := hb
  refine ⟨r * s' + r' * s, s * s', mul_mem hs hs', p.add_mem (p.mul_mem_right _ hr1) (p.mul_mem_right _ hr1'),
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).add_mem (Ideal.mul_mem_right _ _ hr2) (Ideal.mul_mem_right _ _ hr2'), ?_⟩
  have h1 : algebraMap (𝓞 K) K s ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s hs)
  have h2 : algebraMap (𝓞 K) K s' ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s' hs')
  rw [div_add_div _ _ h1 h2, map_add, map_mul, map_mul, map_mul]
  ring
end InJ
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
