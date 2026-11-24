-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.InJ.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:24:24.908468+00:00
-- url     : https://prove2.me/submissions/3f24861d-2d5d-4d65-91d5-2ed3fb770056

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_PIW_AdelClassFin_DictRing_algebraMap_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing


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
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {κ a : K} (hκ : κ ∈ locRing p) (ha : InJ p a) :
    InJ p (κ * a) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hκ
  obtain ⟨v, hv, hvk⟩ := hκ
  obtain ⟨u, hu⟩ := Submodule.mem_one.1 hvk
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  refine ⟨u * r, v * s, mul_mem hv hs, p.mul_mem_left _ hr1, Ideal.mul_mem_left _ _ hr2, ?_⟩
  have h1 : algebraMap (𝓞 K) K v ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz v hv)
  have hκ' : κ = algebraMap (𝓞 K) K u / algebraMap (𝓞 K) K v := by
    rw [hu]
    field_simp
  rw [hκ', map_mul, map_mul, div_mul_div_comm]
end InJ
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
