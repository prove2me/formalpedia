-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.smul_mem_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:03.12+00:00
-- url     : https://prove2.me/submissions/cf911b0b-ee68-4304-8752-bc98a884e0c1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm
end Formalism.HermitianLattices.Ext.L3.WA
