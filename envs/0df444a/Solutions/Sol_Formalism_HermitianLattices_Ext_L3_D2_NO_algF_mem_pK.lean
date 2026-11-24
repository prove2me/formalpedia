-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.algF_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:46:37.869217+00:00
-- url     : https://prove2.me/submissions/177f343f-4a6c-41f2-83c8-2db94f137322

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap F K (s : F) ∈ pK K 𝔭 k := by
  refine (mem_pK h𝔭).2 ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h),
    algebraMap (𝓞 F) (𝓞 K) s, ?_, ?_⟩
  · rw [extP, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hs
  · rw [show ((1 : 𝓞 F) : F) = 1 from rfl, map_one, one_mul]
    rfl
end Formalism.HermitianLattices.Ext.L3.D2.NO
