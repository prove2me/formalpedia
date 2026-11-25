-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.mem_of_dv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:50.707481+00:00
-- url     : https://prove2.me/submissions/356385fd-7892-4566-88eb-4b87efbd1994

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {π : K}
    (h3 : ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
      z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2)
    {z : 𝓞 K} (hz : Dv (locRing P) π (algebraMap (𝓞 K) K z)) : z ∈ P := by
  have hzz : z * z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
    apply h3
    have e : algebraMap (𝓞 K) K (z * z) * π⁻¹ * π⁻¹ =
        (algebraMap (𝓞 K) K z * π⁻¹) * (algebraMap (𝓞 K) K z * π⁻¹) := by
      rw [map_mul]; ring
    show algebraMap (𝓞 K) K (z * z) * π⁻¹ * π⁻¹ ∈ locRing P
    rw [e]
    exact (locRing P).mul_mem hz hz
  have hle : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 ≤ P :=
    (Ideal.pow_le_self two_ne_zero).trans Ideal.map_comap_le
  exact (hP.isPrime.mem_or_mem (hle hzz)).elim id id
end Formalism.L2.SG.Pf.G1
