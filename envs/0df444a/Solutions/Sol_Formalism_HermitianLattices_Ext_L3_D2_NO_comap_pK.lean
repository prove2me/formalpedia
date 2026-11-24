-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.comap_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:45:51.622981+00:00
-- url     : https://prove2.me/submissions/58cd6275-e74f-4ae9-83e7-8be23ab8f4af

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (pK K 𝔭 k).toAddSubgroup.comap (algebraMap (𝓞 K) K).toAddMonoidHom =
      (extP K 𝔭 ^ k).toAddSubgroup := by
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht, w, hw, e⟩ := (mem_pK h𝔭).1 (show algebraMap (𝓞 K) K z ∈ pK K 𝔭 k from hz)
    obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
    have e1 : w = algebraMap (𝓞 F) (𝓞 K) t * z := by
      apply RingOfIntegers.ext
      exact e
    have e2 : z = algebraMap (𝓞 F) (𝓞 K) u * w - algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
      rw [e1, map_sub, map_mul, map_one]
      ring
    show z ∈ extP K 𝔭 ^ k
    rw [e2]
    refine sub_mem (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_right _ _ ?_)
    rw [extP, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hu
  · intro hz
    exact (mem_pK h𝔭).2 ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h), z, hz, by simp⟩
end Formalism.HermitianLattices.Ext.L3.D2.NO
