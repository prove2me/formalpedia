-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.map_symF_sesqL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:57.009795+00:00
-- url     : https://prove2.me/submissions/4ace311e-76c5-48fc-a670-09f8a291fa55

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_symF_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_star_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_add_conj_eq
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
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (sesqL A 𝔭 k).map symF = hermL A 𝔭 k := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · rw [symF_apply, symF_apply, star_add, star_star, add_comm]
    · rw [symF_apply]
      exact (pK K 𝔭 k).add_mem (hs x hx y hy) (star_mem_pK hF h𝔭 (hs y hy x hx))
  · rintro ⟨ht, ht'⟩
    obtain ⟨θ, hθ⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    have hθK : (θ : K) + star (θ : K) = 1 := by
      have := congrArg (algebraMap (𝓞 K) K) hθ
      rw [map_add, map_one, map_one] at this
      exact this
    refine ⟨(θ : K) • t, fun x hx y hy => ?_, ?_⟩
    · have := (pK K 𝔭 k).smul_mem θ (ht' x hx y hy)
      rw [Algebra.smul_def] at this
      exact this
    · ext x y
      rw [symF_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', ht y x]
      rw [← add_mul, hθK, one_mul]
end Formalism.HermitianLattices.Ext.L3.D2.J
