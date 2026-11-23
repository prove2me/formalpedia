-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.discrIdeal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:20.194304+00:00
-- url     : https://prove2.me/submissions/2f98e14e-1e54-4389-81e0-e449dccf0e5a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_mult
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_det_ne_zero


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : discrIdeal h L ≠ ⊥ := by
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (finBasis K V i)
  have hli : LinearIndependent K (fun i => n i • finBasis K V i) := by
    have h1 := (finBasis K V).linearIndependent.units_smul
      (fun i => Units.mk0 (n i : K) (by exact_mod_cast hn i))
    convert h1 using 1
    funext i
    rw [Pi.smul_apply', Units.smul_def, Units.val_mk0, Int.cast_smul_eq_zsmul]
  obtain ⟨g, -, hdet⟩ := exists_gram hLi _ hnx
  intro hbot
  have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hnx, hdet⟩
  rw [hbot, Ideal.mem_bot] at hmem
  apply gram_det_ne_zero h hd _ hli
  rw [← hdet, hmem, map_zero]
end Formalism.HermitianLattices.Ext.L3.LocF
