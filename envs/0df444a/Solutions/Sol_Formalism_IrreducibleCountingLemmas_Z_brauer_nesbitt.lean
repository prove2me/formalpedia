-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:41.407751+00:00
-- url     : https://prove2.me/submissions/29f9e52a-8f8e-4867-ba08-a240db9f8e16

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_asModule
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_asAlgebraHom_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_brauer_nesbitt_algebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : BrauerNesbitt := by
  intro k _ G _ V W _ _ _ _ _ _ ρ τ hρ hτ h
  obtain ⟨e⟩ := brauer_nesbitt_algebra k (MonoidAlgebra k G) ρ.asModule τ.asModule hρ hτ
    (fun a => by
      have := BN.charpoly_asAlgebraHom_eq ρ τ h a
      rw [← BN.cp_asModule, ← BN.cp_asModule] at this
      exact this)
  refine ⟨ρ.asModuleEquiv.symm ≪≫ₗ e.restrictScalars k ≪≫ₗ τ.asModuleEquiv, fun g => ?_⟩
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]
end Formalism.IrreducibleCountingLemmas.Z
