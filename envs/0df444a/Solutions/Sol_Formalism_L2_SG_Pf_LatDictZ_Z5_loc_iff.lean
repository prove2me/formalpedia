-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.loc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:51.701791+00:00
-- url     : https://prove2.me/submissions/fc379b13-2735-410b-a944-46e853ab7a35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_coeOF
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_norm_hcompl
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable (I : AutInst)
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : Fin I.n → I.E) :
    v ∈ locE I p N ↔ ∃ a : 𝓞 I.F, a ∉ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) ∧
      algebraMap (𝓞 I.F) (𝓞 I.E) a • v ∈ N := by
  have := hp.isPrime
  constructor
  · intro h
    obtain ⟨s, hs, hsv⟩ := (Formalism.HermitianLatticesTheory.locBasic_mem_locS).1 h
    obtain ⟨a, ha, t, hat⟩ := norm_hcompl I p s hs
    refine ⟨a, ha, ?_⟩
    rw [hat, mul_smul]
    exact N.smul_mem t hsv
  · rintro ⟨a, ha, hav⟩
    refine (Formalism.HermitianLatticesTheory.locBasic_mem_locS).2 ⟨algebraMap (𝓞 I.F) (𝓞 I.E) a, ?_, hav⟩
    unfold Formalism.HermitianLatticesTheory.hcompl
    refine Submonoid.subset_closure ⟨ha, fun t ht => ?_⟩
    have hfix : star (algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a)) =
        algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a) := by
      rw [coeOF]
      exact (I.cm.fixed _).2 ⟨_, rfl⟩
    rw [hfix] at ht
    rw [IsFractionRing.injective (𝓞 I.E) I.E ht]
    exact ha
end Formalism.L2.SG.Pf.LatDictZ.Z5
