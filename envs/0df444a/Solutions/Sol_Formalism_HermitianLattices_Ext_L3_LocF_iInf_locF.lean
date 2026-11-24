-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:20.211975+00:00
-- url     : https://prove2.me/submissions/7668d9a9-f314-4646-9d68-119a9633f45f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (L : Submodule (𝓞 K) W) :
    (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 L) = L := by
  apply le_antisymm
  · intro x hx
    by_contra hxL
    let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 K))
      (Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) W x) L)
    have hmem : ∀ r : 𝓞 F, r ∈ I ↔ algebraMap (𝓞 F) (𝓞 K) r • x ∈ L := by
      intro r
      simp [I]
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 F) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have h2 := (Submodule.mem_iInf _).mp hx ⟨p, hp⟩
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff hp.isPrime L x).mp h2
    exact ht (hIp ((hmem t).mpr htx))
  · exact le_iInf fun 𝔭 => le_locF 𝔭.1 L
end Formalism.HermitianLattices.Ext.L3.LocF
