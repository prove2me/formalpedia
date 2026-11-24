-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.exists_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:56.073416+00:00
-- url     : https://prove2.me/submissions/7e3db8cd-7a8f-4c27-b6c1-3c6062417a24

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_isom_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ z : K, star z * z = 1 ∧ ∀ y : K, y ∈ loc (K := K) p M ↔ ∃ r ∈ locR (K := K) p, y = r * z := by
  obtain ⟨g, hg, hgM⟩ := hM.2 p hp
  refine ⟨g 1, (mem_isom_iff h1 g).1 hg, fun y => ?_⟩
  have hgx : ∀ x, g x = x * g 1 := by
    intro x
    have : g x = g (x • (1 : K)) := by simp
    rw [this, map_smul, smul_eq_mul]
  rw [← hgM, mem_gmap]
  constructor
  · intro hy
    refine ⟨g.symm y, hy, ?_⟩
    rw [← hgx, LinearEquiv.apply_symm_apply]
  · rintro ⟨r, hr, rfl⟩
    rw [← hgx, LinearEquiv.symm_apply_apply]
    exact hr
end Formalism.MainNotions.BridgeLemVR
