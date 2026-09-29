-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f69fdf6e-0fdd-5a95-be3c-493b8ff44887

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_zb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (S : Set (Gl.Z 0)) (hS : S.Finite) :
    ∃ U : (Gl.Z 0).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z 0)) := by
  classical
  obtain ⟨hfield, hred, hdim, hinf⟩ :=
    CerednikDrinfeld.FormalOmega.MumfordGlue.specialLevel_isField_isReduced_dim_infinite 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl
  have hcomp := CerednikDrinfeld.FormalOmega.MumfordGlue.exists_isClosedImmersion_isIntegral_smoothOfRelativeDimension_one_of_mem_irreducibleComponents_zero 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl
  obtain ⟨hft, hqc⟩ := CerednikDrinfeld.FormalOmega.MumfordGlue.locallyOfFiniteType_and_quasiCompact 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl 0
  have hprop := CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_zb 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl 0
  exact AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) hfield (Gl.Z 0)
    (Gl.zb 0) (Gl.zb_isSeparated 0) hqc hft hred hprop hcomp hdim hinf S hS

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero (solution)
