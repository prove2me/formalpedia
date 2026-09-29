-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueCore_of_isSchottky
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/583f12d7-ffeb-5999-af0a-7ae3630c778f

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Theorems.Thm_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueLevel_of_isSchottky
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀)) :
    Nonempty (MumfordGlueCore 𝒪 π K₀ r g₁ N) := by
  classical
  let L : ∀ n : ℕ, MumfordGlueLevel 𝒪 π K₀ r g₁ N n := fun n =>
    (CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueLevel_of_isSchottky 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype n).some
  have T : ∀ n : ℕ, ∃ zt : (L n).Z ⟶ (L (n + 1)).Z,
      IsPullback zt (L n).zb (L (n + 1)).zb
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) ∧
      ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀,
        (L n).ζ h ≫ zt = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ (L (n + 1)).ζ h :=
    fun n => CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N n (L n) (L (n + 1))
  choose zt hzt hζ using T
  exact ⟨{
    Z := fun n => (L n).Z
    zb := fun n => (L n).zb
    zt := zt
    zt_isPullback := hzt
    zb_flat := fun n => (L n).zb_flat
    zb_isSeparated := fun n => (L n).zb_isSeparated
    ζ := fun h n => (L n).ζ h
    ζ_over := fun h n => (L n).ζ_over h
    ζ_zt := fun h n => hζ n h
    ζ_isOpenImmersion := fun h n => (L n).ζ_isOpenImmersion h
    ζ_cover := fun n => (L n).ζ_cover
    ζ_inv := fun g h n => (L n).ζ_inv g h
    ι := fun n => (L n).ι
    ι_ξ := fun n => (L n).ι_ξ
    ι_η := fun n => (L n).ι_η
    ι_isLocalization := fun n => (L n).ι_isLocalization
    τ := fun g n => (L n).τ g
    τ_spec := fun g hg n => (L n).τ_spec g hg
    α := fun g n => (L n).α g
    α_spec := fun g hg n => (L n).α_spec g hg
    ζ_edge := fun h g n hg => (L n).ζ_edge h g hg
    ζ_vertex := fun h g n hg => (L n).ζ_vertex h g hg
    ζ_preimage_le := fun h h' n => (L n).ζ_preimage_le h h'
    desc := fun n => (L n).desc }⟩

end S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky (solution)
