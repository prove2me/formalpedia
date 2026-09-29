-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.nonempty_mumfordGlue_of_isSchottky
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/49c69c31-0208-5420-a24c-6bebf5e4bac9

import Theorems.Thm_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_rel_and_zeta_overlap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_univ_law
import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlue_of_isSchottky
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
    Nonempty (MumfordGlue 𝒪 π K₀ r g₁ N) := by
  obtain ⟨M⟩ := CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueCore_of_isSchottky 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype
  have hlaws := CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_rel_and_zeta_overlap 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype M
  have huniv := CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_univ_law 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype M
  exact ⟨{
    Z := M.Z
    zb := M.zb
    zt := M.zt
    zt_isPullback := M.zt_isPullback
    zb_flat := M.zb_flat
    zb_isSeparated := M.zb_isSeparated
    ζ := M.ζ
    ζ_over := M.ζ_over
    ζ_zt := M.ζ_zt
    ζ_isOpenImmersion := M.ζ_isOpenImmersion
    ζ_cover := M.ζ_cover
    ζ_inv := M.ζ_inv
    ζ_rel := hlaws.1
    ζ_overlap_local := hlaws.2.1
    ζ_overlap_zar := hlaws.2.2
    ζ_univ := huniv }⟩

end S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlue_of_isSchottky
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlue_of_isSchottky (solution)
