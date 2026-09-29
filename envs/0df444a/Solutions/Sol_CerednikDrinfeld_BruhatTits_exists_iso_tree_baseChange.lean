-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.exists_iso_tree_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c970903c-58cb-52f1-9a6c-86e404c8424c

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange.CerednikDrinfeld.BruhatTits"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "VertRel tree tree_adj_iff BruhatTits.tree"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree_adj_iff VertRel tree"
namespace Transport
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

variable {R' K' R K : Type} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
  [IsFractionRing R' K'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]
  (ι : IntegralHom R' K' R K) (ι' : IntegralHom R K R' K')
  (h₁ : ∀ x : K, ι.toField (ι'.toField x) = x) (h₂ : ∀ x : K', ι'.toField (ι.toField x) = x)

theorem vecMap_apply' (v : Fin 2 → K') (i : Fin 2) : vecMap ι v i = ι.toField (v i) := rfl

include h₂ in
theorem vecMap_vecMap (v : Fin 2 → K') : vecMap ι' (vecMap ι v) = v := by
  funext i
  show ι'.toField (ι.toField (v i)) = v i
  exact h₂ (v i)

include h₂ in

theorem latticeBaseChange_latticeBaseChange (L : Submodule R' (Fin 2 → K')) :
    latticeBaseChange ι' (latticeBaseChange ι L) = L := by
  have hc : vecMap ι' ∘ vecMap ι = id := funext fun v => vecMap_vecMap ι ι' h₂ v
  rw [show latticeBaseChange ι L = Submodule.span R (vecMap ι '' (L : Set (Fin 2 → K'))) from rfl,
    latticeBaseChange_span, ← Set.image_comp, hc, Set.image_id, Submodule.span_eq]

include h₂ in
theorem baseChange_baseChange (v : Vertex R' K') : Vertex.baseChange ι' (Vertex.baseChange ι v) = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeBaseChange_latticeBaseChange ι ι' h₂ L.1))

include h₁ in

theorem toBase_toBase (r : R) : ι.toBase (ι'.toBase r) = r := by
  apply IsFractionRing.injective R K
  rw [← ι.commutes, ← ι'.commutes, h₁]

def baseEquiv (hB₁ : ∀ r : R, ι.toBase (ι'.toBase r) = r) (hB₂ : ∀ r : R', ι'.toBase (ι.toBase r) = r) : R' ≃+* R :=
  RingEquiv.ofRingHom ι.toBase ι'.toBase
    (by ext r; first | exact hB₂ r | exact hB₁ r) (by ext r; first | exact hB₁ r | exact hB₂ r)

theorem baseEquiv_apply (hB₁ : ∀ r : R, ι.toBase (ι'.toBase r) = r) (hB₂ : ∀ r : R', ι'.toBase (ι.toBase r) = r)
    (x : R') : baseEquiv ι ι' hB₁ hB₂ x = ι.toBase x := rfl

include h₁ h₂ in
theorem irreducible_toBase {ϖ : R'} (hϖ : Irreducible ϖ) : Irreducible (ι.toBase ϖ) := by
  rw [← baseEquiv_apply ι ι' (toBase_toBase ι ι' h₁) (toBase_toBase ι' ι h₂) ϖ]
  exact (MulEquiv.irreducible_iff (baseEquiv ι ι' (toBase_toBase ι ι' h₁) (toBase_toBase ι' ι h₂)).toMulEquiv).mpr hϖ

include h₂ in

theorem latticeBaseChange_lt {L M : Submodule R' (Fin 2 → K')} (h : L < M) :
    latticeBaseChange ι L < latticeBaseChange ι M := by
  refine lt_of_le_of_ne (latticeBaseChange_mono ι h.le) fun heq => h.ne ?_
  have := congrArg (latticeBaseChange ι') heq
  rwa [latticeBaseChange_latticeBaseChange ι ι' h₂, latticeBaseChange_latticeBaseChange ι ι' h₂] at this

theorem unitsMap_unitOfNeZero {ϖ : R'} (hϖ : ϖ ≠ 0) (hϖ' : ι.toBase ϖ ≠ 0) :
    Units.map (ι.toField : K' →* K) (unitOfNeZero (K := K') hϖ) = unitOfNeZero (K := K) hϖ' := by
  apply Units.ext
  rw [Units.coe_map, MonoidHom.coe_coe, unitOfNeZero_coe, unitOfNeZero_coe, ι.commutes]

include h₁ h₂ in
theorem adjacentLattice_baseChange {L M : Submodule R' (Fin 2 → K')} (h : AdjacentLattice L M) :
    AdjacentLattice (latticeBaseChange ι L) (latticeBaseChange ι M) := by
  obtain ⟨ϖ, hϖ, hlow, hup⟩ := h
  have hϖR : Irreducible (ι.toBase ϖ) := irreducible_toBase ι ι' h₁ h₂ hϖ
  refine ⟨ι.toBase ϖ, hϖR, ?_, latticeBaseChange_lt ι ι' h₂ hup⟩
  rw [← unitsMap_unitOfNeZero ι hϖ.ne_zero hϖR.ne_zero, ← latticeBaseChange_scalarGL]
  exact latticeBaseChange_lt ι ι' h₂ hlow

include h₁ h₂ in
theorem vertRel_baseChange {x y : Vertex R' K'} (h : VertRel R' K' x y) :
    VertRel R K (Vertex.baseChange ι x) (Vertex.baseChange ι y) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeBaseChange ι L, latticeBaseChange ι M, hL.baseChange ι, hM.baseChange ι, rfl, rfl,
    adjacentLattice_baseChange ι ι' h₁ h₂ hLM⟩

include h₁ h₂ in

def vertexEquiv : Vertex R' K' ≃ Vertex R K where
  toFun := Vertex.baseChange ι
  invFun := Vertex.baseChange ι'
  left_inv := baseChange_baseChange ι ι' h₂
  right_inv := baseChange_baseChange ι' ι h₁

include h₁ h₂ in
theorem adj_iff (x y : Vertex R' K') :
    (tree R K).Adj (Vertex.baseChange ι x) (Vertex.baseChange ι y) ↔ (tree R' K').Adj x y := by
  rw [tree_adj_iff, tree_adj_iff]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨fun hxy => hne (by rw [hxy]), ?_⟩
    rcases hrel with h | h
    · left
      have := vertRel_baseChange ι' ι h₂ h₁ h
      rwa [baseChange_baseChange ι ι' h₂, baseChange_baseChange ι ι' h₂] at this
    · right
      have := vertRel_baseChange ι' ι h₂ h₁ h
      rwa [baseChange_baseChange ι ι' h₂, baseChange_baseChange ι ι' h₂] at this
  · rintro ⟨hne, hrel⟩
    refine ⟨fun hxy => hne ((vertexEquiv ι ι' h₁ h₂).injective hxy), ?_⟩
    exact hrel.imp (vertRel_baseChange ι ι' h₁ h₂) (vertRel_baseChange ι ι' h₁ h₂)

include h₁ h₂ in

def treeIso : tree R' K' ≃g tree R K where
  toEquiv := vertexEquiv ι ι' h₁ h₂
  map_rel_iff' := fun {a b} => adj_iff ι ι' h₁ h₂ a b

include h₁ h₂ in
theorem latticeBaseChange_stdLattice : latticeBaseChange ι (stdLattice R' K') = stdLattice R K := by
  refine le_antisymm (latticeBaseChange_stdLattice_le ι) ?_
  calc stdLattice R K = latticeBaseChange ι (latticeBaseChange ι' (stdLattice R K)) :=
        (latticeBaseChange_latticeBaseChange ι' ι h₁ _).symm
    _ ≤ latticeBaseChange ι (stdLattice R' K') := latticeBaseChange_mono ι (latticeBaseChange_stdLattice_le ι')

include h₁ h₂ in
theorem baseChange_stdVertex : Vertex.baseChange ι (stdVertex R' K') = stdVertex R K := by
  show Vertex.baseChange ι (Vertex.mk R' K' (stdLattice R' K') isFullLattice_stdLattice) =
    Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice
  rw [Vertex.baseChange_mk, Vertex.mk_eq_mk_iff, latticeBaseChange_stdLattice ι ι' h₁ h₂]
  exact Homothetic.refl _

include h₁ h₂ in
theorem main :
    ∃ e : tree R' K' ≃g tree R K,
      (∀ v : Vertex R' K', e v = Vertex.baseChange ι v) ∧
      (∀ v : Vertex R K, e.symm v = Vertex.baseChange ι' v) ∧
      (∀ (g : GL (Fin 2) K') (v : Vertex R' K'), e (g • v) = ι.mapGL g • e v) ∧
      e (stdVertex R' K') = stdVertex R K := by
  refine ⟨treeIso ι ι' h₁ h₂, fun v => rfl, fun v => rfl, fun g v => ?_, baseChange_stdVertex ι ι' h₁ h₂⟩
  show Vertex.baseChange ι (Vertex.act g v) = Vertex.act (ι.mapGL g) (Vertex.baseChange ι v)
  exact Vertex.baseChange_act ι g v

end CerednikDrinfeld.BruhatTits.Transport

theorem solution
    (R' K' R K : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (ι : LT.LatticeTree.IntegralHom R' K' R K) (ι' : LT.LatticeTree.IntegralHom R K R' K')
    (h₁ : ∀ x : K, ι.toField (ι'.toField x) = x) (h₂ : ∀ x : K', ι'.toField (ι.toField x) = x) :
    ∃ e : CerednikDrinfeld.BruhatTits.tree R' K' ≃g CerednikDrinfeld.BruhatTits.tree R K,
      (∀ v : LT.LatticeTree.Vertex R' K', e v = LT.LatticeTree.Vertex.baseChange ι v) ∧
      (∀ v : LT.LatticeTree.Vertex R K, e.symm v = LT.LatticeTree.Vertex.baseChange ι' v) ∧
      (∀ (g : GL (Fin 2) K') (v : LT.LatticeTree.Vertex R' K'), e (g • v) = ι.mapGL g • e v) ∧
      e (LT.LatticeTree.stdVertex R' K') = LT.LatticeTree.stdVertex R K :=
  CerednikDrinfeld.BruhatTits.Transport.main ι ι' h₁ h₂

end S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange (solution)
