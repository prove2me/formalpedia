-- Prove2me | solution 1 for CerednikDrinfeld.map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/50d37e41-cae3-5c8c-8cb1-615c8260ddfe

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Theorems.Thm_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
import Theorems.Thm_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits MulAction

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)
    :
    Γ'.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) ∧
    Mumford.GraphAction ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀) ∧
    (∀ d : (BruhatTits.tree 𝒪 K₀).Dart, Finite (MulAction.stabilizer (↥(Γ'.map ρ)) d)) ∧
    Finite (Mumford.QuotVert ↥(Γ'.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
    Finite (Mumford.QuotEdge ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀)) ∧
    (∃ γ : G, γ ∈ Γ ∧ ρ γ ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀)) ∧
    (∀ x : G, x ∈ Γ → (x ∈ Γ' ↔ ρ x ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))) ∧

    Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree 𝒪 K₀) ∧
    (∀ d : (BruhatTits.tree 𝒪 K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d)) ∧
    Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
    Finite (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree 𝒪 K₀)) ∧
    Γ'.relIndex Γ ≠ 0 := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr

  set H' : Subgroup PGL(2, K₀) := Γ'.map ρ with hH'
  set H : Subgroup PGL(2, K₀) := Γ.map ρ with hH
  set tp := Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) with htp

  obtain ⟨hstabV, hQV', hQE', hle, -, -, -⟩ :=
    CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart 𝒪 hdvr π hπ hres K₀ vdet hvdet G σ Γ Γ' hΓ' ρ hρ hdisc hcocpt

  have hpar : ∀ x : G, ρ x ∈ tp ↔ Even (Multiplicative.toAdd (vdet (σ x))) := by
    intro x
    obtain ⟨u, hu⟩ := (hvdet (σ x) (Multiplicative.toAdd (vdet (σ x)))).mp (by simp)
    refine CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_of_det_eq_mul_zpow 𝒪 K₀ π hπ PGL(2, K₀)
      (MonoidHom.id _) (fun g v => rfl) (ρ x) (σ x) (by rw [hρ]; rfl) u _ ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hu
  have hmemΓ' : ∀ x : G, x ∈ Γ → (x ∈ Γ' ↔ ρ x ∈ tp) := fun x hx => by
    rw [hΓ' x, hpar x]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hH'le : H' ≤ H := Subgroup.map_mono ((fun x hx => ((hΓ' x).mp hx).1 : Γ' ≤ Γ))

  obtain ⟨hconn, hbip⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two 𝒪 K₀
  obtain ⟨-, htype, -⟩ := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    PGL(2, K₀) (BruhatTits.tree 𝒪 K₀) hconn hbip (LT.LatticeTree.stdVertex 𝒪 K₀)
  have hfix_tp : ∀ (g : PGL(2, K₀)) (v : LT.LatticeTree.Vertex 𝒪 K₀), g • v = v → g ∈ tp := by
    intro g v hv
    have h0 : vertexType (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) (g • LT.LatticeTree.stdVertex 𝒪 K₀) = 0 := by
      have := htype g v
      rw [hv] at this
      exact (add_eq_right.mp this.symm)
    rw [htp, Mumford.mem_typePreserving_iff]
    intro w
    rw [htype g w, h0, zero_add]
  have hfix_mem : ∀ (g : PGL(2, K₀)), g ∈ H → ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, g • v = v → g ∈ H' := by
    intro g hg v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_map.mpr ⟨x, (hmemΓ' x hx).mpr (hfix_tp _ v hv), rfl⟩
  refine ⟨hle, inferInstance, ?_, hQV', hQE', ?_, hmemΓ', inferInstance, ?_, ?_, ?_, ?_⟩
  ·
    intro d
    haveI := hstabV d.fst
    refine Finite.of_injective (fun g : stabilizer (↥H') d => (⟨g.1, ?_⟩ : stabilizer (↥H') d.fst)) ?_
    · have := g.2
      rw [MulAction.mem_stabilizer_iff] at this ⊢
      exact congrArg (fun e : (BruhatTits.tree 𝒪 K₀).Dart => e.fst) this
    · intro a b h
      exact Subtype.ext (congrArg Subtype.val h :)
  ·
    obtain ⟨w, hw, hvw⟩ := hodd
    refine ⟨w, hw, ?_⟩
    rw [hpar w, hvw]
    simp
  ·
    intro d
    haveI := hstabV d.fst
    refine Finite.of_injective
      (fun g : stabilizer (↥H) d => (⟨⟨(g.1 : PGL(2, K₀)), ?_⟩, ?_⟩ : stabilizer (↥H') d.fst)) ?_
    · have hg := g.2
      rw [MulAction.mem_stabilizer_iff] at hg
      exact hfix_mem _ g.1.2 d.fst (congrArg (fun e : (BruhatTits.tree 𝒪 K₀).Dart => e.fst) hg)
    · have hg := g.2
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      exact congrArg (fun e : (BruhatTits.tree 𝒪 K₀).Dart => e.fst) hg
    · intro a b h
      have := congrArg (fun z : stabilizer (↥H') d.fst => ((z.1 : ↥H') : PGL(2, K₀))) h
      exact Subtype.ext (Subtype.ext this)
  ·
    haveI := hQV'
    refine Finite.of_surjective
      (Quotient.lift (s := MulAction.orbitRel (↥H') (LT.LatticeTree.Vertex 𝒪 K₀))
        (fun v => (Quotient.mk (MulAction.orbitRel (↥H) (LT.LatticeTree.Vertex 𝒪 K₀)) v)) ?_) ?_
    · intro a b hab
      obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.mp hab
      exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨⟨g.1, hH'le g.2⟩, rfl⟩)
    · rintro ⟨v⟩; exact ⟨Quotient.mk _ v, rfl⟩
  ·
    haveI := hQE'
    refine Finite.of_surjective
      (Quotient.lift (s := MulAction.orbitRel (↥H') (BruhatTits.tree 𝒪 K₀).Dart)
        (fun d => (Quotient.mk (MulAction.orbitRel (↥H) (BruhatTits.tree 𝒪 K₀).Dart) d)) ?_) ?_
    · intro a b hab
      obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.mp hab
      exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨⟨g.1, hH'le g.2⟩, rfl⟩)
    · rintro ⟨v⟩; exact ⟨Quotient.mk _ v, rfl⟩
  ·
    let χ : G →* Multiplicative (ZMod 2) :=
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp (vdet.comp σ)
    have hχ : ∀ x : G, χ x = 1 ↔ Even (Multiplicative.toAdd (vdet (σ x))) := by
      intro x
      show Multiplicative.ofAdd ((Multiplicative.toAdd (vdet (σ x)) : ℤ) : ZMod 2) = 1 ↔ _
      rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_eq_zero_iff_even]
    have hker : Γ'.subgroupOf Γ = (χ.comp Γ.subtype).ker := by
      ext ⟨x, hx⟩
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hχ, hΓ' x]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    haveI : Finite (Set.range (χ.comp Γ.subtype)) := inferInstance
    exact Nat.card_pos.ne'

end S_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
end P2MW
export P2MW.S_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group (solution)
