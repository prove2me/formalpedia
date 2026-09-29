-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/604d8b3b-5451-588e-ad65-361f824e3b6e

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
import Theorems.Thm_CerednikDrinfeld_Mumford_fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits

namespace F0fTreeLattice

theorem relIndex_ne_zero_of_even {G : Type} [Group G] (χ : G →* Multiplicative ℤ)
    (Γ Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (χ x))) :
    Γ'.relIndex Γ ≠ 0 := by
  let ψ : ↥Γ →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (((Multiplicative.toAdd (χ (x : G))) : ℤ) : ZMod 2)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul, toAdd_mul, Int.cast_add, ofAdd_add] }
  have hψ : ∀ x : ↥Γ, ψ x = 1 ↔ Even (Multiplicative.toAdd (χ (x : G))) := by
    intro x
    rw [even_iff_two_dvd]
    change Multiplicative.ofAdd (((Multiplicative.toAdd (χ (x : G))) : ℤ) : ZMod 2) = 1 ↔ _
    rw [ofAdd_eq_one]
    have h := ZMod.intCast_zmod_eq_zero_iff_dvd (Multiplicative.toAdd (χ (x : G))) 2
    simpa using h
  have hker : ψ.ker = Γ'.subgroupOf Γ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΓ', hψ]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  show (Γ'.subgroupOf Γ).index ≠ 0
  rw [← hker, Subgroup.index_ker]
  exact Nat.card_pos.ne'

theorem relIndex_map_ne_zero {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (Γ Γ' : Subgroup G) (hle : Γ' ≤ Γ) (h : Γ'.relIndex Γ ≠ 0) :
    (Γ'.map f).relIndex (Γ.map f) ≠ 0 := by
  have heq : (Γ'.map f).subgroupOf (Γ.map f) = (Γ'.subgroupOf Γ).map (f.subgroupMap Γ) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hle hy⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact hy
      · exact Subtype.ext hyx
    · rintro ⟨z, hz, hzx⟩
      refine ⟨(z : G), ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hz; exact hz
      · exact congrArg Subtype.val hzx
  have hdvd : ((Γ'.map f).subgroupOf (Γ.map f)).index ∣ (Γ'.subgroupOf Γ).index := by
    rw [heq]; exact Subgroup.index_map_dvd _ (MonoidHom.subgroupMap_surjective f Γ)
  intro h0
  apply h
  show (Γ'.subgroupOf Γ).index = 0
  have : ((Γ'.map f).subgroupOf (Γ.map f)).index = 0 := h0
  rw [this] at hdvd
  exact Nat.eq_zero_of_zero_dvd hdvd

theorem zmod2_ne_add_one : ∀ x : ZMod 2, x ≠ x + 1 := by decide

end F0fTreeLattice

open F0fTreeLattice in

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S) :
    (∀ w : LT.LatticeTree.Vertex 𝒪 K₀, Finite (MulAction.stabilizer (↥(Γ'.map ρ)) w)) ∧
    Finite (QuotVert (↥(Γ'.map ρ)) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
    Finite (QuotEdge (↥(Γ'.map ρ)) (BruhatTits.tree 𝒪 K₀)) ∧
    Γ'.map ρ ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) ∧
    (∀ g ∈ Γ'.map ρ, ∀ d : (BruhatTits.tree 𝒪 K₀).Dart, g • d ≠ d.symm) ∧
    (Γ'.map ρ).FG ∧
    (Γ'.map ρ).relIndex (Γ.map ρ) ≠ 0 := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI hfinres : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  obtain ⟨hconn, hbip⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two 𝒪 K₀

  have h1 : ∀ w : LT.LatticeTree.Vertex 𝒪 K₀, Finite (MulAction.stabilizer (↥(Γ'.map ρ)) w) := by
    intro w
    haveI := (hdisc w).to_subtype
    refine Finite.of_injective
      (fun h : ↥(MulAction.stabilizer (↥(Γ'.map ρ)) w) =>
        (⟨((h : ↥(Γ'.map ρ)) : PGL(2, K₀)), (h : ↥(Γ'.map ρ)).2, ?_⟩ :
          ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • w = w})) ?_
    · have hh := h.2
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hh
      exact hh
    · intro a b hab
      have hv := congrArg Subtype.val hab
      dsimp only at hv
      exact Subtype.ext (Subtype.ext hv)

  have h2 : Finite (QuotVert (↥(Γ'.map ρ)) (LT.LatticeTree.Vertex 𝒪 K₀)) := by
    obtain ⟨S, hS⟩ := hcocpt
    refine Finite.of_surjective
      (fun s : ↥S => (Quotient.mk (MulAction.orbitRel (↥(Γ'.map ρ)) (LT.LatticeTree.Vertex 𝒪 K₀)) (s : LT.LatticeTree.Vertex 𝒪 K₀) :
        QuotVert (↥(Γ'.map ρ)) (LT.LatticeTree.Vertex 𝒪 K₀))) ?_
    intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g, hg, hgv⟩ := hS v
    refine ⟨⟨g • v, hgv⟩, ?_⟩
    apply Quotient.sound
    show g • v ∈ MulAction.orbit (↥(Γ'.map ρ)) v
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, rfl⟩

  have h3 : Finite (QuotEdge (↥(Γ'.map ρ)) (BruhatTits.tree 𝒪 K₀)) :=
    CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert 𝒪 K₀ π hπ (G := ↥(Γ'.map ρ))

  have h4 : Γ'.map ρ ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    have hγ' := (hΓ' γ).mp hγ
    obtain ⟨u, hu⟩ := (hvdet (σ γ) (Multiplicative.toAdd (vdet (σ γ)))).mp (by simp)
    have key := CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_of_det_eq_mul_zpow 𝒪 K₀ π hπ
      (PGL(2, K₀)) (MonoidHom.id (PGL(2, K₀))) (fun _ _ => rfl) (ρ γ) (σ γ)
      (by rw [MonoidHom.id_apply]; exact hρ γ) u (Multiplicative.toAdd (vdet (σ γ)))
      (by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hu)
    exact key.mpr hγ'.2

  have h5 : ∀ g ∈ Γ'.map ρ, ∀ d : (BruhatTits.tree 𝒪 K₀).Dart, g • d ≠ d.symm := by
    intro g hg d hd
    have hadj := (CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
      (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) hconn hbip (LT.LatticeTree.stdVertex 𝒪 K₀)).1 d.fst d.snd d.adj
    have hfix := (mem_typePreserving_iff _ _ g).mp (h4 hg) d.fst
    have hmove : g • d.fst = d.snd := by
      rw [← smul_dart_fst, hd]; rfl
    rw [hmove] at hfix
    rw [hfix] at hadj
    exact zmod2_ne_add_one _ hadj

  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · exact (Group.fg_iff_subgroup_fg _).mp
      (CerednikDrinfeld.Mumford.fg_of_finite_stabilizer_of_finite_quotVert_of_finite_quotEdge
        (G := ↥(Γ'.map ρ)) (BruhatTits.tree 𝒪 K₀) hconn h1 h2 h3)
  · exact relIndex_map_ne_zero ρ Γ Γ' (fun x hx => ((hΓ' x).mp hx).1)
      (relIndex_ne_zero_of_even (vdet.comp σ) Γ Γ' hΓ')

end S_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart (solution)
