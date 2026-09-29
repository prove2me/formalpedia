-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ade6ae31-aa69-599a-9abd-842c449521ad

import Theorems.Thm_CerednikDrinfeld_Mumford_pathCycle_mulEquiv_eq_of_iso
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.pathCycle Mumford.GraphAction Mumford.QuotEdge DegeneracyData ribbonKernel BruhatTits.tree_isTree tree BruhatTits.tree BruhatTits.tree_connected_and_colorable_two Mumford.vertexType Mumford.typePreserving"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "pathCycle_mulEquiv_eq_of_iso walkCycle pathCycle GraphAction QuotEdge quotientReversal GraphAction.smul_adj vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter vertexType typePreserving"
namespace ActZNat
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

theorem pathCycle_apply_congr {G W : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] {E E' : Type} (orb : E → QuotEdge G 𝒯) (orb' : E' → QuotEdge G 𝒯)
    (v₀ : W) (g : G) (e : E) (e' : E') (h : orb e = orb' e') :
    pathCycle 𝒯 orb v₀ g e = pathCycle 𝒯 orb' v₀ g e' := by
  unfold pathCycle
  by_cases hr : 𝒯.Reachable v₀ (g • v₀)
  · rw [dif_pos hr, dif_pos hr]
    simp only [walkCycle, h]
  · rw [dif_neg hr, dif_neg hr]
    rfl

def conjEquiv {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) : ↥H ≃* ↥H where
  toFun x := ⟨p * x * p⁻¹, h₁ x x.2⟩
  invFun x := ⟨p⁻¹ * x * p, h₂ x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[scoped simp] theorem conjEquiv_coe {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) (x : ↥H) :
    ((conjEquiv H p h₁ h₂ x : ↥H) : P) = p * x * p⁻¹ := rfl

def smulIso {P W : Type} [Group P] [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯] (p : P) : 𝒯 ≃g 𝒯 where
  toEquiv := MulAction.toPerm p
  map_rel_iff' {a b} := by
    refine ⟨fun h => ?_, fun h => GraphAction.smul_adj p h⟩
    have := GraphAction.smul_adj (𝒯 := 𝒯) p⁻¹ h
    simpa using this

@[scoped simp] theorem smulIso_apply {P W : Type} [Group P] [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯]
    (p : P) (w : W) : smulIso 𝒯 p w = p • w := rfl

theorem smulIso_mapDart {P W : Type} [Group P] [MulAction P W] (𝒯 : SimpleGraph W) [GraphAction P 𝒯]
    (p : P) (d : 𝒯.Dart) : (smulIso 𝒯 p).toHom.mapDart d = p • d := by
  ext <;> rfl

end CerednikDrinfeld.Mumford.ActZNat
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld.Mumford.ActZNat"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld.Mumford"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.CerednikDrinfeld"

open CerednikDrinfeld.Mumford.ActZNat in
theorem solution

    (K₀ : Type) [Field K₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (n : G) (hn : n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G))
    (π : Equiv.Perm E) (s : ℤˣ)
    (hπ : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = 1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = -1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (A : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))
    (hA : ∀ (x : ↥(ribbonKernel D)) (e : E), (A x : E → ℤ) (π e) = ((s : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∀ γ γ' : ↥(Γ.map ρ), (γ' : PGL(2, K₀)) = ρ n * (γ : PGL(2, K₀)) * (ρ n)⁻¹ →
      Φ (Additive.ofMul (Abelianization.of γ')) = A (Φ (Additive.ofMul (Abelianization.of γ))) := by
  classical
  intro γ γ' hconj

  have hT : (BruhatTits.tree R₀ K₀).IsTree := BruhatTits.tree_isTree R₀ K₀
  obtain ⟨hconn, hcol⟩ := BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hτ : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => htp g.2 w
  have hadj : ∀ u v : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u v →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v := by
    intro u v huv h
    have h1 := (vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter (↥(Γ.map ρ))
      (BruhatTits.tree R₀ K₀) hconn hcol (LT.LatticeTree.stdVertex R₀ K₀)).1 u v huv
    rw [h] at h1
    have h2 : (1 : ZMod 2) = 0 := by
      have := congrArg (fun t => t - Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v) h1
      simpa using this.symm
    exact absurd h2 (by decide)

  have h₁ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → ρ n * x * (ρ n)⁻¹ ∈ Γ.map ρ := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨n * m * n⁻¹, (hn m).1 hm, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have h₂ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → (ρ n)⁻¹ * x * ρ n ∈ Γ.map ρ := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨n⁻¹ * m * n, (hn (n⁻¹ * m * n)).2 (by simpa [mul_assoc] using hm), ?_⟩
    rw [map_mul, map_mul, map_inv]
  let φ : ↥(Γ.map ρ) ≃* ↥(Γ.map ρ) := conjEquiv (Γ.map ρ) (ρ n) h₁ h₂
  let ν : BruhatTits.tree R₀ K₀ ≃g BruhatTits.tree R₀ K₀ := smulIso (BruhatTits.tree R₀ K₀) (ρ n)
  have hν : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀), ν (g • w) = φ g • ν w := by
    intro g w
    show ρ n • ((g : PGL(2, K₀)) • w) = ((φ g : ↥(Γ.map ρ)) : PGL(2, K₀)) • (ρ n • w)
    rw [conjEquiv_coe, smul_smul, smul_smul, mul_assoc, inv_mul_cancel, mul_one]

  have hπ' : ∀ (e : E) (d : (BruhatTits.tree R₀ K₀).Dart),
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) d = (eE.symm e).1 →
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ν.toHom.mapDart d) =
        (if s = 1 then (eE.symm (π e)).1
          else quotientReversal ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) (eE.symm (π e)).1) := by
    intro e d hd
    rw [smulIso_mapDart]

    have hd' : Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) d =
        Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (eE.symm e).1.out := by
      rw [hd, Quotient.out_eq]
    obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact hd')

    have htr : ρ n • d = φ δ • (ρ n • (eE.symm e).1.out) := by
      rw [← hδ]
      ext
      · show ρ n • ((δ : PGL(2, K₀)) • ((eE.symm e).1.out).fst) =
          ((φ δ : ↥(Γ.map ρ)) : PGL(2, K₀)) • (ρ n • ((eE.symm e).1.out).fst)
        rw [conjEquiv_coe, smul_smul, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
      · show ρ n • ((δ : PGL(2, K₀)) • ((eE.symm e).1.out).snd) =
          ((φ δ : ↥(Γ.map ρ)) : PGL(2, K₀)) • (ρ n • ((eE.symm e).1.out).snd)
        rw [conjEquiv_coe, smul_smul, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
    have hcls : Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • d) =
        Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • (eE.symm e).1.out) := by
      rw [htr]
      exact Quotient.sound (MulAction.mem_orbit _ _)
    have hπe := hπ (eE.symm e)
    rw [Equiv.apply_symm_apply] at hπe
    by_cases htpn : ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)
    · obtain ⟨hs, he⟩ := hπe.1 htpn
      rw [if_pos hs, he, hcls]
    · obtain ⟨hs, he⟩ := hπe.2 htpn
      have hs1 : s ≠ 1 := by rw [hs]; decide
      rw [if_neg hs1, he, hcls]
      show _ = Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • (eE.symm e).1.out).symm.symm
      rw [SimpleGraph.Dart.symm_symm]

  have key := fun (g : ↥(Γ.map ρ)) (e : E) =>
    pathCycle_mulEquiv_eq_of_iso (BruhatTits.tree R₀ K₀) hT
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj
      eE.symm φ ν hν π s hπ' v₀ g e

  have hΦ' : ∀ (g : ↥(Γ.map ρ)) (e : E), (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) e =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) v₀ g e := by
    intro g e
    have := hΦ g (eE.symm e)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact pathCycle_apply_congr _ _ _ v₀ g _ _ rfl

  have hγ' : γ' = φ γ := Subtype.ext (by rw [conjEquiv_coe]; exact hconj)

  apply Subtype.ext
  funext e₁
  obtain ⟨e, rfl⟩ := π.surjective e₁
  rw [hA, hΦ', hΦ', hγ']
  exact key γ e

end S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle (solution)
