-- Prove2me | solution 1 for CerednikDrinfeld.Omega.isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5fead776-bf71-5a76-98e7-98f946de4519

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CerednikDrinfeld_Ribbon

import Mathlib
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace SchottkyTF

open MulAction

theorem finite_orbitQuot_of_relIndex_ne_zero {G : Type} [Group G] {X : Type} [MulAction G X]
    (Γ Γ'' : Subgroup G) (_hle : Γ'' ≤ Γ) (hidx : Γ''.relIndex Γ ≠ 0)
    [Finite (orbitRel.Quotient ↥Γ X)] : Finite (orbitRel.Quotient ↥Γ'' X) := by
  classical
  haveI : (Γ''.subgroupOf Γ).FiniteIndex := ⟨hidx⟩
  haveI : Finite (↥Γ ⧸ Γ''.subgroupOf Γ) := Subgroup.finite_quotient_of_finiteIndex
  let f : (↥Γ ⧸ Γ''.subgroupOf Γ) × orbitRel.Quotient ↥Γ X → orbitRel.Quotient ↥Γ'' X :=
    fun p => Quotient.mk (orbitRel ↥Γ'' X) ((p.1.out)⁻¹ • p.2.out)
  refine Finite.of_surjective f ?_
  intro o
  induction o using Quotient.inductionOn with
  | h x =>
    set oΓ : orbitRel.Quotient ↥Γ X := Quotient.mk (orbitRel ↥Γ X) x with hoΓ
    have hx₀ : (orbitRel ↥Γ X) oΓ.out x := Quotient.mk_out x
    obtain ⟨γ, hγ⟩ := (orbitRel_apply.mp hx₀ : oΓ.out ∈ orbit ↥Γ x)
    have hxγ : x = γ⁻¹ • oΓ.out := by rw [← hγ, inv_smul_smul]
    set q : ↥Γ ⧸ Γ''.subgroupOf Γ := QuotientGroup.mk γ with hq
    refine ⟨(q, oΓ), ?_⟩
    show Quotient.mk (orbitRel ↥Γ'' X) ((q.out)⁻¹ • oΓ.out) = Quotient.mk (orbitRel ↥Γ'' X) x
    apply Quotient.sound
    have hmem : γ⁻¹ * q.out ∈ Γ''.subgroupOf Γ := by
      rw [← QuotientGroup.eq]; exact (QuotientGroup.out_eq' q).symm ▸ rfl
    show (q.out)⁻¹ • oΓ.out ∈ orbit (↥Γ'') x
    rw [mem_orbit_iff]
    have hmem' : ((q.out : ↥Γ) : G)⁻¹ * (γ : G) ∈ Γ'' := by
      have := Γ''.inv_mem (Subgroup.mem_subgroupOf.mp hmem)
      simpa using this
    refine ⟨⟨_, hmem'⟩, ?_⟩
    rw [Subgroup.mk_smul, hxγ, Subgroup.smul_def, Subgroup.smul_def, Subgroup.coe_inv, Subgroup.coe_inv, mul_smul,
      smul_inv_smul]

theorem finite_orbitQuot_map {G H : Type} [Group G] [Group H] {X : Type} [MulAction G X] [MulAction H X]
    (ρ : G →* H) (hact : ∀ (g : G) (x : X), g • x = ρ g • x) (Γ'' : Subgroup G)
    [Finite (orbitRel.Quotient ↥Γ'' X)] : Finite (orbitRel.Quotient ↥(Γ''.map ρ) X) := by
  let f : orbitRel.Quotient ↥Γ'' X → orbitRel.Quotient ↥(Γ''.map ρ) X :=
    Quotient.map' id (fun a b hab => by
      obtain ⟨γ, hγ⟩ := (orbitRel_apply.mp hab : a ∈ orbit ↥Γ'' b)
      show a ∈ orbit ↥(Γ''.map ρ) b
      rw [mem_orbit_iff]
      refine ⟨⟨ρ γ, Subgroup.mem_map_of_mem ρ γ.2⟩, ?_⟩
      rw [Subgroup.mk_smul, ← hact]
      exact hγ)
  refine Finite.of_surjective f ?_
  intro o
  induction o using Quotient.inductionOn with
  | h x => exact ⟨Quotient.mk _ x, rfl⟩

theorem coe_eq_one_of_pow_mem_finite {H : Type} [Group H] (A : Subgroup H) (F : Subgroup ↥A) [Finite ↥F]
    (T : Subgroup H) (hT : ∀ g ∈ T, IsOfFinOrder g → g = 1)
    {x : ↥A} (hxT : (x : H) ∈ T) {n : ℕ} (hn : n ≠ 0) (hxn : x ^ n ∈ F) : (x : H) = 1 := by
  have h1 : IsOfFinOrder (⟨x ^ n, hxn⟩ : ↥F) := isOfFinOrder_of_finite _
  obtain ⟨m, hm, hm1⟩ := isOfFinOrder_iff_pow_eq_one.mp h1
  have h2 : ((x : H) ^ n) ^ m = 1 := by
    have := congrArg (fun y : ↥F => ((y : ↥A) : H)) hm1
    simpa using this
  have h3 : IsOfFinOrder ((x : H) ^ n) := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h2⟩
  exact hT _ hxT (IsOfFinOrder.of_pow h3 hn)

end SchottkyTF

open MulAction in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G)
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge Γ (BruhatTits.tree R₀ K₀))]
    (hexch : ∃ γ : G, γ ∈ Γ ∧ γ ∉ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))

    (Γ'' : Subgroup G) (hle : Γ'' ≤ Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hidx : Γ''.relIndex (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) ≠ 0)
    (htf : ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1) :
    Mumford.IsSchottky ↥(Γ''.map ρ) (BruhatTits.tree R₀ K₀) := by
  classical
  obtain ⟨hconn, hbip⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hΓ''Γ : Γ'' ≤ Γ := hle.trans inf_le_left
  have hmapΓ : Γ''.map ρ ≤ Γ.map ρ := Subgroup.map_mono hΓ''Γ

  haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
    have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mp hϖ₀
    exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv

  have hactV : ∀ (g : G) (w : LT.LatticeTree.Vertex R₀ K₀), g • w = ρ g • w := hact
  have hactD : ∀ (g : G) (d : (BruhatTits.tree R₀ K₀).Dart), g • d = ρ g • d := by
    intro g d
    apply SimpleGraph.Dart.ext
    exact Prod.ext (hact g d.fst) (hact g d.snd)

  have hidxΓ : Γ''.relIndex Γ ≠ 0 := by
    obtain ⟨⟨φ, hφ⟩, -⟩ := CerednikDrinfeld.Mumford.exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two (G := G)
      (BruhatTits.tree R₀ K₀) hconn hbip (LT.LatticeTree.stdVertex R₀ K₀)
    have h1 : (Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).relIndex Γ ≠ 0 := by
      show ((Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).subgroupOf Γ).index ≠ 0
      have e : (Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).subgroupOf Γ =
          (φ.comp Γ.subtype).ker := by
        rw [← MonoidHom.comap_ker, hφ]; rfl
      rw [e, Subgroup.index_ker]
      exact Nat.card_pos.ne'
    have h2 : (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).relIndex Γ ≠ 0 := by
      rw [inf_comm, Subgroup.inf_relIndex_right]; exact h1
    rw [← Subgroup.relIndex_mul_relIndex Γ'' _ Γ hle inf_le_left]
    exact mul_ne_zero hidx h2

  have hfinV : Finite (orbitRel.Quotient ↥(Γ''.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := by
    haveI : Finite (orbitRel.Quotient ↥Γ'' (LT.LatticeTree.Vertex R₀ K₀)) :=
      SchottkyTF.finite_orbitQuot_of_relIndex_ne_zero Γ Γ'' hΓ''Γ hidxΓ
    exact SchottkyTF.finite_orbitQuot_map ρ hactV Γ''
  have hfinE : Finite (orbitRel.Quotient ↥(Γ''.map ρ) (BruhatTits.tree R₀ K₀).Dart) := by
    haveI : Finite (orbitRel.Quotient ↥Γ'' (BruhatTits.tree R₀ K₀).Dart) :=
      SchottkyTF.finite_orbitQuot_of_relIndex_ne_zero Γ Γ'' hΓ''Γ hidxΓ
    exact SchottkyTF.finite_orbitQuot_map ρ hactD Γ''

  have hnoinv : ∀ (g : ↥(Γ''.map ρ)) (d : (BruhatTits.tree R₀ K₀).Dart), g • d ≠ d.symm := by
    intro g d h
    let x : ↥(Γ.map ρ) := ⟨(g : PGL(2, K₀)), hmapΓ g.2⟩
    have hx2 : x ^ 2 ∈ stabilizer (↥(Γ.map ρ)) d := by
      rw [mem_stabilizer_iff, pow_two, mul_smul]
      have e1 : x • d = d.symm := by rw [Subgroup.smul_def]; rw [Subgroup.smul_def] at h; exact h
      rw [e1, ← Mumford.smul_dart_symm, e1, SimpleGraph.Dart.symm_symm]
    haveI := hfin d
    have hg1 : ((x : ↥(Γ.map ρ)) : PGL(2, K₀)) = 1 :=
      SchottkyTF.coe_eq_one_of_pow_mem_finite (Γ.map ρ) (stabilizer (↥(Γ.map ρ)) d) (Γ''.map ρ) htf g.2 two_ne_zero hx2
    have : (g : PGL(2, K₀)) = 1 := hg1
    rw [Subgroup.smul_def, this, one_smul] at h
    exact (SimpleGraph.Dart.symm_ne d) h.symm

  have hfree : ∀ w : LT.LatticeTree.Vertex R₀ K₀, stabilizer (↥(Γ''.map ρ)) w = ⊥ := by
    intro w
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [mem_stabilizer_iff, Subgroup.smul_def] at hg

    obtain ⟨γ, hγΓ, hγtp⟩ := hexch
    rw [Mumford.mem_typePreserving_iff] at hγtp
    push Not at hγtp
    obtain ⟨v, hv⟩ := hγtp
    have hvne : γ • v ≠ v := fun e => hv (by rw [e])
    have huw : ∃ u : LT.LatticeTree.Vertex R₀ K₀, u ≠ w := by
      by_cases h : v = w
      · exact ⟨γ • v, by rw [← h]; exact hvne⟩
      · exact ⟨v, h⟩
    obtain ⟨u, hu⟩ := huw
    obtain ⟨p⟩ := hconn.preconnected w u
    have hdart : ∃ d : (BruhatTits.tree R₀ K₀).Dart, d.fst = w := by
      cases p with
      | nil => exact absurd rfl hu.symm
      | cons hadj _ => exact ⟨⟨(w, _), hadj⟩, rfl⟩
    obtain ⟨d₀, hd₀⟩ := hdart

    haveI hDf : Finite {d : (BruhatTits.tree R₀ K₀).Dart // d.fst = w} := by
      have hN := CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R₀ K₀ ϖ₀ hϖ₀ w 1
      haveI : Finite ↥({v : LT.LatticeTree.Vertex R₀ K₀ | (BruhatTits.tree R₀ K₀).dist w v ≤ 1}) := hN.to_subtype
      refine Finite.of_injective (fun d : {d : (BruhatTits.tree R₀ K₀).Dart // d.fst = w} =>
        (⟨d.1.snd, by
          show (BruhatTits.tree R₀ K₀).dist w d.1.snd ≤ 1
          have hadj : (BruhatTits.tree R₀ K₀).Adj w d.1.snd := by
            have h := d.1.adj
            have e : d.1.fst = w := d.2
            rwa [e] at h
          rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hadj]⟩ :
          ↥({v : LT.LatticeTree.Vertex R₀ K₀ | (BruhatTits.tree R₀ K₀).dist w v ≤ 1}))) ?_
      intro a b hab
      apply Subtype.ext
      apply SimpleGraph.Dart.ext
      exact Prod.ext (a.2.trans b.2.symm) (congrArg Subtype.val hab)

    let x : ↥(Γ.map ρ) := ⟨(g : PGL(2, K₀)), hmapΓ g.2⟩
    have hxw : (x : PGL(2, K₀)) • w = w := hg
    have hpow : ∀ n : ℕ, ((x ^ n) • d₀).fst = w := by
      intro n
      induction n with
      | zero => rw [pow_zero, one_smul]; exact hd₀
      | succ n ih =>
          rw [pow_succ', mul_smul]
          show (x • (x ^ n • d₀)).toProd.1 = w
          change (x : PGL(2, K₀)) • ((x ^ n • d₀).fst) = w
          rw [ih, hxw]
    obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨(x ^ n) • d₀, hpow n⟩ : {d : (BruhatTits.tree R₀ K₀).Dart // d.fst = w}))
    have he' : x ^ i • d₀ = x ^ j • d₀ := congrArg Subtype.val he

    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · have hst : x ^ (j - i) ∈ stabilizer (↥(Γ.map ρ)) (x ^ i • d₀) := by
        rw [mem_stabilizer_iff, ← mul_smul, pow_sub_mul_pow x hlt.le, ← he']
      haveI := hfin (x ^ i • d₀)
      have := SchottkyTF.coe_eq_one_of_pow_mem_finite (Γ.map ρ) (stabilizer (↥(Γ.map ρ)) (x ^ i • d₀)) (Γ''.map ρ) htf
        g.2 (Nat.sub_ne_zero_of_lt hlt) hst
      exact Subtype.ext this
    · have hst : x ^ (i - j) ∈ stabilizer (↥(Γ.map ρ)) (x ^ j • d₀) := by
        rw [mem_stabilizer_iff, ← mul_smul, pow_sub_mul_pow x hlt.le, he']
      haveI := hfin (x ^ j • d₀)
      have := SchottkyTF.coe_eq_one_of_pow_mem_finite (Γ.map ρ) (stabilizer (↥(Γ.map ρ)) (x ^ j • d₀)) (Γ''.map ρ) htf
        g.2 (Nat.sub_ne_zero_of_lt hlt) hst
      exact Subtype.ext this
  exact ⟨hfree, hnoinv, hfinV, hfinE⟩

end S_CerednikDrinfeld_Omega_isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder (solution)
