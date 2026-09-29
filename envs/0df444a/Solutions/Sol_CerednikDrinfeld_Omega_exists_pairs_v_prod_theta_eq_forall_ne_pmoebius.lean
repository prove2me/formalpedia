-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c1d845c9-2d26-5ac1-a2e5-322ff0aa5fd5

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_Ribbon
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.GroupWithZero.Range
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford
open CerednikDrinfeld MulAction

namespace VALFACTOR

theorem exists_v_eq_prod_v_zpow
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D))
    (hΦ : ∀ g : G, (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g)
    (hfinw : ∀ w : W, Finite ↥(stabilizer G w))
    (K : Type) [Field K] [IsAlgClosed K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (χ : G →* Kˣ) :
    ∃ x : E → K, (∀ e, x e ≠ 0) ∧
      ∀ g : G, Valued.v ((χ g : Kˣ) : K) = ∏ e : E, Valued.v (x e) ^ ((Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) e) := by
  classical
  let vv : Valuation K Γ₀ := Valued.v
  let A : Subgroup Γ₀ˣ := MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vv)

  have hne : ∀ g : G, vv ((χ g : Kˣ) : K) ≠ 0 := fun g => (Valuation.ne_zero_iff vv).mpr (χ g).ne_zero
  let c : G →* ↥A :=
    { toFun := fun g => ⟨Units.mk0 (vv ((χ g : Kˣ) : K)) (hne g), MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass vv) ⟨_, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp [map_mul] }
  have hcval : ∀ g : G, (((c g : ↥A) : Γ₀ˣ) : Γ₀) = vv ((χ g : Kˣ) : K) := fun g => rfl

  have hval : ∀ a : ↥A, ∃ y : K, y ≠ 0 ∧ vv y = ((a : Γ₀ˣ) : Γ₀) := by
    intro a
    have : ((a : Γ₀ˣ) : Γ₀) ∈ Units.val '' (A : Set Γ₀ˣ) := ⟨a, a.2, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at this
    obtain ⟨⟨y, hy⟩, h0⟩ := this
    refine ⟨y, fun h => ?_, hy⟩
    rw [h, map_zero] at hy; exact (a : Γ₀ˣ).ne_zero hy.symm
  have hdiv : ∀ (a : ↥A) (n : ℕ), n ≠ 0 → ∃ b : ↥A, b ^ n = a := by
    intro a n hn
    obtain ⟨y, hy0, hy⟩ := hval a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow hn] at hz; exact hy0 hz.symm
    refine ⟨⟨Units.mk0 (vv z) ((Valuation.ne_zero_iff vv).mpr hz0), MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass vv) ⟨_, rfl⟩⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← map_pow, hz, hy]

  have hc : ∀ (w : W) (g : G), g ∈ stabilizer G w → c g = 1 := by
    intro w g hg
    haveI := hfinw w
    have hfo : IsOfFinOrder (⟨g, hg⟩ : ↥(stabilizer G w)) := isOfFinOrder_of_finite _
    obtain ⟨n, hn, hpow⟩ := hfo.exists_pow_eq_one
    have h1 : (c g) ^ n = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(stabilizer G w)) ^ n = 1 := hpow
      have hg1 : g ^ n = 1 := by simpa using congrArg Subtype.val this
      rw [hg1, map_one]
    have h2 : ((c g : ↥A) : Γ₀ˣ) ^ n = 1 := by
      have := congrArg (fun a : ↥A => (a : Γ₀ˣ)) h1; simpa using this
    have h3 : ((c g : ↥A) : Γ₀ˣ) = 1 := (pow_eq_one_iff_left hn.ne').mp h2
    exact Subtype.ext (by simpa using h3)
  obtain ⟨ν, hν⟩ := CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
    𝒯 hT τ hτ hadj D eE eV ha hb v₀ Φ hΦ (↥A) hdiv c hc
  choose x hx0 hx using fun e => hval (ν e)
  refine ⟨x, hx0, fun g => ?_⟩
  rw [← hcval g, hν g]
  set nn : E → ℤ := ((Φ (Additive.ofMul (Abelianization.of g)) : ↥(ribbonKernel D)) : E → ℤ) with hnn
  have h1 : ((∏ e : E, ν e ^ nn e : ↥A) : Γ₀ˣ) = ∏ e : E, ((ν e : ↥A) : Γ₀ˣ) ^ nn e := by
    rw [← Subgroup.coe_subtype, map_prod]
    simp only [map_zpow, Subgroup.coe_subtype]
  rw [h1, Units.coe_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Units.val_zpow_eq_zpow_val, hx]

end VALFACTOR

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)

    (χ : G →* Kˣ)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) = Valued.v ((χ β : Kˣ) : K) := by
  classical

  haveI : Finite (Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) :=
    CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert R K₀ ϖ hϖ
  letI : Fintype (Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) := Fintype.ofFinite _
  let E := {e : Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}
  let eE : E ≃ {e : Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0} := Equiv.refl _
  have hT := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  let V := Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀)
  let D : CerednikDrinfeld.DegeneracyData E V :=
    ⟨fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
     fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd, fun _ => 1⟩
  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V) (fun _ => rfl) (fun _ => rfl) (LT.LatticeTree.stdVertex R K₀)

  obtain ⟨x, hx0, hx⟩ := VALFACTOR.exists_v_eq_prod_v_zpow (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V)
    (fun _ => rfl) (fun _ => rfl) (LT.LatticeTree.stdVertex R K₀) Φ hΦ hfin K χ

  have hroot : ∀ e : E, ∃ t : K, t ≠ 0 ∧
      Valued.v t ^ ((Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) = Valued.v (x e) := by
    intro e
    set w : ℕ := (Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) with hw
    have hwpos : 0 < w := (Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1).pos
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (x e) hwpos
    refine ⟨t, fun h => hx0 e (by rw [← ht, h, zero_pow hwpos.ne']), ?_⟩
    rw [zpow_natCast, ← map_pow, ht]
  choose t ht0 ht using hroot

  have step : ∀ s : Finset E, ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s' ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s' : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s' : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) =
        ∏ e ∈ s, Valued.v (t e) ^ (((Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun _ _ i => i.elim0, fun β => ?_⟩
      simp
    | insert e s hes ih =>
      obtain ⟨n, a, b, ha, hb, haz, hbz, hS, hprod⟩ := ih
      obtain ⟨m, a', b', ha', hb', haz', hbz', hS', hprod'⟩ :=
        CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
          R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame z₀ hz₀ eE e (t e) (ht0 e) S
      refine ⟨n + m, Fin.append a a', Fin.append b b', ?_, ?_, ?_, ?_, ?_, fun β => ?_⟩
      · intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ha, ha']
      · intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hb, hb']
      · intro i γ; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [haz, haz']
      · intro i γ; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hbz, hbz']
      · intro s' hs' i δ; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hS s' hs' j δ
        · simpa using hS' s' hs' j δ
      · rw [Fin.prod_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [map_mul, hprod β, hprod' β, Finset.prod_insert hes, mul_comm]
  obtain ⟨n, a, b, ha, hb, haz, hbz, hS, hprod⟩ := step Finset.univ
  refine ⟨n, a, b, ha, hb, haz, hbz, hS, fun β => ?_⟩
  rw [hprod β, hx β, hΦ β]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [zpow_mul, ht e]

end S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_forall_ne_pmoebius (solution)
