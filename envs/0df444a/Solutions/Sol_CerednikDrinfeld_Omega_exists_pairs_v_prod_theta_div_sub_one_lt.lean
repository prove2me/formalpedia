-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/98199229-8b7a-5caa-a879-ac4508faa40a

import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace C2bGlue

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_pu {x : K} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this, Valuation.map_one_add_of_lt _ hx]

theorem pu_mul {x y : K} (hx : Valued.v (x - 1) < 1) (hy : Valued.v (y - 1) < 1) : Valued.v (x * y - 1) < 1 := by
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  refine Valuation.map_add_lt _ ?_ hx
  rw [map_mul, v_eq_one_of_pu hx, one_mul]
  exact hy

theorem pu_inv {x : K} (hx : Valued.v (x - 1) < 1) : Valued.v (x⁻¹ - 1) < 1 := by
  have hx1 := v_eq_one_of_pu hx
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hx1]; exact one_ne_zero)
  have : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hx1, inv_one, one_mul]
  exact hx

theorem pu_prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, Valued.v (f i - 1) < 1) :
    Valued.v (∏ i ∈ s, f i - 1) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact pu_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_pow_eq_of_v_eq_one [IsAlgClosed K] (u : Kˣ) (hu : Valued.v ((u : Kˣ) : K) = 1) (n : ℕ) (hn : 0 < n) :
    ∃ x : Kˣ, Valued.v ((x : Kˣ) : K) = 1 ∧ x ^ n = u := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((u : Kˣ) : K) hn
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, zero_pow hn.ne'] at hy; exact u.ne_zero hy.symm
  have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hvy : Valued.v y = 1 := by
    have h := congrArg Valued.v hy
    rw [map_pow, hu] at h
    have hu' : (Units.mk0 (Valued.v y) hvy0) ^ n = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact h
    have := (pow_eq_one_iff.1 hu').resolve_right hn.ne'
    exact (Units.val_mk0 hvy0).symm.trans (congrArg Units.val this)
  refine ⟨Units.mk0 y hy0, by rw [Units.val_mk0]; exact hvy, ?_⟩
  apply Units.ext
  simp [hy]

theorem finite_quotEdge
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))] :
    Finite (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) := by
  classical

  have hdarts : ∀ w : LT.LatticeTree.Vertex R K₀, {d : (CerednikDrinfeld.BruhatTits.tree R K₀).Dart | d.fst = w}.Finite := by
    intro w
    have hball := CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R K₀ ϖ hϖ w 1
    refine Set.Finite.of_injOn (f := fun d : (CerednikDrinfeld.BruhatTits.tree R K₀).Dart => d.snd)
      (fun d hd => ?_) (fun d₁ hd₁ d₂ hd₂ h => ?_) hball
    · show (CerednikDrinfeld.BruhatTits.tree R K₀).dist w d.snd ≤ 1
      rw [Set.mem_setOf_eq] at hd
      rw [← hd, SimpleGraph.dist_eq_one_iff_adj.2 d.adj]
    · rw [Set.mem_setOf_eq] at hd₁ hd₂
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd₁.trans hd₂.symm) h)

  let S : Set (CerednikDrinfeld.BruhatTits.tree R K₀).Dart :=
    ⋃ o : CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀), {d | d.fst = o.out}
  have hS : S.Finite := Set.finite_iUnion fun o => hdarts o.out
  haveI := hS.to_subtype
  refine Finite.of_surjective (fun d : ↥S => (Quotient.mk _ (d : (CerednikDrinfeld.BruhatTits.tree R K₀).Dart) :
    CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h d =>
    let o : CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀) :=
      Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) d.fst
    have ho : ∃ g : G, g • d.fst = o.out := by
      have h := Quotient.mk_out (s := MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) d.fst

      obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 h
      exact ⟨g, hg⟩
    obtain ⟨g, hg⟩ := ho
    refine ⟨⟨g • d, Set.mem_iUnion.2 ⟨o, ?_⟩⟩, ?_⟩
    · show (g • d).fst = o.out
      rw [CerednikDrinfeld.Mumford.smul_dart_fst]; exact hg
    · show Quotient.mk _ (g • d) = Quotient.mk _ d
      exact Quotient.sound ⟨g, rfl⟩

end C2bGlue

open C2bGlue in
set_option maxHeartbeats 1600000 in
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

    (η : G →* Kˣ) (hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1) (hη : ∀ γ : G, IsOfFinOrder γ → η γ = 1) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) = 1 ∧
        Valued.v (((η β : Kˣ) : K) / (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) - 1) < 1 := by
  classical
  haveI hfe := finite_quotEdge R K₀ ϖ hϖ (G := G)
  let E := {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}
  haveI : Fintype E := Fintype.ofFinite E

  obtain ⟨ζ, hζ1, hζ⟩ := CerednikDrinfeld.Omega.exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
    R K₀ K hfin τ hτ hadj (Equiv.refl E) η hη₁ hη

  have hroot : ∀ e : E, ∃ ξ : Kˣ, Valued.v ((ξ : Kˣ) : K) = 1 ∧
      ξ ^ ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) ((Equiv.refl E) e).1 : ℕ+) : ℕ) = ζ e :=
    fun e => exists_pow_eq_of_v_eq_one (ζ e) (hζ1 e) _ (PNat.pos _)
  choose ξ hξ1 hξ using hroot

  have hpair := fun e : E => CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt
    R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame z₀ hz₀ (Equiv.refl E) e (ξ e) (hξ1 e)
  choose a b ha hb ha0 hb0 hab using hpair

  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin E
  refine ⟨n, fun i => a (eqv.symm i), fun i => b (eqv.symm i), fun i => ha _, fun i => hb _, fun i => ha0 _,
    fun i => hb0 _, fun β => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun i _ => (hab (eqv.symm i) β).1
  ·
    set T : E → K := fun e => theta ρ (a e) (b e) z₀ (pmoebius K₀ (ρ β) z₀) with hT
    set mexp : E → ℤ := fun e =>
      ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) ((Equiv.refl E) e).1 : ℕ) : ℤ) *
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => ((Equiv.refl E) e').1)
          (LT.LatticeTree.stdVertex R K₀) β e with hmexp

    have hprodE : (∏ i : Fin n, theta ρ (a (eqv.symm i)) (b (eqv.symm i)) z₀ (pmoebius K₀ (ρ β) z₀)) = ∏ e : E, T e := by
      rw [hT]
      exact Fintype.prod_equiv eqv.symm (fun i => theta ρ (a (eqv.symm i)) (b (eqv.symm i)) z₀ (pmoebius K₀ (ρ β) z₀))
        (fun e => theta ρ (a e) (b e) z₀ (pmoebius K₀ (ρ β) z₀)) (fun i => rfl)

    have hu : ∀ e : E, Valued.v (T e * (((ξ e : Kˣ) : K) ^ mexp e)⁻¹ - 1) < 1 := fun e => (hab e β).2
    have hP := pu_prod (Finset.univ : Finset E) _ fun e _ => hu e
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hP

    have hY : (∏ e : E, ((ξ e : Kˣ) : K) ^ mexp e) = ((η β : Kˣ) : K) := by
      rw [hζ β]
      refine Finset.prod_congr rfl fun e _ => ?_
      rw [hmexp, zpow_mul, ← hξ e, Units.val_pow_eq_pow_val, zpow_natCast]
    rw [hY] at hP

    have hfinal := pu_inv hP
    rw [mul_inv, inv_inv, ← div_eq_inv_mul] at hfinal
    rw [hprodE]
    exact hfinal

end S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt (solution)
