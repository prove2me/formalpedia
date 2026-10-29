-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.mnat2_convex_set_is_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T02:43:11.489193+00:00
-- url     : https://prove2.me/submissions/64cd897d-e324-4c14-823c-fd3ba1a8edbc

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvex
import Theorems.Thm_DiscreteConvex_MConvexSetsB_mconvex_intersection_hull

open scoped BigOperators
open DiscreteConvex.ConjugacyDualityB
namespace ConjugacySetProof

variable {V : Type*} [Fintype V] [DecidableEq V]

private def liftZ (z : V → ℤ) : Option V → ℤ
  | none => - ∑ v, z v
  | some v => z v

private def liftR : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun p := fun o => match o with | none => - ∑ v, p v | some v => p v
  map_add' p q := by
    funext o; cases o <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a p := by
    funext o; cases o <;> simp [Finset.mul_sum]

private def projectR : (Option V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun p := fun v => p (some v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma lift_cast (z : V → ℤ) :
    liftR (fun v => (z v : ℝ)) = fun o => (liftZ z o : ℝ) := by
  funext o; cases o <;> simp [liftR, liftZ]

private lemma lift_embed (D : Set (V → ℤ)) :
    liftR '' IntEmbed D = DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D) := by
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨liftZ z, ⟨by simp [liftZ], hz⟩, (lift_cast z).symm⟩
  · rintro ⟨z, ⟨hs, hz⟩, rfl⟩
    refine ⟨fun v => (z (some v) : ℝ), ⟨fun v => z (some v), hz, rfl⟩, ?_⟩
    funext o; cases o with
    | none => simpa [liftR] using congrArg (fun t : ℤ => (t : ℝ)) hs.symm
    | some v => rfl

private def inBox (a b : V → ℤ) (z : Option V → ℤ) : Prop :=
  ∀ v, a v ≤ z (some v) ∧ z (some v) ≤ b v

private lemma move_box (a b : V → ℤ) (x y : Option V → ℤ)
    (hx : inBox a b x) (hy : inBox a b y) (u v : Option V)
    (hu : y u < x u) (hv : x v < y v) :
    inBox a b (fun w => x w - DiscreteConvex.MConvexSetsB.CharVec u w + DiscreteConvex.MConvexSetsB.CharVec v w) := by
  have huv : u ≠ v := by intro h; subst v; omega
  intro w
  have h1 := hx w
  have h2 := hy w
  by_cases hwu : some w = u
  · subst u
    simp only [DiscreteConvex.MConvexSetsB.CharVec, huv, if_true, if_false]
    omega
  · by_cases hwv : some w = v
    · subst v
      simp only [DiscreteConvex.MConvexSetsB.CharVec, hwu, if_true, if_false]
      omega
    · simpa [DiscreteConvex.MConvexSetsB.CharVec, hwu, hwv] using h1

private lemma restrict_exchange (B : Set (Option V → ℤ)) (hB : DiscreteConvex.MConvexSetsB.ExchangeAxiomB B)
    (a b : V → ℤ) : DiscreteConvex.MConvexSetsB.ExchangeAxiomB (B ∩ {z | inBox a b z}) := by
  intro x hx y hy u hu
  rcases hB x hx.1 y hy.1 u hu with ⟨v, hv, hx', hy'⟩
  refine ⟨v, hv, ⟨hx', move_box a b x y hx.2 hy.2 u v hu hv⟩, hy', ?_⟩
  have h := move_box a b y x hy.2 hx.2 v u hv hu
  have heq : (fun w => y w + DiscreteConvex.MConvexSetsB.CharVec u w - DiscreteConvex.MConvexSetsB.CharVec v w) =
      (fun w => y w - DiscreteConvex.MConvexSetsB.CharVec v w + DiscreteConvex.MConvexSetsB.CharVec u w) := by
    funext w
    omega
  rw [heq]
  exact h

private lemma zero_sum_exchange :
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB {z : Option V → ℤ | ∑ w, z w = 0} := by
  intro x hx y hy u hu
  change y u < x u at hu
  have hv : ∃ v, x v < y v := by
    by_contra! hn
    have hs : ∑ w, y w < ∑ w, x w :=
      Finset.sum_lt_sum (fun w _ => hn w) ⟨u, Finset.mem_univ u, hu⟩
    change ∑ w, x w = 0 at hx
    change ∑ w, y w = 0 at hy
    omega
  rcases hv with ⟨v, hv⟩
  refine ⟨v, hv, ?_, ?_⟩
  · change ∑ w, (x w - DiscreteConvex.MConvexSetsB.CharVec u w + DiscreteConvex.MConvexSetsB.CharVec v w) = 0
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, DiscreteConvex.MConvexSetsB.CharVec] using hx
  · change ∑ w, (y w + DiscreteConvex.MConvexSetsB.CharVec u w - DiscreteConvex.MConvexSetsB.CharVec v w) = 0
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, DiscreteConvex.MConvexSetsB.CharVec] using hy

private lemma exchange_convert (D : Set (V → ℤ)) (h : MNatConvexSet D) :
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB (LiftedSet D) := by
  simpa [MNatConvexSet, ExchangeAxiomB, SuppPos, SuppNeg, IndicatorVec,
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB, DiscreteConvex.MConvexSetsB.SuppPos, DiscreteConvex.MConvexSetsB.SuppNeg, DiscreteConvex.MConvexSetsB.CharVec] using h

private lemma hull_nonempty (B : Set (Option V → ℤ)) {p : Option V → ℝ}
    (hp : p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed B)) : B.Nonempty := by
  have h := convexHull_nonempty_iff.mp (show (convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed B)).Nonempty from ⟨p, hp⟩)
  exact Set.image_nonempty.mp h

private def unitBox (p : V → ℝ) : Set (Option V → ℤ) :=
  {z | ∑ w, z w = 0} ∩ {z | inBox (fun v => ⌊p v⌋) (fun v => ⌈p v⌉) z}

private lemma unitBox_exchange (p : V → ℝ) : DiscreteConvex.MConvexSetsB.ExchangeAxiomB (unitBox p) :=
  restrict_exchange _ zero_sum_exchange _ _

private lemma lifted_sum (D : Set (V → ℤ)) (z : Option V → ℤ)
    (hz : z ∈ LiftedSet D) : ∑ w, z w = 0 := by
  rw [Fintype.sum_option, hz.1]
  omega

private lemma restrict_eq (D : Set (V → ℤ)) (p : V → ℝ) :
    LiftedSet D ∩ unitBox p =
      LiftedSet D ∩ {z | inBox (fun v => ⌊p v⌋) (fun v => ⌈p v⌉) z} := by
  ext z
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, lifted_sum D z h.1, h.2⟩⟩

private lemma restricted_exchange (D : Set (V → ℤ)) (hD : MNatConvexSet D) (p : V → ℝ) :
    DiscreteConvex.MConvexSetsB.ExchangeAxiomB (LiftedSet D ∩ unitBox p) := by
  rw [restrict_eq]
  exact restrict_exchange _ (exchange_convert D hD) _ _

private lemma unitBox_hull (p : V → ℝ) :
    liftR p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed (unitBox p)) := by
  classical
  let S : Set (V → ℝ) := Set.univ.pi (fun v => {(⌊p v⌋ : ℝ), (⌈p v⌉ : ℝ)})
  have hp : p ∈ convexHull ℝ S := by
    apply mem_convexHull_pi
    intro v _
    rw [convexHull_pair, segment_eq_Icc (by exact_mod_cast Int.floor_le_ceil (p v))]
    exact ⟨Int.floor_le _, Int.le_ceil _⟩
  have hmap : liftR '' S ⊆ DiscreteConvex.MConvexSetsB.IntEmbed (unitBox p) := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : ∀ v, q v = (⌊p v⌋ : ℝ) ∨ q v = (⌈p v⌉ : ℝ) := by
      intro v
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq v (Set.mem_univ v)
    let z : V → ℤ := fun v => if q v = (⌊p v⌋ : ℝ) then ⌊p v⌋ else ⌈p v⌉
    have hz : ∀ v, (z v : ℝ) = q v := by
      intro v
      dsimp [z]
      split_ifs with h
      · exact h.symm
      · exact ((hq' v).resolve_left h).symm
    have hb : inBox (fun v => ⌊p v⌋) (fun v => ⌈p v⌉) (liftZ z) := by
      intro v
      have hle := Int.floor_le_ceil (p v)
      dsimp [liftZ, z]
      split_ifs <;> exact ⟨by omega, by omega⟩
    refine ⟨liftZ z, ⟨?_, hb⟩, ?_⟩
    · simp [Fintype.sum_option, liftZ]
    · have hcast : (fun v => (z v : ℝ)) = q := funext hz
      rw [← hcast]
      exact (lift_cast z).symm
  apply convexHull_mono hmap
  rw [← LinearMap.image_convexHull]
  exact ⟨p, hp, rfl⟩

private lemma lifted_hull (D : Set (V → ℤ)) {p : V → ℝ}
    (hp : p ∈ convexHull ℝ (IntEmbed D)) :
    liftR p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D)) := by
  rw [← lift_embed, ← LinearMap.image_convexHull]
  exact ⟨p, hp, rfl⟩

private lemma restricted_hull (D : Set (V → ℤ)) (hD : MNatConvexSet D) {p : V → ℝ}
    (hp : p ∈ convexHull ℝ (IntEmbed D)) :
    liftR p ∈ convexHull ℝ (DiscreteConvex.MConvexSetsB.IntEmbed (LiftedSet D ∩ unitBox p)) := by
  have hd := lifted_hull D hp
  have hb := unitBox_hull p
  rw [DiscreteConvex.MConvexSetsB.mconvex_intersection_hull _ _ (exchange_convert D hD) (unitBox_exchange p)
    (hull_nonempty _ hd) (hull_nonempty _ hb)]
  exact ⟨hd, hb⟩

end ConjugacySetProof

open ConjugacySetProof in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (D : Set (V → ℤ)) (hD : MNat2ConvexSet D) : IsIntegrallyConvex D := by
  classical
  rcases hD with ⟨D1, D2, h1, h2, rfl⟩
  intro p hp
  have hp1 : p ∈ convexHull ℝ (IntEmbed D1) := by
    apply convexHull_mono (s := IntEmbed (D1 ∩ D2)) _ hp
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, rfl⟩
  have hp2 : p ∈ convexHull ℝ (IntEmbed D2) := by
    apply convexHull_mono (s := IntEmbed (D1 ∩ D2)) _ hp
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, rfl⟩
  have h1p := restricted_hull D1 h1 hp1
  have h2p := restricted_hull D2 h2 hp2
  have hboth : liftR p ∈ convexHull ℝ
      (DiscreteConvex.MConvexSetsB.IntEmbed
        ((LiftedSet D1 ∩ unitBox p) ∩ (LiftedSet D2 ∩ unitBox p))) := by
    rw [DiscreteConvex.MConvexSetsB.mconvex_intersection_hull _ _
      (restricted_exchange D1 h1 p) (restricted_exchange D2 h2 p)
      (hull_nonempty _ h1p) (hull_nonempty _ h2p)]
    exact ⟨h1p, h2p⟩
  have hproject : projectR '' DiscreteConvex.MConvexSetsB.IntEmbed
      ((LiftedSet D1 ∩ unitBox p) ∩ (LiftedSet D2 ∩ unitBox p)) ⊆
      IntEmbed ((D1 ∩ D2) ∩ IntegralNeighborhood p) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨fun v => z (some v), ⟨⟨hz.1.1.2, hz.2.1.2⟩, hz.1.2.2⟩, rfl⟩
  apply convexHull_mono hproject
  rw [← LinearMap.image_convexHull]
  exact ⟨liftR p, hboth, rfl⟩

