-- Prove2me | solution 1 for DRConvexOpt.Reform.boundary_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:05:47.101373+00:00
-- url     : https://prove2.me/submissions/e55c5ca4-7816-49a0-9199-27a1f1d8f0bd

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

open MeasureTheory Matrix DRConvexOpt.Reform

namespace DRCOBdAux

lemma tdot {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    (Mᵀ *ᵥ y) ⬝ᵥ z = (M *ᵥ z) ⬝ᵥ y := by
  rw [mulVec_transpose, dotProduct_comm (M *ᵥ z), dotProduct_mulVec]

lemma sinc_trans {α : Type*} [TopologicalSpace α] {A B C : Set α} (h1 : SInc A B)
    (h2 : SInc B C) : SInc A C :=
  h1.trans (interior_subset.trans h2)

lemma conf_closed {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)
    (hK : ∀ i, IsProperCone (d.K i)) (i : Fin (nI + 1)) : IsClosed (d.conf i) := by
  have hc : Continuous fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      d.c i - (d.C i *ᵥ ω.1 + d.D i *ᵥ ω.2) :=
    continuous_const.sub ((continuous_const.matrix_mulVec continuous_fst).add
      (continuous_const.matrix_mulVec continuous_snd))
  exact (hK i).1.preimage hc

lemma nontriv {nP nQ : ℕ} (hdim : 0 < nP + nQ) : Nontrivial ((Fin nP → ℝ) × (Fin nQ → ℝ)) := by
  rcases Nat.eq_zero_or_pos nP with hP | hP
  · have hQ : 0 < nQ := by omega
    refine nontrivial_of_ne (0, 0) (0, fun _ => 1) fun h => ?_
    have := congrFun (congrArg Prod.snd h) ⟨0, hQ⟩
    simp at this
  · refine nontrivial_of_ne (0, 0) (fun _ => 1, 0) fun h => ?_
    have := congrFun (congrArg Prod.fst h) ⟨0, hP⟩
    simp at this

lemma conf_convex {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)
    (hK : ∀ i, IsProperCone (d.K i)) (i : Fin (nI + 1)) : Convex ℝ (d.conf i) := by
  intro ω1 h1 ω2 h2 a b ha hb hab
  have hK1 := (hK i).2.2.1
  have hK2 := (hK i).2.2.2.1
  have key : d.c i - (d.C i *ᵥ (a • ω1 + b • ω2).1 + d.D i *ᵥ (a • ω1 + b • ω2).2) =
      a • (d.c i - (d.C i *ᵥ ω1.1 + d.D i *ᵥ ω1.2)) +
        b • (d.c i - (d.C i *ᵥ ω2.1 + d.D i *ᵥ ω2.2)) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add, mulVec_smul]
    have : d.c i = a • d.c i + b • d.c i := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [this]
    simp only [smul_sub, smul_add]
    abel
  show d.c i - _ ∈ d.K i
  rw [key]
  exact hK1 _ (hK2 _ h1 a ha) _ (hK2 _ h2 b hb)

end DRCOBdAux

open DRCOBdAux in
theorem solution {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hbdd : Bornology.IsBounded (d.conf (Fin.last nI)))
    (hN : Nesting d) (hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI)) (hdim : 0 < nP + nQ)
    (x : Fin nN → ℝ) (i : Fin (nI + 1)) (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ) :
    (∀ ω ∈ cbar d i, v.eval x ω.1 - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β -
        ∑ i' ∈ anc d i, (κ i' - lam i') ≤ 0) ↔
    (∀ ω ∈ d.conf i, v.eval x ω.1 - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β -
        ∑ i' ∈ anc d i, (κ i' - lam i') ≤ 0) := by
  haveI := nontriv hdim
  set h0 := ∑ i' ∈ anc d i, (κ i' - lam i')
  constructor
  · intro h
    -- the sublevel set, as an intersection over the affine pieces
    let g : Fin nL → (Fin nP → ℝ) × (Fin nQ → ℝ) → ℝ := fun l ω =>
      (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l) - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β - h0
    let T : Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) := ⋂ l, {ω | g l ω ≤ 0}
    have hT : ∀ ω, ω ∈ T ↔ v.eval x ω.1 - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β - h0 ≤ 0 := by
      intro ω
      simp only [T, g, Set.mem_iInter, Set.mem_setOf_eq]
      have : v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β + h0 ↔ ∀ l,
          (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l) ≤
            (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β + h0 := by
        unfold PWAff.eval
        rw [Finset.sup'_le_iff]
        simp
      constructor
      · intro hl; have := this.mpr (fun l => by linarith [hl l]); linarith
      · intro hv l; have := this.mp (by linarith) l; linarith
    have hTconv : Convex ℝ T := by
      refine convex_iInter fun l => ?_
      intro ω1 h1 ω2 h2 a b ha hb hab
      simp only [Set.mem_setOf_eq, g] at h1 h2 ⊢
      have e : (v.S l *ᵥ (a • ω1 + b • ω2).1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ (a • ω1 + b • ω2).1 + v.t0 l) -
          (d.A *ᵥ (a • ω1 + b • ω2).1 + d.B *ᵥ (a • ω1 + b • ω2).2) ⬝ᵥ β - h0 =
          a * ((v.S l *ᵥ ω1.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω1.1 + v.t0 l) -
            (d.A *ᵥ ω1.1 + d.B *ᵥ ω1.2) ⬝ᵥ β - h0) +
          b * ((v.S l *ᵥ ω2.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω2.1 + v.t0 l) -
            (d.A *ᵥ ω2.1 + d.B *ᵥ ω2.2) ⬝ᵥ β - h0) := by
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
          mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
          smul_eq_mul]
        linear_combination (-(v.s l ⬝ᵥ x + v.t0 l - h0)) * hab
      rw [e]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ha h1, mul_nonpos_of_nonneg_of_nonpos hb h2]
    have hTclosed : IsClosed T := by
      refine isClosed_iInter fun l => isClosed_le ?_ continuous_const
      simp only [g]
      fun_prop
    -- `C_i` is compact and convex
    have hcomp : IsCompact (d.conf i) :=
      Metric.isCompact_of_isClosed_isBounded (conf_closed d hK i) (hbdd.subset (hsub i))
    have hext : (d.conf i).extremePoints ℝ ⊆ T := by
      intro p hp
      rw [hT]
      refine h p ⟨hp.1, ?_⟩
      simp only [Set.mem_iUnion, not_exists]
      intro k hk hpk
      have hki : SInc (d.conf k) (d.conf i) := by simpa [desc] using hk
      exact Set.disjoint_left.mp (disjoint_interior_extremePoints (d.conf i)) (hki hpk) hp
    have hCT : d.conf i ⊆ T := by
      rw [← closure_convexHull_extremePoints hcomp (conf_convex d hK i)]
      exact closure_minimal (convexHull_min hext hTconv) hTclosed
    intro ω hω
    exact (hT ω).mp (hCT hω)
  · intro h ω hω
    exact h ω hω.1
