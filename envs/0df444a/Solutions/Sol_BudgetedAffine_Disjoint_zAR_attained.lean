-- Prove2me | solution 1 for BudgetedAffine.Disjoint.zAR_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:28:15.631219+00:00
-- url     : https://prove2.me/submissions/15393221-e956-4051-adcc-d717d982144b

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_Polyhedron
import Definitions.Def_ActiveConstraints
import Definitions.Def_BasicSolution
import Definitions.Def_Vertex
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded
import Theorems.Thm_LinearOptimization_polyhedron_bounded_convex_hull_extreme
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite

set_option autoImplicit false
open Matrix

namespace AffDisjZAR

/-- LP attainment with constraints and variables indexed by arbitrary finite types. -/
theorem lp_attain_fintype {R V : Type} [Fintype R] [Fintype V]
    (M : R → V → ℝ) (b : R → ℝ) (c : V → ℝ)
    (hne : ∃ z : V → ℝ, ∀ r, b r ≤ ∑ v, M r v * z v)
    (hbd : ∃ β : ℝ, ∀ z : V → ℝ, (∀ r, b r ≤ ∑ v, M r v * z v) → β ≤ ∑ v, c v * z v) :
    ∃ z : V → ℝ, (∀ r, b r ≤ ∑ v, M r v * z v) ∧
      ∀ z' : V → ℝ, (∀ r, b r ≤ ∑ v, M r v * z' v) → ∑ v, c v * z v ≤ ∑ v, c v * z' v := by
  classical
  set eR := Fintype.equivFin R
  set eV := Fintype.equivFin V
  set A' : Matrix (Fin (Fintype.card R)) (Fin (Fintype.card V)) ℝ :=
    Matrix.of fun i j => M (eR.symm i) (eV.symm j) with hA'
  set b' : Fin (Fintype.card R) → ℝ := fun i => b (eR.symm i) with hb'
  set c' : Fin (Fintype.card V) → ℝ := fun j => c (eV.symm j) with hc'
  have hsum : ∀ (f : V → ℝ), ∑ j : Fin (Fintype.card V), f (eV.symm j) = ∑ v, f v :=
    fun f => Equiv.sum_comp eV.symm f
  -- transport
  have hmem : ∀ z : V → ℝ, (z ∘ eV.symm) ∈ LinearOptimization.polyhedron A' b' ↔
      ∀ r, b r ≤ ∑ v, M r v * z v := by
    intro z
    unfold LinearOptimization.polyhedron
    simp only [Set.mem_setOf_eq, Pi.le_def, hA', hb', Matrix.mulVec, dotProduct, Matrix.of_apply,
      Function.comp_apply]
    constructor
    · intro h r
      have := h (eR r)
      simp only [Equiv.symm_apply_apply] at this
      rwa [hsum (fun v => M r v * z v)] at this
    · intro h i
      rw [hsum (fun v => M (eR.symm i) v * z v)]
      exact h _
  have hcost : ∀ z : V → ℝ, c' ⬝ᵥ (z ∘ eV.symm) = ∑ v, c v * z v := by
    intro z
    simp only [dotProduct, hc', Function.comp_apply]
    exact hsum (fun v => c v * z v)
  have hback : ∀ z' : Fin (Fintype.card V) → ℝ, z' = (z' ∘ eV) ∘ eV.symm := by
    intro z'; funext j; simp
  obtain ⟨z0, hz0⟩ := hne
  have hne' : (LinearOptimization.polyhedron A' b').Nonempty := ⟨_, (hmem z0).2 hz0⟩
  obtain ⟨β, hβ⟩ := hbd
  rcases LinearOptimization.lp_attains_or_unbounded A' b' c' hne' with hbot | ⟨z', hz'P, hz'opt⟩
  · exfalso
    have h0 : ((β : ℝ) : EReal) ≤ LinearOptimization.lpValue c' (LinearOptimization.polyhedron A' b') := by
      unfold LinearOptimization.lpValue
      refine le_iInf₂ (fun y hy => ?_)
      rw [hback y] at hy ⊢
      rw [hcost]
      exact_mod_cast hβ _ ((hmem _).1 hy)
    rw [hbot] at h0
    exact absurd h0 (by simp)
  · refine ⟨z' ∘ eV, ?_, fun z hz => ?_⟩
    · rw [← hmem, ← hback]; exact hz'P
    · have := hz'opt (z ∘ eV.symm) ((hmem z).2 hz)
      rw [hcost, hback z', hcost] at this
      exact this


/-- The disjoint constrained budgeted set is the convex hull of a finite subset of itself. -/
theorem U_finite_hull {m L : ℕ} (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ) :
    ∃ E : Finset (Fin m → ℝ), (↑E : Set (Fin m → ℝ)) ⊆ BudgetedAffine.Disjoint.disjointBudgetSet S w ∧
      BudgetedAffine.Disjoint.disjointBudgetSet S w ⊆ convexHull ℝ (↑E : Set (Fin m → ℝ)) := by
  classical
  set AU : Matrix (Fin (m + (m + L))) (Fin m) ℝ := Matrix.of fun r =>
    Fin.addCases (motive := fun _ => Fin m → ℝ) (fun i => Pi.single i 1)
      (Fin.addCases (motive := fun _ => Fin m → ℝ) (fun i => -Pi.single i 1)
        (fun ℓ => fun i => if i ∈ S ℓ then -w ℓ i else 0)) r with hAU
  set bU : Fin (m + (m + L)) → ℝ := Fin.addCases (motive := fun _ => ℝ) (fun _ => 0)
    (Fin.addCases (motive := fun _ => ℝ) (fun _ => -1) (fun _ => -1)) with hbU
  have hP : LinearOptimization.polyhedron AU bU = BudgetedAffine.Disjoint.disjointBudgetSet S w := by
    ext h
    unfold LinearOptimization.polyhedron BudgetedAffine.Disjoint.disjointBudgetSet
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Fin.forall_fin_add, Fin.forall_fin_add]
    simp only [hAU, hbU, Matrix.mulVec, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      single_dotProduct, one_mul, neg_dotProduct, neg_le_neg_iff]
    have hsum : ∀ ℓ, (fun i => if i ∈ S ℓ then -w ℓ i else 0) ⬝ᵥ h = -∑ i ∈ S ℓ, w ℓ i * h i := by
      intro ℓ
      simp only [dotProduct, ite_mul, zero_mul, neg_mul]
      rw [← Finset.sum_filter, Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
    simp only [hsum, neg_le_neg_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun i => ⟨h1 i, h2 i⟩, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨fun i => (h1 i).1, fun i => (h1 i).2, h3⟩
  have hne : (LinearOptimization.polyhedron AU bU).Nonempty := by
    rw [hP]; exact ⟨0, fun i => ⟨le_rfl, zero_le_one⟩, fun ℓ => by simp⟩
  have hbd : LinearOptimization.IsBoundedSet (LinearOptimization.polyhedron AU bU) := by
    refine ⟨1, fun x hx i => ?_⟩
    rw [hP] at hx
    rw [abs_le]
    constructor <;> linarith [(hx.1 i).1, (hx.1 i).2]
  have hhull := LinearOptimization.polyhedron_bounded_convex_hull_extreme AU bU hne hbd
  have hCS : LinearOptimization.constraintSet (LinearOptimization.generalFormSystem AU bU) =
      LinearOptimization.polyhedron AU bU := by
    ext x
    simp only [LinearOptimization.constraintSet, LinearOptimization.generalFormSystem,
      LinearOptimization.LinearConstraint.IsSatisfiedAt, LinearOptimization.polyhedron,
      Set.mem_setOf_eq, Pi.le_def, Matrix.mulVec]
  have hfin : (Set.extremePoints ℝ (LinearOptimization.polyhedron AU bU)).Finite := by
    refine (LinearOptimization.lp_basic_solutions_finite
      (LinearOptimization.generalFormSystem AU bU)).2.subset (fun x hx => ?_)
    have hxP : x ∈ LinearOptimization.constraintSet (LinearOptimization.generalFormSystem AU bU) := by
      rw [hCS]; exact hx.1
    have hne' : (LinearOptimization.constraintSet (LinearOptimization.generalFormSystem AU bU)).Nonempty := by
      rw [hCS]; exact hne
    have := (LinearOptimization.lp_vertex_extreme_bfs_equiv
      (LinearOptimization.generalFormSystem AU bU) x hne' hxP).out 1 2
    rw [hCS] at this
    exact this.1 hx
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro x hx
    rw [Set.Finite.coe_toFinset] at hx
    rw [← hP]; exact hx.1
  · rw [Set.Finite.coe_toFinset, ← hP]
    exact hhull.le

end AffDisjZAR

open AffDisjZAR in
theorem solution {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : BudgetedAffine.Disjoint.IsPartition S)
    (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (hfin : BudgetedAffine.Budget.zAR A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) ≠ ⊤) :
    ∃ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.IsOptimalAR A B c d X (BudgetedAffine.Disjoint.disjointBudgetSet S w) xs ys := by
  classical
  obtain ⟨k, G, g, hXeq⟩ := hX
  set U := BudgetedAffine.Disjoint.disjointBudgetSet S w with hUdef
  obtain ⟨E, hEU, hUE⟩ := U_finite_hull S w
  have h0U : (0 : Fin m → ℝ) ∈ U := ⟨fun i => ⟨le_rfl, zero_le_one⟩, fun ℓ => by simp⟩
  obtain ⟨e0, he0⟩ : E.Nonempty := by
    by_contra hE
    rw [Finset.not_nonempty_iff_eq_empty] at hE
    have := hUE h0U
    rw [hE, Finset.coe_empty, convexHull_empty] at this
    exact this
  -- the LP
  let M : (Fin k ⊕ ({e // e ∈ E} × Fin n) ⊕ ({e // e ∈ E} × Fin m) ⊕ {e // e ∈ E}) → (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ := Sum.elim (fun κ => Sum.elim (fun j => -G κ j) 0)
    (Sum.elim (fun p => Sum.elim 0 (Sum.elim (fun q => if q = p then 1 else 0) 0))
      (Sum.elim (fun p => Sum.elim (fun j => A p.2 j)
          (Sum.elim (fun q => if q.1 = p.1 then B p.2 q.2 else 0) 0))
        (fun e => Sum.elim 0 (Sum.elim (fun q => if q.1 = e then -d q.2 else 0) (fun _ => 1)))))
  let b : (Fin k ⊕ ({e // e ∈ E} × Fin n) ⊕ ({e // e ∈ E} × Fin m) ⊕ {e // e ∈ E}) → ℝ := Sum.elim (fun κ => -g κ)
    (Sum.elim 0 (Sum.elim (fun p => (p.1 : Fin m → ℝ) p.2) 0))
  let cc : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ := Sum.elim c (Sum.elim 0 (fun _ => 1))
  let xOf : ((Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) → Fin n → ℝ := fun z j => z (Sum.inl j)
  let yOf : ((Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) → {e // e ∈ E} → Fin n → ℝ := fun z e j => z (Sum.inr (Sum.inl (e, j)))
  let tOf : ((Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) → ℝ := fun z => z (Sum.inr (Sum.inr ()))
  have hrowX : ∀ (z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) (κ : Fin k), ∑ v, M (Sum.inl κ) v * z v = -(G *ᵥ xOf z) κ := by
    intro z κ
    simp [M, xOf, Fintype.sum_sum_type, Matrix.mulVec, dotProduct]
  have hrowY : ∀ (z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) (p : {e // e ∈ E} × Fin n), ∑ v, M (Sum.inr (Sum.inl p)) v * z v = yOf z p.1 p.2 := by
    intro z p
    simp [M, yOf, Fintype.sum_sum_type]
  have hrowC : ∀ (z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) (p : {e // e ∈ E} × Fin m), ∑ v, M (Sum.inr (Sum.inr (Sum.inl p))) v * z v =
      (A *ᵥ xOf z) p.2 + (B *ᵥ yOf z p.1) p.2 := by
    intro z p
    simp [M, xOf, yOf, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hrowT : ∀ (z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ) (e : {e // e ∈ E}), ∑ v, M (Sum.inr (Sum.inr (Sum.inr e))) v * z v =
      tOf z - d ⬝ᵥ yOf z e := by
    intro z e
    simp [M, yOf, tOf, Fintype.sum_sum_type, dotProduct, Fintype.sum_prod_type]
    ring
  have hcost : ∀ z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ, ∑ v, cc v * z v = c ⬝ᵥ xOf z + tOf z := by
    intro z
    simp [cc, xOf, tOf, Fintype.sum_sum_type, dotProduct]

  have hfeas_iff : ∀ z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ, (∀ r, b r ≤ ∑ v, M r v * z v) ↔
      (G *ᵥ xOf z ≤ g ∧ (∀ e, 0 ≤ yOf z e) ∧
        (∀ e : {e // e ∈ E}, (e : Fin m → ℝ) ≤ A *ᵥ xOf z + B *ᵥ yOf z e) ∧
        ∀ e, d ⬝ᵥ yOf z e ≤ tOf z) := by
    intro z
    constructor
    · intro h
      refine ⟨fun κ => ?_, fun e j => ?_, fun e i => ?_, fun e => ?_⟩
      · have := h (Sum.inl κ)
        rw [hrowX] at this
        simp only [b, Sum.elim_inl] at this
        linarith
      · have := h (Sum.inr (Sum.inl (e, j)))
        rw [hrowY] at this
        simpa [b] using this
      · have := h (Sum.inr (Sum.inr (Sum.inl (e, i))))
        rw [hrowC] at this
        simpa [b] using this
      · have := h (Sum.inr (Sum.inr (Sum.inr e)))
        rw [hrowT] at this
        simp only [b, Sum.elim_inr, Pi.zero_apply] at this
        linarith
    · rintro ⟨h1, h2, h3, h4⟩ r
      rcases r with κ | p | p | e
      · rw [hrowX]
        simp only [b, Sum.elim_inl]
        linarith [h1 κ]
      · rw [hrowY]
        simpa [b] using h2 p.1 p.2
      · rw [hrowC]
        simpa [b] using h3 p.1 p.2
      · rw [hrowT]
        simp only [b, Sum.elim_inr, Pi.zero_apply]
        linarith [h4 e]
  have hlift : ∀ (x' : Fin n → ℝ) (y' : (Fin m → ℝ) → Fin n → ℝ) (W : ℝ),
      BudgetedAffine.Budget.Feasible A B X U x' y' →
      BudgetedAffine.Budget.worstCost c d U x' y' = (W : EReal) →
      ∃ z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ, (∀ r, b r ≤ ∑ v, M r v * z v) ∧ ∑ v, cc v * z v = W := by
    intro x' y' W hF hW
    let z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ := Sum.elim x' (Sum.elim (fun q => y' q.1.1 q.2) (fun _ => W - c ⬝ᵥ x'))
    refine ⟨z, (hfeas_iff z).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · have := hF.1
      rw [hXeq] at this
      exact this
    · intro e
      exact (hF.2 e.1 (hEU e.2)).1
    · intro e
      exact (hF.2 e.1 (hEU e.2)).2
    · intro e
      have h1 : ((c ⬝ᵥ x' + d ⬝ᵥ y' e.1 : ℝ) : EReal) ≤ (W : EReal) := by
        rw [← hW]
        exact le_iSup₂ (f := fun h (_ : h ∈ U) => ((c ⬝ᵥ x' + d ⬝ᵥ y' h : ℝ) : EReal)) e.1 (hEU e.2)
      have h2 := EReal.coe_le_coe_iff.1 h1
      show d ⬝ᵥ y' e.1 ≤ W - c ⬝ᵥ x'
      linarith
    · rw [hcost]
      show c ⬝ᵥ x' + (W - c ⬝ᵥ x') = W
      ring
  have hreal : ∀ (x' : Fin n → ℝ) (y' : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.Feasible A B X U x' y' →
      BudgetedAffine.Budget.worstCost c d U x' y' ≠ ⊤ →
      ∃ W : ℝ, BudgetedAffine.Budget.worstCost c d U x' y' = (W : EReal) := by
    intro x' y' hF htop
    have hge : ((c ⬝ᵥ x' + d ⬝ᵥ y' 0 : ℝ) : EReal) ≤ BudgetedAffine.Budget.worstCost c d U x' y' :=
      le_iSup₂ (f := fun h (_ : h ∈ U) => ((c ⬝ᵥ x' + d ⬝ᵥ y' h : ℝ) : EReal)) 0 h0U
    exact ⟨_, (EReal.coe_toReal htop (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge)).symm⟩
  -- a feasible solution of finite cost
  have hlt : BudgetedAffine.Budget.zAR A B c d X U < ⊤ := lt_top_iff_ne_top.2 hfin
  unfold BudgetedAffine.Budget.zAR at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨x0, hlt⟩ := hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨y0, hlt⟩ := hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨hF0, hlt0⟩ := hlt
  obtain ⟨W0, hW0⟩ := hreal x0 y0 hF0 (ne_top_of_lt hlt0)
  have hne := hlift x0 y0 W0 hF0 hW0
  have hbd : ∃ β : ℝ, ∀ z : (Fin n ⊕ ({e // e ∈ E} × Fin n) ⊕ Unit) → ℝ, (∀ r, b r ≤ ∑ v, M r v * z v) → β ≤ ∑ v, cc v * z v := by
    refine ⟨0, fun z hz => ?_⟩
    obtain ⟨h1, h2, -, h4⟩ := (hfeas_iff z).1 hz
    rw [hcost]
    have hx : xOf z ∈ X := by rw [hXeq]; exact h1
    have := hcX _ hx
    have := dotProduct_nonneg_of_nonneg hd (h2 ⟨e0, he0⟩)
    have := h4 ⟨e0, he0⟩
    linarith
  obtain ⟨zs, hzs, hzopt⟩ := lp_attain_fintype M b cc (by obtain ⟨z, hz, -⟩ := hne; exact ⟨z, hz⟩) hbd
  obtain ⟨hz1, hz2, hz3, hz4⟩ := (hfeas_iff zs).1 hzs
  have hwt : ∀ h ∈ U, ∃ lam : (Fin m → ℝ) → ℝ, (∀ e ∈ E, 0 ≤ lam e) ∧ ∑ e ∈ E, lam e = 1 ∧
      ∑ e ∈ E, lam e • e = h := fun h hh => Finset.mem_convexHull'.1 (hUE hh)
  choose! lam hlam0 hlam1 hlamh using hwt
  let yE : (Fin m → ℝ) → Fin n → ℝ := fun e => if he : e ∈ E then yOf zs ⟨e, he⟩ else 0
  have hyE : ∀ e (he : e ∈ E), yE e = yOf zs ⟨e, he⟩ := fun e he => by simp [yE, he]
  let ys : (Fin m → ℝ) → Fin n → ℝ := fun h => ∑ e ∈ E, lam h e • yE e
  set xs := xOf zs with hxs
  have hFeas : BudgetedAffine.Budget.Feasible A B X U xs ys := by
    refine ⟨by rw [hXeq]; exact hz1, fun h hh => ⟨?_, fun i => ?_⟩⟩
    · exact Finset.sum_nonneg (fun e he => smul_nonneg (hlam0 h hh e he)
        (by rw [hyE e he]; exact hz2 _))
    · have hBy : (B *ᵥ ys h) i = ∑ e ∈ E, lam h e * (B *ᵥ yE e) i := by
        simp only [ys, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
      have hAx : (A *ᵥ xs) i = ∑ e ∈ E, lam h e * (A *ᵥ xs) i := by
        rw [← Finset.sum_mul, hlam1 h hh, one_mul]
      have hhi : h i = ∑ e ∈ E, lam h e * e i := by
        have := congrFun (hlamh h hh) i
        rw [← this, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [Pi.add_apply, hBy, hAx, hhi, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun e he => ?_)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hlam0 h hh e he)
      have := hz3 ⟨e, he⟩ i
      rw [hyE e he]
      simpa using this
  have hub : BudgetedAffine.Budget.worstCost c d U xs ys ≤ ((c ⬝ᵥ xs + tOf zs : ℝ) : EReal) := by
    unfold BudgetedAffine.Budget.worstCost
    refine iSup₂_le (fun h hh => ?_)
    have hdy : d ⬝ᵥ ys h = ∑ e ∈ E, lam h e * (d ⬝ᵥ yE e) := by
      simp only [ys, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    have : d ⬝ᵥ ys h ≤ tOf zs := by
      rw [hdy]
      calc ∑ e ∈ E, lam h e * (d ⬝ᵥ yE e) ≤ ∑ e ∈ E, lam h e * tOf zs :=
            Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left
              (by rw [hyE e he]; exact hz4 _) (hlam0 h hh e he))
        _ = tOf zs := by rw [← Finset.sum_mul, hlam1 h hh, one_mul]
    exact_mod_cast (by linarith : c ⬝ᵥ xs + d ⬝ᵥ ys h ≤ c ⬝ᵥ xs + tOf zs)
  have hlow : ∀ (x' : Fin n → ℝ) (y' : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.Feasible A B X U x' y' →
      ((c ⬝ᵥ xs + tOf zs : ℝ) : EReal) ≤ BudgetedAffine.Budget.worstCost c d U x' y' := by
    intro x' y' hF
    by_cases htop : BudgetedAffine.Budget.worstCost c d U x' y' = ⊤
    · rw [htop]; exact le_top
    obtain ⟨W, hW⟩ := hreal x' y' hF htop
    obtain ⟨z', hz', hz'c⟩ := hlift x' y' W hF hW
    have := hzopt z' hz'
    rw [hcost, hz'c] at this
    rw [hW]
    exact_mod_cast this
  refine ⟨xs, ys, hFeas, le_antisymm ?_ ?_⟩
  · refine le_trans hub ?_
    unfold BudgetedAffine.Budget.zAR
    exact le_iInf (fun x' => le_iInf (fun y' => le_iInf (fun hF => hlow x' y' hF)))
  · unfold BudgetedAffine.Budget.zAR
    exact le_trans (iInf_le _ xs) (le_trans (iInf_le _ ys) (iInf_le _ hFeas))
