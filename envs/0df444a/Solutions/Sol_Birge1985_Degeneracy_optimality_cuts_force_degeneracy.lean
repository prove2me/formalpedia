-- Prove2me | solution 1 for Birge1985.Degeneracy.optimality_cuts_force_degeneracy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:41:27.621993+00:00
-- url     : https://prove2.me/submissions/75da3e4b-a0bc-4232-8f78-08062f76a923

import Mathlib
import Definitions.Def_BasicSolution
import Definitions.Def_Birge1985_Degeneracy_NodeProblem

set_option autoImplicit false

namespace Birge1985.Degeneracy.P3ccc

open Matrix LinearOptimization Filter Topology Birge1985.Degeneracy

/-- `N` linearly independent rows in `ℝ^N`: every right-hand side is attained, and every
vector is a combination of the rows. -/
theorem solve_rows {ι : Type} {N : ℕ} (a : ι → Fin N → ℝ) (s : Finset ι) (hcard : s.card = N)
    (hli : LinearIndependent ℝ (fun i : s => a i.1)) :
    (∀ δ : ι → ℝ, ∃ w : Fin N → ℝ, ∀ i ∈ s, a i ⬝ᵥ w = δ i) ∧
    (∀ c : Fin N → ℝ, ∃ μ : ι → ℝ, (∀ i, i ∉ s → μ i = 0) ∧ ∑ i ∈ s, μ i • a i = c) := by
  classical
  have hc : Fintype.card s = N := by simpa using hcard
  let e : s ≃ Fin N := Fintype.equivFinOfCardEq hc
  let M : Matrix (Fin N) (Fin N) ℝ := fun k => a (e.symm k).1
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  refine ⟨fun δ => ?_, fun c => ?_⟩
  · obtain ⟨w, hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hM) (fun k => δ (e.symm k).1)
    refine ⟨w, fun i hi => ?_⟩
    have := congrFun hw (e ⟨i, hi⟩)
    simpa [M, Matrix.mulVec] using this
  · obtain ⟨μ', hμ'⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hM) c
    refine ⟨fun i => if h : i ∈ s then μ' (e ⟨i, h⟩) else 0, fun i hi => by simp [hi], ?_⟩
    rw [← hμ', ← Finset.sum_coe_sort s, ← Equiv.sum_comp e.symm]
    funext j
    simp [M, Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem nondeg_active {ι : Type} [Finite ι] {N : ℕ} (C : ι → LinearConstraint N)
    (z : Fin N → ℝ) (hb : IsBasicSolution C z)
    (hnd : {i | (C i).IsActiveAt z}.ncard ≤ N) :
    ∃ s : Finset ι, s.card = N ∧ LinearIndependent ℝ (fun i : s => (C i.1).a) ∧
      ∀ i, (C i).IsActiveAt z ↔ i ∈ s := by
  obtain ⟨-, s, hs, hact, hli⟩ := hb
  refine ⟨s, hs, hli, fun i => ⟨fun hi => ?_, fun hi => hact i hi⟩⟩
  have hsub : (↑s : Set ι) ⊆ {i | (C i).IsActiveAt z} := fun i hi => hact i hi
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hs]; exact hnd)
  have : i ∈ (↑s : Set ι) := by rw [heq]; exact hi
  exact this

theorem sat_of_eq {N : ℕ} (c : LinearConstraint N) (w : Fin N → ℝ) (h : c.a ⬝ᵥ w = c.b) :
    c.IsSatisfiedAt w := by
  rcases c with ⟨a, b, _ | _ | _⟩ <;>
    simp only [LinearConstraint.IsSatisfiedAt] at h ⊢ <;> linarith

/-- Perturbed right-hand sides `b + t β`. -/
def pert {ι : Type} {N : ℕ} (C : ι → LinearConstraint N) (β : ι → ℝ) (t : ℝ) :
    ι → LinearConstraint N :=
  fun i => ⟨(C i).a, (C i).b + t * β i, (C i).rel⟩

theorem eventually_feasible {ι : Type} [Finite ι] {N : ℕ} (C : ι → LinearConstraint N)
    (β : ι → ℝ) (z w : Fin N → ℝ) (hz : z ∈ constraintSet C)
    (hw : ∀ i, (C i).IsActiveAt z →
      (⟨(C i).a, β i, (C i).rel⟩ : LinearConstraint N).IsSatisfiedAt w) :
    ∀ᶠ t in 𝓝[≥] (0:ℝ), z + t • w ∈ constraintSet (pert C β t) := by
  have key : ∀ i, ∀ᶠ t in 𝓝[≥] (0:ℝ), (pert C β t i).IsSatisfiedAt (z + t • w) := by
    intro i
    have hzi := hz i
    have hwi := hw i
    simp only [pert]
    rcases hC : C i with ⟨a, b, rel⟩
    rw [hC] at hzi hwi
    by_cases hact : a ⬝ᵥ z = b
    · have hwi' := hwi hact
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ici] at ht
      rcases rel with _ | _ | _ <;>
        simp only [LinearConstraint.IsSatisfiedAt, dotProduct_add, dotProduct_smul,
          smul_eq_mul] at hwi' hzi ⊢
      · nlinarith [mul_le_mul_of_nonneg_left hwi' ht]
      · nlinarith [mul_le_mul_of_nonneg_left hwi' ht]
      · rw [hact, hwi']
    · have hlim : ∀ u v : ℝ, 0 < u → ∀ᶠ t in 𝓝[≥] (0:ℝ), 0 < u + t * v := by
        intro u v hu
        have ht : Tendsto (fun t : ℝ => u + t * v) (𝓝 0) (𝓝 u) := by
          have := ((tendsto_id (x := 𝓝 (0:ℝ))).mul_const v)
          simpa using (tendsto_const_nhds (x := u)).add this
        exact nhdsWithin_le_nhds (ht.eventually_const_lt hu)
      rcases rel with _ | _ | _ <;> simp only [LinearConstraint.IsSatisfiedAt] at hzi
      · have hpos : 0 < a ⬝ᵥ z - b := by
          rcases lt_or_eq_of_le hzi with h | h
          · linarith
          · exact absurd h.symm hact
        filter_upwards [hlim _ (a ⬝ᵥ w - β i) hpos] with t ht
        simp only [LinearConstraint.IsSatisfiedAt, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
      · have hpos : 0 < b - a ⬝ᵥ z := by
          rcases lt_or_eq_of_le hzi with h | h
          · linarith
          · exact absurd h hact
        filter_upwards [hlim _ (β i - a ⬝ᵥ w) hpos] with t ht
        simp only [LinearConstraint.IsSatisfiedAt, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
      · exact absurd hzi hact
  filter_upwards [Filter.eventually_all.2 key] with t ht
  exact ht

theorem strong_dual {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (cost : Fin N → ℝ) (z : Fin N → ℝ) (hbfs : IsBasicFeasibleSolution C z)
    (hnd : {i | (C i).IsActiveAt z}.ncard ≤ N)
    (hopt : ∀ z' ∈ constraintSet C, cost ⬝ᵥ z ≤ cost ⬝ᵥ z') :
    ∃ μ, IsDualFeasible C cost μ ∧ dualObjective C μ = cost ⬝ᵥ z := by
  classical
  obtain ⟨s, hs, hli, hact⟩ := nondeg_active C z hbfs.1 hnd
  obtain ⟨hsolve, hspan⟩ := solve_rows (fun i => (C i).a) s hs hli
  obtain ⟨μ, hμ0, hμ⟩ := hspan cost
  have hsum : ∑ i, μ i • (C i).a = cost := by
    rw [← hμ]; symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi; simp [hμ0 i hi]
  have hdot : ∀ v, cost ⬝ᵥ v = ∑ i ∈ s, μ i * ((C i).a ⬝ᵥ v) := by
    intro v; rw [← hμ, sum_dotProduct]; simp [smul_dotProduct]
  have probe : ∀ k ∈ s, (C k).rel ≠ .eq → ∀ σ : ℝ, ((C k).rel = .ge → 0 ≤ σ) →
      ((C k).rel = .le → σ ≤ 0) → 0 ≤ μ k * σ := by
    intro k hk hne σ hge hle
    obtain ⟨w, hw⟩ := hsolve (fun i => if i = k then σ else 0)
    have hev := eventually_feasible C (fun _ => 0) z w hbfs.2 (by
      intro i hi
      have his := (hact i).1 hi
      have hwi := hw i his
      by_cases hik : i = k
      · subst hik
        simp only [if_true] at hwi
        rcases hrel : (C i).rel with _ | _ | _ <;>
          simp only [LinearConstraint.IsSatisfiedAt, hrel, hwi]
        · exact hge hrel
        · exact hle hrel
        · exact absurd hrel hne
      · apply sat_of_eq
        simp only [hwi, hik, if_false])
    have hpert : ∀ t, pert C (fun _ => 0) t = C := by
      intro t; funext i; simp [pert]
    obtain ⟨t, ht, htpos⟩ :=
      ((hev.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)).and
        self_mem_nhdsWithin).exists
    rw [hpert] at ht
    have h1 := hopt _ ht
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
    have h2 : 0 ≤ cost ⬝ᵥ w := by
      have : 0 ≤ t * (cost ⬝ᵥ w) := by linarith
      exact nonneg_of_mul_nonneg_right (by linarith) htpos |> fun h => by
        rcases (mul_nonneg_iff_of_pos_left (Set.mem_Ioi.mp htpos)).mp this with h'; exact h'
    rw [hdot w] at h2
    have h3 : ∑ i ∈ s, μ i * (C i).a ⬝ᵥ w = μ k * σ := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [hw i hi])]
      simp [mul_ite, Finset.sum_ite_eq', hk]
    linarith
  refine ⟨μ, ⟨fun k => ⟨fun hge => ?_, fun hle => ?_⟩, hsum⟩, ?_⟩
  · by_cases hk : k ∈ s
    · have := probe k hk (by rw [hge]; decide) 1 (fun _ => zero_le_one) (fun h => by rw [hge] at h; exact absurd h (by decide))
      linarith
    · rw [hμ0 k hk]
  · by_cases hk : k ∈ s
    · have := probe k hk (by rw [hle]; decide) (-1) (fun h => by rw [hle] at h; exact absurd h (by decide))
        (fun _ => by norm_num)
      linarith
    · rw [hμ0 k hk]
  · unfold dualObjective
    rw [hdot z, ← Finset.sum_subset (Finset.subset_univ s)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [((hact i).2 hi)]
    · intro i _ hi; simp [hμ0 i hi]

/-- How the right-hand side of (7.2) moves with the ancestor decision. -/
def beta {nIn : ℕ} (P : NodeProblem nIn) (h : Fin nIn → ℝ) : P.Idx → ℝ
  | .inl k => (P.B *ᵥ h) k
  | .inr _ => 0

theorem beta_neg {nIn : ℕ} (P : NodeProblem nIn) (h : Fin nIn → ℝ) (i : P.Idx) :
    beta P (-h) i = -beta P h i := by
  rcases i with k | i <;> simp [beta, Matrix.mulVec_neg]

theorem constraints_add {nIn : ℕ} (P : NodeProblem nIn) (x h : Fin nIn → ℝ) (t : ℝ) :
    P.constraints (x + t • h) = pert (P.constraints x) (beta P h) t := by
  funext i
  rcases i with k | l | l | i | u <;>
    simp [NodeProblem.constraints, pert, beta, Matrix.mulVec_add, Matrix.mulVec_smul] <;> ring

theorem dualObj_eq {nIn : ℕ} (P : NodeProblem nIn) (lam : P.Idx → ℝ) (x : Fin nIn → ℝ) :
    dualObjective (P.constraints x) lam = P.cutConst lam - P.cutSlope lam ⬝ᵥ x := by
  have hc := constraints_add P 0 x 1
  simp only [zero_add, one_smul] at hc
  rw [hc]
  unfold dualObjective pert NodeProblem.cutConst NodeProblem.cutSlope NodeProblem.eqPart
  simp only [one_mul, mul_add, Finset.sum_add_distrib, neg_dotProduct, sub_neg_eq_add,
    ← Matrix.dotProduct_mulVec]
  congr 1
  rw [Fintype.sum_sum_type]
  simp [beta, dotProduct]

theorem main {nIn : ℕ} (P : NodeProblem nIn)
    {J : Type} [Fintype J] (Q : J → NodeProblem P.n) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (l₁ l₂ : Fin P.s) (hdistinct : (P.E l₁, P.e l₁) ≠ (P.E l₂, P.e l₂))
    (hvalid₁ : IsValidOptimalityCut Q p (P.E l₁) (P.e l₁))
    (hvalid₂ : IsValidOptimalityCut Q p (P.E l₂) (P.e l₂))
    (xbar : Fin P.n → ℝ) (θbar : ℝ)
    (hbind₁ : P.E l₁ ⬝ᵥ xbar + θbar = P.e l₁)
    (hbind₂ : P.E l₂ ⬝ᵥ xbar + θbar = P.e l₂)
    (z : ∀ j, Fin ((Q j).n + 1) → ℝ)
    (hbasic : ∀ j, IsBasicFeasibleSolution ((Q j).constraints xbar) (z j))
    (hopt : ∀ j, (Q j).IsOptimalSolution xbar (z j))
    (lam : ∀ j, (Q j).Idx → ℝ)
    (hdual : ∀ j, IsDualOptimal ((Q j).constraints xbar)
      (Fin.snoc (α := fun _ => ℝ) (Q j).c 1) (lam j))
    (hnot9 : optimalityCutConst Q p lam - optimalityCutSlope Q p lam ⬝ᵥ xbar ≤ θbar) :
    ∃ j, IsDegenerateBasicSolution ((Q j).constraints xbar) (z j) := by
  classical
  by_contra hcon
  push Not at hcon
  have hnd : ∀ j, {i | ((Q j).constraints xbar i).IsActiveAt (z j)}.ncard ≤ (Q j).n + 1 := by
    intro j
    by_contra hlt
    push Not at hlt
    exact hcon j ⟨(hbasic j).1, hlt⟩
  have hsd : ∀ j, (Q j).objective (z j) ≤ dualObjective ((Q j).constraints xbar) (lam j) := by
    intro j
    obtain ⟨μ, hμf, hμv⟩ := strong_dual ((Q j).constraints xbar)
      (Fin.snoc (α := fun _ => ℝ) (Q j).c 1) (z j) (hbasic j) (hnd j)
      (fun z' hz' => (hopt j).2 z' hz')
    have := (hdual j).2 μ hμf
    unfold NodeProblem.objective
    linarith
  have hfeas : ∀ j, z j ∈ (Q j).feasibleSet xbar := fun j => (hopt j).1
  have hθ1 : θbar ≤ ∑ j, p j * (Q j).objective (z j) := by
    have := hvalid₁ xbar z hfeas
    linarith
  have hcut : optimalityCutConst Q p lam - optimalityCutSlope Q p lam ⬝ᵥ xbar =
      ∑ j, p j * dualObjective ((Q j).constraints xbar) (lam j) := by
    simp only [optimalityCutConst, optimalityCutSlope, sum_dotProduct, smul_dotProduct,
      smul_eq_mul, dualObj_eq, mul_sub, Finset.sum_sub_distrib]
  have hθ2 : ∑ j, p j * (Q j).objective (z j) ≤ θbar := by
    have : ∑ j, p j * (Q j).objective (z j) ≤
        ∑ j, p j * dualObjective ((Q j).constraints xbar) (lam j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hsd j) (hp j).le
    linarith
  -- one-sided directional bound for a valid binding cut
  have ev : ∀ (h' : Fin P.n → ℝ) (w' : ∀ j, Fin ((Q j).n + 1) → ℝ),
      (∀ j i, ((Q j).constraints xbar i).IsActiveAt (z j) →
        ((Q j).constraints xbar i).a ⬝ᵥ w' j = beta (Q j) h' i) →
      ∀ l, IsValidOptimalityCut Q p (P.E l) (P.e l) → P.E l ⬝ᵥ xbar + θbar = P.e l →
        -(P.E l ⬝ᵥ h') ≤ ∑ j, p j * (Q j).objective (w' j) := by
    intro h' w' hw' l hval hbind
    have hev : ∀ j, ∀ᶠ t in 𝓝[≥] (0:ℝ),
        z j + t • w' j ∈ constraintSet (pert ((Q j).constraints xbar) (beta (Q j) h') t) :=
      fun j => eventually_feasible _ _ _ _ (hfeas j)
        (fun i hi => sat_of_eq _ _ (hw' j i hi))
    obtain ⟨t, ht, htpos⟩ :=
      (((Filter.eventually_all.2 hev).filter_mono
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)).and self_mem_nhdsWithin).exists
    have hv := hval (xbar + t • h') (fun j => z j + t • w' j) (by
      intro j
      unfold NodeProblem.feasibleSet
      rw [constraints_add]
      exact ht j)
    have hexp : ∑ j, p j * (Q j).objective (z j + t • w' j) =
        ∑ j, p j * (Q j).objective (z j) + t * ∑ j, p j * (Q j).objective (w' j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [NodeProblem.objective, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [hexp, dotProduct_add, dotProduct_smul, smul_eq_mul] at hv
    have htp : (0:ℝ) < t := htpos
    have : t * (-(P.E l ⬝ᵥ h')) ≤ t * ∑ j, p j * (Q j).objective (w' j) := by nlinarith
    exact le_of_mul_le_mul_left this htp
  have hslope : ∀ h : Fin P.n → ℝ, P.E l₁ ⬝ᵥ h = P.E l₂ ⬝ᵥ h := by
    intro h
    have hw : ∀ j, ∃ w : Fin ((Q j).n + 1) → ℝ, ∀ i,
        ((Q j).constraints xbar i).IsActiveAt (z j) →
          ((Q j).constraints xbar i).a ⬝ᵥ w = beta (Q j) h i := by
      intro j
      obtain ⟨s, hs, hli, hact⟩ := nondeg_active _ (z j) (hbasic j).1 (hnd j)
      obtain ⟨w, hw⟩ :=
        (solve_rows (fun i => ((Q j).constraints xbar i).a) s hs hli).1 (beta (Q j) h)
      exact ⟨w, fun i hi => hw i ((hact i).1 hi)⟩
    choose w hw using hw
    have hwn : ∀ j i, ((Q j).constraints xbar i).IsActiveAt (z j) →
        ((Q j).constraints xbar i).a ⬝ᵥ (-w j) = beta (Q j) (-h) i := by
      intro j i hi
      rw [dotProduct_neg, hw j i hi, beta_neg]
    have hneg : ∑ j, p j * (Q j).objective (-w j) = -∑ j, p j * (Q j).objective (w j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [NodeProblem.objective, dotProduct_neg]
      ring
    have a1 := ev h w hw l₁ hvalid₁ hbind₁
    have a2 := ev h w hw l₂ hvalid₂ hbind₂
    have b1 := ev (-h) (fun j => -w j) hwn l₁ hvalid₁ hbind₁
    have b2 := ev (-h) (fun j => -w j) hwn l₂ hvalid₂ hbind₂
    rw [hneg, dotProduct_neg] at b1 b2
    linarith
  have hE : P.E l₁ = P.E l₂ := by
    funext k
    have := hslope (Pi.single k 1)
    simpa [dotProduct_single] using this
  apply hdistinct
  have he : P.e l₁ = P.e l₂ := by rw [← hbind₁, ← hbind₂, hE]
  rw [hE, he]

end Birge1985.Degeneracy.P3ccc


open Matrix LinearOptimization Birge1985.Degeneracy in
theorem solution {nIn : ℕ} (P : NodeProblem nIn)
    {J : Type} [Fintype J] (Q : J → NodeProblem P.n) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (l₁ l₂ : Fin P.s) (hdistinct : (P.E l₁, P.e l₁) ≠ (P.E l₂, P.e l₂))
    (hvalid₁ : IsValidOptimalityCut Q p (P.E l₁) (P.e l₁))
    (hvalid₂ : IsValidOptimalityCut Q p (P.E l₂) (P.e l₂))
    (xbar : Fin P.n → ℝ) (θbar : ℝ)
    (hbind₁ : P.E l₁ ⬝ᵥ xbar + θbar = P.e l₁)
    (hbind₂ : P.E l₂ ⬝ᵥ xbar + θbar = P.e l₂)
    (z : ∀ j, Fin ((Q j).n + 1) → ℝ)
    (hbasic : ∀ j, IsBasicFeasibleSolution ((Q j).constraints xbar) (z j))
    (hopt : ∀ j, (Q j).IsOptimalSolution xbar (z j))
    (lam : ∀ j, (Q j).Idx → ℝ)
    (hdual : ∀ j, IsDualOptimal ((Q j).constraints xbar)
      (Fin.snoc (α := fun _ => ℝ) (Q j).c 1) (lam j))
    (hnot9 : optimalityCutConst Q p lam - optimalityCutSlope Q p lam ⬝ᵥ xbar ≤ θbar) :
    ∃ j, IsDegenerateBasicSolution ((Q j).constraints xbar) (z j) := by
  exact Birge1985.Degeneracy.P3ccc.main P Q p hp l₁ l₂ hdistinct hvalid₁ hvalid₂ xbar θbar hbind₁ hbind₂
    z hbasic hopt lam hdual hnot9
