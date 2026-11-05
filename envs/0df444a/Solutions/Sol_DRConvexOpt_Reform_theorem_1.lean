-- Prove2me | solution 1 for DRConvexOpt.Reform.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:58:54.662455+00:00
-- url     : https://prove2.me/submissions/a23f5699-cabe-49c4-9ea1-adf6c38b91e3

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Theorems.Thm_DRConvexOpt_Reform_lemma_1
import Theorems.Thm_DRConvexOpt_Reform_moment_duality
import Theorems.Thm_DRConvexOpt_Reform_partition_step
import Theorems.Thm_DRConvexOpt_Reform_boundary_step
import Theorems.Thm_DRConvexOpt_Reform_theorem_1_if

open MeasureTheory Matrix DRConvexOpt.Reform

theorem solution {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hN : Nesting d) (hS1 : MomentSlater d) (hS2 : ConfSlater d)
    (x : Fin nN → ℝ) (w : ℝ) :
    (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ↔
    ∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ)
      (φ : (i : Fin (nI + 1)) → Fin nL → Fin (d.L i) → ℝ),
      (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i l, φ i l ∈ dualCone (d.K i)) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ i l, d.c i ⬝ᵥ φ i l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ i l + d.Aᵀ *ᵥ β = (v.S l)ᵀ *ᵥ x + v.tv l ∧
        (d.D i)ᵀ *ᵥ φ i l + d.Bᵀ *ᵥ β = 0 := by
  -- every confidence set lies in `C_I`, a consequence of (S1) and (N)
  have hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI) := by
    intro i
    by_cases hi : i = Fin.last nI
    · subst hi; exact le_rfl
    obtain ⟨ε, hε, hS⟩ := hS1
    rcases hN i (Fin.last nI) hi with h | h | h
    · exact h.trans interior_subset
    · exfalso
      obtain ⟨μ, hfin, hnull, -, -, hpr⟩ := hS d.b (fun j => if j = Fin.last nI then ε else -ε)
        (fun k => by simp [hε.le]) (fun j => by split_ifs <;> simp [abs_of_pos hε])
      have h1 := hpr (Fin.last nI)
      have h2 := hpr i
      simp only [if_neg hi, if_true, Set.mem_Icc] at h1 h2
      have hmono : μ.real (d.conf (Fin.last nI)) ≤ μ.real (d.conf i) :=
        measureReal_mono (h.trans interior_subset) (measure_ne_top _ _)
      have := (hp i).2.2
      rw [hC1.2.1] at h1
      linarith [h1.1, h2.2]
    · exfalso
      obtain ⟨μ, hfin, hnull, -, -, hpr⟩ := hS d.b (fun _ => ε)
        (fun k => by simp [hε.le]) (fun j => by simp [abs_of_pos hε])
      have h2 := (hpr i).1
      have h0 : μ (d.conf i) = 0 := measure_mono_null h.subset_compl_right hnull
      have : μ.real (d.conf i) = 0 := by simp [Measure.real, h0]
      have := (hp i).1
      linarith
  constructor
  · intro h3
    obtain ⟨β, κ, lam, hκ, hlam, hobj, hdual⟩ :=
      (moment_duality d v hK hp hC1 hS1 x w).mp h3
    -- the dual constraint on each `C_i`, with the antecedent sum
    have hci : ∀ i, ∀ ω ∈ d.conf i,
        v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β + ∑ i' ∈ anc d i, (κ i' - lam i') := by
      by_cases hdim : 0 < nP + nQ
      · intro i ω hω
        have hp1 := (partition_step d v hK hC1.1 hN hsub hdim x β κ lam).mp hdual i
        have hp2 := (boundary_step d v hK hC1.1 hN hsub hdim x i β κ lam).mp
          (fun ω hω => by linarith [hp1 ω hω]) ω hω
        linarith
      · classical
        intro i ω hω
        have hss : ∀ a b : (Fin nP → ℝ) × (Fin nQ → ℝ), a = b := fun a b =>
          Prod.ext (funext fun k => absurd k.2 (by omega)) (funext fun k => absurd k.2 (by omega))
        have hd := hdual ω (hsub i hω)
        have hanc : anc d i = Finset.univ.filter (fun j => ω ∈ d.conf j) := by
          ext j
          simp only [anc, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (rfl | hj)
            · exact hω
            · exact interior_subset (hj hω)
          · intro hj
            right
            intro a _
            have : d.conf j = Set.univ := Set.eq_univ_of_forall fun b => hss ω b ▸ hj
            rw [this, interior_univ]; trivial
        have hsum : ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j) =
            ∑ i' ∈ anc d i, (κ i' - lam i') := by
          rw [hanc, Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : ω ∈ d.conf j <;> simp [hj]
        linarith
    have hφ : ∀ i, ∃ φ : Fin nL → Fin (d.L i) → ℝ, ∀ l, φ l ∈ dualCone (d.K i) ∧
        d.c i ⬝ᵥ φ l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ l = (v.S l)ᵀ *ᵥ x + v.tv l + -(d.Aᵀ *ᵥ β) ∧
        (d.D i)ᵀ *ᵥ φ l = -(d.Bᵀ *ᵥ β) := by
      intro i
      refine (lemma_1 (d.C i) (d.D i) (d.c i) (d.K i) (hK i) (hS2 i) v x
        (-(d.Aᵀ *ᵥ β)) (-(d.Bᵀ *ᵥ β)) _).mp ?_
      intro ω hω
      have := hci i ω hω
      have e1 : (-(d.Aᵀ *ᵥ β)) ⬝ᵥ ω.1 = -((d.A *ᵥ ω.1) ⬝ᵥ β) := by
        rw [neg_dotProduct, mulVec_transpose, dotProduct_comm (d.A *ᵥ ω.1), dotProduct_mulVec]
      have e2 : (-(d.Bᵀ *ᵥ β)) ⬝ᵥ ω.2 = -((d.B *ᵥ ω.2) ⬝ᵥ β) := by
        rw [neg_dotProduct, mulVec_transpose, dotProduct_comm (d.B *ᵥ ω.2), dotProduct_mulVec]
      rw [add_dotProduct] at this
      rw [e1, e2]
      linarith
    choose φ hφ using hφ
    refine ⟨β, κ, lam, φ, hκ, hlam, fun i l => (hφ i l).1, hobj, fun i l => ⟨(hφ i l).2.1, ?_, ?_⟩⟩
    · rw [(hφ i l).2.2.1]; abel
    · rw [(hφ i l).2.2.2]; abel
  · exact theorem_1_if d v hK hC1 hN x w
