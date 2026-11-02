-- Prove2me | solution 1 for GenPayoffSG.Solvable.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:45:37.616778+00:00
-- url     : https://prove2.me/submissions/62206461-ffed-4a4e-bfc3-c371c9a66476

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_ReachQ

open MeasureTheory ProbabilityTheory ENNReal GenPayoffSG.Solvable

set_option linter.unusedSectionVars false

namespace GPSGEq10

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

lemma frestrictLe_succ (y : Run I S A) (n : ℕ) :
    Preorder.frestrictLe (n + 1) y =
      GenPayoffSG.Solvable.extend (Preorder.frestrictLe n y) (coordAction (y (n + 1)))
        (coordState (n + 1) (y (n + 1))) := by
  funext ⟨k, hk⟩
  unfold GenPayoffSG.Solvable.extend
  by_cases hkn : k ≤ n
  · simp [hkn]
  · have : k = n + 1 := by have := Finset.mem_Iic.1 hk; omega
    subst this
    simp [hkn]
    rfl

lemma stepPMF_apply (G : Game I S A) (σ : Profile G) (n : ℕ) (h : Hist I S A n)
    (a : ∀ i, A i) (s : S) :
    stepPMF G σ n h ((a, s) : Coord I S A (n + 1)) = actionPMF G σ n h a * G.p (lastState h) a s := by
  change ((actionPMF G σ n h).bind (fun a => (G.p (lastState h) a).map
    (fun s' => ((a, s') : (∀ i, A i) × S)))) ((a, s) : (∀ i, A i) × S) = _
  rw [PMF.bind_apply, tsum_eq_single a]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((a, s) : (∀ i, A i) × S) = (a, s') := by
        intro he; exact hs' (Prod.ext_iff.1 he).2.symm
      simp [this]
  · intro a' ha'
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((a, s) : (∀ i, A i) × S) = (a', s') := by
      intro s' he; exact ha' (Prod.ext_iff.1 he).1.symm
    simp [this]

/-- The marginal of a product of independent mixed actions. -/
lemma marginal (τ : ∀ k, PMF (A k)) (i : I) (bi : A i) :
    ∑ a : ∀ k, A k, (if a i = bi then ∏ k, τ k (a k) else 0) = τ i bi := by
  let t : ∀ k, Finset (A k) := Function.update (fun _ => Finset.univ) i {bi}
  have hfil : Finset.univ.filter (fun a : ∀ k, A k => a i = bi) = Fintype.piFinset t := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro ha k
      by_cases hk : k = i
      · subst hk; simp [t, ha]
      · simp [t, Function.update_of_ne hk]
    · intro ha
      simpa [t] using ha i
  rw [← Finset.sum_filter, hfil, ← Finset.prod_univ_sum]
  rw [Fintype.prod_eq_single i]
  · simp [t]
  · intro k hk
    simp only [t, Function.update_of_ne hk]
    have := PMF.tsum_coe (τ k)
    rwa [tsum_fintype] at this

/-- Key one-step identity: integrating `Λᵢ(h, ·)` against the next action of player `i`
gives the probability that the next history lies in `Q`. -/
lemma key (G : Game I S A) (σ : Profile G) (Q : Set (Σ n, Hist I S A n)) (i : I) {j : ℕ}
    (h : Hist I S A j) :
    ∫⁻ c, reachProb G σ Q i h (coordAction c i) ∂(stepKernel G σ j h) =
      stepKernel G σ j h {c : Coord I S A (j + 1) |
        (⟨j + 1, GenPayoffSG.Solvable.extend h (coordAction c) (coordState (j + 1) c)⟩ :
          Σ m, Hist I S A m) ∈ Q} := by
  classical
  change ∫⁻ c, _ ∂(stepPMF G σ j h).toMeasure = (stepPMF G σ j h).toMeasure _
  rw [lintegral_countable', (stepPMF G σ j h).toMeasure_apply MeasurableSet.of_discrete]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete)]
  change ∑' c : (∀ k, A k) × S, reachProb G σ Q i h (c.1 i) * stepPMF G σ j h c =
    ∑' c : (∀ k, A k) × S, Set.indicator {c : (∀ k, A k) × S |
        (⟨j + 1, GenPayoffSG.Solvable.extend h c.1 c.2⟩ : Σ m, Hist I S A m) ∈ Q}
      (stepPMF G σ j h) c
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
  have hL : ∀ a : ∀ k, A k, ∑' s, reachProb G σ Q i h ((a, s).1 i) * stepPMF G σ j h (a, s) =
      reachProb G σ Q i h (a i) * actionPMF G σ j h a := by
    intro a
    simp_rw [stepPMF_apply, ← mul_assoc]
    rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  simp_rw [hL]
  unfold reachProb
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun s => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq]
  by_cases hQ : (⟨j + 1, GenPayoffSG.Solvable.extend h b s⟩ : Σ m, Hist I S A m) ∈ Q
  · rw [if_pos hQ, stepPMF_apply]
    have : ∀ a : ∀ k, A k,
        (if b i = a i ∧ (⟨j + 1, GenPayoffSG.Solvable.extend h b s⟩ : Σ m, Hist I S A m) ∈ Q
          then (∏ k ∈ Finset.univ.erase i, σ k j h (b k)) * G.p (lastState h) b s else 0) *
          actionPMF G σ j h a =
        ((∏ k ∈ Finset.univ.erase i, σ k j h (b k)) * G.p (lastState h) b s) *
          (if a i = b i then ∏ k, σ k j h (a k) else 0) := by
      intro a
      by_cases hab : a i = b i
      · rw [if_pos ⟨hab.symm, hQ⟩, if_pos hab]
        simp [actionPMF, PMF.ofFintype_apply]
      · have : ¬ b i = a i := fun e => hab e.symm
        simp [this, hab]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, tsum_fintype, marginal (fun k => σ k j h) i (b i)]
    simp only [actionPMF, PMF.ofFintype_apply]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => σ k j h (b k)) (Finset.mem_univ i)]
    ring
  · rw [if_neg hQ]
    refine ENNReal.tsum_eq_zero.2 fun a => ?_
    rw [if_neg (fun hh => hQ hh.2), zero_mul]

end GPSGEq10

open GPSGEq10

theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
  (G : Game I S A) (σ : Profile G) (s : S) (Q : Set (Σ n, Hist I S A n))
    (hQH : ∀ q ∈ Q, Feasible G q.2)
    (hQ : ∀ q ∈ Q, ∀ q' ∈ Q, Extends q.2 q'.2 → q = q')
    (i : I) (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (θ : Run I S A → ℕ∞) (hθ : IsStoppingTime Filtration.piLE θ) :
    ∫⁻ r, fictCount G σ Q i r m₀ (θ r) ∂(playMeasure G σ 0 (initHist s)) =
      playMeasure G σ 0 (initHist s)
        {r | ∃ m : ℕ, m₀ ≤ m ∧ (m : ℕ∞) ≤ θ r ∧
          (⟨m, Preorder.frestrictLe m r⟩ : Σ k, Hist I S A k) ∈ Q} := by
  classical
  set μ := playMeasure G σ 0 (initHist s) with hμ
  set κ := stepKernel G σ
  -- the stopping-time events `{θ ≤ j}` are determined by the prefix of length `j`
  have hT : ∀ j : ℕ, ∃ T : Set (Hist I S A j),
      Preorder.frestrictLe j ⁻¹' T = {r | θ r ≤ (j : ℕ∞)} := by
    intro j
    have := hθ j
    rw [Filtration.piLE_eq_comap_frestrictLe, MeasurableSpace.measurableSet_comap] at this
    obtain ⟨T, _, hT⟩ := this
    exact ⟨T, hT⟩
  choose T hT using hT
  have hθT : ∀ j r, ((j + 1 : ℕ) : ℕ∞) ≤ θ r ↔ Preorder.frestrictLe j r ∉ T j := by
    intro j r
    have := congrArg (r ∈ ·) (hT j)
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, eq_iff_iff] at this
    rw [this, not_le, Nat.cast_succ, ENat.add_one_le_iff (ENat.natCast_ne_top j)]
  let φ : ∀ j : ℕ, Run I S A → Hist I S A j × Coord I S A (j + 1) :=
    fun j x => (Preorder.frestrictLe j x, x (j + 1))
  have hφ : ∀ j, Measurable (φ j) := fun j => by fun_prop
  have hmap : ∀ j, μ.map (φ j) =
      (Kernel.partialTraj κ 0 j (initHist s)) ⊗ₘ (κ j) := fun j =>
    (Kernel.partialTraj_compProd_eq_map_traj (κ := κ) (Nat.zero_le j)).symm
  -- the summands of `fictCount`
  let Gj : ∀ j : ℕ, Hist I S A j × Coord I S A (j + 1) → ℝ≥0∞ := fun j p =>
    if m₀ ≤ j + 1 ∧ p.1 ∉ T j then reachProb G σ Q i p.1 (coordAction p.2 i) else 0
  let E' : ∀ j : ℕ, Set (Hist I S A j × Coord I S A (j + 1)) := fun j =>
    {p | (m₀ ≤ j + 1 ∧ p.1 ∉ T j) ∧
      (⟨j + 1, GenPayoffSG.Solvable.extend p.1 (coordAction p.2) (coordState (j + 1) p.2)⟩ :
        Σ m, Hist I S A m) ∈ Q}
  have hfict : ∀ r, fictCount G σ Q i r m₀ (θ r) = ∑' j, Gj j (φ j r) := by
    intro r
    unfold fictCount
    refine tsum_congr fun j => ?_
    simp only [Gj, φ]
    by_cases hc : m₀ ≤ j + 1 ∧ ((j + 1 : ℕ) : ℕ∞) ≤ θ r
    · rw [if_pos hc, if_pos ⟨hc.1, (hθT j r).1 hc.2⟩]
    · rw [if_neg hc, if_neg]
      rintro ⟨h1, h2⟩
      exact hc ⟨h1, (hθT j r).2 h2⟩
  have hstep : ∀ j, ∫⁻ r, Gj j (φ j r) ∂μ = μ (φ j ⁻¹' E' j) := by
    intro j
    have hGm : Measurable (Gj j) := measurable_of_countable _
    have hE : MeasurableSet (E' j) := MeasurableSet.of_discrete
    rw [← lintegral_map hGm (hφ j), ← Measure.map_apply (hφ j) hE, hmap j,
      Measure.lintegral_compProd hGm, Measure.compProd_apply hE]
    refine lintegral_congr fun h => ?_
    by_cases hc : m₀ ≤ j + 1 ∧ h ∉ T j
    · simp only [Gj, if_pos hc]
      rw [key G σ Q i h]
      congr 1
      ext c
      simp [E', hc]
    · simp only [Gj, if_neg hc, lintegral_zero]
      have : Prod.mk h ⁻¹' E' j = ∅ := by
        ext c; simp only [E', Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1; exact absurd h1 hc
      rw [this, measure_empty]
  -- the events `E j` are pairwise disjoint because `Q` is an antichain
  have hEj : ∀ j r, r ∈ φ j ⁻¹' E' j ↔ (m₀ ≤ j + 1 ∧ ((j + 1 : ℕ) : ℕ∞) ≤ θ r) ∧
      (⟨j + 1, Preorder.frestrictLe (j + 1) r⟩ : Σ m, Hist I S A m) ∈ Q := by
    intro j r
    simp only [Set.mem_preimage, E', φ, Set.mem_ofPred_eq]
    rw [hθT j r, frestrictLe_succ r j]
  have hdisj : Pairwise (Function.onFun Disjoint fun j => φ j ⁻¹' E' j) := by
    intro j j' hne
    refine Set.disjoint_left.2 fun r h1 h2 => ?_
    rw [hEj] at h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hQ _ h1.2 _ h2.2 ⟨show j + 1 ≤ j' + 1 by omega, fun k hk => rfl⟩
      have h3 := congrArg Sigma.fst this
      dsimp only at h3
      omega
    · have := hQ _ h2.2 _ h1.2 ⟨show j' + 1 ≤ j + 1 by omega, fun k hk => rfl⟩
      have h3 := congrArg Sigma.fst this
      dsimp only at h3
      omega
  have hUnion : (⋃ j, φ j ⁻¹' E' j) = {r | ∃ m : ℕ, m₀ ≤ m ∧ (m : ℕ∞) ≤ θ r ∧
      (⟨m, Preorder.frestrictLe m r⟩ : Σ k, Hist I S A k) ∈ Q} := by
    ext r
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj⟩
      rw [hEj] at hj
      exact ⟨j + 1, hj.1.1, hj.1.2, hj.2⟩
    · rintro ⟨m, h1, h2, h3⟩
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact ⟨j, (hEj j r).2 ⟨⟨h1, h2⟩, h3⟩⟩
  have hGmeas : ∀ j, AEMeasurable (fun r => Gj j (φ j r)) μ := fun j =>
    ((measurable_of_countable (Gj j)).comp (hφ j)).aemeasurable
  simp_rw [hfict]
  rw [lintegral_tsum hGmeas, ← hUnion,
    measure_iUnion hdisj (fun j => hφ j MeasurableSet.of_discrete)]
  exact tsum_congr hstep
