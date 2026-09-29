-- Prove2me | solution 1 for BanditAlgorithm.mdp_compact_confidence_optimistic_bellman_solution
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T16:33:10.84179+00:00
-- url     : https://prove2.me/submissions/a4ee2a00-6c56-4e6d-b360-5f33eb8119d2

import Theorems.Thm_BanditAlgorithm_mdp_compact_confidence_discounted_bellman_solution
import Theorems.Thm_BanditAlgorithm_mdp_span_le_gain_mul_diameter
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_le_of_bellman_ineq
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
Extended value iteration converges (L&S §38.5; Jaksch–Ortner–Auer §3.1).

The vanishing-discount argument for the extended MDP.  For each `γ < 1` let
`V_γ` be the discounted extended value function and put
`ρ_γ = (1-γ) max_s V_γ(s) ∈ [0,1]`.  Splitting the discount factor shows that
`(ρ_γ, V_γ)` solves the average-reward Bellman *inequality* for every transition
matrix in the confidence set — in particular for the genuine MDP `M`, so
`mdp_span_le_gain_mul_diameter` bounds `span(V_γ)` by `ρ_γ D(M) ≤ D(M)`
uniformly in `γ`.  The recentred functions therefore live in a compact cube, the
optimistic rows live in the compact confidence sets, and the maximising actions
live in a finite set; so along a subsequence everything converges with a
constant action map, and the defect in the greedy equality is squeezed to zero.
-/

variable {S A : ℕ}

private lemma probVecMulLe {p u : Fin S → ℝ} {c : ℝ} (hp0 : ∀ s', 0 ≤ p s')
    (hp1 : ∑ s', p s' = 1) (h : ∀ s', u s' ≤ c) : ∑ s', p s' * u s' ≤ c := by
  calc ∑ s', p s' * u s' ≤ ∑ s', p s' * c :=
        Finset.sum_le_sum fun s' _ ↦ mul_le_mul_of_nonneg_left (h s') (hp0 s')
    _ = c := by rw [← Finset.sum_mul, hp1, one_mul]

private lemma leProbVecMul {p u : Fin S → ℝ} {c : ℝ} (hp0 : ∀ s', 0 ≤ p s')
    (hp1 : ∑ s', p s' = 1) (h : ∀ s', c ≤ u s') : c ≤ ∑ s', p s' * u s' := by
  calc c = ∑ s', p s' * c := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ s', p s' * u s' :=
        Finset.sum_le_sum fun s' _ ↦ mul_le_mul_of_nonneg_left (h s') (hp0 s')

private lemma probVecMulSubConst {p : Fin S → ℝ} (hp1 : ∑ s', p s' = 1)
    (u : Fin S → ℝ) (c : ℝ) :
    ∑ s', p s' * (u s' - c) = (∑ s', p s' * u s') - c := by
  have h : ∑ s', p s' * (u s' - c)
      = (∑ s', p s' * u s') - ∑ s', p s' * c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ ↦ by ring
  rw [h, ← Finset.sum_mul, hp1, one_mul]

theorem solution {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hCne : ∀ s a, (C s a).Nonempty)
    (hCcomp : ∀ s a, IsCompact (C s a))
    (hCprob : ∀ s a, ∀ p ∈ C s a, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1)
    (M : FiniteMDP S A) (hMr : M.r = r) (hMD : mdpDiameterENN M ≠ ⊤)
    (hMC : ∀ s a, (fun s' ↦ ((M.P s a s' : ℝ))) ∈ C s a) :
    ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ s s', v s - v s' ≤ ρ * mdpDiameter M) ∧
      (∀ s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * v s' ≤ ρ + v s) ∧
      (∀ s, q s ∈ C s (f s)) ∧
      (∀ s, ρ + v s = r s (f s) + ∑ s', q s s' * v s') ∧
      mdpOptimalGain M ≤ ρ := by
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  have hD0 : (0 : ℝ) ≤ mdpDiameter M := ENNReal.toReal_nonneg
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → ℝ, ∀ k, γ k = 1 - 1 / ((k : ℝ) + 1) :=
    ⟨fun k ↦ 1 - 1 / ((k : ℝ) + 1), fun _ ↦ rfl⟩
  have hkpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k ↦ by positivity
  have hone : ∀ k, 1 - γ k = 1 / ((k : ℝ) + 1) := fun k ↦ by rw [hγ]; ring
  have hγ1 : ∀ k, γ k < 1 := by
    intro k
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [hγ]; linarith
  have hγ0 : ∀ k, 0 ≤ γ k := by
    intro k
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hkpos k)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hγ]; linarith
  have hγpos : ∀ k, (0 : ℝ) < 1 - γ k := fun k ↦ by linarith [hγ1 k]
  choose V f q hVbox hVle hq hVeq using fun k ↦
    mdp_compact_confidence_discounted_bellman_solution hS hA r hr C hCne hCcomp hCprob
      (γ k) (hγ0 k) (hγ1 k)
  choose smax hsmax using fun k ↦ Finite.exists_max (V k)
  choose smin hsmin using fun k ↦ Finite.exists_min (V k)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℕ → ℝ, ∀ k, ρ' k = (1 - γ k) * V k (smax k) :=
    ⟨fun k ↦ (1 - γ k) * V k (smax k), fun _ ↦ rfl⟩
  have hρ0 : ∀ k, 0 ≤ ρ' k := by
    intro k; rw [hρ']; exact mul_nonneg (le_of_lt (hγpos k)) (hVbox k (smax k)).1
  have hρ1 : ∀ k, ρ' k ≤ 1 := by
    intro k
    have h1 : V k (smax k) ≤ 1 / (1 - γ k) := (hVbox k _).2
    have h3 : (1 - γ k) * V k (smax k) ≤ (1 - γ k) * (1 / (1 - γ k)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hγpos k))
    have h4 : (1 - γ k) * (1 / (1 - γ k)) = 1 := by
      field_simp
      exact div_self (ne_of_gt (hγpos k))
    rw [hρ']; linarith
  -- `(ρ' k, V k)` solves the average-reward Bellman inequality for the whole family
  have hAvg : ∀ k s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * V k s' ≤ ρ' k + V k s := by
    intro k s a p hp
    obtain ⟨hp0, hp1⟩ := hCprob s a p hp
    have h1 := hVle k s a p hp
    have h2 : ∑ s', p s' * V k s' ≤ V k (smax k) := probVecMulLe hp0 hp1 (hsmax k)
    have h3 : (0 : ℝ) ≤ 1 - γ k := le_of_lt (hγpos k)
    rw [hρ']
    nlinarith [mul_nonneg h3 (sub_nonneg.mpr h2)]
  have hAvgM : ∀ k s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * V k s' ≤ ρ' k + V k s := by
    intro k s a
    rw [hMr]
    exact hAvg k s a _ (hMC s a)
  have hspan : ∀ k s s', V k s - V k s' ≤ ρ' k * mdpDiameter M := fun k s s' ↦
    mdp_span_le_gain_mul_diameter M (ρ' k) (hρ0 k) (V k) 0 (1 / (1 - γ k))
      (hVbox k) (hAvgM k) hMD s s'
  have hρD : ∀ k, ρ' k * mdpDiameter M ≤ mdpDiameter M := by
    intro k
    nlinarith [hρ0 k, hρ1 k, hD0]
  obtain ⟨s₀⟩ : Nonempty (Fin S) := inferInstance
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Fin S → ℝ, ∀ k s, w k s = V k s - V k s₀ :=
    ⟨fun k s ↦ V k s - V k s₀, fun _ _ ↦ rfl⟩
  have hwbox : ∀ k s, w k s ∈ Set.Icc (-mdpDiameter M) (mdpDiameter M) := by
    intro k s
    have h1 := hspan k s₀ s
    have h2 := hspan k s s₀
    have h3 := hρD k
    rw [hw]
    exact ⟨by linarith, by linarith⟩
  have hwbell : ∀ k s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * w k s' ≤ ρ' k + w k s := by
    intro k s a p hp
    obtain ⟨-, hp1⟩ := hCprob s a p hp
    have hshift : ∑ s', p s' * w k s' = (∑ s', p s' * V k s') - V k s₀ := by
      simp only [hw]
      exact probVecMulSubConst hp1 (V k) (V k s₀)
    have h := hAvg k s a p hp
    rw [hshift, hw]
    linarith
  have heps : ∀ k s,
      0 ≤ ρ' k + w k s - (r s (f k s) + ∑ s', q k s s' * w k s') ∧
      ρ' k + w k s - (r s (f k s) + ∑ s', q k s s' * w k s')
        ≤ (1 - γ k) * mdpDiameter M := by
    intro k s
    obtain ⟨hq0, hq1⟩ := hCprob s (f k s) (q k s) (hq k s)
    have hshift : ∑ s', q k s s' * w k s' = (∑ s', q k s s' * V k s') - V k s₀ := by
      simp only [hw]
      exact probVecMulSubConst hq1 (V k) (V k s₀)
    have hEmax : ∑ s', q k s s' * V k s' ≤ V k (smax k) :=
      probVecMulLe hq0 hq1 (hsmax k)
    have hEmin : V k (smin k) ≤ ∑ s', q k s s' * V k s' :=
      leProbVecMul hq0 hq1 (hsmin k)
    have hsp := hspan k (smax k) (smin k)
    have hρDk := hρD k
    have hg : (0 : ℝ) ≤ 1 - γ k := le_of_lt (hγpos k)
    have heq := hVeq k s
    have hMxE0 : 0 ≤ V k (smax k) - ∑ s', q k s s' * V k s' := by linarith
    have hMxE : V k (smax k) - (∑ s', q k s s' * V k s') ≤ mdpDiameter M := by
      linarith
    rw [hshift, hw, hρ']
    constructor
    · nlinarith [mul_nonneg hg hMxE0]
    · nlinarith [mul_le_mul_of_nonneg_left hMxE hg]
  have hfreq : ∃ g : Fin S → Fin A, ∃ᶠ k in Filter.atTop, f k = g := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ᶠ k in Filter.atTop, ∀ g : Fin S → Fin A, f k ≠ g := by
      rw [Filter.eventually_all]
      intro g
      simpa [Filter.not_frequently] using hcon g
    obtain ⟨k, hk⟩ := hall.exists
    exact hk (f k) rfl
  obtain ⟨g, hgfreq⟩ := hfreq
  obtain ⟨ψ, hψmono, hψ⟩ := Filter.extraction_of_frequently_atTop hgfreq
  have hKcompact : IsCompact
      ((Set.univ.pi fun _ : Fin S ↦ Set.Icc (-mdpDiameter M) (mdpDiameter M)) ×ˢ
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ.pi fun s : Fin S ↦ C s (g s)))) :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).prod
      (isCompact_Icc.prod (isCompact_univ_pi fun s ↦ hCcomp s (g s)))
  have hmem : ∀ j : ℕ, (w (ψ j), ρ' (ψ j), q (ψ j)) ∈
      ((Set.univ.pi fun _ : Fin S ↦ Set.Icc (-mdpDiameter M) (mdpDiameter M)) ×ˢ
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ.pi fun s : Fin S ↦ C s (g s)))) := by
    intro j
    refine ⟨fun s _ ↦ hwbox (ψ j) s, ⟨hρ0 _, hρ1 _⟩, fun s _ ↦ ?_⟩
    have h := hq (ψ j) s
    rw [hψ j] at h
    exact h
  obtain ⟨⟨v, ρ, Q⟩, hlimmem, φ, hφmono, htend⟩ := hKcompact.tendsto_subseq hmem
  have htendw : Filter.Tendsto (fun j ↦ w (ψ (φ j))) Filter.atTop (nhds v) := by
    have h := (continuous_fst.tendsto ((v : Fin S → ℝ), ρ, Q)).comp htend
    simpa [Function.comp_def] using h
  have htendρ : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j))) Filter.atTop (nhds ρ) := by
    have h := ((continuous_fst.comp continuous_snd).tendsto
      ((v : Fin S → ℝ), ρ, Q)).comp htend
    simpa [Function.comp_def] using h
  have htendQ : Filter.Tendsto (fun j ↦ q (ψ (φ j))) Filter.atTop (nhds Q) := by
    have h := ((continuous_snd.comp continuous_snd).tendsto
      ((v : Fin S → ℝ), ρ, Q)).comp htend
    simpa [Function.comp_def] using h
  have htw : ∀ s, Filter.Tendsto (fun j ↦ w (ψ (φ j)) s) Filter.atTop (nhds (v s)) :=
    fun s ↦ (tendsto_pi_nhds.mp htendw) s
  have htq : ∀ s s', Filter.Tendsto (fun j ↦ q (ψ (φ j)) s s') Filter.atTop
      (nhds (Q s s')) := fun s s' ↦
    (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp htendQ) s)) s'
  have hσmono : StrictMono (fun j ↦ ψ (φ j)) := hψmono.comp hφmono
  have hfσ : ∀ j, f (ψ (φ j)) = g := fun j ↦ hψ (φ j)
  have hvbox : ∀ s, v s ∈ Set.Icc (-mdpDiameter M) (mdpDiameter M) :=
    fun s ↦ hlimmem.1 s (Set.mem_univ s)
  have hvbell : ∀ s a, ∀ p ∈ C s a, r s a + ∑ s', p s' * v s' ≤ ρ + v s := by
    intro s a p hp
    have hL : Filter.Tendsto
        (fun j ↦ r s a + ∑ s', p s' * w (ψ (φ j)) s') Filter.atTop
        (nhds (r s a + ∑ s', p s' * v s')) :=
      tendsto_const_nhds.add
        (tendsto_finset_sum _ fun s' _ ↦ tendsto_const_nhds.mul (htw s'))
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) + w (ψ (φ j)) s) Filter.atTop
        (nhds (ρ + v s)) := htendρ.add (htw s)
    exact le_of_tendsto_of_tendsto' hL hR fun j ↦ hwbell _ s a p hp
  have hγlim : Filter.Tendsto (fun k : ℕ ↦ (1 - γ k) * mdpDiameter M) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) * mdpDiameter M)
        Filter.atTop (nhds (0 * mdpDiameter M)) := h1.mul tendsto_const_nhds
    simp only [hone]
    simpa using h2
  have hγlimσ : Filter.Tendsto (fun j ↦ (1 - γ (ψ (φ j))) * mdpDiameter M) Filter.atTop
      (nhds 0) := hγlim.comp hσmono.tendsto_atTop
  have hveq : ∀ s, ρ + v s = r s (g s) + ∑ s', Q s s' * v s' := by
    intro s
    have hL : Filter.Tendsto
        (fun j ↦ r s (g s) + ∑ s', q (ψ (φ j)) s s' * w (ψ (φ j)) s') Filter.atTop
        (nhds (r s (g s) + ∑ s', Q s s' * v s')) :=
      tendsto_const_nhds.add
        (tendsto_finset_sum _ fun s' _ ↦ (htq s s').mul (htw s'))
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) + w (ψ (φ j)) s) Filter.atTop
        (nhds (ρ + v s)) := htendρ.add (htw s)
    refine le_antisymm ?_ ?_
    · have hL' : Filter.Tendsto
          (fun j ↦ (r s (g s) + ∑ s', q (ψ (φ j)) s s' * w (ψ (φ j)) s')
            + (1 - γ (ψ (φ j))) * mdpDiameter M) Filter.atTop
          (nhds (r s (g s) + ∑ s', Q s s' * v s')) := by
        simpa using hL.add hγlimσ
      refine le_of_tendsto_of_tendsto' hR hL' fun j ↦ ?_
      have h := (heps (ψ (φ j)) s).2
      rw [hfσ j] at h
      linarith
    · refine le_of_tendsto_of_tendsto' hL hR fun j ↦ ?_
      have h := (heps (ψ (φ j)) s).1
      rw [hfσ j] at h
      linarith
  have hvspan : ∀ s s', v s - v s' ≤ ρ * mdpDiameter M := by
    intro s s'
    have hL : Filter.Tendsto (fun j ↦ w (ψ (φ j)) s - w (ψ (φ j)) s') Filter.atTop
        (nhds (v s - v s')) := (htw s).sub (htw s')
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) * mdpDiameter M) Filter.atTop
        (nhds (ρ * mdpDiameter M)) := htendρ.mul tendsto_const_nhds
    refine le_of_tendsto_of_tendsto' hL hR fun j ↦ ?_
    have h := hspan (ψ (φ j)) s s'
    rw [hw, hw]
    linarith
  have hvbellM : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s := by
    intro s a
    rw [hMr]
    exact hvbell s a _ (hMC s a)
  have hopt : mdpOptimalGain M ≤ ρ :=
    mdp_optimal_gain_le_of_bellman_ineq hS hA M ρ v (-mdpDiameter M) (mdpDiameter M)
      hvbox hvbellM
  exact ⟨ρ, v, g, Q, hlimmem.2.1.1, hlimmem.2.1.2, hvspan, hvbell,
    fun s ↦ hlimmem.2.2 s (Set.mem_univ s), hveq, hopt⟩
