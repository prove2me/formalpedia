-- Prove2me | solution 1 for BertsekasDP.needle_cost_first_variation
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T21:59:28.653814+00:00
-- url     : https://prove2.me/submissions/5827cc8a-28a0-49a8-aa15-973a162908c6

import Theorems.Thm_BertsekasDP_needle_perturbed_trajectory_exists
import Theorems.Thm_BertsekasDP_admissible_cost_integrand_intervalIntegrable
import Theorems.Thm_BertsekasDP_needle_interval_cost_average_limit
import Theorems.Thm_BertsekasDP_perturbed_terminal_cost_adjoint_limit

open Filter
open scoped Topology

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (hh : ContDiff ℝ 1 M.h)
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x p : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (hp : ContinuousOn p (Set.Icc 0 M.T))
    (hterm : p M.T = gradient M.h (x M.T))
    (F : Finset ℝ)
    (hadj : ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) (huτ : ContinuousAt u τ)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v ∈ M.U) :
    ∃ xε : ℝ → ℝ → EuclideanSpace ℝ (Fin n),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        BertsekasCTAdmissibleFrom M 0 M.x0
          (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε)) ∧
      Tendsto
        (fun ε =>
          (BertsekasCTCostFrom M 0
            (fun s => if s ∈ Set.Ioc (τ - ε) τ then v else u s) (xε ε) -
              BertsekasCTCostFrom M 0 u x) / ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (BertsekasHamiltonian M (x τ) v (p τ) -
          BertsekasHamiltonian M (x τ) (u τ) (p τ))) := by
  classical
  obtain ⟨xe, K, hev, hfirst⟩ :=
    BertsekasDP.needle_perturbed_trajectory_exists M hf u x hadm τ hτ huτ v hv
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ.1)
  refine ⟨xe, hev.mono fun ε hε => hε.1, ?_⟩
  -- the tail contribution, through the adjoint pairing
  have hy4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (xe ε) (Set.Icc τ M.T) ∧
        ∃ G : Finset ℝ, ∀ t ∈ Set.Icc τ M.T \ (G : Set ℝ),
          HasDerivAt (xe ε) (M.f (xe ε t) (u t)) t := by
    filter_upwards [hev] with ε hε
    obtain ⟨-, -, hcont, -, G, hG⟩ := hε.1
    refine ⟨hcont.mono (Set.Icc_subset_Icc_left hτ.1.le), insert τ G, ?_⟩
    intro t ht
    have hne : t ≠ τ := by
      intro h
      exact ht.2 (by simp [h])
    have hgt : τ < t := lt_of_le_of_ne ht.1.1 (Ne.symm hne)
    have hmem : t ∈ Set.Icc 0 M.T \ (G : Set ℝ) := by
      refine ⟨⟨le_trans hτ.1.le ht.1.1, ht.1.2⟩, ?_⟩
      intro hc
      exact ht.2 (by simp [hc])
    have hnot : t ∉ Set.Ioc (τ - ε) τ := fun hc => absurd hc.2 (not_le.mpr hgt)
    simpa only [if_neg hnot] using hG t hmem
  have hA := BertsekasDP.perturbed_terminal_cost_adjoint_limit M hf hg hh u x p hadm hp
    hterm F hadj τ hτ xe hy4 (M.f (x τ) v - M.f (x τ) (u τ)) hfirst
  -- the needle interval contribution
  have hy3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (xe ε) (Set.Icc (τ - ε) τ) ∧
        ∀ s ∈ Set.Icc (τ - ε) τ, ‖xe ε s - x τ‖ ≤ K * ε := by
    filter_upwards [hev, hlt] with ε hε hετ
    exact ⟨hε.1.2.2.1.mono (Set.Icc_subset_Icc (by linarith) hτ.2.le), hε.2.2⟩
  have hB := BertsekasDP.needle_interval_cost_average_limit M hg.continuous u x hadm τ hτ
    huτ v xe K hy3
  -- assemble
  have hval : (inner ℝ (p τ) (M.f (x τ) v - M.f (x τ) (u τ)) : ℝ) +
      (M.g (x τ) v - M.g (x τ) (u τ)) =
      BertsekasHamiltonian M (x τ) v (p τ) - BertsekasHamiltonian M (x τ) (u τ) (p τ) := by
    simp only [BertsekasHamiltonian, inner_sub_right]
    ring
  rw [← hval]
  refine Tendsto.congr' ?_ (hA.add hB)
  filter_upwards [hev, hlt, self_mem_nhdsWithin] with ε hε hετ hεpos
  have hεpos : (0 : ℝ) < ε := hεpos
  have h0 : (0 : ℝ) ≤ τ - ε := by linarith
  have hle : τ - ε ≤ τ := by linarith
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) M.T := ⟨le_rfl, (hτ.1.trans hτ.2).le⟩
  have hmem1 : τ - ε ∈ Set.Icc (0 : ℝ) M.T := ⟨h0, by linarith [hτ.2]⟩
  have hmem2 : τ ∈ Set.Icc (0 : ℝ) M.T := ⟨hτ.1.le, hτ.2.le⟩
  have hmem3 : M.T ∈ Set.Icc (0 : ℝ) M.T := ⟨(hτ.1.trans hτ.2).le, le_rfl⟩
  have hI1 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    _ _ hε.1 0 (τ - ε) hmem0 hmem1
  have hI2 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    _ _ hε.1 (τ - ε) τ hmem1 hmem2
  have hI3 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    _ _ hε.1 τ M.T hmem2 hmem3
  have hJ1 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    u x hadm 0 (τ - ε) hmem0 hmem1
  have hJ2 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    u x hadm (τ - ε) τ hmem1 hmem2
  have hJ3 := BertsekasDP.admissible_cost_integrand_intervalIntegrable M hg.continuous 0 M.x0
    u x hadm τ M.T hmem2 hmem3
  have c1 : (∫ t in (0 : ℝ)..(τ - ε),
      M.g (xe ε t) (if t ∈ Set.Ioc (τ - ε) τ then v else u t)) =
      ∫ t in (0 : ℝ)..(τ - ε), M.g (x t) (u t) := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    rw [Set.uIcc_of_le h0] at hs
    have hnot : s ∉ Set.Ioc (τ - ε) τ := fun hc => absurd hc.1 (not_lt.mpr hs.2)
    simp only [if_neg hnot, hε.2.1 s hs]
  have c2 : (∫ t in (τ - ε)..τ,
      M.g (xe ε t) (if t ∈ Set.Ioc (τ - ε) τ then v else u t)) =
      ∫ t in (τ - ε)..τ, M.g (xe ε t) v := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.uIoc_of_le hle] at hs
    simp only [if_pos hs]
  have c3 : (∫ t in τ..M.T,
      M.g (xe ε t) (if t ∈ Set.Ioc (τ - ε) τ then v else u t)) =
      ∫ t in τ..M.T, M.g (xe ε t) (u t) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.uIoc_of_le hτ.2.le] at hs
    have hnot : s ∉ Set.Ioc (τ - ε) τ := fun hc => absurd hc.2 (not_le.mpr hs.1)
    simp only [if_neg hnot]
  have hsplitU : (∫ t in (0 : ℝ)..M.T,
      M.g (xe ε t) (if t ∈ Set.Ioc (τ - ε) τ then v else u t)) =
      (∫ t in (0 : ℝ)..(τ - ε), M.g (x t) (u t)) +
        (∫ t in (τ - ε)..τ, M.g (xe ε t) v) +
        (∫ t in τ..M.T, M.g (xe ε t) (u t)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI1.trans hI2) hI3,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, c1, c2, c3]
  have hsplitx : (∫ t in (0 : ℝ)..M.T, M.g (x t) (u t)) =
      (∫ t in (0 : ℝ)..(τ - ε), M.g (x t) (u t)) +
        (∫ t in (τ - ε)..τ, M.g (x t) (u t)) +
        (∫ t in τ..M.T, M.g (x t) (u t)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hJ1.trans hJ2) hJ3,
      ← intervalIntegral.integral_add_adjacent_intervals hJ1 hJ2]
  simp only [BertsekasCTCostFrom, hsplitU, hsplitx]
  rw [div_eq_inv_mul]
  ring
