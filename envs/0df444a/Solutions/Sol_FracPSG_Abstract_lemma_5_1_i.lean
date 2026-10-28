-- Prove2me | solution 1 for FracPSG.Abstract.lemma_5_1_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:18:12.786262+00:00
-- url     : https://prove2.me/submissions/df9e0e7b-464e-4963-9c71-d94870f5d3a0

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

open FracPSG.Abstract NonconvexSplitting.Shared NonconvexSplitting.ADMMKL in
theorem solution {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH3 : H3 h z) :
    omega0 h z = {zbar | ∃ k : ℕ → ℕ, StrictMono k ∧
        Tendsto (fun n => z (k n)) atTop (𝓝 zbar) ∧
        Tendsto (fun n => h (z (k n))) atTop (𝓝 (h zbar))} ∧
      (omega0 h z).Nonempty ∧
      ∀ zbar ∈ omega0 h z, Antitone (fun n => h (z n)) ∧
        Tendsto (fun n => h (z n)) atTop (𝓝 (h zbar)) := by
  have hanti : Antitone (fun n => h (z n)) := by
    apply antitone_nat_of_succ_le
    intro n
    have h1 := hH1 n
    have h2 : (0 : EReal) ≤ ((α n * Δ n ^ 2 : ℝ) : EReal) := by
      exact_mod_cast mul_nonneg (hset.alpha_pos n).le (sq_nonneg _)
    exact le_trans (le_add_of_nonneg_right h2) h1
  have hconv : Tendsto (fun n => h (z n)) atTop (𝓝 (⨅ n, h (z n))) := tendsto_atTop_iInf hanti
  have hset_eq : omega0 h z = {zbar | ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n => z (k n)) atTop (𝓝 zbar) ∧
      Tendsto (fun n => h (z (k n))) atTop (𝓝 (h zbar))} := by
    ext zbar
    constructor
    · rintro ⟨hcl, hlim⟩
      obtain ⟨k, hk, hkt⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcl
      exact ⟨k, hk, hkt, hlim.comp hk.tendsto_atTop⟩
    · rintro ⟨k, hk, hkt, hkh⟩
      refine ⟨?_, ?_⟩
      · exact (hkt.mapClusterPt).of_comp hk.tendsto_atTop
      · have h1 : Tendsto (fun n => h (z (k n))) atTop (𝓝 (⨅ n, h (z n))) :=
          hconv.comp hk.tendsto_atTop
        have := tendsto_nhds_unique h1 hkh
        rw [← this]
        exact hconv
  refine ⟨hset_eq, ?_, fun zbar hz => ⟨hanti, hz.2⟩⟩
  obtain ⟨k, hk, zt, hzt, hht⟩ := hH3
  rw [hset_eq]
  exact ⟨zt, k, hk, hzt, hht⟩
