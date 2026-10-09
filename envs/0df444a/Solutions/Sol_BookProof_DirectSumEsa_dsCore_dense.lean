-- Prove2me | solution 1 for BookProof.DirectSumEsa.dsCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:52:45.065044+00:00
-- url     : https://prove2.me/submissions/1120579e-8196-4860-b3bb-de0a0ad15b9a

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.dsCore_dense
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (hD : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) :
    Dense ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2)) := by

  classical
  refine Metric.dense_iff.2 (fun f ε hε => ?_)
  have hsum : HasSum (fun i => lp.single 2 i ((f : ∀ i, G i) i)) f :=
    lp.hasSum_single (by simp) f
  have hev : ∀ᶠ s : Finset ι in Filter.atTop,
      (∑ i ∈ s, lp.single 2 i ((f : ∀ i, G i) i)) ∈ Metric.ball f (ε / 2) :=
    hsum (Metric.ball_mem_nhds f (by positivity))
  obtain ⟨s, hs⟩ := hev.exists
  have hδpos : 0 < ε / (2 * (s.card + 1)) := by positivity
  have hchoice : ∀ i : ι, ∃ d : G i, d ∈ D i ∧ ‖d - (f : ∀ i, G i) i‖ < ε / (2 * (s.card + 1)) := by
    intro i
    obtain ⟨d, hdball, hdmem⟩ := Metric.dense_iff.1 (hD i) ((f : ∀ i, G i) i) _ hδpos
    refine ⟨d, hdmem, ?_⟩
    rw [← dist_eq_norm]
    simpa [dist_comm] using hdball
  choose d hdmem hdclose using hchoice
  refine ⟨∑ i ∈ s, lp.single 2 i (d i), ?_, ?_⟩
  · have hgF : ‖(∑ i ∈ s, lp.single 2 i (d i))
        - ∑ i ∈ s, lp.single 2 i ((f : ∀ i, G i) i)‖ ≤ ∑ i ∈ s, ‖d i - (f : ∀ i, G i) i‖ := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [← lp.single_sub]
      exact le_of_eq (lp.norm_single (by norm_num) i _)
    have hcard : ∑ i ∈ s, ‖d i - (f : ∀ i, G i) i‖ ≤ s.card * (ε / (2 * (s.card + 1))) := by
      refine le_trans (Finset.sum_le_card_nsmul s _ (ε / (2 * (s.card + 1)))
        (fun i _ => (hdclose i).le)) ?_
      simp [nsmul_eq_mul]
    have hlt : (s.card : ℝ) * (ε / (2 * (s.card + 1))) < ε / 2 := by
      have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
      have hpos : (0 : ℝ) < 2 * ((s.card : ℝ) + 1) := by positivity
      rw [mul_div_assoc', div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hε, hc]
    have hball : dist (∑ i ∈ s, lp.single 2 i ((f : ∀ i, G i) i)) f < ε / 2 := hs
    have : dist (∑ i ∈ s, lp.single 2 i (d i)) f < ε := by
      calc dist (∑ i ∈ s, lp.single 2 i (d i)) f
          ≤ dist (∑ i ∈ s, lp.single 2 i (d i))
              (∑ i ∈ s, lp.single 2 i ((f : ∀ i, G i) i))
            + dist (∑ i ∈ s, lp.single 2 i ((f : ∀ i, G i) i)) f := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
            rw [dist_eq_norm]
            exact add_lt_add_of_le_of_lt (lt_of_le_of_lt (le_trans hgF hcard) hlt).le hball
        _ = ε := by ring
    simpa [Metric.mem_ball] using this
  · exact Submodule.sum_mem _ (fun i _ => single_mem_dsCore i ⟨d i, hdmem i⟩)
