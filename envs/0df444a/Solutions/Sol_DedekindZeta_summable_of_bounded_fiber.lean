-- Prove2me | solution 1 for DedekindZeta.summable_of_bounded_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:22.435566+00:00
-- url     : https://prove2.me/submissions/55b4bae6-39ed-4a44-98a4-e2505ba8fec4

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution {ι : Type*} {κ : Type*}
    {f : ι → ℝ} {h : κ → ℝ} {ψ : ι → κ} {c : ℝ} {N : ℕ}
    (hf : ∀ i, f i = c * h (ψ i)) (hc : 0 ≤ c) (hh : Summable h)
    (hhnn : ∀ k, 0 ≤ h k) (hfin : ∀ k, Finite {i // ψ i = k})
    (hcard : ∀ k, Nat.card {i // ψ i = k} ≤ N) :
    Summable f := by
  have hfnn : ∀ i, 0 ≤ f i := fun i => by
    rw [hf i]; exact mul_nonneg hc (hhnn _)
  set f' : ι → ℝ≥0 := fun i => (f i).toNNReal with hf'
  have hcoe : ∀ i, (f' i : ℝ) = f i := fun i => Real.coe_toNNReal _ (hfnn i)
  have hofReal : ∀ i, ENNReal.ofReal (f i) = (f' i : ℝ≥0∞) := fun i => by
    rw [hf', ENNReal.ofReal]
  have htsum_h : (∑' k, ENNReal.ofReal (h k)) = ENNReal.ofReal (∑' k, h k) :=
    (ENNReal.ofReal_tsum_of_nonneg hhnn hh).symm
  -- Per-fibre bound: a constant summed over a fibre of card `≤ N`.
  have step3b : ∀ k, (∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (h k) := by
    intro k
    have hconst : ∀ (i : {i // ψ i = k}),
        ENNReal.ofReal (h (ψ i.1)) = ENNReal.ofReal (h k) := by
      rintro ⟨i, rfl⟩; rfl
    rw [tsum_congr hconst]
    haveI : Finite {i // ψ i = k} := hfin k
    rw [ENNReal.tsum_const]
    gcongr
    calc (ENat.card {i // ψ i = k} : ℝ≥0∞)
        = ((Nat.card {i // ψ i = k} : ℕ∞) : ℝ≥0∞) := by rw [ENat.card_eq_coe_natCard]
      _ ≤ ((N : ℕ∞) : ℝ≥0∞) := by rw [ENat.toENNReal_le]; exact_mod_cast hcard k
      _ = (N : ℝ≥0∞) := by rw [ENat.toENNReal_coe]
  have key : (∑' i, ENNReal.ofReal (f i)) ≠ ∞ := by
    have step2 : (∑' i, ENNReal.ofReal (f i))
        = ENNReal.ofReal c * ∑' i, ENNReal.ofReal (h (ψ i)) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun i => by rw [hf i, ENNReal.ofReal_mul hc])
    have e1 : (∑' i, ENNReal.ofReal (h (ψ i)))
        = ∑' (p : Σ k, {i // ψ i = k}), ENNReal.ofReal (h (ψ p.2.1)) :=
      ((Equiv.sigmaFiberEquiv ψ).tsum_eq
        (fun i => ENNReal.ofReal (h (ψ i)))).symm
    have step3 : (∑' i, ENNReal.ofReal (h (ψ i)))
        = ∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)) := by
      rw [e1, ENNReal.tsum_sigma']
    have hbound : (∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
        ≤ (N : ℝ≥0∞) * ENNReal.ofReal (∑' k, h k) := by
      calc (∑' k, ∑' (i : {i // ψ i = k}), ENNReal.ofReal (h (ψ i.1)))
          ≤ ∑' k, (N : ℝ≥0∞) * ENNReal.ofReal (h k) := ENNReal.tsum_le_tsum step3b
        _ = (N : ℝ≥0∞) * ∑' k, ENNReal.ofReal (h k) := ENNReal.tsum_mul_left
        _ = (N : ℝ≥0∞) * ENNReal.ofReal (∑' k, h k) := by rw [htsum_h]
    rw [step2, step3]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ne_top_of_le_ne_top ?_ hbound
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top
  have hsummable' : Summable f' := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simp_rw [← hofReal]; exact key
  exact (NNReal.summable_coe.mpr hsummable').congr hcoe
end DedekindZeta
