-- Prove2me | solution 1 for CSeparatedNPComplete.exists_antitone_secant_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:50:53.734747+00:00
-- url     : https://prove2.me/submissions/fab085b0-497b-42ae-a684-33198646e900

module
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Order.Monotone.Extension
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_ConvexSlopes
public import Theorems.Thm_CSeparatedNPComplete_convex_secant_mono

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (u v : Fin n → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    ∃ c : Fin n → ℝ, Antitone c ∧
      ∀ i, f (u i) - f (v i) = c i * (u i - v i) := by
  let d : Fin n → ℝ := fun i => (f (u i) - f (v i)) / (u i - v i)
  let t : Set (Fin n) := {i | u i ≠ v i}
  have hd : AntitoneOn d t := by
    intro i hi j hj hij
    exact convex_secant_mono hf (hv_mem j) (hv_mem i) (hu_mem j) (hu_mem i)
      hj.symm hi.symm (hv hij) (hu hij)
  have hfinite : (d '' t).Finite := (Set.toFinite t).image d
  obtain ⟨c, hc, heq⟩ := hd.exists_antitone_extension hfinite.bddBelow hfinite.bddAbove
  refine ⟨c, hc, fun i => ?_⟩
  by_cases hi : u i = v i
  · simp [hi]
  · rw [← heq hi]
    exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hi)).symm
end CSeparatedNPComplete
