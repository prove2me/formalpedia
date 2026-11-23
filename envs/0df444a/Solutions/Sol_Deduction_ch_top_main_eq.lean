-- Prove2me | solution 1 for Deduction.ch_top_main_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:17.98326+00:00
-- url     : https://prove2.me/submissions/793c7fef-e9aa-48af-8f69-c0567c3d879d

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
namespace Deduction
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (hId : IdentU Dd tr D N ell TT a w eT eP) (u0 : U0) :
    Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w (tr u0) j)).re := by
  obtain ⟨ha, hw, hg, hL, -⟩ := hId
  have hf : (f : ℝ) = (#(PhiSet (H := H)) : ℝ) := by
    have := Fintype.card_congr eP
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    exact_mod_cast this
  have hsum : ∀ g : E0 × H → ℝ, ∑ ρ : Fin f, g (eP ρ) = ∑ x ∈ PhiSet, g x := by
    intro g
    rw [← Finset.sum_coe_sort PhiSet]
    exact Equiv.sum_comp eP (fun x => g x)
  unfold Data.Main
  simp only [ha, hw, hg, hL, hsum, hf]
  rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort TT]
  rw [← Equiv.sum_comp eT]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  simp [MAIN, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  left
  left
  exact hsum (fun x => Real.log (w (tr u0) j x))
end Deduction
