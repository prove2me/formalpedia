-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lemma_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:55.007079+00:00
-- url     : https://prove2.me/submissions/f42ad5d0-2d51-4186-b66d-8243b394b9d7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_block_height_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_algebraMap_unit_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_charpoly_theta_eq_prod
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_mul_eq_X_pow_smul_one
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_minorsDvd_frobenius_of_sum_bound
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_diagonal_entry_eq_unit_mul
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_theta_diagonal_entry_eq
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_alpha_bounds_hold
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minor_bound_extra_holds
import Theorems.Thm_Formalism_CohomologicalDescent_charpolyDiagBlocks_holds
import Theorems.Thm_Formalism_CohomologicalDescent_map_cast_le_of_map_neg_mul_le
import Theorems.Thm_Formalism_CohomologicalDescent_shiftBound_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : LemmaWFull := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  have hlp : l.Prime := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact shiftBound_holds ι σ l h (fun i => kap i s) (fun i => wt i s) hlp.two_le
      (fun i => hwt i s) (fun i => hα i s) i
  · intro i
    have hΘ : (thetaOf (W.Gam i)).BlockTriangular W.b := by
      intro a b hab
      change coeff 1 (W.Gam i a b) = 0
      rw [hΓ i hab, map_zero]
    have h1 := charpolyDiagBlocks_holds F n (thetaOf (W.Gam i)) W.b (Finset.univ.image W.pos)
      (fun j => -W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F)) hΘ
      (by
        intro s hs' j hj
        obtain ⟨s0, _, rfl⟩ := Finset.mem_image.mp hs'
        exact hpos s0 j hj) (charpoly_theta_eq_prod l h W u c U' hu hN i)
    rw [Finset.image_val_of_injOn hinj.injOn, Multiset.map_map] at h1
    apply map_cast_le_of_map_neg_mul_le l hlp F (W.red (algebraMap ℤ_[l] O c)) (reduction_algebraMap_unit_ne_zero l W.red c hc)
    have e : ((fun s => thetaOf (W.Gam i) s s) ∘ W.pos) =
        fun s : Fin t => -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
      funext s
      exact theta_diagonal_entry_eq l h W σ u c U' wt kap hl2 hW i s
    rw [e] at h1
    exact h1
  · intro ν hν i
    have hI : Function.Injective (fun s => W.b (W.pos s)) :=
      fun x y hxy => hinj (hpos y (W.pos x) hxy)
    generalize hch : Finset.univ.image (fun s => W.b (W.pos s)) = ch at *
    generalize hm : ∑ r ∈ Finset.univ.image W.b \ ch, ν r = m at *
    by_contra hcon
    push Not at hcon
    have hA0 : 0 ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h := by
      refine add_nonneg (Finset.sum_nonneg fun s _ => ?_) (by positivity)
      have := (hα i s).1; linarith
    generalize hA : ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h = A
      at *
    have hmin := minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i (t + m) (A.toNat + 1) (fun J hJ => by
      have := hcon J hJ
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega)
    let al : ℕ → ℕ := fun r => if hr : ∃ s, W.b (W.pos s) = r then
      ((l : ℤ) * kap (σ i) (Classical.choose hr) + wt i (Classical.choose hr) -
        kap i (Classical.choose hr)).toNat else 0
    have hal : ∀ s, al (W.b (W.pos s)) = ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      intro s
      have hr : ∃ s', W.b (W.pos s') = W.b (W.pos s) := ⟨s, rfl⟩
      simp only [al, dif_pos hr]
      rw [hI (Classical.choose_spec hr)]
    have hcard : ch.card = t := by
      rw [← hch, Finset.card_image_of_injective _ hI]; simp
    obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hN i
    have hbl := (block_height_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b X_ne_zero (hΦ i) hM).2
    have h1 := minor_bound_extra_holds (F⟦X⟧) X n h (A.toNat + 1) (W.Phi l σ i) W.b ch al ν X_prime
      (hΦ i)
      (by
        rw [← hch]
        intro r hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (by
        intro r hr
        rw [← hch] at hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        refine ⟨W.pos s, fun j => ⟨hpos s j, fun h0 => by rw [h0]⟩, ?_⟩
        rw [hal s]
        exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s).2)
      (fun r hr => ⟨⟨_, hbl r⟩, hν r hr⟩)
      (by rw [hcard, hm]; exact hmin)
    have hsum : ∑ r ∈ ch, al r = ∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      rw [← hch, Finset.sum_image (fun x _ y _ hxy => hI hxy)]
      exact Finset.sum_congr rfl fun s _ => hal s
    rw [hsum, hm] at h1
    have h2 : ((∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat : ℕ) : ℤ) =
        ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Int.toNat_of_nonneg (hα i s).1]; ring
    have h3 : ((A.toNat + 1 : ℕ) : ℤ) ≤ ((∑ s : Fin t,
        ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat + m * h : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 h2
    rw [h2, hA, Int.toNat_of_nonneg hA0] at h3
    omega
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
