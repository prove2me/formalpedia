-- Prove2me | solution 1 for Formalism.CohomologicalDescent.twisted_block_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:00:19.345911+00:00
-- url     : https://prove2.me/submissions/9cb60eb4-bc46-44aa-a144-ef2a4e8b8291

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Theorems.Thm_Formalism_CohomologicalDescent_le_sum_of_dvd_det_submatrix
import Theorems.Thm_Formalism_CohomologicalDescent_map_cast_le_of_map_neg_mul_le
import Theorems.Thm_Formalism_CohomologicalDescent_lw_det_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
private lemma sub_one_mul_abs_kap_le {ι : Type} [Fintype ι] (σ : Equiv.Perm ι) (l h : ℕ) (hl : 2 ≤ l)
    (w kap : ι → ℤ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (h : ℤ))
    (hd : ∀ i, 0 ≤ (l : ℤ) * kap (σ i) + w i - kap i ∧ (l : ℤ) * kap (σ i) + w i - kap i ≤ (h : ℤ))
    (i : ι) : ((l : ℤ) - 1) * |kap i| ≤ (h : ℤ) := by
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => |kap i|)
  have hσ : σ (σ.symm i₀) = i₀ := σ.apply_symm_apply i₀
  have h1 := hd (σ.symm i₀)
  rw [hσ] at h1
  have h2 := hw (σ.symm i₀)
  have hm : |kap (σ.symm i₀)| ≤ |kap i₀| := hi₀ (σ.symm i₀)
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast hl
  have hl' : (0 : ℤ) ≤ (l : ℤ) - 1 := by linarith
  have key : (l : ℤ) * |kap i₀| ≤ |kap (σ.symm i₀)| + h := by
    rcases abs_cases (kap i₀) with ⟨e0, _⟩ | ⟨e0, _⟩ <;>
      rcases abs_cases (kap (σ.symm i₀)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rw [e0, e1] <;> nlinarith
  have h3 : ((l : ℤ) - 1) * |kap i₀| ≤ h := by nlinarith
  calc ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap i₀| := mul_le_mul_of_nonneg_left (hi₀ i) hl'
    _ ≤ h := h3
end Formalism.CohomologicalDescent
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution : LemmaWAssembled := by
  intro ι _ σ l h t n F _ _ W U' bot kap c hl hW hb hd
  obtain ⟨ha, hinj, hpos, hΘ, hchar, hdiag, hΦ, hΦd, hc⟩ := hW
  have hbp : Function.Injective (W.b ∘ W.pos) := fun s s' hs => hinj (hpos s' (W.pos s) hs)
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact sub_one_mul_abs_kap_le σ l h hl.two_le (fun i => bot i + ((s : ℕ) : ℤ)) (fun i => kap i s)
      (fun i => hb i s) (fun i => hd i s) i
  · intro i
    have hdvd : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) ∣
        (W.Θ i).charpoly := by
      show _ ∣ (Matrix.charmatrix (W.Θ i)).det
      rw [(hΘ i).charmatrix.det]
      have e : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) =
          ∏ k ∈ Finset.univ.image (W.b ∘ W.pos),
            ((Matrix.charmatrix (W.Θ i)).toSquareBlock W.b k).det := by
        rw [Finset.prod_image (fun s _ s' _ hs => hbp hs)]
        refine Finset.prod_congr rfl fun s _ => ?_
        simp only [Function.comp_apply]
        rw [lw_det_block _ W.b (W.pos s) (hpos s), Matrix.charmatrix_apply_eq]
      rw [e]
      apply Finset.prod_dvd_prod_of_subset
      intro k hk
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
      obtain ⟨s, rfl⟩ := hk
      exact ⟨W.pos s, rfl⟩
    have hne : (W.Θ i).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hr := Polynomial.roots.le_of_dvd hne hdvd
    rw [hchar i] at hr
    have r1 : (∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))).roots =
        Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun s => Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    have r2 : (∏ u, (Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))).roots =
        Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun u => Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    rw [r1, r2] at hr
    have e2 : Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val =
        Multiset.map (fun s : Fin t => -W.a * (((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ)) : F))
          Finset.univ.val := Multiset.map_congr rfl (fun s _ => hdiag i s)
    rw [e2] at hr
    exact map_cast_le_of_map_neg_mul_le l hl F W.a ha Finset.univ.val Finset.univ.val
      (fun s : Fin t => bot i + ((s : ℕ) : ℤ) - kap i s) (U' i) hr
  · intro i
    have hm := le_sum_of_dvd_det_submatrix (PowerSeries.X : PowerSeries F) PowerSeries.X_prime (W.Φ i) W.b W.pos hinj
      hpos (hΦ i) (fun s => ((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat)
      (hΦd i) (c i) (hc i)
    have hm' : ((c i : ℕ) : ℤ) ≤ ∑ s : Fin t,
        ((((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat : ℕ) : ℤ) := by
      exact_mod_cast hm
    calc (c i : ℤ) ≤ _ := hm'
      _ = ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Int.toNat_of_nonneg (hd i s).1]
        ring
end Formalism.CohomologicalDescent
