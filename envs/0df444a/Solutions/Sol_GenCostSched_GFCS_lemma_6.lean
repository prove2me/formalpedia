-- Prove2me | solution 1 for GenCostSched.GFCS.lemma_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:31:38.075009+00:00
-- url     : https://prove2.me/submissions/4b8b2372-ce12-4749-abe2-fd02ed590067
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model
import Theorems.Thm_GenCostSched_GFCS_dual_attainment

open MeasureTheory Set
open scoped ENNReal

namespace GFCSLem6Aux
open GenCostSched.GFCS

/-- Offline weak duality for GFCS(s). -/
theorem offWD {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (hG : ∀ j ∈ A, ∀ t, s ≤ t → 0 ≤ G j t) (hρ : ∀ j ∈ A, 0 < ρ j)
    (a : Fin m → ℝ) (β : ℝ → ℝ) (hfeas : IsOffDualFeas G s A a β) :
    ENNReal.ofReal (offDualObj s A ρ a β) ≤ rnf G s A ρ := by
  obtain ⟨hβint, ha0, hβ0, hcon⟩ := hfeas
  have hBnn : 0 ≤ ∫ t in Ici s, β t := by
    apply setIntegral_nonneg_of_ae_restrict
    exact (ae_restrict_iff' measurableSet_Ici).2 (hβ0.mono fun t ht ht0 => ht (mem_Ici.1 ht0))
  have hBeq : ENNReal.ofReal (∫ t in Ici s, β t) = ∫⁻ t in Ici s, ENNReal.ofReal (β t) := by
    apply ofReal_integral_eq_lintegral_ofReal hβint
    exact (ae_restrict_iff' measurableSet_Ici).2 (hβ0.mono fun t ht ht0 => ht (mem_Ici.1 ht0))
  unfold rnf
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxm, hxnn, hx0, hxA, hxc, hxv⟩ := hx
  set F : Fin m → ℝ → ℝ≥0∞ := fun j t => ENNReal.ofReal (β t) * ENNReal.ofReal (x j t) with hF
  have hFm : ∀ j, AEMeasurable (F j) (volume.restrict (Ici s)) := fun j =>
    (hβint.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mul
      ((hxm j).ennreal_ofReal.aemeasurable)
  have hjob : ∀ j ∈ A, ENNReal.ofReal (a j * ρ j) ≤
      (∫⁻ t in Ici s, F j t) + ∫⁻ t, ENNReal.ofReal (G j t * x j t) := by
    intro j hj
    calc ENNReal.ofReal (a j * ρ j) = ENNReal.ofReal (a j) * ENNReal.ofReal (ρ j) :=
          ENNReal.ofReal_mul (ha0 j hj)
      _ ≤ ENNReal.ofReal (a j) * ∫⁻ t, ENNReal.ofReal (x j t) := by gcongr; exact hxv j hj
      _ = ∫⁻ t, ENNReal.ofReal (a j) * ENNReal.ofReal (x j t) := by
          rw [lintegral_const_mul _ (hxm j).ennreal_ofReal]
      _ ≤ ∫⁻ t, ((Ici s).indicator (F j) t + ENNReal.ofReal (G j t * x j t)) := by
          apply lintegral_mono_ae
          filter_upwards [hcon j hj, hβ0] with t h1 h2
          by_cases hts : s ≤ t
          · rw [indicator_of_mem (mem_Ici.2 hts)]
            have hb := h2 hts
            have hle := h1 hts
            rw [← ENNReal.ofReal_mul (ha0 j hj)]
            simp only [hF]
            rw [← ENNReal.ofReal_mul hb]
            calc ENNReal.ofReal (a j * x j t) ≤ ENNReal.ofReal (β t * x j t + G j t * x j t) := by
                  apply ENNReal.ofReal_le_ofReal
                  nlinarith [hxnn j t]
              _ ≤ _ := ENNReal.ofReal_add_le
          · rw [hx0 j t (lt_of_not_ge hts)]; simp
      _ = (∫⁻ t in Ici s, F j t) + ∫⁻ t, ENNReal.ofReal (G j t * x j t) := by
          rw [lintegral_add_left' ((aemeasurable_indicator_iff measurableSet_Ici).2 (hFm j)),
            lintegral_indicator measurableSet_Ici]
  have hsum : ENNReal.ofReal (∑ j ∈ A, a j * ρ j) ≤
      (∑ j ∈ A, ∫⁻ t in Ici s, F j t) + offCost G x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (ha0 j hj) (hρ j hj).le)]
    unfold offCost
    calc ∑ j ∈ A, ENNReal.ofReal (a j * ρ j)
        ≤ ∑ j ∈ A, ((∫⁻ t in Ici s, F j t) + ∫⁻ t, ENNReal.ofReal (G j t * x j t)) :=
          Finset.sum_le_sum hjob
      _ = (∑ j ∈ A, ∫⁻ t in Ici s, F j t) + ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (G j t * x j t) :=
          Finset.sum_add_distrib
      _ ≤ _ := by
          gcongr
          exact Finset.subset_univ A
  have hFsum : ∑ j ∈ A, ∫⁻ t in Ici s, F j t ≤ ENNReal.ofReal (∫ t in Ici s, β t) := by
    rw [← lintegral_finsetSum' _ (fun j _ => hFm j), hBeq]
    apply lintegral_mono
    intro t
    simp only [hF]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hxnn j t)]
    calc ENNReal.ofReal (β t) * ENNReal.ofReal (∑ j ∈ A, x j t)
        ≤ ENNReal.ofReal (β t) * ENNReal.ofReal 1 := by
          gcongr
          exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun j _ _ => hxnn j t)).trans (hxc t)
      _ = _ := by simp
  have key : ENNReal.ofReal (∑ j ∈ A, a j * ρ j) ≤
      ENNReal.ofReal (∫ t in Ici s, β t) + offCost G x :=
    hsum.trans (add_le_add hFsum le_rfl)
  unfold offDualObj
  rw [ENNReal.ofReal_sub _ hBnn]
  exact tsub_le_iff_left.2 key

end GFCSLem6Aux

open GenCostSched.GFCS in
theorem solution {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (k : Fin m) (hk : k ∉ A) (hA : ∀ j ∈ A, I.r j ≤ s)
    (hrk : I.r k = s) (hρ : ∀ j ∈ A, 0 < ρ j) (hρk : ρ k = I.v k)
    (a' : Fin m → ℝ) (β' : ℝ → ℝ) (hopt : IsOffOptDual I.g s (insert k A) ρ a' β') :
    rnf I.g s (insert k A) ρ ≤ rnf I.g s A ρ + ENNReal.ofReal (a' k * I.v k) := by
  have hA' : ∀ j ∈ insert k A, I.r j ≤ s := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hrk.le
    · exact hA j hj
  have hρ' : ∀ j ∈ insert k A, 0 < ρ j := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [hρk]; exact (hI j).1
    · exact hρ j hj
  obtain ⟨hfin, a0, β0, hmax, hobj⟩ := dual_attainment I hI s (insert k A) ρ hA' hρ'
  have hle : offDualObj s (insert k A) ρ a0 β0 ≤ offDualObj s (insert k A) ρ a' β' :=
    hopt.2 a0 β0 hmax.1.1
  -- restriction of (a', β') to A is feasible
  obtain ⟨hβint, ha0, hβ0, hcon⟩ := hopt.1
  have hfeasA : IsOffDualFeas I.g s A a' β' :=
    ⟨hβint, fun j hj => ha0 j (Finset.mem_insert_of_mem hj), hβ0,
      fun j hj => hcon j (Finset.mem_insert_of_mem hj)⟩
  have hG : ∀ j ∈ A, ∀ t, s ≤ t → 0 ≤ I.g j t := fun j hj t ht =>
    (hI j).2.2.1 t ((hA j hj).trans ht)
  have hwd := GFCSLem6Aux.offWD I.g s A ρ hG hρ a' β' hfeasA
  have hsplit : offDualObj s (insert k A) ρ a' β' =
      a' k * I.v k + offDualObj s A ρ a' β' := by
    unfold offDualObj
    rw [Finset.sum_insert hk, hρk]; ring
  calc rnf I.g s (insert k A) ρ = ENNReal.ofReal (rnf I.g s (insert k A) ρ).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (a' k * I.v k + offDualObj s A ρ a' β') := by
        apply ENNReal.ofReal_le_ofReal
        rw [← hobj, ← hsplit]; exact hle
    _ ≤ ENNReal.ofReal (a' k * I.v k) + ENNReal.ofReal (offDualObj s A ρ a' β') :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (a' k * I.v k) + rnf I.g s A ρ := by gcongr
    _ = rnf I.g s A ρ + ENNReal.ofReal (a' k * I.v k) := add_comm _ _
