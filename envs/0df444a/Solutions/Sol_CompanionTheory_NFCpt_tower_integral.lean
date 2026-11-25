-- Prove2me | solution 1 for CompanionTheory.NFCpt.tower_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:05.80141+00:00
-- url     : https://prove2.me/submissions/1cdbefda-1c59-4a62-9231-86989a9f59f6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy
import Theorems.Thm_CompanionTheory_NFCpt_ae_coords_ne_zero
import Theorems.Thm_CompanionTheory_NFCpt_ae_ne_zero_c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology
namespace CompanionTheory.NFCpt
theorem _root_.solution : ∀ (n : ℕ) (E : (j : ℕ) → (Fin j → ℂ) → ℝ),
    AEStronglyMeasurable (E n) volume → (∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c) →
    (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ a, c a ≠ 0) →
      Integrable (fun t : ℂ => E (j + 1) (Fin.snoc c t)) ∧ ∫ t : ℂ, E (j + 1) (Fin.snoc c t) = E j c) →
    Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0)
  | 0, E, _, _, _ => by
    have e : E 0 = fun _ => E 0 (fun a => a.elim0) := funext fun c => congrArg _ (Subsingleton.elim _ _)
    refine ⟨by rw [e]; exact integrable_const _, ?_⟩
    rw [e, integral_const]
    simp [Measure.real, volume_pi]
  | n + 1, E, hm, h0, hs => by
    let e : (Fin (n + 1) → ℂ) ≃ᵐ (Fin n → ℂ) × ℂ :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last n)).trans MeasurableEquiv.prodComm
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n))
    have he : ∀ q : (Fin n → ℂ) × ℂ, e.symm q = Fin.snoc q.1 q.2 := by
      intro q
      apply e.injective
      rw [e.apply_symm_apply]
      simp [e, MeasurableEquiv.piFinSuccAbove]
      ext <;> rfl
    set G : (Fin n → ℂ) × ℂ → ℝ := fun q => E (n + 1) (Fin.snoc q.1 q.2) with hG
    have hGe : G = E (n + 1) ∘ e.symm := funext fun q => by simp [hG, he]
    have hGm : AEStronglyMeasurable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [hGe]
      exact hm.comp_measurePreserving (hmp.symm e)
    have hGpos : ∀ c : Fin n → ℂ, (∀ a, c a ≠ 0) → ∀ᵐ t : ℂ, 0 ≤ G (c, t) := by
      intro c hc
      filter_upwards [ae_ne_zero_c] with t ht
      refine h0 _ fun a => ?_
      induction a using Fin.lastCases with
      | last => simpa using ht
      | cast i => simpa using hc i
    have hae : (fun c : Fin n → ℂ => ∫ t, G (c, t)) =ᵐ[volume] E n := by
      filter_upwards [ae_coords_ne_zero n] with c hc
      exact (hs n (Nat.lt_succ_self n) c hc).2
    have hmn : AEStronglyMeasurable (E n) volume := hGm.integral_prod_right'.congr hae
    have h0n : ∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c := by
      intro c hc
      rw [← (hs n (Nat.lt_succ_self n) c hc).2]
      exact integral_nonneg_of_ae (hGpos c hc)
    obtain ⟨hI, hV⟩ := solution n E hmn h0n fun j hj => hs j (Nat.lt_succ_of_lt hj)
    have hGI : Integrable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hGm]
      refine ⟨?_, ?_⟩
      · filter_upwards [ae_coords_ne_zero n] with c hc
        exact (hs n (Nat.lt_succ_self n) c hc).1
      · refine hI.congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← (hs n (Nat.lt_succ_self n) c hc).2]
        refine integral_congr_ae ?_
        filter_upwards [hGpos c hc] with t ht
        exact (Real.norm_of_nonneg ht).symm
    refine ⟨?_, ?_⟩
    · have : E (n + 1) = G ∘ e := funext fun c => by simp [hGe]
      rw [this]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).2 hGI
    · have h1 : ∫ c, E (n + 1) c = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
        have := hmp.integral_comp' G
        rw [← show ∫ q, G q = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) from rfl, ← this]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp [hGe]
      rw [h1, integral_prod G hGI, integral_congr_ae hae, hV]
end CompanionTheory.NFCpt
