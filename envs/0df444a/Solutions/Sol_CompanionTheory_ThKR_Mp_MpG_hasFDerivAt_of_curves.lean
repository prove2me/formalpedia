-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpG.hasFDerivAt_of_curves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:12.559357+00:00
-- url     : https://prove2.me/submissions/65a66e67-737b-46ff-918e-b89afab69b14

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp CompanionTheory.ThKR.Mp.MpG
namespace CompanionTheory.ThKR.Mp.MpG
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (h : ∀ (c : ℝ → E) (v : E), c 0 = x₀ → HasDerivAt c v 0 → HasDerivAt (fun t => Φ (c t)) (L v) 0) :
    HasFDerivAt Φ L x₀ := by
  classical
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  by_contra hf
  obtain ⟨y0, hy0, hb0⟩ := exists_seq_forall_of_frequently (not_eventually.1 hf)
  have hne0 : ∀ n, y0 n ≠ 0 := fun n e => hb0 n (by simp [e])
  obtain ⟨v, -, φ, hφ, hv⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq (x := fun n => ‖y0 n‖⁻¹ • y0 n)
    (fun n => by simp [norm_smul, hne0 n])
  let y : ℕ → E := fun n => y0 (φ n)
  have hne : ∀ n, ‖y n‖ ≠ 0 := fun n => norm_ne_zero_iff.2 (hne0 _)
  let w : ℝ → E := fun t => if e : ∃ n, ‖y n‖ = t then y e.choose else t • v
  have w0 : w 0 = 0 := by
    have : ¬∃ n, ‖y n‖ = 0 := fun ⟨n, e⟩ => hne n e
    simp only [w, dif_neg this, zero_smul]
  have hw : HasDerivAt w v 0 := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hv δ hδ
    have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range N, t ≠ ‖y m‖ :=
      (Finset.eventually_all _).2 fun m _ => eventually_ne_nhds (hne m).symm
    filter_upwards [this] with t ht
    rw [w0, sub_zero, sub_zero]
    by_cases e : ∃ n, ‖y n‖ = t
    · have e1 := e.choose_spec
      have hm : N ≤ e.choose := not_lt.1 fun hlt => ht _ (Finset.mem_range.2 hlt) e1.symm
      have h1 := (hN _ hm).le
      rw [dist_eq_norm] at h1
      have h2 : w t - t • v = t • (‖y e.choose‖⁻¹ • y e.choose - v) := by
        rw [smul_sub, smul_smul, e1, mul_inv_cancel₀ (e1 ▸ hne _), one_smul]
        simp only [w, dif_pos e]
      rw [h2, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · simp only [w, dif_neg e, sub_self, norm_zero]
      positivity
  have h1 := (h (fun t => x₀ + w t) v (by simp [w0]) (hw.const_add x₀)).fun_sub (L.hasFDerivAt.comp_hasDerivAt 0 hw)
  rw [sub_self, hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h1
  have h2 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using (hy0.comp hφ.tendsto_atTop).norm
  obtain ⟨n, hn⟩ := (h2.eventually (h1 hε)).exists
  have e : ∃ m, ‖y m‖ = ‖y n‖ := ⟨n, rfl⟩
  have e2 : w ‖y n‖ = y e.choose := by simp only [w, dif_pos e]
  refine hb0 (φ e.choose) ?_
  simp only [Function.comp, w0, e2, add_zero, map_zero, sub_zero, smul_zero, norm_norm] at hn
  rw [sub_right_comm]
  exact hn.trans_eq (congrArg (ε * ·) e.choose_spec.symm)
end CompanionTheory.ThKR.Mp.MpG
