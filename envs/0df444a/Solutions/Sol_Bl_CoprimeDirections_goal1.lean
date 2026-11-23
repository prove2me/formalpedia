-- Prove2me | solution 1 for Bl.CoprimeDirections.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:04.402576+00:00
-- url     : https://prove2.me/submissions/e0089ce2-6eba-4098-bedd-ecb6327ab5d0

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1
namespace Bl.CoprimeDirections
private lemma cdir {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {v h : E} {s B : ℝ}
    (hh : h ≠ 0) (hs : 0 < s)
    (hd : ∀ w, ‖w - v‖ ≤ s → DifferentiableAt ℂ f w)
    (hB : ∀ w, ‖w - v‖ ≤ s → ‖f w‖ ≤ B) :
    ‖fderiv ℂ f v h‖ ≤ B / s * ‖h‖ := by
  have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  set R := s / ‖h‖ with hR
  have hRpos : 0 < R := div_pos hs hhn
  set g : ℂ → F := fun z => f (v + z • h) with hg
  have hmem : ∀ z : ℂ, ‖z‖ ≤ R → ‖(v + z • h) - v‖ ≤ s := by
    intro z hz
    rw [add_sub_cancel_left, norm_smul]
    calc ‖z‖ * ‖h‖ ≤ R * ‖h‖ := by gcongr
      _ = s := by rw [hR]; field_simp
  have hgd : ∀ z : ℂ, ‖z‖ ≤ R → DifferentiableAt ℂ g z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => v + z • h) z :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const h)
    exact (hd _ (hmem z hz)).comp z h1
  have hdc : DiffContOnCl ℂ g (Metric.ball (0:ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0:ℂ) hRpos.ne']
    intro z hz
    apply (hgd z _).differentiableWithinAt
    simpa using hz
  have hC : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖g z‖ ≤ B := by
    intro z hz
    apply hB
    apply hmem
    exact le_of_eq (by simpa using hz)
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc hC
  have hderiv : deriv g 0 = fderiv ℂ f v h := by
    have h1 : HasDerivAt (fun z : ℂ => v + z • h) h 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const h).const_add v
    have h2 : HasFDerivAt f (fderiv ℂ f v) (v + (0:ℂ) • h) := by
      simpa using (hd v (by simp [hs.le])).hasFDerivAt
    exact (h2.comp_hasDerivAt (0:ℂ) h1).deriv
  rw [← hderiv]
  calc ‖deriv g 0‖ ≤ B / R := hest
    _ = B / s * ‖h‖ := by rw [hR, div_div_eq_mul_div]; ring
private lemma cop {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {v : E} {s B : ℝ}
    (hs : 0 < s) (hB0 : 0 ≤ B)
    (hd : ∀ w, ‖w - v‖ ≤ s → DifferentiableAt ℂ f w)
    (hB : ∀ w, ‖w - v‖ ≤ s → ‖f w‖ ≤ B) :
    ‖fderiv ℂ f v‖ ≤ B / s := by
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hB0 hs.le) ?_
  intro h
  by_cases hh : h = 0
  · simp [hh]
  · exact cdir hh hs hd hB
private lemma key {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) {k : ℕ}
    (hO : Asymptotics.IsBigO (nhds x) f fun v => ‖v - x‖ ^ (k + 1 + 1)) :
    Asymptotics.IsBigO (nhds x) (fderiv ℂ f) fun v => ‖v - x‖ ^ (k + 1) := by
  obtain ⟨C, hCpos, hCb⟩ := hO.exists_pos
  have hev : ∀ᶠ w in nhds x, w ∈ U ∧ ‖f w‖ ≤ C * ‖‖w - x‖ ^ (k + 1 + 1)‖ :=
    (hU.eventually_mem hx).and hCb.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hfd0 : fderiv ℂ f x = 0 := (hO.hasFDerivAt (by omega)).fderiv
  refine Asymptotics.IsBigO.of_bound (C * 2 ^ (k + 1 + 1)) ?_
  have hnear : ∀ᶠ v in nhds x, dist v x < ε / 2 := Metric.ball_mem_nhds x (half_pos hε)
  filter_upwards [hnear] with v hv
  rw [Real.norm_eq_abs, abs_pow, abs_norm]
  by_cases hvx : v = x
  · subst hvx
    simp [hfd0]
  · have hρ : 0 < ‖v - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvx)
    have hρ' : ‖v - x‖ ≠ 0 := hρ.ne'
    rw [dist_eq_norm] at hv
    have hw : ∀ w, ‖w - v‖ ≤ ‖v - x‖ → dist w x < ε ∧ ‖w - x‖ ≤ 2 * ‖v - x‖ := by
      intro w hw
      have : ‖w - x‖ ≤ ‖w - v‖ + ‖v - x‖ := norm_sub_le_norm_sub_add_norm_sub w v x
      constructor
      · rw [dist_eq_norm]; linarith
      · linarith
    have hbd := cop (f := f) (v := v) (s := ‖v - x‖) (B := C * (2 * ‖v - x‖) ^ (k + 1 + 1)) hρ
      (by positivity)
      (fun w hw' => hf.differentiableAt (hU.mem_nhds (hball (hw w hw').1).1))
      (fun w hw' => by
        have h1 := (hball (hw w hw').1).2
        rw [Real.norm_eq_abs, abs_pow, abs_norm] at h1
        calc ‖f w‖ ≤ C * ‖w - x‖ ^ (k + 1 + 1) := h1
          _ ≤ C * (2 * ‖v - x‖) ^ (k + 1 + 1) := by
            gcongr
            exact (hw w hw').2)
    calc ‖fderiv ℂ f v‖ ≤ C * (2 * ‖v - x‖) ^ (k + 1 + 1) / ‖v - x‖ := hbd
      _ = C * 2 ^ (k + 1 + 1) * ‖v - x‖ ^ (k + 1) := by
        rw [mul_pow]; field_simp; ring
end Bl.CoprimeDirections
end

set_option autoImplicit false
universe u_1
open Bl Bl.CoprimeDirections
namespace Bl.CoprimeDirections
theorem _root_.solution :
  ∀ {n : Nat} {F : Type u_1} [inst : NormedAddCommGroup.{u_1} F] [inst_1 : NormedSpace.{0, u_1} Complex F]
  {f : ReciprocityTheory.L2DbarEstimates.V n → F} {U : Set.{0} (ReciprocityTheory.L2DbarEstimates.V n)} {x : ReciprocityTheory.L2DbarEstimates.V n},
  IsOpen.{0} U →
    Membership.mem.{0, 0} U x →
      DifferentiableOn.{0, 0, u_1} Complex f U →
        ∀ {m : Nat},
          (Asymptotics.IsBigO.{0, u_1, 0} (nhds.{0} x) f fun (v : ReciprocityTheory.L2DbarEstimates.V n) ↦
              HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} v x))
                (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} m 1) 1)) →
            Asymptotics.IsBigO.{0, u_1, 0} (nhds.{0} x) (fderiv.{0, 0, u_1} Complex f) fun (v : ReciprocityTheory.L2DbarEstimates.V n) ↦
              HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} v x)) (HAdd.hAdd.{0, 0, 0} m 1) := by
  intro n F _ _ f U x hU hx hf m hO
  exact key hU hx hf hO
end Bl.CoprimeDirections
