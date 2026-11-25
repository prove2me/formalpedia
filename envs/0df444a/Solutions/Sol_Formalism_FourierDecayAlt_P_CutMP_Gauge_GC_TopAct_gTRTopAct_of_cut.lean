-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct.gTRTopAct_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:59.279876+00:00
-- url     : https://prove2.me/submissions/8d929d36-6ea9-41fe-9200-f96d0f513ab9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_interp
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_vdm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_pt_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_mdim_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
theorem _root_.solution (hQ : QTop) : GTRTopAct := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk X
  obtain ⟨W, hW⟩ := vdm_inv (P.k + 2)

  have hpt : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
      ∃ a : ℕ → (Wq →L[ℂ] Wp), (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) ∧
        a P.k = ∑ b : Fin (mdim P.k P.r (Fin.last P.r)),
          EH P.k P.r (posL P.k P.r (Fin.last P.r) b) (posL P.k P.r (Fin.last P.r) b)
            ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 := by
    intro Φ x hx
    have hmem := Φ.2
    obtain ⟨_, hs, _⟩ := hmem
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x hx
    set D : Set (Mx P.k P.r) := {g | (x.1, g) ∈ U} with hDdef
    have hc : ContDiff ℝ ∞ (fun g : Mx P.k P.r => (x.1, g)) := contDiff_prodMk_right x.1
    have hD : IsOpen D := hU.preimage hc.continuous
    have hf : SmoothLev P.k P.r (Fin.last P.r) D ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) := by
      intro g₀ hg₀
      refine ⟨D, fun g => F (x.1, g), hD, hg₀.2, ?_, fun g hgD hgG => hΦ (x.1, g) hgD hgG⟩
      exact hF.comp hc.contDiffOn (fun g hg => hg)
    have hg : x.2 ∈ Glev P.k P.r (Fin.last P.r) ∩ D := ⟨hx.2.1, by simpa [hDdef] using hxU⟩
    obtain ⟨a, ha, htop⟩ := pt_poly hQ D hD _ hf hg
    have hm : mdim P.k P.r (Fin.last P.r) + 1 = P.k + 2 := by rw [mdim_last]
    have hm1 : mdim P.k P.r (Fin.last P.r) - 1 = P.k := by rw [mdim_last]; rfl
    refine ⟨a, fun Y => ?_, ?_⟩
    · rw [X.t_apply Y 0 0 Φ x hx, ← hm]
      exact ha Y
    · rw [← htop, hm1]

  let c : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun j =>
    if h : j < P.k + 2 then ∑ i : Fin (P.k + 2), W ⟨j, h⟩ i • X.t ((i : ℕ) : ℂ) 0 0 else 0
  have hval : ∀ (T : Module.End ℂ (RadSp P.k P.r z z' π π')) (Φ : RadSp P.k P.r z z' π π') x,
      x ∉ DomR P.k P.r z z' → ((T Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
    intro T Φ x hx
    have hmem := (T Φ).2
    obtain ⟨h0, _, _⟩ := hmem
    exact h0 x hx
  have hc : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z', ∀ (a : ℕ → (Wq →L[ℂ] Wp)),
      (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) →
      ∀ j ∈ Finset.range (P.k + 2), ((c j Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = a j := by
    intro Φ x hx a ha j hj
    have hj' : j < P.k + 2 := Finset.mem_range.1 hj
    have e1 : c j = ∑ i : Fin (P.k + 2), W ⟨j, hj'⟩ i • X.t ((i : ℕ) : ℂ) 0 0 := dif_pos hj'
    rw [e1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    exact interp (P.k + 2) W hW (fun Y => ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      a ha ⟨j, hj'⟩
  refine ⟨c, fun Y => ?_, 0, fun Φ x hx => ?_⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext c0 g
    by_cases hx : (c0, g) ∈ DomR P.k P.r z z'
    · obtain ⟨a, ha, -⟩ := hpt Φ (c0, g) hx
      have hL := ha Y
      simp only at hL
      rw [hL, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
      congr 1
      exact (hc Φ (c0, g) hx a ha j hj).symm
    · have h1 := hval (X.t Y 0 0) Φ (c0, g) hx
      have h2 := hval (∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) Φ (c0, g) hx
      simp only at h1 h2
      rw [h1, h2]
  · obtain ⟨a, ha, htop⟩ := hpt Φ x hx
    rw [hc Φ x hx a ha P.k (Finset.mem_range.2 (by omega)), htop]
    simp
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
