-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCRef_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:26.624121+00:00
-- url     : https://prove2.me/submissions/1a777355-13cc-4181-bb42-bb34e947d120

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
private theorem contDiffOn_modA_ann (P : M.Par) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTCRefOfCut := by
  intro hReal hCurvId hCurvTr hTrace hAn Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨e0, he0, hk0, A0, B0, hAB, hC, hn⟩ := hTrace Wp Wq P Bs X d hH
  have hB : ∀ ρ, ∀ ζ ∈ Ann P, B0 ρ ζ = star (A0 ρ ζ) := hReal Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC
  refine ⟨e0, he0, hk0, A0, B0, hAB, hC,
    hCurvTr Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC hB (hCurvId Wp Wq P Bs X d hH), ?_⟩
  intro ρ R hR hR2
  obtain ⟨n, hn'⟩ := hn ρ
  refine ⟨n, ?_⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := contDiffOn_modA_ann P ρ
  have key := hAn (max P.TT 0) (fun w => modA P ρ w - A0 ρ w) ((n : ℝ) / 2) (le_max_right _ _)
    ((hsm.sub (hAB ρ).1).mono (fun ζ hζ => show P.TT < Complex.normSq ζ from
      lt_of_le_of_lt (le_max_left _ _) (show max P.TT 0 < Complex.normSq ζ from hζ)))
    (fun ζ hζ => hn' ζ (show P.TT < Complex.normSq ζ from lt_of_le_of_lt (le_max_left _ _) hζ)) R hR (max_lt hR2 (pow_pos hR 2))
  rw [key]; ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
