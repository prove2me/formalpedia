-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.second_shift_slice_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:48:29.759168+00:00
-- url     : https://prove2.me/submissions/2c9f0e03-8fa8-48c5-90be-f74918ff0acd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLocalCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLSliceDZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTSSLSliceDZ := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl T hT Φ Φ' c c' hc hc' hEq ζ hζ
  obtain ⟨n, A, -, hTA⟩ := hT
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hU : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ⟩
  have hq' : ((c', ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ⟩
  have hev : (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ')) =ᶠ[nhds ζ]
      (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ')) := by
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    have m : ((c, ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ'⟩
    have m' : ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ'⟩
    unfold NF.radR
    rw [Set.indicator_of_mem m, Set.indicator_of_mem m']
    exact hEq ζ' hζ'
  have e1 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) =
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq]
  have e2 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq']
  have h1 := hTA Φ (c, ζ) hq
  have h2 := hTA Φ' (c', ζ) hq'
  dsimp only at h1 h2
  rw [← e1, ← e2, h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
