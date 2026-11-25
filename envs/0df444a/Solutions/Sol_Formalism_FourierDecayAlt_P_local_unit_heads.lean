-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_unit_heads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:33.073221+00:00
-- url     : https://prove2.me/submissions/8b824d14-2c6f-4c10-a1a0-8db45cfaeb56

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : LocalUnitHeads := by
  intro hP hN0 K _ _ _ R ψ hD E α _ s m σ u η F Θ hm hG hΘ t ht
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  apply tb
  have hG' : ∀ h ∈ F.image η, A5.InGLR R h := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hx
    exact hG h hh
  have h7 := Jx9.pull η F _ (p7 hG' ((u : K) * σ t))
  have h4 := Jx9.pull η F _ (p4 (u * Units.map (σ : E →* K) (Units.mk0 t ht)))
  have hψ : ∀ r ∈ R, ψ r = 1 := by
    have := (hD.selfDual 1).2 R.one_mem
    intro r hr
    simpa using this r hr
  have hτ : ((u * Units.map (σ : E →* K) (Units.mk0 t ht) : Kˣ) : K) = (u : K) * σ t := by simp
  have hmem : (t ∈ (pullSys R ψ s σ u η Θ).L) ↔ (u : K) * σ t ∈ R := Iff.rfl
  refine Jx9.psd_congr (Jx9.psd_add h7 h4) ?_
  intro x hx y hy
  have h0 : A5.N0 R ψ (η x) (η y) = 1 :=
    hN0 K R ψ hψ _ _ (by rw [hm x hx, hm y hy]) (hG x hx) (hG y hy)
  simp only [hmem, h0, hτ]
  simp only [pullSys, dif_pos (And.intro ht ht)]
  ring
end Formalism.FourierDecayAlt.P
