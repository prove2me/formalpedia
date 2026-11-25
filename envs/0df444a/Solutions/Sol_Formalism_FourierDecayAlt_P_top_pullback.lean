-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:32.952315+00:00
-- url     : https://prove2.me/submissions/3e011272-6e75-43c1-8449-09b8398bb5e9

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_clauseF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_finClasses

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
theorem _root_.solution : TopPullback := by
  intro hP K _ _ _ R ψ hD E α _ σ u τ₀ η F Θ hΘ
  obtain ⟨p1, p2, p3, p4, p5, _, _⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro t t' ht ht' h hh h' hh' hne
    have htt : t = t' := by
      by_contra hn
      apply hne
      simp only [topSys, if_neg hn]
    show t⁻¹ - t'⁻¹ ∈ (⊥ : AddSubgroup E)
    rw [htt, sub_self]; exact AddSubgroup.zero_mem _
  ·
    intro t ht
    apply tb
    refine Jx9.psd_congr (Jx9.pull η F _ (p2 ((u : K) * σ t - τ₀))) ?_
    intro x _ y _
    simp only [topSys, if_true]
  ·
    intro t t' htt h _ h' _
    show Θ ((u : K) * σ t - τ₀) (η h) (η h') = Θ ((u : K) * σ t' - τ₀) (η h) (η h')
    have hr : (u : K) * σ (t - t') ∈ R := htt
    have e : (u : K) * σ t - τ₀ = ((u : K) * σ t' - τ₀) + (u : K) * σ (t - t') := by
      rw [map_sub]; ring
    rw [e, p1 _ _ hr]
  ·
    intro t
    exact tb _ (Jx9.pull η F _ (p2 _))
  ·
    intro t ht
    apply tb
    refine Jx9.psd_congr (Jx9.psd_zero F) ?_
    intro x _ y _
    simp only [topSys, if_true, sub_self]
  ·
    intro R0 hR0
    apply tb
    have hinj : Set.InjOn (fun t : E => (u : K) * σ t - τ₀) R0 := by
      intro t ht t' ht' e
      apply hR0 t ht t' ht'
      show (u : K) * σ (t - t') ∈ R
      have e' : (u : K) * σ t - τ₀ = (u : K) * σ t' - τ₀ := e
      have e'' : (u : K) * σ t = (u : K) * σ t' := sub_left_injective e'
      rw [map_sub, mul_sub, e'', sub_self]; exact R.zero_mem
    have h1 := Jx9.clauseF R (F.image η) Θ
      (fun h h' => ((A5.cSize R h ^ 1 * A5.cSize R h' ^ 1 : ℝ) : ℂ) * A5.N0 R ψ h h') p1 p2
      (Jx9.finClasses R hD.isOpen _ Θ p3) p5 (R0.image fun t : E => (u : K) * σ t - τ₀)
      (by
        intro y hy y' hy' hyy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        obtain ⟨t', ht', rfl⟩ := mem_image.1 hy'
        have : t = t' := by
          apply hR0 t ht t' ht'
          show (u : K) * σ (t - t') ∈ R
          have e : (u : K) * σ (t - t') = ((u : K) * σ t - τ₀) - ((u : K) * σ t' - τ₀) := by
            rw [map_sub]; ring
          rw [e]; exact hyy
        rw [this])
    have h2 := Jx9.pull η F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [topSys]
    rw [sum_image hinj]
end Formalism.FourierDecayAlt.P
