-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:29.144117+00:00
-- url     : https://prove2.me/submissions/96d14095-4b93-43aa-9df1-64b59bf04efe

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr
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
theorem _root_.solution : LocalPullback := by
  intro hP hA2 K _ _ _ R ψ hD E α _ s m σ u η F Θ hs hm hΘ
  obtain ⟨p1, p2, p3, p4, p5, _, _⟩ := hΘ
  have tb : ∀ (k : α → α → ℂ), A5.IsPSD F k → TB.PSDOn F k :=
    fun k h => ((hP α F k).1).2 (((hP α F k).2).1 h)
  have hτ : ∀ (t : E) (ht : t ≠ 0),
      ((u * Units.map (σ : E →* K) (Units.mk0 t ht) : Kˣ) : K) = (u : K) * σ t := by
    intro t ht; simp
  have hτi : ∀ (t : E) (ht : t ≠ 0),
      (((u * Units.map (σ : E →* K) (Units.mk0 t ht))⁻¹ : Kˣ) : K) = ((u⁻¹ : Kˣ) : K) * σ t⁻¹ := by
    intro t ht
    rw [mul_inv, Units.val_mul, ← map_inv]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro t t' ht ht' h hh h' hh' hne
    simp only [pullSys, dif_pos (And.intro ht ht')] at hne
    have := hA2.2 K R ψ hD s hs (η h) (η h') _ _ (by rw [hm h hh, hm h' hh']) hne
    rw [hτi, hτi] at this
    show t⁻¹ - t'⁻¹ ∈ R.toAddSubgroup.comap
      ((AddMonoidHom.mulLeft ((u⁻¹ : Kˣ) : K)).comp σ.toAddMonoidHom)
    rw [AddSubgroup.mem_comap]
    simpa [mul_sub] using this
  ·
    intro t ht
    apply tb
    have h1 := hA2.1 K R ψ hD s hs m
      (F.image fun h => (η h, u * Units.map (σ : E →* K) (Units.mk0 t ht)))
      (by
        intro x hx
        obtain ⟨h, hh, rfl⟩ := mem_image.1 hx
        exact hm h hh)
    have h2 := Jx9.pull (fun h => (η h, u * Units.map (σ : E →* K) (Units.mk0 t ht))) F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys, dif_pos (And.intro ht ht)]
  ·
    intro t t' htt h _ h' _
    show Θ ((u : K) * σ t) (η h) (η h') = Θ ((u : K) * σ t') (η h) (η h')
    have hr : (u : K) * σ (t - t') ∈ R := htt
    have e : (u : K) * σ t = (u : K) * σ t' + (u : K) * σ (t - t') := by rw [map_sub]; ring
    rw [e, p1 _ _ hr]
  ·
    intro t
    exact tb _ (Jx9.pull η F _ (p2 _))
  ·
    intro t ht
    apply tb
    have h2 := Jx9.pull η F _ (p4 (u * Units.map (σ : E →* K) (Units.mk0 t ht)))
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys, dif_pos (And.intro ht ht), hτ]
  ·
    intro R0 hR0
    apply tb
    have hinj : Set.InjOn (fun t : E => (u : K) * σ t) R0 := by
      intro t ht t' ht' e
      apply hR0 t ht t' ht'
      show (u : K) * σ (t - t') ∈ R
      have e' : (u : K) * σ t = (u : K) * σ t' := e
      rw [map_sub, mul_sub, e', sub_self]; exact R.zero_mem
    have h1 := Jx9.clauseF R (F.image η) Θ
      (fun h h' => ((A5.cSize R h ^ s * A5.cSize R h' ^ s : ℝ) : ℂ) * A5.N0 R ψ h h') p1 p2
      (Jx9.finClasses R hD.isOpen _ Θ p3) p5 (R0.image fun t : E => (u : K) * σ t)
      (by
        intro y hy y' hy' hyy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        obtain ⟨t', ht', rfl⟩ := mem_image.1 hy'
        have : t = t' := by
          apply hR0 t ht t' ht'
          show (u : K) * σ (t - t') ∈ R
          rw [map_sub, mul_sub]; exact hyy
        rw [this])
    have h2 := Jx9.pull η F _ h1
    refine Jx9.psd_congr h2 ?_
    intro x _ y _
    simp only [pullSys]
    rw [sum_image hinj]
end Formalism.FourierDecayAlt.P
