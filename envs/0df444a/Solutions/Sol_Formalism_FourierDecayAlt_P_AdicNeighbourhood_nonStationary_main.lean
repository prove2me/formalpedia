-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.nonStationary_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:00.213319+00:00
-- url     : https://prove2.me/submissions/0a6fa7e2-ef5d-476b-ad3e-ea3bb696c924

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_crit
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_taylor
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_avg_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_finite_quot
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_compact_mulR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K]
open Classical
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution : NonStationary := by
  intro K _ _ _ R ψ hD hn m _ L₀ Λ₁ B Q hL₀ hΛ₁ hB hQ _
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨a, ha⟩ := h.bounded hL₀.2
  obtain ⟨d, hd⟩ := h.bounded hQ
  obtain ⟨j, hj⟩ := h.crit hn m a B (hB.1.mem_nhds B.zero_mem)
  obtain ⟨b, hb⟩ := h.basis ((B : Set K) ∩ (Λ₁ : Set K))
    (Filter.inter_mem (hB.1.mem_nhds B.zero_mem) (hΛ₁.1.mem_nhds Λ₁.zero_mem))
  have hψR : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hD.selfDual 1).2 R.one_mem r hr
  refine ⟨I R ((ϖ ^ (2 * (a + j) + (1 + b + d + a * m)) : Kˣ) : K), I_nhds h.isOpen _, ?_⟩
  intro t D' A ht hD'Q hA Λ hΛ hInv
  obtain ⟨τ, hτ, et⟩ := ht
  rw [Units.val_pow_eq_pow_val] at et
  obtain ⟨κ, hκ⟩ : ∃ κ : K, κ = (ϖ : K) ^ (1 + b + d + a * m) * τ := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = (ϖ : K) ^ (a + j) * κ := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : K, ν = (ϖ : K) ^ a * μ := ⟨_, rfl⟩
  obtain ⟨ti, hti⟩ : ∃ ti : K, ti = ((t⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨ϖi, hϖi⟩ : ∃ p : K, p = ((ϖ⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have htt : (t : K) * ti = 1 := by rw [hti]; simp
  have hϖϖ : (ϖ : K) ^ j * ϖi ^ j = 1 := by rw [hϖi, ← mul_pow]; simp
  have etν : (t : K) = (ϖ : K) ^ j * ν := by rw [et, hν, hμ, hκ]; ring
  have hμ2 : μ ^ 2 = κ * (t : K) := by rw [etν, hν, hμ]; ring
  have hμI : μ ∈ I R (ϖ : K) :=
    ⟨(ϖ : K) ^ (a + j + b + d + a * m) * τ, R.mul_mem (R.pow_mem h.mem _) hτ, by
      rw [hμ, hκ]; ring⟩
  have hNB : ∀ v ∈ mulR R ν, v ∈ B ∧ v ∈ Λ₁ := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hv
    have e : ν * r = (ϖ : K) ^ b * ((ϖ : K) ^ (a + a + j + 1 + d + a * m) * τ * r) := by
      rw [hν, hμ, hκ]; ring
    rw [e]
    exact hb _ (R.mul_mem (R.mul_mem (R.pow_mem h.mem _) hτ) hr)
  have := finite_quot (mulR R ν) Λ (compact_mulR h.isCompact ν) hΛ.1
  unfold intK
  rw [← hti] at hInv ⊢
  rw [avg_zero Λ (mulR R ν) _ hInv ?_, mul_zero]
  intro x
  have hE : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) →
      ((∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B) ↔
        ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B) := by
    intro v hv
    constructor
    · rintro ⟨z, hz, hk⟩
      refine ⟨z, hz, fun k => ?_⟩
      have e : x k - (z : K) = ((x + v) k - (z : K)) - v k := by simp only [Pi.add_apply]; ring
      rw [e]; exact B.sub_mem (hk k) (hNB _ (hv k)).1
    · rintro ⟨z, hz, hk⟩
      refine ⟨z, hz, fun k => ?_⟩
      have e : (x + v) k - (z : K) = (x k - (z : K)) + v k := by simp only [Pi.add_apply]; ring
      rw [e]; exact B.add_mem (hk k) (hNB _ (hv k)).1
  have hAv : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) → A (x + v) = A x :=
    fun v hv => hA.2 x v fun i => (hNB _ (hv i)).2
  by_cases hEx : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B
  · left
    intro v hv
    exact if_pos ((hE v hv).2 hEx)
  by_cases hAx : A x = 0
  · left
    intro v hv
    show (if _ then _ else _) = _
    rw [hAv v hv, hAx, zero_mul, ite_self]
  right
  have hsup := hA.1 x hAx
  obtain ⟨xi, hxi⟩ : ∃ xi : Fin m → K, xi = fun k => Ring.inverse (x k) := ⟨_, rfl⟩
  have hxxi : ∀ k, x k * xi k = 1 := fun k => by
    rw [hxi]; exact Ring.mul_inverse_cancel _ (hsup k).2.1
  have hxiR : ∀ k, (ϖ : K) ^ a * xi k ∈ R := fun k => by
    rw [hxi]; exact ha _ (hsup k).2.2
  obtain ⟨G, hG⟩ : ∃ G : Fin m → K, G = fun k => 1 - (D' : K) * (xi k * ∏ i, xi i) := ⟨_, rfl⟩
  have hnot : ¬ ∀ k, 1 - (D' : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j) :=
    fun hall => hEx (hj D' x xi hxxi (fun k => ha _ (hsup k).1) hall)
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  have hk2 : ¬ (G k * ϖi ^ j ∈ R) := by
    intro hc
    apply hk
    refine ⟨_, hc, ?_⟩
    rw [hG]
    linear_combination (-(1 - (D' : K) * (xi k * ∏ i, xi i))) * hϖϖ
  rw [← hD.selfDual] at hk2
  push Not at hk2
  obtain ⟨r, hr, hrψ⟩ := hk2
  have formula : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) →
      (if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B then (0 : ℂ)
        else A (x + v) * ψ (g0 (D' : K) (x + v) * ti)) =
      A x * ψ (g0 (D' : K) x * ti) * ψ ((∑ i, v i * G i) * ti) := by
    intro v hv
    rw [if_neg (fun hc => hEx ((hE v hv).1 hc)), hAv v hv]
    obtain ⟨ρ, hρ, e⟩ := h.taylor m a (D' : K) x xi v μ hμI hxxi hxiR (fun i => by
      obtain ⟨r, hr, e⟩ := mem_mulR.1 (hv i)
      exact ⟨r, hr, by rw [e, hν]⟩)
    have hP : ∏ i, ((ϖ : K) ^ a * xi i) ∈ R := R.prod_mem fun i _ => hxiR i
    have eP : ∏ i, ((ϖ : K) ^ a * xi i) = (ϖ : K) ^ (a * m) * ∏ i, xi i := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    have hZ : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti ∈ R := by
      have e3 : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti =
          ((ϖ : K) ^ d * (D' : K)) * (∏ i, ((ϖ : K) ^ a * xi i)) * ((ϖ : K) ^ (1 + b) * τ) * ρ := by
        rw [eP, hμ2, hκ]
        linear_combination ((D' : K) * (∏ i, xi i) * ((ϖ : K) ^ (1 + b + d + a * m) * τ) * ρ) * htt
      rw [e3]
      exact R.mul_mem (R.mul_mem (R.mul_mem (hd _ hD'Q) hP) (R.mul_mem (R.pow_mem h.mem _) hτ)) hρ
    have e4 : g0 (D' : K) (x + v) * ti = g0 (D' : K) x * ti + (∑ i, v i * G i) * ti +
        (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti := by
      rw [e, hG]; ring
    rw [e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψR _ hZ, mul_one, mul_assoc]
  refine ⟨k, ν * r, mem_mulR.2 ⟨r, hr, rfl⟩, ψ (G k * ϖi ^ j * r), hrψ, fun v hv => ?_⟩
  have hv' : ∀ i, (v + Pi.single k (ν * r) : Fin m → K) i ∈ mulR R ν := by
    intro i
    refine (mulR R ν).add_mem (hv i) ?_
    by_cases hik : i = k
    · subst hik; simpa using mem_mulR.2 ⟨r, hr, rfl⟩
    · simp [hik]
  have f1 := formula _ hv'
  have f2 := formula v hv
  rw [← add_assoc] at f1
  refine f1.trans ?_
  show _ = _ * (if _ then _ else _)
  rw [f2]
  have e5 : (∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i) * ti =
      (∑ i, v i * G i) * ti + G k * ϖi ^ j * r := by
    have e6 : ∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i = ∑ i, v i * G i + ν * r * G k := by
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul]
    have e7 : ν * ti = ϖi ^ j := by
      rw [etν] at htt
      linear_combination (ϖi ^ j) * htt - (ν * ti) * hϖϖ
    rw [e6]
    linear_combination (r * G k) * e7
  rw [e5, AddChar.map_add_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
