-- Prove2me | solution 1 for DiazModulus.isPrime_iInf_ker_eval_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:08:45.622974+00:00
-- url     : https://prove2.me/submissions/3666c5e8-6652-4223-aad2-b5e0456b57ba

import Mathlib

open Complex ComplexConjugate

/-! # The vanishing ideal of an analytic image is prime

For an analytic map `F : E → ℂ^σ` on a normed `ℂ`-space `E`, every polynomial `f` gives an analytic function
`e ↦ f(F e)` on `E` (`AnalyticOnNhd.aeval_mvPolynomial`). The ideal `⨅_e ker(eval (F e))` of polynomials vanishing
on the image does not contain `1` (evaluate at `0 ∈ E`). If `fg` vanishes on the image but `f(F e₀) ≠ 0` and
`g(F e₁) ≠ 0`, then `f ∘ F ≠ 0` on a neighbourhood of `e₀` (continuity), so `g ∘ F` vanishes there, and by the
identity theorem on the connected space `E` (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) it
vanishes everywhere, contradicting `g(F e₁) ≠ 0`. -/

theorem solution {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → σ → ℂ) (hF : ∀ i, AnalyticOnNhd ℂ (fun e => F e i) Set.univ) :
    (⨅ e : E, RingHom.ker (MvPolynomial.eval (F e))).IsPrime := by
  have hφ : ∀ f : MvPolynomial σ ℂ, AnalyticOnNhd ℂ (fun e => MvPolynomial.eval (F e) f) Set.univ := by
    intro f
    have := AnalyticOnNhd.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ) (f := F) hF f
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : MvPolynomial σ ℂ) ∈ ⨅ e : E, RingHom.ker (MvPolynomial.eval (F e)) := by
      rw [h]; trivial
    simp only [Submodule.mem_iInf, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero (h1 0)
  · intro f g hfg
    simp only [Submodule.mem_iInf, RingHom.mem_ker, map_mul] at hfg ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := hcon
    -- `φ_f ≠ 0` near `e₀`, so `φ_g = 0` near `e₀`, so `φ_g ≡ 0`.
    have hcont : ContinuousAt (fun e => MvPolynomial.eval (F e) f) e₀ :=
      (hφ f e₀ (Set.mem_univ _)).continuousAt
    have hne : ∀ᶠ e in nhds e₀, MvPolynomial.eval (F e) f ≠ 0 := hcont.eventually_ne he₀
    have hzero : (fun e => MvPolynomial.eval (F e) g) =ᶠ[nhds e₀] 0 := by
      filter_upwards [hne] with e he
      have := hfg e
      simpa [he] using this
    have := (hφ g).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ e₀) hzero (Set.mem_univ e₁)
    exact he₁ this
