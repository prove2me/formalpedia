-- Prove2me | solution 1 for EntireDivisor.exists_eq_mul_iff_iteratedDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:48:38.076735+00:00
-- url     : https://prove2.me/submissions/eac4d52f-1f6f-4fed-a9b7-c11045f52ae3

import Mathlib

set_option autoImplicit false

open Filter Topology

lemma entireDivisor_jets_iff_le_aux {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (N : ℕ∞) :
    (∀ m : ℕ, (m : ℕ∞) < N → iteratedDeriv m g z = 0) ↔ N ≤ analyticOrderAt g z := by
  induction N using ENat.recTopCoe with
  | top =>
    constructor
    · intro H
      refine ENat.forall_natCast_le_iff_le.mp fun a _ => ?_
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mpr
        fun i _ => H i (ENat.natCast_lt_top i)
    · intro H m _
      have : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g z := le_trans le_top H
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp this m (Nat.lt_succ_self m)
  | coe n =>
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
    simp only [Nat.cast_lt]

theorem solution (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    (∃ h : ℂ → ℂ, Differentiable ℂ h ∧ g = f * h) ↔
      ∀ z : ℂ, ∀ m : ℕ, (m : ℕ∞) < analyticOrderAt f z → iteratedDeriv m g z = 0 := by
  have key : (∀ z : ℂ, ∀ m : ℕ, (m : ℕ∞) < analyticOrderAt f z → iteratedDeriv m g z = 0) ↔
      ∀ z, analyticOrderAt f z ≤ analyticOrderAt g z :=
    forall_congr' fun z => entireDivisor_jets_iff_le_aux (hg.analyticAt z) _
  rw [key]
  constructor
  · rintro ⟨h, hh, rfl⟩ z
    rw [analyticOrderAt_mul (hf.analyticAt z) (hh.analyticAt z)]
    exact le_self_add
  · intro H
    by_cases hf0 : f = 0
    · refine ⟨0, differentiable_const 0, ?_⟩
      subst hf0
      ext z
      have h1 : analyticOrderAt (0 : ℂ → ℂ) z = ⊤ := by
        rw [analyticOrderAt_eq_top]; exact Filter.Eventually.of_forall fun _ => rfl
      have h2 := H z
      rw [h1, top_le_iff, analyticOrderAt_eq_top] at h2
      simpa using h2.self_of_nhds
    · have hfin : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z hz =>
        hf0 ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).mp hz)
      set φ : ℂ → ℂ := g / f with hφdef
      have hφ : MeromorphicOn φ Set.univ := fun z _ =>
        (hg.analyticAt z).meromorphicAt.div (hf.analyticAt z).meromorphicAt
      set h := toMeromorphicNFOn φ Set.univ with hdef
      have hne : ∀ z, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := fun z =>
        ((hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero).resolve_left
          (fun h' => hfin z (analyticOrderAt_eq_top.mpr h'))
      have hord : ∀ z, 0 ≤ meromorphicOrderAt φ z := by
        intro z
        have hn : analyticOrderAt f z = (analyticOrderNatAt f z : ℕ∞) :=
          (Nat.cast_analyticOrderNatAt (hfin z)).symm
        obtain ⟨F, hFa, hF0, hF⟩ := (hf.analyticAt z).analyticOrderAt_eq_natCast.mp hn
        obtain ⟨G, hGa, hG⟩ := (natCast_le_analyticOrderAt (hg.analyticAt z)).mp
          (hn.symm.trans_le (H z))
        refine ((hφ z trivial).meromorphicOrderAt_nonneg_iff).mpr ⟨G / F, hGa.div hFa hF0, ?_⟩
        filter_upwards [self_mem_nhdsWithin, hF.filter_mono nhdsWithin_le_nhds,
          hG.filter_mono nhdsWithin_le_nhds] with w hw hFw hGw
        have hw' : (w - z) ^ (analyticOrderNatAt f z) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr hw)
        simp only [hφdef, Pi.div_apply, hFw, hGw, smul_eq_mul]
        exact mul_div_mul_left _ _ hw'
      have hNF : MeromorphicNFOn h Set.univ := meromorphicNFOn_toMeromorphicNFOn φ Set.univ
      have han : ∀ z, AnalyticAt ℂ h z := fun z =>
        (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
          (by rw [hdef, meromorphicOrderAt_toMeromorphicNFOn hφ (Set.mem_univ z)]; exact hord z)
      refine ⟨h, fun z => (han z).differentiableAt, ?_⟩
      funext z
      have e1 : (f * h) =ᶠ[𝓝[≠] z] g := by
        filter_upwards [hφ.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z), hne z]
          with w hw hfw
        show f w * toMeromorphicNFOn φ Set.univ w = g w
        rw [hw, hφdef, Pi.div_apply]
        field_simp
      have e2 : (f * h) =ᶠ[𝓝 z] g :=
        (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
          ((hf.analyticAt z).continuousAt.mul (han z).continuousAt)
          (hg.analyticAt z).continuousAt).mp e1
      exact (e2.eq_of_nhds).symm
