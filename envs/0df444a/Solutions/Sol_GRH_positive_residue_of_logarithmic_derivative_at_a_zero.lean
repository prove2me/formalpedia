-- Prove2me | solution 1 for GRH.positive_residue_of_logarithmic_derivative_at_a_zero
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:45:28.860797+00:00
-- url     : https://prove2.me/submissions/fad41d90-4877-4138-bc76-78355bfecb8b

import Definitions.Def_GRH_SplitPrimeLower
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp

open Filter Topology

theorem solution (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hP0 : P ≠ 0)
    (b : ℂ) (hb : P b = 0) :
    ∃ m : ℕ, 0 < m ∧ (∀ᶠ z in 𝓝[≠] b, P z ≠ 0) ∧
      Tendsto (fun z => (z-b)*logDeriv P z) (𝓝[≠] b) (𝓝 (m:ℂ)) := by
  have ha (z : ℂ) : AnalyticAt ℂ P z := hP.analyticAt z
  have hf := mt (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero b ha).1 hP0
  obtain ⟨g,hg,hg0,he⟩ := ((ha b).analyticOrderAt_ne_top).mp hf
  let m := analyticOrderNatAt P b
  change P =ᶠ[𝓝 b] fun z => (z-b)^m * g z at he
  have hm : 0 < m := by
    by_contra! h
    have e : m = 0 := Nat.eq_zero_of_le_zero h
    have v := he.self_of_nhds
    simp [hb,e] at v
    exact hg0 v.symm
  have hg' := hg.continuousAt.eventually_ne hg0
  have hn : ∀ᶠ z in 𝓝[≠] b, P z ≠ 0 := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hg'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hv hd
    exact hz ▸ mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hd)) hv
  have lim : Tendsto (fun z => (m:ℂ)+(z-b)*logDeriv g z) (𝓝[≠] b) (𝓝 (m:ℂ)) := by
    have cg : ContinuousAt (logDeriv g) b := hg.deriv.continuousAt.div hg.continuousAt hg0
    have h : ContinuousAt (fun z : ℂ => (m:ℂ)+(z-b)*logDeriv g z) b := (continuousAt_const (y:=(m:ℂ))).add ((continuousAt_id.sub_const b).mul cg)
    simpa using h.continuousWithinAt.tendsto (s:={b}ᶜ)
  refine ⟨m,hm,hn,lim.congr' ?_⟩
  filter_upwards [he.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds,
    hg'.filter_mono nhdsWithin_le_nhds, hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hv ha' hne
  have hz0 : z-b ≠ 0 := sub_ne_zero.mpr hne
  have leq : logDeriv P z = logDeriv (fun w => (w-b)^m*g w) z := by
    simp only [logDeriv_apply, hz.deriv_eq, hz.self_of_nhds]
  rw [leq,logDeriv_mul (f:=fun w : ℂ => (w-b)^m) (g:=g) z (pow_ne_zero m hz0) hv (by fun_prop) ha'.differentiableAt,
    logDeriv_fun_pow (f:=fun w : ℂ => w-b) (differentiableAt_id.sub_const b) m]
  simp only [logDeriv_apply,deriv_sub_const,deriv_id'']
  field_simp
