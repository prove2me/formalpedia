-- Prove2me | solution 1 for Disjunctive.RayCGLP.cglpy_optimal_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:27:43.437596+00:00
-- url     : https://prove2.me/submissions/a015143c-9030-462a-8036-c798981e036c

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

open Filter Topology Disjunctive.RayCGLP

lemma clm_eq_dot_core {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin n → ℝ, ∀ x, f x = dotProduct a x := by
  classical
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
  conv_lhs => rw [pi_eq_sum_univ x]
  simp [map_sum, map_smul, dotProduct, mul_comm]

lemma cone_closed_core {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDclosed : IsClosed PD)
    (y α0 : Fin n → ℝ) (β0 : ℝ) (hα0 : ∀ x ∈ PD, β0 ≤ dotProduct α0 x)
    (hy : dotProduct α0 y = 1) :
    IsClosed {x : Fin n → ℝ | ∃ s : ℝ, 0 ≤ s ∧ x - s • y ∈ PD} := by
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨xs, hxs, hlim⟩ := hx
  choose s hs0 hsP using hxs
  have hcont : Continuous fun z : Fin n → ℝ => dotProduct α0 z := by fun_prop
  have hlim2 : Tendsto (fun k => dotProduct α0 (xs k)) atTop (𝓝 (dotProduct α0 x)) :=
    (hcont.tendsto x).comp hlim
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hlim2).bddAbove
  have hsB : ∀ k, s k ∈ Set.Icc 0 (B - β0) := by
    intro k
    refine ⟨hs0 k, ?_⟩
    have h1 := hα0 _ (hsP k)
    have h2 : dotProduct α0 (xs k) ≤ B := hB ⟨k, rfl⟩
    rw [dotProduct_sub, dotProduct_smul, hy, smul_eq_mul] at h1
    linarith
  obtain ⟨s0, hs0mem, φ, hφ, hφlim⟩ := (isCompact_Icc).tendsto_subseq hsB
  refine ⟨s0, hs0mem.1, ?_⟩
  exact hPDclosed.mem_of_tendsto ((hlim.comp hφ.tendsto_atTop).sub (hφlim.smul_const y))
    (Eventually.of_forall fun k => hsP (φ k))

theorem solution {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (alphaT : Fin n → ℝ) (betaT : ℝ) (hopt : IsCGLPYOptimal PD y xbar alphaT betaT)
    (lamStar : ℝ) (hlam : IsLeast {lam : ℝ | xbar + lam • y ∈ PD} lamStar) :
    dotProduct alphaT xbar - betaT = -lamStar ∧
      dotProduct alphaT (xbar + lamStar • y) = betaT := by
  obtain ⟨⟨hval, hy⟩, hmin⟩ := hopt
  have hz : xbar + lamStar • y ∈ PD := hlam.1
  have hweak : -lamStar ≤ dotProduct alphaT xbar - betaT := by
    have := hval _ hz
    rw [dotProduct_add, dotProduct_smul, hy, smul_eq_mul] at this
    linarith
  set C : Set (Fin n → ℝ) := {x | ∃ s : ℝ, 0 ≤ s ∧ x - s • y ∈ PD} with hC
  have hCconv : Convex ℝ C := by
    intro a ha b hb t1 t2 ht1 ht2 ht
    obtain ⟨sa, hsa, ha'⟩ := ha
    obtain ⟨sb, hsb, hb'⟩ := hb
    refine ⟨t1 * sa + t2 * sb, by positivity, ?_⟩
    have := hPDconv ha' hb' ht1 ht2 ht
    convert this using 1
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hCclosed : IsClosed C := cone_closed_core PD hPDclosed y alphaT betaT hval hy
  have hPDC : ∀ x ∈ PD, x ∈ C := fun x hx => ⟨0, le_rfl, by simpa using hx⟩
  have hstrong : ∀ ε : ℝ, 0 < ε → dotProduct alphaT xbar - betaT ≤ -lamStar + ε := by
    intro ε hε
    set p : Fin n → ℝ := xbar + (lamStar - ε) • y with hp
    have hpC : p ∉ C := by
      rintro ⟨s, hs, hps⟩
      have hmem : lamStar - ε - s ∈ {lam : ℝ | xbar + lam • y ∈ PD} := by
        show xbar + (lamStar - ε - s) • y ∈ PD
        convert hps using 1
        rw [hp, sub_smul, sub_smul]
        abel
      have := hlam.2 hmem
      linarith
    obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hpC
    obtain ⟨a, ha⟩ := clm_eq_dot_core f
    have hfp : f p = f xbar + (lamStar - ε) * f y := by
      rw [hp, map_add, map_smul, smul_eq_mul]
    have hfz : u < f xbar + lamStar * f y := by
      have := hfC _ (hPDC _ hz)
      rwa [map_add, map_smul, smul_eq_mul] at this
    have hpos : 0 < f y := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have hfeas : IsCGLPYFeasible PD y ((1 / f y) • a) (u / f y) := by
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [smul_dotProduct, smul_eq_mul, ← ha]
        have := hfC x (hPDC x hx)
        rw [div_le_iff₀ hpos]
        field_simp
        linarith
      · rw [smul_dotProduct, smul_eq_mul, ← ha]
        field_simp
    have h1 := hmin _ _ hfeas
    rw [smul_dotProduct, smul_eq_mul, ← ha] at h1
    have h2 : 1 / f y * f xbar - u / f y = (f xbar - u) / f y := by ring
    rw [h2] at h1
    have h3 : (f xbar - u) / f y < -(lamStar - ε) := by
      rw [div_lt_iff₀ hpos]
      linarith
    linarith
  have heq : dotProduct alphaT xbar - betaT = -lamStar := by
    apply le_antisymm _ hweak
    apply le_of_forall_pos_le_add
    intro ε hε
    exact hstrong ε hε
  refine ⟨heq, ?_⟩
  rw [dotProduct_add, dotProduct_smul, hy, smul_eq_mul]
  linarith

#print axioms solution
