-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:00.633028+00:00
-- url     : https://prove2.me/submissions/cb0a1969-7612-4528-9692-f0c76d054800

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

private theorem diffN_apply (mu : ℝ) (z : maxDom (velSym mu)) :
    diffMaxN mu (diffMaxEquiv mu z) = velUnitary ((diagMax (velSym mu) z : L2I Vel)) := by
  simp only [diffMaxN, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

private theorem diffE_coe (mu : ℝ) (z : maxDom (velSym mu)) :
    ((diffMaxEquiv mu z : diffMaxDom mu) : L2d 3) = velUnitary ((z : L2I Vel)) := rfl

private theorem coe_sum_single {ι : Type*} [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) (k : ι) :
    ((∑ i ∈ S, lp.single 2 i (u i) : L2I ι) : ι → ℂ) k = if k ∈ S then u k else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply, ih]
      by_cases hka : k = a
      · subst hka
        simp [ha]
      · simp [hka, Finset.mem_insert]

/-- Truncations lie in the finite-mode domain. -/
private theorem sum_single_mem_finiteModes {ι : Type*} [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) :
    (∑ i ∈ S, lp.single 2 i (u i) : L2I ι) ∈ lpFiniteModes ι :=
  Submodule.sum_mem _ fun i _ => lpSingle_mem_lpFiniteModes i (u i)

/-- **The finite-mode states are a core for the comparison operator.**  Every
state of the maximal domain is approximated, simultaneously in the norm and in
the graph norm of `N`, by its finite truncations: the momentum-representation
form of "`C_c^∞` is a core". -/
private theorem approxSeq {ι : Type*} (c : ι → ℝ) (x : maxDom c) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom c, (y : L2I ι) ∈ lpFiniteModes ι ∧
      ‖(y : L2I ι) - (x : L2I ι)‖ < ε ∧ ‖diagMax c y - diagMax c x‖ < ε := by
  classical
  set u : ι → ℂ := fun k => ((x : L2I ι) : ι → ℂ) k with hu
  set v : ι → ℂ := fun k => ((diagMax c x : L2I ι) : ι → ℂ) k with hv
  have hxsum : HasSum (fun i => lp.single 2 i (u i)) ((x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hvsum : HasSum (fun i => lp.single 2 i (v i)) ((diagMax c x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hx1 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (u i) : L2I ι) - (x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hxsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  have hx2 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (v i) : L2I ι) - (diagMax c x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hvsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  obtain ⟨S, hS1, hS2⟩ := (hx1.and hx2).exists
  refine ⟨⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
    finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩,
    sum_single_mem_finiteModes S u, hS1, ?_⟩
  have hdiag : (diagMax c ⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
      finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩ : L2I ι)
      = (∑ i ∈ S, lp.single 2 i (v i) : L2I ι) := by
    refine lp.ext (funext fun k => ?_)
    rw [diagMax_coe, coe_sum_single, coe_sum_single]
    by_cases hk : k ∈ S
    · simp [hk, hv, hu]
    · simp [hk]
  rw [hdiag]
  exact hS2

theorem solution (mu : ℝ) (z : diffMaxDom mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : diffMaxDom mu, (y : L2d 3) ∈ (polyGaussCore (d := 3)) ∧
      ‖(y : L2d 3) - (z : L2d 3)‖ < ε ∧ ‖diffMaxN mu y - diffMaxN mu z‖ < ε := by
  obtain ⟨z', rfl⟩ := (diffMaxEquiv mu).surjective z
  obtain ⟨y', hy1, hy2, hy3⟩ := approxSeq (velSym mu) z' ε hε
  refine ⟨diffMaxEquiv mu y', ?_, ?_, ?_⟩
  · rw [diffE_coe]
    exact velUnitary_mem_core ⟨(y' : L2I Vel), hy1⟩
  · rw [diffE_coe, diffE_coe, ← map_sub, velUnitary.norm_map]
    exact hy2
  · rw [diffN_apply, diffN_apply, ← map_sub, velUnitary.norm_map]
    exact hy3

#print axioms solution
