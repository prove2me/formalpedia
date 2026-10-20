-- Prove2me | solution 1 for BookProof.TensorCore.exists_core_approx
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T16:09:48.983818+00:00
-- url     : https://prove2.me/submissions/ca2b7d52-ae0a-42c9-89fc-e3cda44bf4fd

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.exists_core_approx
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_TensorCore_norm_tmul_sub_le
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply
import Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_graphCore
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)
theorem tc_incl_succ_tmul (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = ((a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b : (Hs.pow (n+1)).carrier) := by
  simp [inclPow]

theorem tc_der_succ_tmul (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) = (A a ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b : (Hs.pow (n+1)).carrier) := by
  simp [derPow]

theorem tc_tmul_closure (hcore : IsGraphCore D A) (n : ℕ)
    (ih : ∀ b : ((domSpace Hs D₂).pow n), graphPow Hs D₂ A n b ∈
      (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) ∈
      (Submodule.map (graphPow Hs D₂ A (n + 1))
        (corePow Hs D₂ D (n + 1))).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  set X := inclPow Hs D₂ n b
  set Y := derPow Hs D₂ A n b
  set K : ℝ := ‖X‖ + ‖Y‖ + ‖(a : Hs.carrier)‖ + ‖A a‖ + 2 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min 1 (ε / (2 * K)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ ε / 2 := by
    have : δ ≤ ε / (2 * K) := min_le_right _ _
    calc δ * K ≤ ε / (2 * K) * K := by gcongr
      _ = ε / 2 := by field_simp
  obtain ⟨a', ha'D, ha1, ha2⟩ := hcore a δ hδpos
  have hb := ih b
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hb
  obtain ⟨z, hz, hzd⟩ := hb δ hδpos
  obtain ⟨b', hb'core, rfl⟩ := hz
  refine ⟨graphPow Hs D₂ A (n + 1) (a' ⊗ₜ[ℂ] b'),
    ⟨a' ⊗ₜ[ℂ] b', tmul_mem_corePow Hs D₂ D ha'D hb'core, rfl⟩, ?_⟩
  simp only [graphPow, LinearMap.prod_apply, Function.prod, Prod.dist_eq, LinearIsometry.coe_toLinearMap] at hzd ⊢
  rw [max_lt_iff] at hzd
  obtain ⟨h1, h2⟩ := hzd
  rw [dist_eq_norm] at h1 h2
  rw [tc_incl_succ_tmul, tc_incl_succ_tmul, tc_der_succ_tmul, tc_der_succ_tmul, dist_eq_norm,
    dist_eq_norm]
  set X' := inclPow Hs D₂ n b'
  set Y' := derPow Hs D₂ A n b'
  have ha'n : ‖(a' : Hs.carrier)‖ ≤ ‖(a : Hs.carrier)‖ + δ := by
    have := norm_sub_norm_le (a' : Hs.carrier) (a : Hs.carrier)
    rw [norm_sub_rev] at this; linarith
  have hAa'n : ‖A a'‖ ≤ ‖A a‖ + δ := by
    have := norm_sub_norm_le (A a') (A a)
    rw [norm_sub_rev] at this; linarith
  have e1 := norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier) X X'
  have e2 := norm_tmul_sub_le (A a) (A a') X X'
  have e3 := norm_tmul_sub_le (a : Hs.carrier) (a' : Hs.carrier) Y Y'
  have p1 : ‖(a : Hs.carrier) - a'‖ * ‖X‖ ≤ δ * ‖X‖ := by gcongr
  have p2 : ‖(a' : Hs.carrier)‖ * ‖X - X'‖ ≤ (‖(a : Hs.carrier)‖ + δ) * δ := by gcongr
  have p3 : ‖A a - A a'‖ * ‖X‖ ≤ δ * ‖X‖ := by gcongr
  have p4 : ‖A a'‖ * ‖X - X'‖ ≤ (‖A a‖ + δ) * δ := by gcongr
  have p5 : ‖(a : Hs.carrier) - a'‖ * ‖Y‖ ≤ δ * ‖Y‖ := by gcongr
  have p6 : ‖(a' : Hs.carrier)‖ * ‖Y - Y'‖ ≤ (‖(a : Hs.carrier)‖ + δ) * δ := by gcongr
  have hn1 : 0 ≤ ‖X‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖Y‖ := norm_nonneg _
  have hn3 : 0 ≤ ‖(a : Hs.carrier)‖ := norm_nonneg _
  have hn4 : 0 ≤ ‖A a‖ := norm_nonneg _
  have hδδ : δ * δ ≤ δ := by nlinarith
  rw [max_lt_iff]
  constructor
  · nlinarith
  · have : A a ⊗ₜ[ℂ] X + (a : Hs.carrier) ⊗ₜ[ℂ] Y - (A a' ⊗ₜ[ℂ] X' + (a' : Hs.carrier) ⊗ₜ[ℂ] Y')
        = (A a ⊗ₜ[ℂ] X - A a' ⊗ₜ[ℂ] X') + ((a : Hs.carrier) ⊗ₜ[ℂ] Y - (a' : Hs.carrier) ⊗ₜ[ℂ] Y') := by
      abel
    rw [this]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    nlinarith

theorem tc_range_le (hcore : IsGraphCore D A) (n : ℕ) :
    LinearMap.range (graphPow Hs D₂ A n)
      ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure := by
  induction n with
  | zero =>
    refine le_trans ?_ (Submodule.le_topologicalClosure _)
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by simp [corePow], rfl⟩
  | succ n ih =>
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | tmul a b =>
      exact tc_tmul_closure Hs D₂ A D hcore n (fun b => ih ⟨b, rfl⟩) a b
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem tc_core_approx (hcore : IsGraphCore D A) (n : ℕ)
    (x : ((domSpace Hs D₂).pow n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ corePow Hs D₂ D n,
      ‖inclPow Hs D₂ n x - inclPow Hs D₂ n y‖ < ε ∧
        ‖derPow Hs D₂ A n x - derPow Hs D₂ A n y‖ < ε := by
  have h := tc_range_le Hs D₂ A D hcore n ⟨x, rfl⟩
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at h
  obtain ⟨z, ⟨y, hy, rfl⟩, hd⟩ := h ε hε
  refine ⟨y, hy, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd
  simpa only [graphPow, LinearMap.prod_apply, Function.prod,
    LinearIsometry.coe_toLinearMap] using hd

theorem tc_isGraphCore (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n) := by
  rintro ⟨v, x₀, rfl⟩ ε hε
  obtain ⟨y₀, hy, h1, h2⟩ := tc_core_approx Hs D₂ A D hcore n x₀ hε
  refine ⟨⟨inclPow Hs D₂ n y₀, y₀, rfl⟩, ⟨y₀, hy, rfl⟩, ?_, ?_⟩
  · simpa using h1
  · rw [sectorOp_apply Hs D₂ A n _ x₀ rfl, sectorOp_apply Hs D₂ A n _ y₀ rfl]
    exact h2

open BookProof.TensorCore in
theorem solution (hcore : IsGraphCore D A) (n : ℕ)
    (x : ((domSpace Hs D₂).pow n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ corePow Hs D₂ D n,
      ‖inclPow Hs D₂ n x - inclPow Hs D₂ n y‖ < ε ∧
        ‖derPow Hs D₂ A n x - derPow Hs D₂ A n y‖ < ε := by 
  exact tc_core_approx Hs D₂ A D hcore n x hε
