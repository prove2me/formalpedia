-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:20:30.145249+00:00
-- url     : https://prove2.me/submissions/fa2844bf-38cd-48cd-8f99-c9f033d16c00

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {ι : Type*}

theorem solution (ι : Type*) [Infinite ι] :
    lpFiniteModes ι ≠ (⊤ : Submodule ℂ (lp (fun _ : ι => ℂ) 2)) := by
  classical
  set e : ℕ ↪ ι := Infinite.natEmbedding ι with he
  set φ : ι → ℂ := fun i => if h : ∃ k, e k = i then 1 / ((Classical.choose h : ℕ) + 1 : ℂ) else 0
    with hφ
  have hval : ∀ k : ℕ, φ (e k) = 1 / ((k : ℂ) + 1) := by
    intro k
    have hex : ∃ j, e j = e k := ⟨k, rfl⟩
    have hchoose : Classical.choose hex = k := e.injective (Classical.choose_spec hex)
    simp only [hφ, dif_pos hex, hchoose]
  have hout : ∀ i ∉ Set.range e, ‖φ i‖ ^ 2 = 0 := by
    intro i hi
    have : ¬ ∃ k, e k = i := fun ⟨k, hk⟩ => hi ⟨k, hk⟩
    simp [hφ, dif_neg this]
  have hsummable : Summable fun i => ‖φ i‖ ^ 2 := by
    refine (e.injective.summable_iff hout).1 ?_
    have hcomp : (fun k : ℕ => ‖φ (e k)‖ ^ 2) = fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2 := by
      funext k
      have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hval k, hcast, norm_div, norm_one, Complex.norm_natCast]
      push_cast
      ring
    have hsum : Summable fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2 := by
      have hbase := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      refine ((summable_nat_add_iff 1).2 hbase).congr fun k => ?_
      push_cast
      rw [div_pow, one_pow]
    rw [Function.comp_def, hcomp]
    exact hsum
  have hmem : Memℓp φ 2 := by
    apply memℓp_gen
    simpa using hsummable
  intro htop
  have hg : (⟨φ, hmem⟩ : lp (fun _ : ι => ℂ) 2) ∈ lpFiniteModes ι := htop ▸ Submodule.mem_top
  rw [mem_lpFiniteModes] at hg
  have hsub : Set.range e ⊆ Function.support φ := by
    rintro _ ⟨k, rfl⟩
    have : φ (e k) ≠ 0 := by
      rw [hval k]
      refine one_div_ne_zero ?_
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]
      exact_mod_cast Nat.succ_ne_zero k
    simpa [Function.mem_support] using this
  exact (Set.infinite_range_of_injective e.injective) (hg.subset hsub)


#print axioms solution
