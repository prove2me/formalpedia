-- Prove2me | solution 1 for BookProof.FarisLavine.mulComparison_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:13.831172+00:00
-- url     : https://prove2.me/submissions/7ca7139d-d67d-4843-83c3-8990e70c38a6

-- Generated from ChapterFarisLavine.lean — solution of BookProof.FarisLavine.mulComparison_surjective
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_coe
open BookProof.FarisLavine





variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) (g : L2Nat) :
    ∃ x : mulSymbolDomain lam, (mulComparison lam x : L2Nat) + (x : L2Nat) = g := by

  have hpos : ∀ n, (0 : ℝ) < 1 + |lam n| := fun n => by positivity
  set fn : ℕ → ℂ := fun n => ((g : L2Nat) : ℕ → ℂ) n / ((1 + |lam n| : ℝ) : ℂ) with hfn
  have hle : ∀ n, ‖fn n‖ ≤ ‖((g : L2Nat) : ℕ → ℂ) n‖ := by
    intro n
    rw [hfn]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    rw [div_le_iff₀ (hpos n)]
    nlinarith [norm_nonneg (((g : L2Nat) : ℕ → ℂ) n), abs_nonneg (lam n)]
  have hmem : Memℓp fn 2 := memLpTwo_of_norm_le g.2 hle
  have hdom : (⟨fn, hmem⟩ : L2Nat) ∈ mulSymbolDomain lam := by
    refine memLpTwo_of_norm_le g.2 fun n => ?_
    have hval : ‖mulSymbolFun lam fn n‖
        = |lam n| / (1 + |lam n|) * ‖((g : L2Nat) : ℕ → ℂ) n‖ := by
      simp only [mulSymbolFun, hfn, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos n)]
      ring
    rw [show ((⟨fn, hmem⟩ : L2Nat) : ℕ → ℂ) = fn from rfl, hval]
    have hfrac : |lam n| / (1 + |lam n|) ≤ 1 := by
      rw [div_le_one (hpos n)]
      linarith
    nlinarith [norm_nonneg (((g : L2Nat) : ℕ → ℂ) n), abs_nonneg (lam n)]
  refine ⟨⟨⟨fn, hmem⟩, hdom⟩, ?_⟩
  ext n
  simp only [lp.coeFn_add, Pi.add_apply, mulComparison, mulSymbolOp_coe, mulSymbolFun]
  have hne : ((1 + |lam n| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos n)
  change ((|lam n| : ℝ) : ℂ) * fn n + fn n = ((g : L2Nat) : ℕ → ℂ) n
  rw [hfn]
  field_simp
  push_cast
  ring
