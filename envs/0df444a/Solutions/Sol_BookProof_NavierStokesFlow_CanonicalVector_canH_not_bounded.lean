-- Prove2me | solution 1 for BookProof.NavierStokesFlow.CanonicalVector.canH_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:16:04.806988+00:00
-- url     : https://prove2.me/submissions/c5adedec-ef0d-47db-89c8-efd139393f0c

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
  BookProof.NavierStokesFlow BookProof.NavierStokesFlow.CanonicalVector

namespace P4987

open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
  BookProof.NavierStokesFlow BookProof.NavierStokesFlow.CanonicalVector

theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) : crd (ann i x) = aFun i (crd x) := rfl
theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) : crd (cre i x) = cFun i (crd x) := rfl

theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := rfl
theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := rfl

theorem crd_pos (i : Fin 3) (x : lpFiniteModes Vel) : crd (pos i x) = pFun i (crd x) := by
  simp only [pos, pFun, LinearMap.smul_apply, LinearMap.add_apply, crd_smul, crd_add,
    crd_ann, crd_cre]

theorem crd_mom (i : Fin 3) (x : lpFiniteModes Vel) : crd (mom i x) = mFun i (crd x) := by
  rw [mom, mFun, LinearMap.smul_apply, crd_smul, LinearMap.sub_apply, sub_eq_add_neg,
    ← neg_one_smul ℂ (ann i x), crd_add, crd_smul, crd_ann, crd_cre, neg_one_smul,
    ← sub_eq_add_neg]

theorem crd_fieldV (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (i : Fin 3)
    (x : lpFiniteModes Vel) : crd (fieldV A c i x) = vFun A c i (crd x) := by
  simp only [fieldV, vFun, LinearMap.add_apply, Fin.sum_univ_three,
    LinearMap.smul_apply, LinearMap.id_apply, crd_add, crd_smul, crd_pos]

theorem crd_canH (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (x : lpFiniteModes Vel) : crd (canH A c x) = canFun A c (crd x) := by
  funext γ
  simp only [canH, canFun, Fin.sum_univ_three, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, crd_add, crd_smul, crd_mom, crd_fieldV,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]


/-- the basis state `(n,0,0)` in coordinates -/
theorem crd_coreState (n : ℕ) :
    crd (coreState ![n, 0, 0]) =
      fun δ => if δ 0 = n ∧ δ 1 = 0 ∧ δ 2 = 0 then (1 : ℂ) else 0 := by
  funext δ
  have h : crd (coreState ![n, 0, 0]) δ = (Pi.single (![n, 0, 0] : Vel) (1 : ℂ) : Vel → ℂ) δ := by
    simp [crd, coreState, lp.single_apply]
  rw [h, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> simp [h0, h1, h2]

theorem canFun_coreState (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (n : ℕ) :
    canFun A c (crd (coreState ![n, 0, 0])) ![n + 2, 0, 0] =
      Complex.I * ((A 0 0 / 2 * (Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [crd_coreState]
  simp [canFun, mFun, vFun, pFun, cFun, aFun, raise, lower, Function.update_apply,
    Fin.sum_univ_three]
  have h1 : ¬ (n + 1 + 1 = n) := by omega
  have h2 : ¬ (n + 2 + 1 + 1 = n) := by omega
  have h3 : ¬ (n + 2 + 1 = n) := by omega
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [h1, h2, h3, if_false, sub_zero, neg_zero, add_zero]
  linear_combination (Complex.I * (A 0 0 : ℂ) * ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ)
    * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * hinv

end P4987

open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow BookProof.NavierStokesFlow.CanonicalVector in
theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ x : lpFiniteModes Vel, ‖(x : L2I Vel)‖ = 1
      ∧ C < ‖((canH A c x : lpFiniteModes Vel) : L2I Vel)‖ := by
  have hApos : 0 < |A 0 0| := abs_pos.mpr hA
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |C| / |A 0 0|)
  have hn' : 2 * |C| < |A 0 0| * n := by
    rw [div_lt_iff₀ hApos] at hn; linarith
  refine ⟨coreState ![n, 0, 0], ?_, ?_⟩
  · show ‖(lp.single 2 (![n, 0, 0] : Vel) (1 : ℂ) : L2I Vel)‖ = 1
    rw [lp.norm_single (by norm_num)]
    simp
  · have hle := lp.norm_apply_le_norm (p := 2) (by norm_num)
      ((canH A c (coreState ![n, 0, 0]) : L2I Vel)) ![n + 2, 0, 0]
    have hval : ((canH A c (coreState ![n, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 2, 0, 0] =
        Complex.I * ((A 0 0 / 2 * (Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      have h := congrFun (P4987.crd_canH A c (coreState ![n, 0, 0])) ![n + 2, 0, 0]
      rw [P4987.canFun_coreState] at h
      exact h
    rw [hval, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at hle
    have hP : 0 ≤ Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1) := by positivity
    have hb : (n : ℝ) + 1 ≤ Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1) := by
      calc (n : ℝ) + 1 = Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    rw [abs_mul, abs_div, abs_two, abs_of_nonneg hP] at hle
    have hm := mul_le_mul_of_nonneg_left hb (le_of_lt (half_pos hApos))
    have hC := le_abs_self C
    nlinarith
