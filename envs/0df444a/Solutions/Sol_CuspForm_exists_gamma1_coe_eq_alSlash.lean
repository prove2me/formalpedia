-- Prove2me | solution 1 for CuspForm.exists_gamma1_coe_eq_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/94f87dd9-dd73-5a5f-b778-67e46ce27653

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash

set_option autoImplicit false

open scoped MatrixGroups ModularForm

noncomputable section

open scoped Pointwise

namespace ALMod

open ModularForm

variable {M q : ℕ}

def conjMat (W : AtkinLehnerDatum M q) (A B c' D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a * A + W.b * (M : ℤ) * c' - (W.R : ℤ) * (q : ℤ) * W.a * B - (W.R : ℤ) * W.b * D,
      -(W.a * W.b * A) + (q : ℤ) * W.a ^ 2 * B + W.a * W.b * D - W.b ^ 2 * (W.R : ℤ) * c';
    (M : ℤ) * (A - (W.R : ℤ) * B - D) + (q : ℤ) * (M : ℤ) * c',
      -(W.b * (W.R : ℤ) * A) - W.b * (M : ℤ) * c' + W.a * (M : ℤ) * B + (q : ℤ) * W.a * D]

theorem mat_mul_eq_conjMat_mul (W : AtkinLehnerDatum M q) (A B c' D : ℤ) :
    W.mat * !![A, B; (M : ℤ) * c', D] = conjMat W A B c' D * W.mat := by
  have hM : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := W.hM_int
  have hbz := W.bezout
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AtkinLehnerDatum.mat, conjMat, Matrix.mul_apply, Fin.sum_univ_two, hM]
  · linear_combination (-((q : ℤ) * (W.a * A + W.b * (W.R : ℤ) * c'))) * hbz
  · linear_combination (-((q : ℤ) * W.a * B + W.b * D)) * hbz
  · linear_combination (-((q : ℤ) * (W.R : ℤ) * (A + (q : ℤ) * c'))) * hbz
  · linear_combination (-((q : ℤ) * (W.R : ℤ) * B + (q : ℤ) * D)) * hbz

theorem coe_SL_GL (γ : SL(2, ℤ)) :
    (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

theorem exists_mem_Gamma1_alGL_mul_eq [NeZero M] (W : AtkinLehnerDatum M q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 M ∧
      W.alGL * (γ : GL (Fin 2) ℝ) = (δ : GL (Fin 2) ℝ) * W.alGL := by
  obtain ⟨hA, hD, hC⟩ := CongruenceSubgroup.Gamma1_mem M γ |>.mp hγ

  obtain ⟨c', hc'⟩ : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hC
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hAdef
  set B := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hBdef
  set D := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hDdef
  have hγe : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![A, B; (M : ℤ) * c', D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hAdef, hBdef, hDdef, hc']
  have hmul := mat_mul_eq_conjMat_mul W A B c' D

  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (W.q_pos).ne'
  have hdet : (conjMat W A B c' D).det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_mul, W.det_mat, ← hγe, γ.2, mul_one] at h
    have h' : (conjMat W A B c' D).det * (q : ℤ) = 1 * (q : ℤ) := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ hq0 h'
  refine ⟨⟨conjMat W A B c' D, hdet⟩, ?_, ?_⟩
  ·
    rw [CongruenceSubgroup.Gamma1_mem]
    have hbez : ((q : ZMod M)) * (W.a : ZMod M) - (W.R : ZMod M) * (W.b : ZMod M) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod M) W.bezout
      push_cast at this
      exact this
    have hMz : ((M : ℕ) : ZMod M) = 0 := ZMod.natCast_self M
    have hqR : (q : ZMod M) * (W.R : ZMod M) = 0 := by
      have := congrArg (Nat.cast : ℕ → ZMod M) W.hM
      push_cast at this
      rw [ZMod.natCast_self] at this
      exact this.symm
    have hA1 : ((A : ℤ) : ZMod M) = 1 := hA
    have hD1 : ((D : ℤ) : ZMod M) = 1 := hD
    refine ⟨?_, ?_, ?_⟩
    · show (((q : ℤ) * W.a * A + W.b * (M : ℤ) * c' - (W.R : ℤ) * (q : ℤ) * W.a * B - (W.R : ℤ) * W.b * D : ℤ) : ZMod M) = 1
      push_cast
      rw [hMz, hA1, hD1]
      linear_combination hbez - (W.a : ZMod M) * (B : ZMod M) * hqR
    · show ((-(W.b * (W.R : ℤ) * A) - W.b * (M : ℤ) * c' + W.a * (M : ℤ) * B + (q : ℤ) * W.a * D : ℤ) : ZMod M) = 1
      push_cast
      rw [hMz, hA1, hD1]
      linear_combination hbez
    · show (((M : ℤ) * (A - (W.R : ℤ) * B - D) + (q : ℤ) * (M : ℤ) * c' : ℤ) : ZMod M) = 0
      push_cast
      rw [hMz]
      ring
  ·
    apply Units.ext
    simp only [Units.val_mul, AtkinLehnerDatum.alGL_coe]
    rw [coe_SL_GL γ, coe_SL_GL ⟨conjMat W A B c' D, hdet⟩]
    show W.mat.map (algebraMap ℤ ℝ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) =
      (conjMat W A B c' D).map (algebraMap ℤ ℝ) * W.mat.map (algebraMap ℤ ℝ)
    rw [hγe, ← Matrix.map_mul, ← Matrix.map_mul, hmul]

abbrev Γ1 (M : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem le_conj_alGL [NeZero M] (W : AtkinLehnerDatum M q) :
    Γ1 M ≤ ConjAct.toConjAct W.alGL⁻¹ • Γ1 M := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ, hδ, hW⟩ := exists_mem_Gamma1_alGL_mul_eq W γ hγ
  refine ⟨δ, hδ, ?_⟩
  show ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) = W.alGL * ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * W.alGL⁻¹
  rw [hW, mul_inv_cancel_right]

variable {k : ℤ}

def restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) :
    ⇑(restrictCusp h f) = ⇑f := rfl

def slashCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) : CuspForm Γ₂ k :=
  restrictCusp hg (CuspForm.translate f g)

@[scoped simp] theorem coe_slashCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : CuspForm Γ₁ k) :
    ⇑(slashCusp g hg f) = ⇑f ∣[k] g := rfl

end ALMod
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash.ALMod"

end
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash.ALMod"

theorem solution
    (M q : ℕ) [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f :=
  ⟨ALMod.slashCusp W.alGL (ALMod.le_conj_alGL W) f, rfl⟩

end S_CuspForm_exists_gamma1_coe_eq_alSlash
end P2MW
export P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash (solution)
