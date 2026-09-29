-- Prove2me | solution 1 for CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3c4b682f-80ad-5470-a62e-319bbaaff28c

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped MatrixGroups ModularForm

namespace DiaW

open CongruenceSubgroup

variable {M : ℕ} [NeZero M] {p : ℕ}

def tauMat (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ) * W.a * α - W.a * W.b * ((M : ℤ) * γ') + (p : ℤ) * (W.R : ℤ) * β - W.b * (W.R : ℤ) * δ,
      α * W.b - (W.R : ℤ) * γ' * W.b ^ 2 + (p : ℤ) * β - W.b * δ;
    (p : ℤ) * (-(W.R : ℤ) * W.a * α + W.a ^ 2 * ((M : ℤ) * γ') - (W.R : ℤ) ^ 2 * β + W.a * (W.R : ℤ) * δ),
      -(W.R : ℤ) * α * W.b + W.a * W.b * ((M : ℤ) * γ') - (p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * W.a * δ]

theorem mat_mul_tauMat (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ) :
    W.mat * tauMat W α β γ' δ = !![α, β; (M : ℤ) * γ', δ] * W.mat := by
  have hb := W.bezout
  have hM := W.hM_int
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.mat, tauMat, hM]
  · linear_combination (α * ((p : ℤ) * W.a) + β * ((p : ℤ) * (W.R : ℤ))) * hb
  · linear_combination (α * W.b + β * (p : ℤ)) * hb
  · linear_combination (((p : ℤ) * (W.R : ℤ)) * γ' * ((p : ℤ) * W.a) + δ * ((p : ℤ) * (W.R : ℤ))) * hb
  · linear_combination (((p : ℤ) * (W.R : ℤ)) * γ' * W.b + δ * (p : ℤ)) * hb

theorem det_tauMat (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ) (hσ : α * δ - β * ((M : ℤ) * γ') = 1) :
    (tauMat W α β γ' δ).det = 1 := by
  have h := congrArg Matrix.det (mat_mul_tauMat W α β γ' δ)
  rw [Matrix.det_mul, Matrix.det_mul, W.det_mat, Matrix.det_fin_two_of, hσ, one_mul] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
  exact mul_left_cancel₀ hp (h.trans (mul_one _).symm)

theorem tauMat_lowerLeft (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ) :
    tauMat W α β γ' δ 1 0 = (M : ℤ) * (-(W.a * α) - (W.R : ℤ) * β + W.a * δ + (p : ℤ) * W.a ^ 2 * γ') := by
  have hM := W.hM_int
  simp [tauMat, hM]
  ring

theorem tauMat_lowerRight_sub (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ) :
    tauMat W α β γ' δ 1 1 - δ = (W.R : ℤ) * (-(α * W.b) - (p : ℤ) * β + W.b * δ + W.a * W.b * (p : ℤ) * γ') := by
  have hb := W.bezout
  have hM := W.hM_int
  simp [tauMat, hM]
  linear_combination δ * hb

theorem tauMat_lowerRight_mul_sub_one (W : ModularForm.AtkinLehnerDatum M p) (α β γ' δ : ℤ)
    (hσ : α * δ - β * ((M : ℤ) * γ') = 1) :
    tauMat W α β γ' δ 1 1 * δ - 1 =
      (p : ℤ) * (-(W.a * α * δ) + W.a * δ ^ 2 - (W.R : ℤ) * β * δ + (W.R : ℤ) * γ' * (W.a * W.b * δ + β)) := by
  have hb := W.bezout
  have hM := W.hM_int
  simp [tauMat, hM]
  rw [hM] at hσ
  linear_combination (α * δ) * hb + hσ

open CongruenceSubgroup in
theorem main
    (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d' = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∧
      ZMod.unitsMap hpM (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) := by
  have hD := CuspForm.stableD M H k
  let σ : Gamma0 M := CuspForm.gammaLift M d

  set α : ℤ := (σ : SL(2, ℤ)) 0 0 with hα
  set β : ℤ := (σ : SL(2, ℤ)) 0 1 with hβ
  set γ : ℤ := (σ : SL(2, ℤ)) 1 0 with hγ
  set δ : ℤ := (σ : SL(2, ℤ)) 1 1 with hδ
  obtain ⟨γ', hγ'⟩ : (M : ℤ) ∣ γ := (ZMod.intCast_zmod_eq_zero_iff_dvd γ M).mp (Gamma0_mem.mp σ.2)
  have hdetσ : α * δ - β * ((M : ℤ) * γ') = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (σ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at h
    rw [← hγ']
    linarith [h]
  have hσmat : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (M : ℤ) * γ', δ] := by
    rw [← hγ']
    ext i j; fin_cases i <;> fin_cases j <;> rfl

  let τSL : SL(2, ℤ) := ⟨tauMat W α β γ' δ, det_tauMat W α β γ' δ hdetσ⟩
  have hτ0 : τSL ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show ((tauMat W α β γ' δ 1 0 : ℤ) : ZMod M) = 0
    rw [tauMat_lowerLeft]
    push_cast
    simp
  let τ : Gamma0 M := ⟨τSL, hτ0⟩
  let d' : (ZMod M)ˣ := CohCarrier.gamma0Units M τ
  have hd : CohCarrier.gamma0Units M σ = d := CuspForm.gamma0Units_gammaLift d
  have hdval : (d : ZMod M) = (δ : ZMod M) := by
    rw [← hd, CohCarrier.val_gamma0Units]; rfl
  have hd'val : (d' : ZMod M) = ((tauMat W α β γ' δ 1 1 : ℤ) : ZMod M) := by
    show (CohCarrier.gamma0Units M τ : ZMod M) = _
    rw [CohCarrier.val_gamma0Units]; rfl
  refine ⟨d', ?_, ?_, ?_⟩
  ·
    apply Units.ext
    have hRM : M / p ∣ M := Nat.div_dvd_of_dvd hpM
    show ((ZMod.unitsMap hRM d' : (ZMod (M / p))ˣ) : ZMod (M / p)) = ((ZMod.unitsMap hRM d : (ZMod (M / p))ˣ) : ZMod (M / p))
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, hdval, hd'val, ZMod.castHom_apply, ZMod.cast_intCast hRM]
    rw [← sub_eq_zero, ← Int.cast_sub, tauMat_lowerRight_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hR : (M / p : ℕ) = W.R := Nat.div_eq_of_eq_mul_left W.q_pos (by rw [Nat.mul_comm]; exact W.hM)
    rw [hR]
    exact Dvd.intro _ rfl
  ·
    apply Units.ext
    show ((ZMod.unitsMap hpM (d' * d) : (ZMod p)ˣ) : ZMod p) = 1
    simp only [map_mul, Units.val_mul, ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, hdval, hd'val, ZMod.castHom_apply,
      ZMod.cast_intCast hpM]
    rw [← Int.cast_mul, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, tauMat_lowerRight_mul_sub_one W α β γ' δ hdetσ,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.intro _ rfl
  ·
    have hWτ : (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * W.alGL =
        W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ τSL : GL (Fin 2) ℝ) := by
      apply Units.ext
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (algebraMap ℤ ℝ)) (mat_mul_tauMat W α β γ' δ)
      simp only [Matrix.map_mul] at h
      rw [← hσmat] at h
      show ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) * (W.mat).map (algebraMap ℤ ℝ) =
        (W.mat).map (algebraMap ℤ ℝ) * (tauMat W α β γ' δ).map (algebraMap ℤ ℝ)
      exact h.symm
    rw [ModularForm.alSlash_def, CuspForm.coe_diamondLinH_apply k hD, ← SlashAction.slash_mul, hWτ, SlashAction.slash_mul,
      ← ModularForm.alSlash_def, ← hG, CuspForm.coe_diamondLinH_eq_slash k hD d' τ rfl G]

end DiaW

theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d' = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∧
      ZMod.unitsMap hpM (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) :=
  DiaW.main M p hpM H hHp W k d f G hG

#print axioms solution

end S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
end P2MW
export P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash (solution)
