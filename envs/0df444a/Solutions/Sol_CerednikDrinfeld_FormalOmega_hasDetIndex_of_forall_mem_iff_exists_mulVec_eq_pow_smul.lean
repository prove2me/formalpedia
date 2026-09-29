-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/03d23f2c-4881-536a-a819-1a511cbe9a52

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace LIBody

open Matrix LT.LatticeTree

variable {p : ℕ} [Fact p.Prime]

noncomputable def up (w : Fin 2 → ℤ_[p]) : Fin 2 → ℚ_[p] := fun i => ((w i : ℤ_[p]) : ℚ_[p])

theorem up_eq_comp (w : Fin 2 → ℤ_[p]) : up w = (algebraMap ℤ_[p] ℚ_[p]) ∘ w := by
  funext i; simp [up, PadicInt.algebraMap_apply]

theorem up_smul (a : ℤ_[p]) (w : Fin 2 → ℤ_[p]) : up (a • w) = (a : ℚ_[p]) • up w := by
  funext i; simp [up]

theorem mem_stdLattice_iff (v : Fin 2 → ℚ_[p]) :
    v ∈ stdLattice ℤ_[p] ℚ_[p] ↔ ∃ w : Fin 2 → ℤ_[p], v = up w := by
  rw [mem_stdLattice]
  constructor
  · intro hv
    choose w hw using hv
    refine ⟨w, ?_⟩
    funext i; simp [up, ← hw i, PadicInt.algebraMap_apply]
  · rintro ⟨w, rfl⟩ i
    exact ⟨w i, by simp [up, PadicInt.algebraMap_apply]⟩

theorem up_mem_stdLattice (w : Fin 2 → ℤ_[p]) : up w ∈ stdLattice ℤ_[p] ℚ_[p] :=
  (mem_stdLattice_iff _).2 ⟨w, rfl⟩

noncomputable def upM (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  γ.map (algebraMap ℤ_[p] ℚ_[p])

theorem upM_mulVec (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (w : Fin 2 → ℤ_[p]) :
    upM γ *ᵥ up w = up (γ *ᵥ w) := by
  funext i
  rw [up_eq_comp, up_eq_comp, Function.comp_apply, RingHom.map_mulVec]
  rfl

theorem upM_det (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) : (upM γ).det = (γ.det : ℚ_[p]) := by
  have := RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) γ
  rw [RingHom.mapMatrix_apply, PadicInt.algebraMap_apply] at this
  exact this.symm

theorem upM_adjugate (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) : (upM γ).adjugate = upM γ.adjugate := by
  have := RingHom.map_adjugate (algebraMap ℤ_[p] ℚ_[p]) γ
  simpa [upM, RingHom.mapMatrix_apply] using this.symm

theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem ppow_ne_zero (n : ℕ) : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ p_ne_zero

theorem clause_iff (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]ˣ) (e h : ℕ)
    (hγ : γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h) (v : Fin 2 → ℚ_[p]) :
    (∃ (m : ℕ) (w c : Fin 2 → ℤ_[p]),
        (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
          γ.mulVec w = (p : ℤ_[p]) ^ (e + m) • c) ↔
      ∃ c : Fin 2 → ℤ_[p], upM γ *ᵥ v = (p : ℚ_[p]) ^ e • up c := by
  constructor
  · rintro ⟨m, w, c, hv, hw⟩
    refine ⟨c, ?_⟩
    have h1 : upM γ *ᵥ ((p : ℚ_[p]) ^ m • v) = (p : ℚ_[p]) ^ m • ((p : ℚ_[p]) ^ e • up c) := by
      rw [show (fun i => ((w i : ℤ_[p]) : ℚ_[p])) = up w from rfl] at hv
      rw [hv, upM_mulVec, show γ *ᵥ w = γ.mulVec w from rfl, hw, up_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [Matrix.mulVec_smul] at h1
    exact smul_right_injective _ (ppow_ne_zero m) h1
  · rintro ⟨c, hc⟩

    refine ⟨h, ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • ((p : ℤ_[p]) ^ e • (γ.adjugate *ᵥ c)), c, ?_, ?_⟩
    ·
      have h1 : (upM γ).adjugate *ᵥ (upM γ *ᵥ v) = (p : ℚ_[p]) ^ e • up (γ.adjugate *ᵥ c) := by
        rw [hc, Matrix.mulVec_smul, upM_adjugate, upM_mulVec]
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        upM_det, hγ] at h1

      change (p : ℚ_[p]) ^ h • v = up _
      rw [up_smul, up_smul]
      have hu : ((u : ℤ_[p]) : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
        rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
      have hu' : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
        rw [mul_comm]; exact hu
      have h2 := congrArg (fun x => (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) • x) h1
      simp only [smul_smul] at h2
      rw [PadicInt.coe_mul, ← mul_assoc, hu', one_mul, PadicInt.coe_pow, PadicInt.coe_natCast] at h2
      rw [h2, PadicInt.coe_pow, PadicInt.coe_natCast, smul_smul]
    ·
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
        Matrix.smul_mulVec, Matrix.one_mulVec, hγ, smul_smul, smul_smul, pow_add]
      congr 1
      have hu : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) = 1 := Units.inv_mul _
      linear_combination ((p : ℤ_[p]) ^ e * (p : ℤ_[p]) ^ h) * hu

noncomputable def γGL (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hdet : (upM γ).det ≠ 0) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (upM γ) hdet

noncomputable def sGL (e : ℕ) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℚ_[p]) ^ e • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
    (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact pow_ne_zero _ (ppow_ne_zero e))

end LIBody

open LIBody Matrix LT.LatticeTree in
theorem solution
    (p : ℕ) [Fact p.Prime] (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]ˣ) (e h : ℕ)
    (hγ : γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h)
    (N : Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ v : Fin 2 → ℚ_[p], v ∈ N ↔
      ∃ (m : ℕ) (w c : Fin 2 → ℤ_[p]),
        (p : ℚ_[p]) ^ m • v = (fun i => ((w i : ℤ_[p]) : ℚ_[p])) ∧
          γ.mulVec w = (p : ℤ_[p]) ^ (e + m) • c) :
    FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N (2 * (e : ℤ) - (h : ℤ)) := by
  classical

  have hu0 : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]; exact u.ne_zero
  have hdet : (upM γ).det = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ h := by
    rw [upM_det, hγ, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  have hdet0 : (upM γ).det ≠ 0 := by rw [hdet]; exact mul_ne_zero hu0 (ppow_ne_zero h)
  set G : GL (Fin 2) ℚ_[p] := γGL γ hdet0 with hG
  have hGval : (G : Matrix (Fin 2) (Fin 2) ℚ_[p]) = upM γ := by
    rw [hG]; rfl
  set g : GL (Fin 2) ℚ_[p] := sGL e * G⁻¹ with hg

  have hmem : ∀ v : Fin 2 → ℚ_[p], v ∈ N ↔ ∃ c : Fin 2 → ℤ_[p], upM γ *ᵥ v = (p : ℚ_[p]) ^ e • up c :=
    fun v => (hN v).trans (clause_iff γ u e h hγ v)
  refine ⟨g, ?_, u⁻¹, ?_⟩
  ·
    ext v
    rw [mem_latticeMap, hmem]
    have hsval : ((sGL (p := p) e : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
        (p : ℚ_[p]) ^ e • 1 := rfl
    have hgmul : ∀ x, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ x =
        (p : ℚ_[p]) ^ e • (((G⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ x) := by
      intro x
      rw [hg, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hsval, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    have hGG : upM γ * (((G⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])) = 1 := by
      rw [← hGval, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    have hGG' : (((G⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])) * upM γ = 1 := by
      rw [← hGval, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_stdLattice_iff w).1 hw
      refine ⟨c, ?_⟩
      rw [hgmul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
    · rintro ⟨c, hc⟩
      refine ⟨up c, up_mem_stdLattice c, ?_⟩
      have := congrArg (fun x => (((G⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])) *ᵥ x) hc
      simp only [Matrix.mulVec_mulVec, hGG', Matrix.one_mulVec, Matrix.mulVec_smul] at this
      rw [hgmul, ← this]
  ·
    rw [hg, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hGval, hdet]
    have hsval : ((sGL (p := p) e : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
        (p : ℚ_[p]) ^ e • 1 := rfl
    rw [hsval, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [PadicInt.algebraMap_apply, PadicInt.algebraMap_apply]
    have hu1 : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = (((u : ℤ_[p]) : ℚ_[p]))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one])
    rw [hu1, PadicInt.coe_natCast, zpow_sub₀ p_ne_zero,
      show (2 * (e : ℤ)) = ((2 * e : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      div_eq_mul_inv, mul_inv, ← pow_mul']
    ring

end S_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_hasDetIndex_of_forall_mem_iff_exists_mulVec_eq_pow_smul (solution)
