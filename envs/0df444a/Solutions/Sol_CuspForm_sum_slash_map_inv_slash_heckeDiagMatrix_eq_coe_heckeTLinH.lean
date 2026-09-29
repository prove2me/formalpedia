-- Prove2me | solution 1 for CuspForm.sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/43e9844e-3dc4-541b-b621-830e5d494e89

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspForm_stableT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace CuspForm
p2m_export "CuspForm" "ext gammaLift unitOfPrimeNotDvd gammaLift_apply_11 StableT heckeTLinH coe_heckeTLinH_apply stableT"
p2m_open "CuspForm"

namespace FullLevelTransport

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

@[scoped simp] theorem mapQ_apply (g : GL (Fin 2) ℚ) (i j : Fin 2) :
    (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g : GL (Fin 2) ℝ) i j =
      (((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) := by
  rw [Matrix.GeneralLinearGroup.map_apply]; rfl

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

def scalarGL (u : ℝˣ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) u

@[scoped simp] theorem val_scalarGL (u : ℝˣ) :
    ((scalarGL u : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(u : ℝ), 0; 0, u] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarGL, Matrix.GeneralLinearGroup.scalar]

theorem scalarGL_inv (u : ℝˣ) : (scalarGL u)⁻¹ = scalarGL u⁻¹ := by
  rw [scalarGL, scalarGL, map_inv]

theorem det_scalarGL_val (u : ℝˣ) : ((scalarGL u).det : ℝ) = u * u := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]
  ring

theorem slash_two_scalarGL (f : ℍ → ℂ) (u : ℝˣ) : f ∣[(2 : ℤ)] scalarGL u = f := by
  ext τ
  have hu : (u : ℝ) ≠ 0 := u.ne_zero
  have hσ : σ (scalarGL u) = .refl ℝ ℂ := by
    rw [σ, if_pos]
    rw [det_scalarGL_val]
    exact mul_self_pos.mpr hu
  rw [ModularForm.slash_apply, hσ, det_scalarGL_val]
  rw [show (scalarGL u : GL (Fin 2) ℝ) • τ = τ from glScalar_smul u τ]
  rw [show denom (scalarGL u : GL (Fin 2) ℝ) τ = ((u : ℝ) : ℂ) from denom_scalar u τ]
  rw [abs_mul_self]
  have hu' : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_mul]
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg, zpow_two, mul_assoc,
    mul_inv_cancel₀ (mul_ne_zero hu' hu'), mul_one]

section matrices

variable {q ℓ : ℕ}

theorem finite_identity (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (γ : GL (Fin 2) ℚ) (t s : ℤ)
    (hγ : ((γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1])
    (hts : t = q * s) (j : ℕ) (m : ℤ) (hjm : (j : ℤ) + ℓ * m = -s)
    (T' : SL(2, ℤ)) (h00 : T' 0 0 = 1) (h01 : T' 0 1 = m) (h10 : T' 1 0 = 0) (h11 : T' 1 1 = 1)
    (u : ℝˣ) (hu : (u : ℝ) = ℓ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * ModularForm.heckeDiagMatrix q *
        ((mapGL ℝ T' : GL (Fin 2) ℝ) * ModularForm.heckeMatrix ℓ j) =
      ModularForm.heckeDiagMatrix q * scalarGL u := by
  have hjm' : (j : ℝ) + (ℓ : ℝ) * (m : ℝ) = -(s : ℝ) := by exact_mod_cast hjm
  have hts' : (t : ℝ) = (q : ℝ) * (s : ℝ) := by exact_mod_cast hts
  have h00' : ((T' 0 0 : ℤ) : ℝ) = 1 := by rw [h00]; push_cast; ring
  have h01' : ((T' 0 1 : ℤ) : ℝ) = m := by rw [h01]
  have h10' : ((T' 1 0 : ℤ) : ℝ) = 0 := by rw [h10]; push_cast; ring
  have h11' : ((T' 1 1 : ℤ) : ℝ) = 1 := by rw [h11]; push_cast; ring
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hγ, ModularForm.val_heckeDiagMatrix hq,
      ModularForm.val_heckeMatrix hℓ, hu, h00', h01', h10', h11', -mul_eq_zero, -zero_eq_mul]
  all_goals first
    | ring1
    | linear_combination (ℓ : ℝ) * (q : ℝ) * hjm' + (ℓ : ℝ) * hts'

theorem infinite_identity (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (M' : ℕ) (σ' ρ : SL(2, ℤ)) (b' c' : ℤ)
    (hb : σ' 0 1 = q * b') (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c')
    (hρ00 : ρ 0 0 = σ' 1 1) (hρ01 : ρ 0 1 = -(ℓ * b')) (hρ10 : ρ 1 0 = -(q * q * M' * c'))
    (hρ11 : ρ 1 1 = σ' 0 0)
    (γinf : GL (Fin 2) ℚ)
    (hγinf : ((γinf : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
    (u : ℝˣ) (hu : (u : ℝ) = ℓ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γinf * ModularForm.heckeDiagMatrix q *
        ((mapGL ℝ ρ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) =
      ModularForm.heckeDiagMatrix q * scalarGL u := by
  have hdet : ((σ' 0 0 : ℤ) : ℝ) * (σ' 1 1 : ℝ) - (σ' 0 1 : ℝ) * (σ' 1 0 : ℝ) = 1 := by
    exact_mod_cast det_eq σ'
  have hb' : ((σ' 0 1 : ℤ) : ℝ) = (q : ℝ) * (b' : ℝ) := by rw [hb]; push_cast; ring
  have hc' : ((σ' 1 0 : ℤ) : ℝ) = (q : ℝ) * (M' : ℝ) * (ℓ : ℝ) * (c' : ℝ) := by
    rw [hc]; push_cast; ring
  have hρ00' : ((ρ 0 0 : ℤ) : ℝ) = (σ' 1 1 : ℝ) := by rw [hρ00]
  have hρ01' : ((ρ 0 1 : ℤ) : ℝ) = -((ℓ : ℝ) * (b' : ℝ)) := by rw [hρ01]; push_cast; ring
  have hρ10' : ((ρ 1 0 : ℤ) : ℝ) = -((q : ℝ) * (q : ℝ) * (M' : ℝ) * (c' : ℝ)) := by
    rw [hρ10]; push_cast; ring
  have hρ11' : ((ρ 1 1 : ℤ) : ℝ) = (σ' 0 0 : ℝ) := by rw [hρ11]
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hγinf, ModularForm.val_heckeDiagMatrix hq,
      ModularForm.val_heckeDiagMatrix hℓ, hu, hρ00', hρ01', hρ10', hρ11', -mul_eq_zero, -zero_eq_mul]
  all_goals first
    | ring1
    | linear_combination (q : ℝ) * (ℓ : ℝ) * hdet + (q : ℝ) * (ℓ : ℝ) * (σ' 0 1 : ℝ) * hc'
    | linear_combination (σ' 0 0 : ℝ) * (ℓ : ℝ) * hb'
    | linear_combination (q : ℝ) * (σ' 1 1 : ℝ) * (ℓ : ℝ) * hc'
    | linear_combination (ℓ : ℝ) * hdet + (ℓ : ℝ) * (σ' 1 0 : ℝ) * hb'

end matrices

theorem conj_eq_of_mul_eq {G : Type*} [Group G] (g D Z S : G) (h : g * D * Z = D * S) :
    D⁻¹ * g⁻¹ * D = Z * S⁻¹ :=
  calc D⁻¹ * g⁻¹ * D = D⁻¹ * g⁻¹ * (D * S) * S⁻¹ := by group
    _ = D⁻¹ * g⁻¹ * (g * D * Z) * S⁻¹ := by rw [h]
    _ = Z * S⁻¹ := by group

theorem sum_range_eq_sum_zmod {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommMonoid A] (F : ℕ → A) :
    ∑ j ∈ Finset.range ℓ, F j = ∑ x : ZMod ℓ, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod ℓ)) (fun x : ZMod ℓ ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

section GammaH

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem val_gamma0Units_eq (γ : CongruenceSubgroup.Gamma0 M) :
    (CohCarrier.gamma0Units M γ : ZMod M) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := rfl

theorem T_zpow_mem_GammaH (m : ℤ) : ModularGroup.T ^ m ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : ModularGroup.T ^ m ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T_zpow]
    simp
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T ^ m, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units_eq, Units.val_one]
    simp [ModularGroup.coe_T_zpow]
  rw [this]
  exact one_mem H

theorem mul_inv_mem_GammaH_of_div_mem (ρ τ : CongruenceSubgroup.Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ * (CohCarrier.gamma0Units M τ)⁻¹ ∈ H) :
    (ρ : SL(2, ℤ)) * ((τ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * τ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((τ : SL(2, ℤ)))⁻¹, (ρ * τ⁻¹).2⟩ : CongruenceSubgroup.Gamma0 M) =
      ρ * τ⁻¹ := rfl
  rw [e1, map_mul, map_inv]
  exact h

theorem slash_mapGL_mul_eq_of_div_mem (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ τ : CongruenceSubgroup.Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ * (CohCarrier.gamma0Units M τ)⁻¹ ∈ H) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((mapGL ℝ (τ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (mapGL ℝ ((ρ : SL(2, ℤ)) * ((τ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (mapGL ℝ (τ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH_of_div_mem ρ τ h))]

end GammaH

def ellUnit {ℓ : ℕ} (hℓ : ℓ.Prime) : ℝˣ := Units.mk0 (ℓ : ℝ) (by exact_mod_cast hℓ.ne_zero)

theorem val_ellUnit {ℓ : ℕ} (hℓ : ℓ.Prime) : ((ellUnit hℓ : ℝˣ) : ℝ) = ℓ := rfl

section Main

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')

omit [NeZero M'] in
include hℓ in

theorem finite_term
    (F' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (γ : GL (Fin 2) ℚ) (t : ℤ) (htq : (q : ℤ) ∣ t)
    (hγ : ((γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) :
    ((⇑F' ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q)⁻¹) ∣[(2 : ℤ)]
        Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ⁻¹) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q =
      ⇑F' ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (-((t / q : ℤ) : ZMod ℓ)).val := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  set s : ℤ := t / q with hs
  have hts : t = q * s := (Int.mul_ediv_cancel' htq).symm
  set x : ZMod ℓ := -((s : ℤ) : ZMod ℓ) with hx

  have hdvd : (ℓ : ℤ) ∣ (-s - (x.val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hx]
    ring
  set m : ℤ := (-s - (x.val : ℤ)) / ℓ with hm
  have hjm : (x.val : ℤ) + ℓ * m = -s := by
    rw [hm, Int.mul_ediv_cancel' hdvd]; ring
  have key := finite_identity hq hℓ.ne_zero γ t s hγ hts x.val m hjm (ModularGroup.T ^ m)
    (by rw [ModularGroup.coe_T_zpow]; rfl) (by rw [ModularGroup.coe_T_zpow]; rfl)
    (by rw [ModularGroup.coe_T_zpow]; rfl) (by rw [ModularGroup.coe_T_zpow]; rfl)
    (ellUnit hℓ) (val_ellUnit hℓ)
  have hconj := conj_eq_of_mul_eq _ _ _ _ key
  have hT : ⇑F' ∣[(2 : ℤ)] (mapGL ℝ (ModularGroup.T ^ m) : GL (Fin 2) ℝ) = ⇑F' :=
    SlashInvariantFormClass.slash_action_eq F' _ (Subgroup.mem_map_of_mem _ (T_zpow_mem_GammaH m))
  simp only [← SlashAction.slash_mul, Matrix.GeneralLinearGroup.map_inv]
  rw [hconj, SlashAction.slash_mul, SlashAction.slash_mul, hT, scalarGL_inv, slash_two_scalarGL]

def rho (σ' : SL(2, ℤ)) (b' c' : ℤ) (hb : σ' 0 1 = q * b') (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c') :
    SL(2, ℤ) :=
  ⟨!![σ' 1 1, -(ℓ * b'); -(q * q * M' * c'), σ' 0 0], by
    have hdet := det_eq σ'
    rw [Matrix.det_fin_two_of]
    rw [hb, hc] at hdet
    push_cast at hdet
    linear_combination hdet⟩

omit [Fact q.Prime] [NeZero M'] in
theorem rho_mem_Gamma0 (σ' : SL(2, ℤ)) (b' c' : ℤ) (hb : σ' 0 1 = q * b')
    (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c') :
    rho q M' (ℓ := ℓ) σ' b' c' hb hc ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M') := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show ((-(q * q * M' * c' : ℤ) : ℤ) : ZMod (q ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_neg.mpr ⟨c', by push_cast; ring⟩

omit [Fact q.Prime] [NeZero M'] in
theorem rho_apply_one_one (σ' : SL(2, ℤ)) (b' c' : ℤ) (hb : σ' 0 1 = q * b')
    (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c') :
    (rho q M' (ℓ := ℓ) σ' b' c' hb hc) 1 1 = σ' 0 0 := rfl

omit [NeZero M'] in
include hℓ in

theorem infinite_term
    (F' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (σ' : SL(2, ℤ)) (b' c' : ℤ) (hb : σ' 0 1 = q * b') (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c')
    (γinf : GL (Fin 2) ℚ)
    (hγinf : ((γinf : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    ((⇑F' ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q)⁻¹) ∣[(2 : ℤ)]
        Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γinf⁻¹) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q =
      ⇑F' ∣[(2 : ℤ)] ((mapGL ℝ (rho q M' σ' b' c' hb hc) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ) := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have key := infinite_identity hq hℓ.ne_zero M' σ' (rho q M' σ' b' c' hb hc) b' c' hb hc
    rfl rfl rfl rfl γinf hγinf (ellUnit hℓ) (val_ellUnit hℓ)
  have hconj := conj_eq_of_mul_eq _ _ _ _ key
  simp only [← SlashAction.slash_mul, Matrix.GeneralLinearGroup.map_inv]
  rw [hconj, SlashAction.slash_mul, scalarGL_inv, slash_two_scalarGL]

theorem gamma0Units_rho_div_mem (σ' : SL(2, ℤ)) (b' c' : ℤ) (hb : σ' 0 1 = q * b')
    (hc : σ' 1 0 = (q * M' * ℓ : ℕ) * c') (hσa : ((σ' 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q)) :
    CohCarrier.gamma0Units (q ^ 2 * M') ⟨rho q M' σ' b' c' hb hc, rho_mem_Gamma0 q M' σ' b' c' hb hc⟩ *
        (CohCarrier.gamma0Units (q ^ 2 * M')
          (gammaLift (q ^ 2 * M') (unitOfPrimeNotDvd hℓ hℓN)))⁻¹ ∈
      ModularCurve.FullLevel.levelH q M' := by
  rw [ModularCurve.FullLevel.mem_levelH_iff, map_mul, map_inv, mul_inv_eq_one]
  ext
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, val_gamma0Units_eq,
    ZMod.castHom_apply]
  rw [gammaLift_apply_11 hℓ hℓN, ZMod.cast_natCast (ModularCurve.FullLevel.dvd_sq_mul q M')]
  rw [rho_apply_one_one, ZMod.cast_intCast (ModularCurve.FullLevel.dvd_sq_mul q M'), hσa]

end Main

end FullLevelTransport
p2m_reactivate "P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.CuspForm.FullLevelTransport"

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.CuspForm.FullLevelTransport P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.CuspForm"

open CuspForm.FullLevelTransport in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')
    (t : Fin ℓ → ℤ) (htq : ∀ i, (q : ℤ) ∣ t i) (htℓ : Function.Injective fun i => ((t i : ℤ) : ZMod ℓ))
    (γ : Fin ℓ → GL (Fin 2) ℚ)
    (hγ : ∀ i, ((γ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t i : ℚ); 0, 1])
    (σ : SL(2, ℤ)) (hσb : (q : ℤ) ∣ σ 0 1) (hσc : ((q * M' * ℓ : ℕ) : ℤ) ∣ σ 1 0)
    (hσa : ((σ 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q))
    (γinf : GL (Fin 2) ℚ)
    (hγinf : ((γinf : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
    (f : UpperHalfPlane → ℂ)
    (F' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    ((∑ i, f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γ i)⁻¹) +
        f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γinf⁻¹) ∣[(2 : ℤ)]
        ModularForm.heckeDiagMatrix q =
      ⇑(CuspForm.heckeTLinH 2 hℓ hℓN F') := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  have hf : f = ⇑F' ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q)⁻¹ := by
    rw [hF', ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  subst hf

  have hT := CuspForm.stableT (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') 2 hℓ hℓN
  rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓN hT F']
  rw [SlashAction.add_slash, SlashAction.sum_slash]
  obtain ⟨b', hb⟩ := hσb
  obtain ⟨c', hc⟩ := hσc
  congr 1
  ·
    rw [Finset.sum_congr rfl fun i _ => finite_term q M' hℓ F' (γ i) (t i) (htq i) (hγ i)]

    have einj : Function.Injective fun i : Fin ℓ => -((t i / q : ℤ) : ZMod ℓ) := by
      intro i₁ i₂ h
      simp only [neg_inj] at h
      apply htℓ
      show ((t i₁ : ℤ) : ZMod ℓ) = ((t i₂ : ℤ) : ZMod ℓ)
      rw [← Int.mul_ediv_cancel' (htq i₁), ← Int.mul_ediv_cancel' (htq i₂)]
      push_cast
      rw [h]
    have ebij : Function.Bijective fun i : Fin ℓ => -((t i / q : ℤ) : ZMod ℓ) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨einj, by simp [ZMod.card]⟩
    rw [ModularForm.heckeU_def, sum_range_eq_sum_zmod]
    exact Fintype.sum_bijective _ ebij _ _ fun i => rfl
  ·
    rw [infinite_term q M' hℓ F' σ b' c' hb hc γinf hγinf]
    exact slash_mapGL_mul_eq_of_div_mem 2 (fun g hg => SlashInvariantFormClass.slash_action_eq F' g hg)
      ⟨rho q M' σ b' c' hb hc, rho_mem_Gamma0 q M' σ b' c' hb hc⟩
      (CuspForm.gammaLift (q ^ 2 * M') (CuspForm.unitOfPrimeNotDvd hℓ hℓN))
      (gamma0Units_rho_div_mem q M' hℓ hℓN σ b' c' hb hc hσa) _

end
p2m_reactivate "P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.CuspForm.FullLevelTransport P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.CuspForm"

end S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
end P2MW
export P2MW.S_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH (solution)
