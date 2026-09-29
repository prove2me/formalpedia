-- Prove2me | solution 1 for CohCarrier.pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/679134df-d5ee-5d56-b40d-57654ce32dbe

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodTransfer
import Definitions.Def_ModularCurve_CupPairing
import Theorems.Thm_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq
import Theorems.Thm_ModularCurve_CupPairing_pair_comp_eq_of_conjRel
import Theorems.Thm_ModularCurve_CupPairing_exists_isPrimitive
import Theorems.Thm_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "GammaHLower dvd_of_mem_GammaHLower conjLowerL heckeTlower coresAdd mem_Gamma0Upper gamma0Units GammaH mem_GammaH_iff H1 conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom diamondRaw conjLowerMat conjLowerMat_conjUpperMat frickeMat N_dvd_of_mem_GammaH coe_frickeHom frickeEquiv frickeEquiv_apply frickeH1 frickeH1_eq_comp"
namespace GammaHCup
p2m_open "CohCarrier"

section Generic

variable {G : Type*} [Group G]

theorem mem_map_subtype_iff {Γ : Subgroup G} {K : Subgroup Γ} {a : G} :
    a ∈ K.map Γ.subtype ↔ ∃ h : a ∈ Γ, (⟨a, h⟩ : Γ) ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨a, h⟩, hk, rfl⟩

scoped instance map_subtype_finiteIndex (Γ : Subgroup G) [Γ.FiniteIndex] (K : Subgroup Γ)
    [K.FiniteIndex] : (K.map Γ.subtype).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩

end Generic

section Swap

open ModularCurve.CupPairing ModularCurve.PDPairing

theorem pair_swap (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) :
    pair Γ ψ φ = - pair Γ φ ψ := by
  obtain ⟨h, hh⟩ := ModularCurve.CupPairing.exists_isPrimitive Γ φ ψ
  have hh' : IsPrimitive ψ φ (fun g => - h g) := by
    intro g g'
    dsimp only
    rw [hh, omega_swap]
    ring
  rw [ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive Γ φ ψ h hh,
    ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive Γ ψ φ _ hh']
  have : (fun g => - h g) = (-1 : ℚ) • h := by
    funext g
    simp
  rw [this, cuspSum_smul]
  ring

end Swap

section Level

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

theorem isCongruenceSubgroup_GammaH : IsCongruenceSubgroup (GammaH N H) := by
  refine ⟨N, NeZero.ne _, fun A hA => ?_⟩
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have h0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact h10
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have : gamma0Units N ⟨A, h0⟩ = 1 := by
    apply Units.ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]; exact one_mem H

scoped instance finiteIndex_GammaH : (GammaH N H).FiniteIndex :=
  (isCongruenceSubgroup_GammaH N H).finiteIndex

variable (q : ℕ) [NeZero q] {A : Type*} [AddCommGroup A]

theorem heckeT_eq_coresAdd (φ : H1 N H A) :
    heckeT N H q A φ =
      coresAdd (GammaHUpper N H q) (φ.comp (MonoidHom.toAdditive (conjL N H q))) :=
  rfl

theorem heckeTlower_eq_coresAdd (φ : H1 N H A) :
    heckeTlower N H q A φ =
      coresAdd (GammaHLower N H q) (φ.comp (MonoidHom.toAdditive (conjLowerL N H q))) :=
  rfl

abbrev GU : Subgroup SL(2, ℤ) := (GammaHUpper N H q).map (GammaH N H).subtype

abbrev GL' : Subgroup SL(2, ℤ) := (GammaHLower N H q).map (GammaH N H).subtype

variable {N H q}

theorem mem_GU_iff {A : SL(2, ℤ)} :
    A ∈ GU N H q ↔ A ∈ GammaH N H ∧ (q : ℤ) ∣ A 0 1 := by
  rw [mem_map_subtype_iff]
  constructor
  · rintro ⟨h, hk⟩
    refine ⟨h, ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper] at hk
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hk
  · rintro ⟨h, hd⟩
    refine ⟨h, ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd

theorem mem_GL_iff {A : SL(2, ℤ)} :
    A ∈ GL' N H q ↔ A ∈ GammaH N H ∧ ((q * N : ℕ) : ℤ) ∣ A 1 0 := by
  rw [mem_map_subtype_iff]
  constructor
  · rintro ⟨h, hk⟩
    refine ⟨h, ?_⟩
    rw [Subgroup.mem_subgroupOf, Gamma0_mem] at hk
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hk
  · rintro ⟨h, hd⟩
    refine ⟨h, ?_⟩
    rw [Subgroup.mem_subgroupOf, Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd

def toKU (A : GU N H q) : GammaHUpper N H q :=
  ⟨⟨(A : SL(2, ℤ)), (mem_map_subtype_iff.mp A.2).1⟩, (mem_map_subtype_iff.mp A.2).2⟩

def toKL (B : GL' N H q) : GammaHLower N H q :=
  ⟨⟨(B : SL(2, ℤ)), (mem_map_subtype_iff.mp B.2).1⟩, (mem_map_subtype_iff.mp B.2).2⟩

@[scoped simp] theorem coe_toKU (A : GU N H q) : ((toKU A : GammaH N H) : SL(2, ℤ)) = A := rfl
@[scoped simp] theorem coe_toKL (B : GL' N H q) : ((toKL B : GammaH N H) : SL(2, ℤ)) = B := rfl

theorem toKU_mk (k : GammaHUpper N H q) :
    toKU (⟨((k : GammaH N H) : SL(2, ℤ)), Subgroup.mem_map_of_mem (GammaH N H).subtype k.2⟩ :
      GU N H q) = k := rfl

theorem toKL_mk (k : GammaHLower N H q) :
    toKL (⟨((k : GammaH N H) : SL(2, ℤ)), Subgroup.mem_map_of_mem (GammaH N H).subtype k.2⟩ :
      GL' N H q) = k := rfl

@[scoped simp] theorem conjLowerMat_apply_01 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 0 1 = A 0 1 * d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_00 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 0 0 = A 0 0 := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_11 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 1 1 = A 1 1 := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_10 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 1 0 = A 1 0 / d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjUpperMat_apply_00 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 0 1) :
    (conjUpperMat d A h) 0 0 = A 0 0 := by
  simp [conjUpperMat]

@[scoped simp] theorem conjUpperMat_apply_01 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 0 1) :
    (conjUpperMat d A h) 0 1 = A 0 1 / d := by
  simp [conjUpperMat]

theorem conjUpperMat_conjLowerMat (d : ℕ) [NeZero d] (A : SL(2, ℤ)) (hc : (d : ℤ) ∣ A 1 0)
    (hb : (d : ℤ) ∣ (conjLowerMat d A hc) 0 1) : conjUpperMat d (conjLowerMat d A hc) hb = A := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, conjUpperMat, Int.ediv_mul_cancel hc, Int.mul_ediv_cancel _ hd]

theorem conjL_mem_GL (k : GammaHUpper N H q) :
    ((conjL N H q k : GammaH N H) : SL(2, ℤ)) ∈ GL' N H q := by
  refine mem_GL_iff.mpr ⟨(conjL N H q k).2, ?_⟩
  show ((q * N : ℕ) : ℤ) ∣ (conjUpperMat q (k : SL(2, ℤ)) (dvd_of_mem_GammaHUpper N H q k)) 1 0
  rw [conjUpperMat_apply_10]
  have hN : (N : ℤ) ∣ (k : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (mem_GammaH_iff.mp (k : GammaH N H).2).1)
  push_cast
  rw [mul_comm (q : ℤ)]
  exact mul_dvd_mul_right hN _

theorem conjLowerL_mem_GU (k : GammaHLower N H q) :
    ((conjLowerL N H q k : GammaH N H) : SL(2, ℤ)) ∈ GU N H q := by
  refine mem_GU_iff.mpr ⟨(conjLowerL N H q k).2, ?_⟩
  show (q : ℤ) ∣ (conjLowerMat q (k : SL(2, ℤ)) (dvd_of_mem_GammaHLower N H q k)) 0 1
  rw [conjLowerMat_apply_01]
  exact dvd_mul_left _ _

def fwd (A : GU N H q) : GL' N H q :=
  ⟨((conjL N H q (toKU A) : GammaH N H) : SL(2, ℤ)), conjL_mem_GL (toKU A)⟩

def bwd (B : GL' N H q) : GU N H q :=
  ⟨((conjLowerL N H q (toKL B) : GammaH N H) : SL(2, ℤ)), conjLowerL_mem_GU (toKL B)⟩

theorem coe_fwd (A : GU N H q) :
    ((fwd A : GL' N H q) : SL(2, ℤ)) = conjUpperMat q (A : SL(2, ℤ)) (mem_GU_iff.mp A.2).2 := rfl

theorem coe_bwd (B : GL' N H q) :
    ((bwd B : GU N H q) : SL(2, ℤ)) =
      conjLowerMat q (B : SL(2, ℤ)) (dvd_of_mem_GammaHLower N H q (toKL B)) := rfl

def congE : GU N H q ≃* GL' N H q where
  toFun := fwd
  invFun := bwd
  left_inv A := by
    apply Subtype.ext
    rw [coe_bwd]
    exact conjLowerMat_conjUpperMat q (A : SL(2, ℤ)) (mem_GU_iff.mp A.2).2 _
  right_inv B := by
    apply Subtype.ext
    rw [coe_fwd]
    exact conjUpperMat_conjLowerMat q (B : SL(2, ℤ)) (dvd_of_mem_GammaHLower N H q (toKL B)) _
  map_mul' A B := by
    apply Subtype.ext
    show ((conjL N H q (toKU (A * B)) : GammaH N H) : SL(2, ℤ)) =
      ((conjL N H q (toKU A) : GammaH N H) : SL(2, ℤ)) * ((conjL N H q (toKU B) : GammaH N H) : SL(2, ℤ))
    rw [← Subgroup.coe_mul, ← map_mul]
    rfl

theorem congE_apply (A : GU N H q) : congE A = fwd A := rfl
theorem congE_symm_apply (B : GL' N H q) : (congE (N := N) (H := H) (q := q)).symm B = bwd B := rfl

theorem trace_congE (A : GU N H q) :
    (((congE A : GL' N H q) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [congE_apply, coe_fwd, Matrix.trace_fin_two, Matrix.trace_fin_two, conjUpperMat_apply_00,
    conjUpperMat_apply_11]

theorem trace_congE_symm (B : GL' N H q) :
    ((((congE (N := N) (H := H) (q := q)).symm B : GU N H q) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [congE_symm_apply, coe_bwd, Matrix.trace_fin_two, Matrix.trace_fin_two, conjLowerMat_apply_00,
    conjLowerMat_apply_11]

def alphaGL (q : ℕ) [NeZero q] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (q : ℝ)]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne q])

theorem alphaGL_det_pos : 0 < ((alphaGL q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  show 0 < (!![(1 : ℝ), 0; 0, (q : ℝ)]).det
  rw [Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero, one_mul]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)

theorem conjRel_congE (A : GU N H q) :
    ModularCurve.Period.conjRel (alphaGL q) (A : SL(2, ℤ)) ((congE A : GL' N H q) : SL(2, ℤ)) := by
  have hb : (q : ℤ) ∣ (A : SL(2, ℤ)) 0 1 := (mem_GU_iff.mp A.2).2
  have hbq : (((A : SL(2, ℤ)) 0 1 / q : ℤ) : ℝ) * q = (((A : SL(2, ℤ)) 0 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hb
  unfold ModularCurve.Period.conjRel
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, congE_apply, coe_fwd]
  show !![(1 : ℝ), 0; 0, (q : ℝ)] * _ = _ * !![(1 : ℝ), 0; 0, (q : ℝ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, conjUpperMat, hbq, mul_comm]

theorem neg_one_mem_GU_iff : (-1 : SL(2, ℤ)) ∈ GU N H q ↔ (-1 : SL(2, ℤ)) ∈ GammaH N H := by
  refine ⟨fun h => Subgroup.map_subtype_le _ h, fun h => mem_GU_iff.mpr ⟨h, ?_⟩⟩
  have : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by simp
  rw [this]; exact dvd_zero _

theorem neg_one_mem_GL_iff : (-1 : SL(2, ℤ)) ∈ GL' N H q ↔ (-1 : SL(2, ℤ)) ∈ GammaH N H := by
  refine ⟨fun h => Subgroup.map_subtype_le _ h, fun h => mem_GL_iff.mpr ⟨h, ?_⟩⟩
  have : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  rw [this]; exact dvd_zero _

theorem mult_GU : ModularCurve.CupPairing.mult (GU N H q) = ModularCurve.CupPairing.mult (GammaH N H) := by
  unfold ModularCurve.CupPairing.mult
  by_cases h : (-1 : SL(2, ℤ)) ∈ GammaH N H
  · rw [if_pos h, if_pos (neg_one_mem_GU_iff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (neg_one_mem_GU_iff.mp h'))]

theorem mult_GL : ModularCurve.CupPairing.mult (GL' N H q) = ModularCurve.CupPairing.mult (GammaH N H) := by
  unfold ModularCurve.CupPairing.mult
  by_cases h : (-1 : SL(2, ℤ)) ∈ GammaH N H
  · rw [if_pos h, if_pos (neg_one_mem_GL_iff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (neg_one_mem_GL_iff.mp h'))]

def incU : GU N H q →* GammaH N H := Subgroup.inclusion (Subgroup.map_subtype_le _)
def incL : GL' N H q →* GammaH N H := Subgroup.inclusion (Subgroup.map_subtype_le _)

@[scoped simp] theorem coe_incU (A : GU N H q) : ((incU A : GammaH N H) : SL(2, ℤ)) = A := rfl
@[scoped simp] theorem coe_incL (B : GL' N H q) : ((incL B : GammaH N H) : SL(2, ℤ)) = B := rfl

end Level

section Diamond

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ}

def conjEquiv (σ : Gamma0 N) : GammaH N H ≃* GammaH N H where
  toFun := conjHom N H σ
  invFun := conjHom N H σ⁻¹
  left_inv γ := by
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inv, inv_inv]
    group
  right_inv γ := by
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inv, inv_inv]
    group
  map_mul' := map_mul _

theorem coe_conjEquiv (σ : Gamma0 N) (γ : GammaH N H) :
    ((conjEquiv σ γ : GammaH N H) : SL(2, ℤ)) = (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ :=
  rfl

theorem conjRel_conjEquiv (σ : Gamma0 N) (γ : GammaH N H) :
    ModularCurve.Period.conjRel (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ))) (γ : SL(2, ℤ))
      ((conjEquiv σ γ : GammaH N H) : SL(2, ℤ)) := by
  unfold ModularCurve.Period.conjRel
  rw [coe_conjEquiv, map_mul, map_mul, map_inv]
  group

theorem det_mapGL_pos (σ : SL(2, ℤ)) :
    0 < ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
  exact one_pos

theorem diamondRaw_eq_comp (σ : Gamma0 N) (φ : H1 N H ℚ) :
    diamondRaw N H ℚ σ φ = φ.comp (MonoidHom.toAdditive (conjEquiv σ).toMonoidHom) :=
  AddMonoidHom.ext fun _ => rfl

variable (N) in

def frickeGL [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (N : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne N])

theorem frickeGL_det_pos [NeZero N] :
    0 < ((frickeGL N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  show 0 < (!![(0 : ℝ), -1; (N : ℝ), 0]).det
  rw [Matrix.det_fin_two_of]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  linarith

theorem conjRel_frickeEquiv [NeZero N] (γ : GammaH N H) :
    ModularCurve.Period.conjRel (frickeGL N) (γ : SL(2, ℤ))
      ((frickeEquiv N H γ : GammaH N H) : SL(2, ℤ)) := by
  have hc : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := N_dvd_of_mem_GammaH N H γ
  have hcN : (N : ℝ) * (((γ : SL(2, ℤ)) 1 0 / N : ℤ) : ℝ) = (((γ : SL(2, ℤ)) 1 0 : ℤ) : ℝ) := by
    exact_mod_cast Int.mul_ediv_cancel' hc
  unfold ModularCurve.Period.conjRel
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, frickeEquiv_apply, coe_frickeHom]
  show !![(0 : ℝ), -1; (N : ℝ), 0] * _ = _ * !![(0 : ℝ), -1; (N : ℝ), 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frickeMat, hcN, mul_comm]

theorem frickeH1_eq_comp [NeZero N] (φ : H1 N H ℚ) :
    frickeH1 N H ℚ φ = φ.comp (MonoidHom.toAdditive (frickeEquiv N H).toMonoidHom) :=
  AddMonoidHom.ext fun _ => rfl

end Diamond

section Main

open ModularCurve.Period ModularCurve.CupPairing

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

theorem pair_heckeT (q : ℕ) [NeZero q] (φ ψ : H1 N H ℚ)
    (hφ : IsParabolicHom (GammaH N H) φ) (hψ : IsParabolicHom (GammaH N H) ψ) :
    pair (GammaH N H) (heckeT N H q ℚ φ) ψ = pair (GammaH N H) φ (heckeTlower N H q ℚ ψ) := by
  let e : GU N H q ≃* GL' N H q := congE

  let y' : Additive (GU N H q) →+ ℚ :=
    φ.comp (MonoidHom.toAdditive ((incL (N := N) (H := H) (q := q)).comp e.toMonoidHom))
  let xK : Additive (GU N H q) →+ ℚ := ψ.comp (MonoidHom.toAdditive (incU (N := N) (H := H) (q := q)))
  let xL : Additive (GL' N H q) →+ ℚ := φ.comp (MonoidHom.toAdditive (incL (N := N) (H := H) (q := q)))
  let w : Additive (GL' N H q) →+ ℚ :=
    ψ.comp (MonoidHom.toAdditive ((incU (N := N) (H := H) (q := q)).comp e.symm.toMonoidHom))
  have hy' : IsParabolicHom (GU N H q) y' := by
    intro A hA
    refine hφ _ ?_
    show ((((e A : GL' N H q) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
    rw [trace_congE]; exact hA
  have hxL : IsParabolicHom (GL' N H q) xL := fun B hB => hφ _ hB
  have hw : IsParabolicHom (GL' N H q) w := by
    intro B hB
    refine hψ _ ?_
    show ((((e.symm B : GU N H q) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
    rw [trace_congE_symm]; exact hB
  have hmΓ : mult (GammaH N H) ≠ 0 := mult_ne_zero _

  have h1 : pair (GammaH N H) ψ (heckeT N H q ℚ φ) = pair (GU N H q) xK y' := by
    have h := ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq (GammaH N H) (GammaHUpper N H q)
      ψ xK y' (φ.comp (MonoidHom.toAdditive (conjL N H q))) hψ hy' (fun _ => rfl) (fun _ => rfl)
    rw [mult_GU, ← heckeT_eq_coresAdd] at h
    exact mul_left_cancel₀ hmΓ h

  have h2 : pair (GU N H q) y' xK = pair (GL' N H q) xL w := by
    have hxe : y' = xL.comp (MonoidHom.toAdditive e.toMonoidHom) := AddMonoidHom.ext fun _ => rfl
    have hye : xK = w.comp (MonoidHom.toAdditive e.toMonoidHom) := by
      refine AddMonoidHom.ext fun a => ?_
      show ψ (Additive.ofMul (incU (Additive.toMul a))) =
        ψ (Additive.ofMul (incU (e.symm (e (Additive.toMul a)))))
      rw [e.symm_apply_apply]
    rw [hxe, hye]
    exact ModularCurve.CupPairing.pair_comp_eq_of_conjRel (GU N H q) (GL' N H q) (alphaGL q) e
      alphaGL_det_pos (fun A => conjRel_congE A) xL w hxL hw

  have h3 : pair (GammaH N H) φ (heckeTlower N H q ℚ ψ) = pair (GL' N H q) xL w := by
    have h := ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq (GammaH N H) (GammaHLower N H q)
      φ xL w (ψ.comp (MonoidHom.toAdditive (conjLowerL N H q))) hφ hw (fun _ => rfl) (fun _ => rfl)
    rw [mult_GL, ← heckeTlower_eq_coresAdd] at h
    exact mul_left_cancel₀ hmΓ h

  rw [pair_swap (GammaH N H) ψ, h1, ← pair_swap, h2, ← h3]

theorem pair_diamondRaw (σ : Gamma0 N) (φ ψ : H1 N H ℚ)
    (hφ : IsParabolicHom (GammaH N H) φ) (hψ : IsParabolicHom (GammaH N H) ψ) :
    pair (GammaH N H) (diamondRaw N H ℚ σ φ) (diamondRaw N H ℚ σ ψ) = pair (GammaH N H) φ ψ := by
  rw [diamondRaw_eq_comp, diamondRaw_eq_comp]
  exact ModularCurve.CupPairing.pair_comp_eq_of_conjRel (GammaH N H) (GammaH N H)
    (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ))) (conjEquiv σ) (det_mapGL_pos _)
    (fun γ => conjRel_conjEquiv σ γ) φ ψ hφ hψ

theorem pair_frickeH1 (φ ψ : H1 N H ℚ)
    (hφ : IsParabolicHom (GammaH N H) φ) (hψ : IsParabolicHom (GammaH N H) ψ) :
    pair (GammaH N H) (frickeH1 N H ℚ φ) (frickeH1 N H ℚ ψ) = pair (GammaH N H) φ ψ := by
  rw [frickeH1_eq_comp, frickeH1_eq_comp]
  exact ModularCurve.CupPairing.pair_comp_eq_of_conjRel (GammaH N H) (GammaH N H)
    (frickeGL N) (frickeEquiv N H) frickeGL_det_pos (fun γ => conjRel_frickeEquiv γ) φ ψ hφ hψ

end Main

end CohCarrier.GammaHCup
p2m_reactivate "P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.CohCarrier P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.CohCarrier.GammaHCup"
p2m_reactivate "P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.CohCarrier"

end
p2m_reactivate "P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.CohCarrier P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.CohCarrier.GammaHCup"

open CohCarrier.GammaHCup in
theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (φ ψ : CohCarrier.H1 N H ℚ)
    (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) φ)
    (hψ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) ψ) :
    (∀ (q : ℕ) [NeZero q],
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.heckeT N H q ℚ φ) ψ =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ (CohCarrier.heckeTlower N H q ℚ ψ)) ∧
    (∀ σ : CongruenceSubgroup.Gamma0 N,
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.diamondRaw N H ℚ σ φ)
          (CohCarrier.diamondRaw N H ℚ σ ψ) =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ) ∧
    ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.frickeH1 N H ℚ φ)
        (CohCarrier.frickeH1 N H ℚ ψ) =
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ :=
  ⟨fun q _ => pair_heckeT N H q φ ψ hφ hψ, fun σ => pair_diamondRaw N H σ φ ψ hφ hψ,
    pair_frickeH1 N H φ ψ hφ hψ⟩

end S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
end P2MW
export P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1 (solution)
