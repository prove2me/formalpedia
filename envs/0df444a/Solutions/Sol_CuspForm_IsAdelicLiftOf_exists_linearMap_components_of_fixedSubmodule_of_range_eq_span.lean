-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.exists_linearMap_components_of_fixedSubmodule_of_range_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ed07ad19-66c0-538f-a0b9-c07ba2304778

import Mathlib
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsAdelicLiftOf_eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.AdelicLevel AdelicDock

noncomputable section

namespace W7E3

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K]

def archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) : AdeleRing R K)

theorem mapMatrix_arch_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (adeleArch R K).mapMatrix (archMat R K g) = g := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]

theorem mapMatrix_fin_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (adeleFin R K).mapMatrix (archMat R K g) = 1 := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply]

theorem archMat_one : archMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_archMat, map_one])
    (by rw [mapMatrix_fin_archMat, map_one])

theorem archMat_mul (g h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    archMat R K (g * h) = archMat R K g * archMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_archMat, mapMatrix_arch_archMat, mapMatrix_arch_archMat])
    (by rw [map_mul, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mul_one])

def archEmbed : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := archMat R K g
      inv := archMat R K ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix _ _ _)
      val_inv := by rw [← archMat_mul, Units.mul_inv, archMat_one]
      inv_val := by rw [← archMat_mul, Units.inv_mul, archMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat_mul R K _ _)

@[scoped simp] theorem coe_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ((archEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = archMat R K g := rfl

theorem glArch_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) : glArch R K (archEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, coe_archEmbed]
  rfl

theorem glFin_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) : glFin R K (archEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, coe_archEmbed, Units.val_one]
  rfl

theorem ext_arch_fin {g h : GL (Fin 2) (AdeleRing R K)} (h₁ : glArch R K g = glArch R K h)
    (h₂ : glFin R K g = glFin R K h) : g = h := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq R K
  · refine Matrix.ext fun i j => ?_
    have e := congrFun (congrFun (congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
      (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    simpa [glArch_apply, RingHom.mapMatrix_apply, adeleArch_apply] using e
  · refine Matrix.ext fun i j => ?_
    have e := congrFun (congrFun (congrArg (fun x : GL (Fin 2) (FiniteAdeleRing R K) =>
      (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) h₂) i) j
    simpa [glFin_apply, RingHom.mapMatrix_apply, adeleFin_apply] using e

theorem archEmbed_glArch_mul_finEmbed_glFin (g : GL (Fin 2) (AdeleRing R K)) :
    archEmbed R K (glArch R K g) * finEmbed R K (glFin R K g) = g := by
  apply ext_arch_fin R K
  · rw [map_mul, glArch_archEmbed, glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_archEmbed, glFin_finEmbed, one_mul]

theorem archEmbed_mul_finEmbed_comm (a : GL (Fin 2) (InfiniteAdeleRing K)) (b : GL (Fin 2) (FiniteAdeleRing R K)) :
    archEmbed R K a * finEmbed R K b = finEmbed R K b * archEmbed R K a := by
  apply ext_arch_fin R K
  · rw [map_mul, map_mul, glArch_archEmbed, glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_archEmbed, glFin_finEmbed, one_mul, mul_one]

theorem eq_archEmbed_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing R K)} (hh : glFin R K h = 1) :
    h = archEmbed R K (glArch R K h) := by
  conv_lhs => rw [← archEmbed_glArch_mul_finEmbed_glFin R K h, hh, map_one, mul_one]

end Generic

section Rat

local notation "𝔸GL" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

noncomputable def realEquiv (w : InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)

noncomputable def realToInfAdele : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun w => (realEquiv w).symm.toRingHom

theorem realToInfAdele_apply (x : ℝ) (w : InfinitePlace ℚ) : realToInfAdele x w = (realEquiv w).symm x := rfl

noncomputable def realToArch : GL (Fin 2) ℝ →* 𝔸GL :=
  (archEmbed (𝓞 ℚ) ℚ).comp (Matrix.GeneralLinearGroup.map realToInfAdele)

theorem glFin_realToArch (M : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (realToArch M) = 1 := by
  rw [realToArch, MonoidHom.comp_apply, glFin_archEmbed]

theorem glArch_realToArch (M : GL (Fin 2) ℝ) :
    glArch (𝓞 ℚ) ℚ (realToArch M) = Matrix.GeneralLinearGroup.map realToInfAdele M := by
  rw [realToArch, MonoidHom.comp_apply, glArch_archEmbed]

theorem ratArchGL2_def (g : 𝔸GL) : LanglandsTunnell.ratArchGL2 g =
    Matrix.GeneralLinearGroup.map (realEquiv default).toRingHom (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) := rfl

theorem ratArchGL2_inv (g : 𝔸GL) : LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [ratArchGL2_def, ratArchGL2_def, map_inv, map_inv, map_inv]

theorem ratArchGL2_realToArch (M : GL (Fin 2) ℝ) : LanglandsTunnell.ratArchGL2 (realToArch M) = M := by
  rw [ratArchGL2_def, glArch_realToArch]
  ext i j
  simp [archComponent_apply, Matrix.GeneralLinearGroup.map_apply, realToInfAdele_apply]

theorem eq_realToArch_of_glFin_eq_one {h : 𝔸GL} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    h = realToArch (LanglandsTunnell.ratArchGL2 h) := by
  rw [eq_archEmbed_of_glFin_eq_one (𝓞 ℚ) ℚ hh, realToArch, MonoidHom.comp_apply]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  funext w
  have hw : w = default := Subsingleton.elim _ _
  subst hw
  rw [Matrix.GeneralLinearGroup.map_apply, realToInfAdele_apply, ratArchGL2_def,
    Matrix.GeneralLinearGroup.map_apply, archComponent_apply, glArch_archEmbed]
  simp

end Rat

end W7E3
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

end
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

noncomputable section

namespace Comp
p2m_open "Comp"

open NumberField UpperHalfPlane

local notation "𝔸GL" => AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ

def toMat (τ : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![τ.im, τ.re; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [τ.im_ne_zero])

theorem toMat_apply (τ : ℍ) (i j : Fin 2) : (toMat τ : Matrix (Fin 2) (Fin 2) ℝ) i j = !![τ.im, τ.re; 0, 1] i j := rfl

theorem det_toMat (τ : ℍ) : (toMat τ).det.val = τ.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det !![τ.im, τ.re; 0, 1] = τ.im
  rw [Matrix.det_fin_two_of]; ring

theorem det_toMat_pos (τ : ℍ) : 0 < (toMat τ).det.val := by
  rw [det_toMat]; exact τ.im_pos

theorem toMat_mem_GLPos (τ : ℍ) : toMat τ ∈ Matrix.GLPos (Fin 2) ℝ :=
  (Matrix.mem_glpos _).mpr (det_toMat_pos τ)

theorem denom_toMat (τ : ℍ) : denom (toMat τ) UpperHalfPlane.I = 1 := by
  simp [denom, toMat_apply]

theorem toMat_smul_I (τ : ℍ) : toMat τ • UpperHalfPlane.I = τ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_toMat_pos τ)]
  simp only [num, denom, toMat_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, UpperHalfPlane.coe_I, Complex.ofReal_zero, zero_mul, Complex.ofReal_one, zero_add, div_one]
  apply Complex.ext <;> simp

theorem slash_toMat_apply_I (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[(2 : ℤ)] toMat τ) UpperHalfPlane.I = (τ.im : ℂ) * F τ := by
  rw [ModularForm.slash_apply, toMat_smul_I, denom_toMat, det_toMat, one_zpow, mul_one,
    abs_of_pos τ.im_pos]
  have hσ : σ (toMat τ) = .refl ℝ ℂ := by
    unfold σ; rw [if_pos (det_toMat_pos τ)]
  rw [hσ]
  simp [mul_comm]

theorem eq_of_forall_slash_ratArchGL2_apply (F G : UpperHalfPlane → ℂ)
    (hFG : ∀ h : 𝔸GL, NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I =
          (G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  funext τ
  have h := hFG (W7E3.realToArch (toMat τ)) (W7E3.glFin_realToArch _)
    (by rw [W7E3.ratArchGL2_realToArch]; exact toMat_mem_GLPos τ)
  rw [W7E3.ratArchGL2_realToArch, slash_toMat_apply_I, slash_toMat_apply_I] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr τ.im_ne_zero) h

end Comp
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

end
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

namespace W7E3

variable (q : ℕ) [Fact q.Prime]

noncomputable abbrev diagQ (u : ℤ_[q]ˣ) : GL (Fin 2) ℚ_[q] :=
  NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u)

noncomputable abbrev diagZ (u : ℤ_[q]ˣ) : GL (Fin 2) ℤ_[q] := NumberField.AdelicLevel.diagOne u

theorem map_diagZ (u : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) (diagZ q u) = diagQ q u := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, NumberField.AdelicLevel.diagOne_coe_apply, diagZ, diagQ]
  fin_cases i <;> fin_cases j <;> simp

theorem map_toZMod_diagZ (u : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := q)) (diagZ q u) =
      CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, NumberField.AdelicLevel.diagOne_coe_apply, diagZ,
    CuspidalType.diagElem]
  fin_cases i <;> fin_cases j <;> simp

theorem map_gl2IntegralLift (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) (LocalNewvector.gl2IntegralLift q k) =
      (k : GL (Fin 2) ℚ_[q]) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact LocalNewvector.coe_gl2IntegralLift_apply q k i j

theorem map_toZMod_gl2IntegralLift (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) :
    Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := q)) (LocalNewvector.gl2IntegralLift q k) =
      LocalNewvector.gl2ReductionHom q k := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, LocalNewvector.gl2ReductionHom_apply]

theorem map_mapGL_padicInt (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) =
      Matrix.SpecialLinearGroup.mapGL ℚ_[q] γ := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL]

theorem map_toZMod_mapGL_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := q)) (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) :
        GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod q) := by
  simp [Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL]

theorem coe_GL_eq_mapGL (γ : SL(2, ℤ)) : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl

end W7E3
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

open scoped ModularForm

namespace Comp
p2m_open "Comp"

section
variable (q : ℕ) [Fact q.Prime] {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}

def IsComp (y : LocalNewvector.AdelicSpan Φ) (u : ℤ_[q]ˣ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
    NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        (LocalNewvector.AdelicSpan.toFn Φ y).toFn
            (h * AdelicDock.padicToAdelic q
              (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
          (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

variable {q}

theorem IsComp.unique {y : LocalNewvector.AdelicSpan Φ} {u : ℤ_[q]ˣ} {F G : UpperHalfPlane → ℂ}
    (hF : IsComp q y u F) (hG : IsComp q y u G) : F = G :=
  eq_of_forall_slash_ratArchGL2_apply F G fun h h1 h2 => (hF h h1 h2).symm.trans (hG h h1 h2)

theorem sigma_apply_of_mem_GLPos {A : GL (Fin 2) ℝ} (hA : A ∈ Matrix.GLPos (Fin 2) ℝ) (c : ℂ) :
    UpperHalfPlane.σ A c = c := by
  rw [Matrix.mem_glpos] at hA
  simp only [UpperHalfPlane.σ, if_pos hA, ContinuousAlgEquiv.refl_apply]

theorem IsComp.add {y y' : LocalNewvector.AdelicSpan Φ} {u : ℤ_[q]ˣ} {F F' : UpperHalfPlane → ℂ}
    (hF : IsComp q y u F) (hF' : IsComp q y' u F') : IsComp q (y + y') u (F + F') := by
  intro h h1 h2
  rw [SlashAction.add_slash, Pi.add_apply, ← hF h h1 h2, ← hF' h h1 h2]
  rfl

theorem IsComp.smul {y : LocalNewvector.AdelicSpan Φ} {u : ℤ_[q]ˣ} {F : UpperHalfPlane → ℂ}
    (hF : IsComp q y u F) (c : ℂ) : IsComp q (c • y) u (c • F) := by
  intro h h1 h2
  rw [ModularForm.smul_slash, Pi.smul_apply, sigma_apply_of_mem_GLPos h2, smul_eq_mul, ← hF h h1 h2]
  rfl

theorem IsComp.zero (u : ℤ_[q]ˣ) : IsComp q (0 : LocalNewvector.AdelicSpan Φ) u 0 := by
  intro h h1 h2
  rw [SlashAction.zero_slash, Pi.zero_apply]
  rfl

theorem IsComp.of_diagOne_smul {y : LocalNewvector.AdelicSpan Φ} {u : ℤ_[q]ˣ} {F : UpperHalfPlane → ℂ}
    (hF : IsComp q y u F) :
    IsComp q ((NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : GL (Fin 2) ℚ_[q]) • y) 1 F := by
  intro h h1 h2
  rw [← hF h h1 h2, LocalNewvector.AdelicSpan.padic_smul_def, LocalNewvector.AdelicSpan.toFn_smul,
    LocalNewvector.AdelicFnCarrier.toFn_smul, map_one, map_one, map_one, mul_one]

end
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

section FIXI

variable {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
  {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
  {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
  (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)

theorem map_mem_fixedSubmodule (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) :
    f (w : V) ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ) := by
  intro k hk
  rw [← hf, w.2 k hk]

theorem map_mem_span
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ)) (v : V) :
    f v ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) := by
  rw [← hfr]; exact LinearMap.mem_range_self f v

theorem eq_zero_of_forall_isComp_zero (hΦg : g.IsAdelicLiftOf Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
    (h0 : ∀ u : ℤ_[q]ˣ, IsComp q (f (w : V)) u 0) : w = 0 := by
  have hfw : f (w : V) = 0 := by
    refine CuspForm.IsAdelicLiftOf.eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
      q hΦg (f (w : V)) (map_mem_span q V f hfr _) (map_mem_fixedSubmodule q V f hf w) fun u h hh hpos => ?_
    rw [h0 u h hh hpos, SlashAction.zero_slash, Pi.zero_apply]
  have hw : (w : V) = 0 := hfi (by rw [hfw, map_zero])
  exact Subtype.ext hw

theorem mapGL_mem_gl2CongruenceSubgroup_zero (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℚ_[q] γ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff]
  constructor
  · intro i j
    rw [← W7E3.map_mapGL_padicInt, Matrix.GeneralLinearGroup.map_apply]
    exact PadicInt.norm_le_one _
  · intro i j
    rw [← map_inv, ← W7E3.map_mapGL_padicInt, Matrix.GeneralLinearGroup.map_apply]
    exact PadicInt.norm_le_one _

noncomputable def slToK0 (γ : SL(2, ℤ)) : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) :=
  ⟨Matrix.SpecialLinearGroup.mapGL ℚ_[q] γ, mapGL_mem_gl2CongruenceSubgroup_zero q γ⟩

theorem coe_slToK0 (γ : SL(2, ℤ)) : (slToK0 q γ : GL (Fin 2) ℚ_[q]) = Matrix.SpecialLinearGroup.mapGL ℚ_[q] γ := rfl

theorem gl2IntegralLift_slToK0 (γ : SL(2, ℤ)) :
    LocalNewvector.gl2IntegralLift q (slToK0 q γ) = Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  apply Subtype.ext
  show ((LocalNewvector.gl2IntegralLift q (slToK0 q γ) : GL (Fin 2) ℤ_[q]) i j : ℚ_[q]) = _
  rw [LocalNewvector.coe_gl2IntegralLift_apply, coe_slToK0]
  have := congrArg (fun m : GL (Fin 2) ℚ_[q] => (m : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j) (W7E3.map_mapGL_padicInt q γ)
  simp only [Matrix.GeneralLinearGroup.map_apply] at this
  exact this.symm

theorem det_gl2IntegralLift_slToK0 (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q (slToK0 q γ)) = 1 := by
  rw [gl2IntegralLift_slToK0, Matrix.SpecialLinearGroup.det_mapGL]

theorem gl2ReductionHom_slToK0 (γ : SL(2, ℤ)) :
    LocalNewvector.gl2ReductionHom q (slToK0 q γ) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [← W7E3.map_toZMod_gl2IntegralLift, gl2IntegralLift_slToK0, W7E3.map_toZMod_mapGL_apply]
  rfl

theorem diagElem_one : CuspidalType.diagElem q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [CuspidalType.diagElem_val]
  fin_cases i <;> fin_cases j <;> simp

theorem coe_mem_coe {Γ : Subgroup SL(2, ℤ)} {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) :
    ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨δ, hδ, rfl⟩

theorem isComp_one_rho_of_isComp_one (hqM' : ¬ q ∣ M') (hΦg : g.IsAdelicLiftOf Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
    (F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : IsComp q (f (w : V)) 1 ⇑F) :
    IsComp q (f ((LocalNewvector.gl2ReductionRep q V
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)) w :
          ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) : V)) 1
      ((⇑F) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by

  obtain ⟨γt, hγtM, hγtq⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)

  have hdet := det_gl2IntegralLift_slToK0 q γ
  have hγq : ∀ i j : Fin 2, (((γt : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom 1) *
          LocalNewvector.gl2ReductionHom q (slToK0 q γ) *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (1 * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q (slToK0 q γ)))))⁻¹ :
          CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j := by
    intro i j
    rw [hdet, mul_one, map_one, diagElem_one, one_mul, inv_one, mul_one, gl2ReductionHom_slToK0]
    have := congrArg (fun m : SL(2, ZMod q) => (m : Matrix (Fin 2) (Fin 2) (ZMod q)) i j) hγtq
    simpa [Matrix.SpecialLinearGroup.toGL] using this
  have hF' : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          (LocalNewvector.AdelicSpan.toFn Φ (f (w : V))).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom
                  (1 * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q (slToK0 q γ)))))) =
            ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
    intro h hh hp
    rw [hdet, mul_one]
    exact hF h hh hp
  have key := CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component q hΦg
    (f (w : V)) (map_mem_span q V f hfr _) (map_mem_fixedSubmodule q V f hf w) (slToK0 q γ) 1 γt hγtM hγq F hF'

  have hδq : γt⁻¹ * γ ∈ CongruenceSubgroup.Gamma q := by
    rw [← (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').2.1, map_mul, map_inv, hγtq,
      inv_mul_cancel]
  have hδ0 : γt⁻¹ * γ ∈ CongruenceSubgroup.Gamma0 M' := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) hγ
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hγtM).2.2.1
  have hδ : γt⁻¹ * γ ∈ (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) :=
    ⟨hδq, hδ0⟩
  have hslash : (⇑F) ∣[(2 : ℤ)] ((γt⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (⇑F) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [show γt⁻¹ = (γt⁻¹ * γ) * γ⁻¹ by group, W7E3.coe_GL_eq_mapGL, map_mul, SlashAction.slash_mul,
      ← W7E3.coe_GL_eq_mapGL, ← W7E3.coe_GL_eq_mapGL,
      SlashInvariantForm.slash_action_eqn F _ (coe_mem_coe hδ)]

  intro h hh hp
  have hρ : ((LocalNewvector.gl2ReductionRep q V
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)) w :
          ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) : V) =
      (slToK0 q γ : GL (Fin 2) ℚ_[q]) • (w : V) := by
    rw [← gl2ReductionHom_slToK0]
    exact LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply q V (slToK0 q γ) w
  rw [hρ, hf, LocalNewvector.AdelicSpan.padic_smul_def, LocalNewvector.AdelicSpan.toFn_smul,
    LocalNewvector.AdelicFnCarrier.toFn_smul, map_one, map_one, map_one, mul_one]
  have k1 := key h hh hp
  rw [map_one, map_one, one_mul] at k1
  rw [k1, hslash]

end FIXI
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

section Model

variable {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
  {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
  {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
  (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
  (hfi : Function.Injective f)
  (hfr : LinearMap.range f =
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))

local notation "Wq" => LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V
local notation "Γq" => (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ))

include hΦg hf hfr in

theorem exists_isComp (u : ℤ_[q]ˣ) (w : Wq) : ∃ F : CuspForm Γq 2, IsComp q (f (w : V)) u ⇑F :=
  CuspForm.IsAdelicLiftOf.exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
    q hΦg (f (w : V)) (map_mem_span q V f hfr (w : V)) (map_mem_fixedSubmodule q V f hf w) u

private noncomputable def _root_.Comp.comp (u : ℤ_[q]ˣ) (w : Wq) : CuspForm Γq 2 :=
  (exists_isComp q hΦg V f hf hfr u w).choose

p2m_export "Comp" "comp"
theorem isComp_comp (u : ℤ_[q]ˣ) (w : Wq) : IsComp q (f (w : V)) u ⇑(comp q hΦg V f hf hfr u w) :=
  (exists_isComp q hΦg V f hf hfr u w).choose_spec

theorem eq_comp_of_isComp {u : ℤ_[q]ˣ} {w : Wq} {F : CuspForm Γq 2} (hF : IsComp q (f (w : V)) u ⇑F) :
    F = comp q hΦg V f hf hfr u w :=
  DFunLike.coe_injective (hF.unique (isComp_comp q hΦg V f hf hfr u w))

noncomputable def Fc (u : ℤ_[q]ˣ) : Wq →ₗ[ℂ] CuspForm Γq 2 where
  toFun := comp q hΦg V f hf hfr u
  map_add' w w' := by
    symm
    apply eq_comp_of_isComp
    have h := (isComp_comp q hΦg V f hf hfr u w).add (isComp_comp q hΦg V f hf hfr u w')
    rw [← map_add] at h
    simpa only [Submodule.coe_add, CuspForm.coe_add] using h
  map_smul' c w := by
    symm
    apply eq_comp_of_isComp
    have h := (isComp_comp q hΦg V f hf hfr u w).smul c
    rw [← map_smul] at h
    simpa only [Submodule.coe_smul, RingHom.id_apply, CuspForm.coe_smul] using h

theorem Fc_apply (u : ℤ_[q]ˣ) (w : Wq) : Fc q hΦg V f hf hfr u w = comp q hΦg V f hf hfr u w := rfl

theorem diagOne_mem_K0 (u : ℤ_[q]ˣ) :
    (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : GL (Fin 2) ℚ_[q]) ∈
      FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [NumberField.AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [PadicInt.norm_le_one]
  · rw [← map_inv, NumberField.AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [PadicInt.norm_le_one]

theorem gl2ReductionHom_diagOne (u : ℤ_[q]ˣ) :
    LocalNewvector.gl2ReductionHom q ⟨_, diagOne_mem_K0 q u⟩ =
      CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [LocalNewvector.gl2ReductionHom_apply, CuspidalType.diagElem_val]
  have hlift : ((LocalNewvector.gl2IntegralLift q ⟨_, diagOne_mem_K0 q u⟩ : GL (Fin 2) ℤ_[q]) :
      Matrix (Fin 2) (Fin 2) ℤ_[q]) i j = Matrix.diagonal ![(u : ℤ_[q]), 1] i j := by
    apply PadicInt.ext
    rw [LocalNewvector.coe_gl2IntegralLift_apply]
    show (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) :
      Matrix (Fin 2) (Fin 2) ℚ_[q]) i j = _
    rw [NumberField.AdelicLevel.diagOne_coe_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      fin_cases i
      · simp [PadicInt.Coe.ringHom]
        rfl
      · simp
    · rw [if_neg hij, if_neg hij, PadicInt.coe_zero]
  rw [hlift, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    fin_cases i
    · simp
    · simp
  · rw [if_neg hij, map_zero]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp
    · simp
    · exact absurd rfl hij

include hf in

theorem map_rho_diagElem (u : ℤ_[q]ˣ) (w : Wq) :
    f ((LocalNewvector.gl2ReductionRep q V (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u)) w : Wq) : V) =
      (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : GL (Fin 2) ℚ_[q]) • f (w : V) := by
  rw [← gl2ReductionHom_diagOne q u, LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply, hf]

theorem Fc_one_rho_diagElem (u : ℤ_[q]ˣ) (w : Wq) :
    Fc q hΦg V f hf hfr 1 (LocalNewvector.gl2ReductionRep q V
        (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u)) w) = Fc q hΦg V f hf hfr u w := by
  rw [Fc_apply, Fc_apply]
  symm
  apply eq_comp_of_isComp
  rw [map_rho_diagElem q V f hf u w]
  exact (isComp_comp q hΦg V f hf hfr u w).of_diagOne_smul

end Model
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

end Comp
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

namespace Comp
p2m_open "Comp"
section Model2

variable {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
  {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
  {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
  (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
  (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
  (hfi : Function.Injective f)
  (hfr : LinearMap.range f =
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))

local notation "Wq" => LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V
local notation "Γq" => (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ))

include hfi in

theorem eq_zero_of_forall_Fc_eq_zero (w : Wq) (h0 : ∀ u : ℤ_[q]ˣ, Fc q hΦg V f hf hfr u w = 0) : w = 0 := by
  have hfw : f (w : V) = 0 := by
    refine CuspForm.IsAdelicLiftOf.eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
      q hΦg (f (w : V)) (map_mem_span q V f hfr (w : V)) (map_mem_fixedSubmodule q V f hf w) ?_
    intro u h h1 h2
    have hc := isComp_comp q hΦg V f hf hfr u w h h1 h2
    rw [← Fc_apply, h0 u, CuspForm.coe_zero, SlashAction.zero_slash, Pi.zero_apply] at hc
    exact hc
  have hw : (w : V) = 0 := hfi (by rw [hfw, map_zero])
  exact Subtype.ext hw

theorem coe_Fc_one_rho_gamma0 (hqM' : ¬ q ∣ M') (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (w : Wq) :
    ⇑(Fc q hΦg V f hf hfr 1 (LocalNewvector.gl2ReductionRep q V
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)) w)) =
      (⇑(Fc q hΦg V f hf hfr 1 w)) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [Fc_apply, Fc_apply]
  exact (isComp_comp q hΦg V f hf hfr 1 _).unique
    (isComp_one_rho_of_isComp_one q V f hqM' hΦg hf hfr γ hγ w (comp q hΦg V f hf hfr 1 w)
      (isComp_comp q hΦg V f hf hfr 1 w))

end Model2
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"
end Comp
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span.W7E3"

theorem solution
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime] (hqM' : ¬ q ∣ M')
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ)) :
    ∃ Fc : ℤ_[q]ˣ → (↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
        CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2),
      (∀ (u : ℤ_[q]ˣ) (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
          (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ (f (w : V))).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
              ((⇑(Fc u w)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) ∧
      (∀ (u : ℤ_[q]ˣ) (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) (G : UpperHalfPlane → ℂ),
        (∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
          NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ (f (w : V))).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
              ((G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)) →
        ⇑(Fc u w) = G) ∧
      (∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V), (∀ u : ℤ_[q]ˣ, Fc u w = 0) → w = 0) ∧
      (∀ (u : ℤ_[q]ˣ) (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
        Fc 1 (LocalNewvector.gl2ReductionRep q V
            (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u)) w) = Fc u w) ∧
      (∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
        ⇑(Fc 1 (LocalNewvector.gl2ReductionRep q V
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)) w)) =
          (⇑(Fc 1 w)) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  refine ⟨Comp.Fc q hΦg V f hf hfr, ?_, ?_, ?_, ?_, ?_⟩
  · intro u w h h1 h2
    exact Comp.isComp_comp q hΦg V f hf hfr u w h h1 h2
  · intro u w G hG
    exact (Comp.isComp_comp q hΦg V f hf hfr u w).unique hG
  · intro w h0
    exact Comp.eq_zero_of_forall_Fc_eq_zero q hΦg V f hf hfi hfr w h0
  · intro u w
    exact Comp.Fc_one_rho_diagElem q hΦg V f hf hfr u w
  · intro γ hγ w
    exact Comp.coe_Fc_one_rho_gamma0 q hΦg V f hf hfr hqM' γ hγ w

end S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span (solution)
