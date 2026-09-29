-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ebd4e859-bc60-589b-bbd9-d8fb2464f3f1

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

noncomputable section

namespace P2M
namespace TorusStrip

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => HeightOneSpectrum.adicCompletion F v
local notation "Ov" => HeightOneSpectrum.adicCompletionIntegers F v

section Local

variable {F v}

theorem diagPi_mul_unipotentInt (piv : Ov) (hpiv0 : algebraMap Ov Kv piv ≠ 0) (b : Ov) :
    diagPi piv hpiv0 * unipotentInt Kv b = unipotentInt (R := Ov) Kv (piv * b) * diagPi piv hpiv0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagPi, coe_unipotentInt, coe_unipotentInt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul]

theorem diagPi_pow_mul_unipotentInt (piv : Ov) (hpiv0 : algebraMap Ov Kv piv ≠ 0) (e : ℕ) (b : Ov) :
    diagPi piv hpiv0 ^ e * unipotentInt Kv b = unipotentInt (R := Ov) Kv (piv ^ e * b) * diagPi piv hpiv0 ^ e := by
  induction e generalizing b with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, mul_assoc, diagPi_mul_unipotentInt piv hpiv0 b, ← mul_assoc, ih (piv * b), mul_assoc,
      pow_succ, ← mul_assoc (piv ^ e) piv b]

end Local

theorem eq_of_glArch_eq_of_glFin_eq' {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ((finComponent (𝓞 F) F w x : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))
      = (finAdeleEval (𝓞 F) F w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem eq_of_forall_finComponent_eq {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w x = finComponent (𝓞 F) F w y) : x = y := by
  apply Units.ext
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
  rw [← coe_finComponent, ← coe_finComponent, h w]

theorem mul_finEmbed_localEmbed_comm (g : AdelicGL2 (𝓞 F) F)
    (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) (m : GL (Fin 2) Kv) :
    g * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) * g := by
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_finEmbed]
    refine eq_of_forall_finComponent_eq F fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hg, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v m hw, one_mul, mul_one]

theorem mapMatrix_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    f.mapMatrix ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = ((unipotentGL2 (f x) : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem coe_glFin (x : AdelicGL2 (𝓞 F) F) :
    ((glFin (𝓞 F) F x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = (adeleFin (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply]

theorem coe_glArch (x : AdelicGL2 (𝓞 F) F) :
    ((glArch (𝓞 F) F x : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      = (adeleArch (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]

theorem unipotentInt_eq_unipotentGL2 (b : Ov) :
    unipotentInt (R := Ov) Kv b = unipotentGL2 (algebraMap Ov Kv b) := by
  apply Units.ext
  rw [coe_unipotentInt, unipotentGL2_coe]

theorem finEmbed_localEmbed_unipotentInt (b : Ov) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (unipotentInt (R := Ov) Kv b)) =
      unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt F v (algebraMap Ov Kv b)) := by
  set y : Kv := algebraMap Ov Kv b with hy
  have h1 : adeleArch (𝓞 F) F (NumberField.StandardAddChar.adeleSingleAt F v y) = 0 := rfl
  have h2 : adeleFin (𝓞 F) F (NumberField.StandardAddChar.adeleSingleAt F v y)
      = NumberField.StandardAddChar.finAdeleSingleAt F v y := rfl
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [glArch_finEmbed]
    apply Units.ext
    rw [coe_glArch, mapMatrix_unipotentGL2, h1, unipotentGL2_zero]
  · rw [glFin_finEmbed]
    refine eq_of_forall_finComponent_eq F fun w => ?_
    apply Units.ext
    rw [coe_finComponent F w (glFin (𝓞 F) F _), coe_glFin, mapMatrix_unipotentGL2, mapMatrix_unipotentGL2, h2,
      finAdeleEval_apply]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, NumberField.StandardAddChar.finAdeleSingleAt_apply_self,
        unipotentInt_eq_unipotentGL2]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v _ hw,
        NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F v y hw, unipotentGL2_zero]

theorem valued_coe_le_one (b : Ov) : Valued.v (algebraMap Ov Kv b) ≤ WithZero.exp (0 : ℤ) := by
  rw [WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 b.2

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (y : AdelicGL2 (𝓞 F) F) :
    y * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * y := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact ((Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun r' => Commute.all _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).eq).symm

theorem coe_GL_scalar {A : Type*} [CommRing A] (u : Aˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = Matrix.scalar (Fin 2) (u : A) := rfl

theorem mapMatrix_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    f.mapMatrix (Matrix.scalar (Fin 2) a) = Matrix.scalar (Fin 2) (f a) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem finEmbed_scalar (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finEmbed (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      centralScalar (𝓞 F) F (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) u) := by
  apply Units.ext
  rw [coe_finEmbed, coe_GL_scalar]
  change finMat (𝓞 F) F (Matrix.scalar (Fin 2) (u : FiniteAdeleRing (𝓞 F) F))
    = Matrix.scalar (Fin 2) (finIncl (𝓞 F) F (u : FiniteAdeleRing (𝓞 F) F))
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [mapMatrix_arch_finMat, mapMatrix_scalar, adeleArch_apply, finIncl_apply_fst, map_one]
  · rw [mapMatrix_fin_finMat, mapMatrix_scalar, adeleFin_apply, finIncl_apply_snd]

theorem localEmbed_diagPi_mul_localRepInf (piv : Ov) (hpiv0 : algebraMap Ov Kv piv ≠ 0) :
    localEmbed (𝓞 F) F v (diagPi piv hpiv0 * localRepInf piv hpiv0) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localUnit (𝓞 F) F v (Units.mk0 (algebraMap Ov Kv piv) hpiv0)) := by
  refine eq_of_forall_finComponent_eq F fun w => ?_
  apply Units.ext
  rw [coe_finComponent F w (Matrix.GeneralLinearGroup.scalar _ _), coe_GL_scalar, mapMatrix_scalar,
    finAdeleEval_apply]
  by_cases hw : w = v
  · subst hw
    rw [finComponent_localEmbed_self, localUnit_apply_self, Units.val_mul, coe_diagPi, coe_localRepInf,
      Units.val_mk0, Matrix.scalar_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  · rw [finComponent_localEmbed_of_ne (𝓞 F) F v _ hw, localUnit_apply_of_ne _ _ _ _ hw, Units.val_one, map_one]

theorem finEmbed_localEmbed_diagPi_mul_localRepInf (piv : Ov) (hpiv0 : algebraMap Ov Kv piv ≠ 0) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi piv hpiv0 * localRepInf piv hpiv0)) =
      centralScalar (𝓞 F) F (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
        (localUnit (𝓞 F) F v (Units.mk0 (algebraMap Ov Kv piv) hpiv0))) := by
  rw [localEmbed_diagPi_mul_localRepInf, finEmbed_scalar]

end P2M.TorusStrip

end

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2 P2M.TorusStrip in
theorem solution
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * x) = χ z * φ x)
    (g : AdelicGL2 (𝓞 F) F) (e : ℕ) :
    whittakerCoefficient F pins ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ (e + 1) * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))) =
      χ (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (localUnit (𝓞 F) F v (Units.mk0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0))) *
        whittakerCoefficient F pins ψ φ 1 (g * heckeGen (𝓞 F) F v ^ e) := by
  set z : (AdeleRing (𝓞 F) F)ˣ := Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
    (localUnit (𝓞 F) F v (Units.mk0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) with hz
  have hkey : heckeGen (𝓞 F) F v * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))
      = centralScalar (𝓞 F) F z := by
    rw [← hgen, ← map_mul, ← map_mul, finEmbed_localEmbed_diagPi_mul_localRepInf F v ϖ hϖ0]
  have hpt : g * heckeGen (𝓞 F) F v ^ (e + 1) * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))
      = g * heckeGen (𝓞 F) F v ^ e * centralScalar (𝓞 F) F z := by
    rw [pow_succ, ← mul_assoc g, mul_assoc (g * heckeGen (𝓞 F) F v ^ e), hkey]
  rw [hpt]
  letI := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc (unipotentGL2 x), mul_centralScalar_comm F z, hcent, mul_assoc]

end S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq (solution)
