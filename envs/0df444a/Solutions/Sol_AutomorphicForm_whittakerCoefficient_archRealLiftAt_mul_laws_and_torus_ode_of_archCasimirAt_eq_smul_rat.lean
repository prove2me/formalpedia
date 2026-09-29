-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4f2a1894-e8f4-5bb3-8c71-55bb1a6778fd

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.StandardAddChar MeasureTheory

noncomputable section

namespace P2Chi

abbrev hw : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace

abbrev eR : (Rat.infinitePlace).Completion ≃+* ℝ := ringEquivRealOfIsReal hw

theorem glInf_ext {x y : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ Rat.infinitePlace x = archComponent ℚ Rat.infinitePlace y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  funext v
  have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
  subst hv
  have := congrArg (fun m : GL (Fin 2) (Rat.infinitePlace).Completion =>
    (m : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion) i j) h
  exact this

theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt hw m) =
      archGLIncl ℚ Rat.infinitePlace (glEquivOfRingEquiv eR.symm m) :=
  glArch_adelicArchGLIncl ℚ _

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem archComponent_glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ (archRealGLAt hw m)) = glEquivOfRingEquiv eR.symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem unipotent_ratArchLine_eq (t : ℝ) :
    (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) : AdelicGL2 (𝓞 ℚ) ℚ) =
      archRealGLAt hw (unipotentGL2 t) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · apply glInf_ext
    rw [archComponent_glArch_archRealGLAt]
    ext i j
    rw [glEquivOfRingEquiv_apply_entry, archComponent_apply]
    show (adeleArch (𝓞 ℚ) ℚ) (((unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) :
        GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) Rat.infinitePlace =
      eR.symm (((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
    rw [adeleArch_apply]
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> rfl
  · rw [glFin_archRealGLAt]
    apply Units.ext
    apply Matrix.ext
    intro i j
    show (adeleFin (𝓞 ℚ) ℚ) (((unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) :
        GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    rw [adeleFin_apply]
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> rfl

theorem archRealGLAt_scalar_mul_comm (t : ℝˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) * g =
      g * archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul]
    apply glInf_ext
    rw [map_mul, map_mul, archComponent_glArch_archRealGLAt]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hsc : ((glEquivOfRingEquiv eR.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) t) :
        GL (Fin 2) (Rat.infinitePlace).Completion) : Matrix (Fin 2) (Fin 2) _) =
        (eR.symm (t : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion) := by
      ext i j
      rw [glEquivOfRingEquiv_apply_entry]
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
    rw [hsc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [map_mul, map_mul, glFin_archRealGLAt, one_mul, mul_one]

theorem adelicArchGLInclAt_map_scalar (t : ℝˣ) :
    adelicArchGLInclAt ℚ Rat.infinitePlace
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) =
      archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) := by
  rfl

theorem archRealLiftAt_of (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    archRealLiftAt hw (Matrix.of.symm x) = archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx) :=
  archRealLiftAt_of_det_ne_zero hw hx

theorem archRealLiftAt_coeGL (m : GL (Fin 2) ℝ) :
    archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) = archRealGLAt hw m := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [archRealLiftAt_of _ hm]
  congr 1
  exact Units.ext rfl

theorem mult_rat_infinitePlace : (Rat.infinitePlace).mult = 1 := by
  rw [NumberField.InfinitePlace.mult, if_pos hw]

theorem infTraceSum_ratArchLine (t : ℝ) : infTraceSum ℚ (ratArchLine t) = t := by
  unfold infTraceSum
  rw [Fintype.sum_subsingleton _ Rat.infinitePlace, mult_rat_infinitePlace, Nat.cast_one, one_mul,
    ratArchLine_apply, ← extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_re]
  show extensionEmbeddingOfIsReal hw ((ringEquivRealOfIsReal hw).symm t) = t
  rw [← ringEquivRealOfIsReal_apply hw]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply t

theorem psiArch_ratArchLine (t : ℝ) :
    psiArch (ratArchLine t) = Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, Fintype.prod_subsingleton _ Rat.infinitePlace,
    psiArchPlace_apply, ratArchLine_apply]
  congr 2
  have : extensionEmbeddingOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)
      ((ringEquivRealOfIsReal (isReal_rat_infinitePlace Rat.infinitePlace)).symm t) = t := by
    rw [← ringEquivRealOfIsReal_apply]
    exact (ringEquivRealOfIsReal hw).apply_symm_apply t
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this

theorem stdAddChar_ratArchLine (t : ℝ) :
    stdAddChar ℚ ((ratArchLine t, 0) : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  show (adelicTraceData ℚ).psiK _ = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  show psiArch ((adelicTraceData ℚ).traceInf (ratArchLine t)) * psiFin ((adelicTraceData ℚ).traceFin 0) = _
  rw [map_zero, AddChar.map_zero_eq_one, mul_one]
  show psiArch (traceInfHom ℚ (ratArchLine t)) = _
  rw [traceInfHom_apply, infTraceSum_ratArchLine, psiArch_ratArchLine]

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  unfold psiPadicFun
  set a : ℤ := (exists_pPow_approx x).choose
  set k : ℕ := (exists_pPow_approx x).choose_spec.choose
  have : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k) =
      ((-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

set_option synthInstance.maxHeartbeats 1600000 in
theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  rw [psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _

theorem norm_psiFin (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin x‖ = 1 := by
  show ‖∏ᶠ v, psiV v (x v)‖ = 1
  by_cases hfin : (Function.mulSupport fun v => psiV v (x v)).Finite
  · rw [finprod_eq_prod _ hfin, norm_prod]
    exact Finset.prod_eq_one fun v _ => norm_psiV v (x v)
  · rw [finprod_of_infinite_mulSupport hfin, norm_one]

theorem norm_psiArchPlace (v : InfinitePlace ℚ) (x : v.Completion) : ‖psiArchPlace v x‖ = 1 := by
  rw [psiArchPlace_apply]
  set r : ℝ := InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x
  rw [show (2 * (Real.pi : ℂ) * Complex.I) * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_psiArch (x : InfiniteAdeleRing ℚ) : ‖psiArch x‖ = 1 := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiArchPlace v (x v)

theorem norm_psiQ (x : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ x‖ = 1 := by
  rw [psiQ_apply, norm_mul, norm_psiArch, norm_psiFin, one_mul]

theorem norm_stdAddChar (x : AdeleRing (𝓞 ℚ) ℚ) : ‖stdAddChar ℚ x‖ = 1 := by
  show ‖(adelicTraceData ℚ).psiK x‖ = 1
  rw [AdelicTraceData.psiK_apply]
  exact norm_psiQ _

section Nu

open NumberField.TateGlobal NumberField.AdelicVolume

def nu (g : AdelicGL2 (𝓞 ℚ) ℚ) : ℝ := ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)

theorem nu_pos (g : AdelicGL2 (𝓞 ℚ) ℚ) : 0 < nu g := ideleNorm_pos _

theorem nu_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) : nu (g * h) = nu g * nu h := by
  simp only [nu, map_mul, ideleNorm_mul]

theorem norm_det_glEquivOfRingEquiv_symm (m : GL (Fin 2) ℝ) :
    ‖((glEquivOfRingEquiv eR.symm m : GL (Fin 2) (Rat.infinitePlace).Completion) :
        Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion).det‖ = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  have e : ((glEquivOfRingEquiv eR.symm m : GL (Fin 2) (Rat.infinitePlace).Completion) :
      Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion) =
      (eR.symm.toRingHom).mapMatrix ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [e, ← RingHom.map_det]
  have h := norm_ringEquivRealOfIsReal hw (eR.symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
  rw [RingEquiv.apply_symm_apply] at h
  rw [show (eR.symm.toRingHom) ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
    eR.symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det from rfl, ← h, Real.norm_eq_abs]

theorem archDetNorm_archRealGLAt (m : GL (Fin 2) ℝ) :
    archDetNorm Rat.infinitePlace (archRealGLAt hw m) = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  unfold archDetNorm
  rw [archComponent_glArch_archRealGLAt, norm_det_glEquivOfRingEquiv_symm]

theorem nu_archRealGLAt (m : GL (Fin 2) ℝ) :
    nu (archRealGLAt hw m) = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  unfold nu
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ (archRealGLAt hw m)
    (by rw [glFin_archRealGLAt]; exact Subgroup.one_mem _)]
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, archDetNorm_archRealGLAt, mult_rat_infinitePlace, pow_one]

theorem nu_unipotentGL2 (v : AdeleRing (𝓞 ℚ) ℚ) : nu (unipotentGL2 v) = 1 := by
  unfold nu
  have : Matrix.GeneralLinearGroup.det (unipotentGL2 v : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
    simp
  rw [this]
  unfold ideleNorm
  rw [map_one]
  rfl

end Nu

section Laws

variable (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (α : ℚ)

theorem whittakerCoefficient_central_mul (Z g : AdelicGL2 (𝓞 ℚ) ℚ) (c : ℂ)
    (hZ : ∀ v : AdeleRing (𝓞 ℚ) ℚ, unipotentGL2 v * Z = Z * unipotentGL2 v) (hφ : ∀ g', φ (Z * g') = c * φ g') :
    whittakerCoefficient ℚ pins ψ φ α (Z * g) = c * whittakerCoefficient ℚ pins ψ φ α g := by
  letI := pins.nS
  show (∫ v, φ (unipotentGL2 v * (Z * g)) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v)) ∂pins.ν) =
    c * ∫ v, φ (unipotentGL2 v * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v)) ∂pins.ν
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [← mul_assoc, hZ, mul_assoc, hφ, mul_assoc]

theorem whittakerCoefficient_mul_right (R g : AdelicGL2 (𝓞 ℚ) ℚ) (c : ℂ) (hφ : ∀ g', φ (g' * R) = c * φ g') :
    whittakerCoefficient ℚ pins ψ φ α (g * R) = c * whittakerCoefficient ℚ pins ψ φ α g := by
  letI := pins.nS
  show (∫ v, φ (unipotentGL2 v * (g * R)) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v)) ∂pins.ν) =
    c * ∫ v, φ (unipotentGL2 v * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v)) ∂pins.ν
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [← mul_assoc, hφ, mul_assoc]

theorem norm_whittakerCoefficient_le (g : AdelicGL2 (𝓞 ℚ) ℚ) (B : ℝ)
    (hprob : @IsProbabilityMeasure _ pins.nS pins.ν) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hB : ∀ v : AdeleRing (𝓞 ℚ) ℚ, ‖φ (unipotentGL2 v * g)‖ ≤ B) :
    ‖whittakerCoefficient ℚ pins ψ φ α g‖ ≤ B := by
  letI := pins.nS
  haveI := hprob
  show ‖∫ v, φ (unipotentGL2 v * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v)) ∂pins.ν‖ ≤ B
  have h := norm_integral_le_of_norm_le_const (μ := pins.ν) (C := B)
    (f := (fun v => φ (unipotentGL2 v * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * v))))
    (Filter.Eventually.of_forall fun v => by
      rw [norm_mul, hψ, mul_one]
      exact hB v)
  simpa using h

end Laws

section Mats

open LanglandsTunnell.Converse

theorem det_unip (t : ℝ) : (ArchR.unip t).det = 1 := by
  simp [ArchR.unip, Matrix.det_fin_two_of]

theorem unipotentGL2_real_coe (t : ℝ) : ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.unip t := rfl

theorem mkOfDetNeZero_unip_mul (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0)
    (h : (ArchR.unip t * x).det ≠ 0) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (ArchR.unip t * x) h =
      unipotentGL2 t * Matrix.GeneralLinearGroup.mkOfDetNeZero x hx :=
  Units.ext rfl

theorem mkOfDetNeZero_smul (t : ℝ) (ht : 0 < t) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0)
    (h : (t • x).det ≠ 0) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (t • x) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne') * Matrix.GeneralLinearGroup.mkOfDetNeZero x hx := by
  apply Units.ext
  show t • x = Matrix.diagonal (fun _ => t) * x
  rw [Matrix.smul_eq_diagonal_mul]

end Mats

end P2Chi

end

open P2Chi IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse NumberField.StandardAddChar MeasureTheory in

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (k : ℤ) (lam e ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (hk : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ)
    (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt Rat.isReal_infinitePlace) φ g‖ ≤ B)
    (hΩ : archCasimirAt Rat.isReal_infinitePlace φ = lam • φ)
    (hcent : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ Rat.infinitePlace (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₀ : glArch (𝓞 ℚ) ℚ g₀ = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun x =>
      whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1
        (archRealLiftAt Rat.isReal_infinitePlace (Matrix.of.symm x) * g₀)
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x) ∧
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x) ∧
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      DifferentiableOn ℝ (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * k : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0) ∧
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N) := by
  intro A
  have hψG : IsGlobalAddChar ℚ (stdAddChar ℚ) := isGlobalAddChar_stdAddChar ℚ
  have hA : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, A x = whittakerCoefficient ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) (stdAddChar ℚ) φ 1 (archRealLiftAt hw (Matrix.of.symm x) * g₀) := fun x => rfl

  have hleftβ : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g := by
    intro β g
    have : globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
      apply Units.ext
      ext i j
      show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (((unipotentGL2 β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
      fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]
    rw [← this]
    exact hleft _ g
  have hper : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) * g) = φ (unipotentGL2 u * g) := by
    intro g β u
    rw [unipotentGL2_add, mul_assoc, hleftβ]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro t x hx
    have hdet : (ArchR.unip t * x).det ≠ 0 := by
      rw [Matrix.det_mul, det_unip, one_mul]; exact hx
    rw [hA, hA, archRealLiftAt_of _ hdet, archRealLiftAt_of _ hx, mkOfDetNeZero_unip_mul t x hx hdet, map_mul,
      ← unipotent_ratArchLine_eq, mul_assoc,
      AutomorphicForm.whittakerCoefficient_unipotentGL2_mul ℚ D _ _ (stdAddChar ℚ) hψG.principalInvariant φ _
        (hper _) 1 (ratArchLine t, 0)]
    congr 1
    rw [map_one, one_mul, stdAddChar_ratArchLine]
    rfl
  ·
    intro t x ht hx
    have hdet : (t • x).det ≠ 0 := by
      rw [Matrix.det_smul, Fintype.card_fin]
      exact mul_ne_zero (pow_ne_zero _ ht.ne') hx
    rw [hA, hA, archRealLiftAt_of _ hdet, archRealLiftAt_of _ hx, mkOfDetNeZero_smul t ht x hx hdet, map_mul,
      mul_assoc]
    refine whittakerCoefficient_central_mul _ (stdAddChar ℚ) φ 1 _ _ (((t : ℂ)) ^ e)
      (fun v => (archRealGLAt_scalar_mul_comm (Units.mk0 t ht.ne') (unipotentGL2 v)).symm) fun g' => ?_
    rw [← adelicArchGLInclAt_map_scalar]
    exact hcent (Units.mk0 t ht.ne') ht g'
  ·
    intro r x
    have he' : ∀ y : ℝ, ‖eR.symm y‖ = ‖y‖ := by
      intro y
      have := norm_ringEquivRealOfIsReal hw (eR.symm y)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm

    let r' : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion := rowIsometrySubgroup₀Map eR.symm he' r
    have hr'val : (r' : GL (Fin 2) (Rat.infinitePlace).Completion) = glEquivOfRingEquiv eR.symm r := rfl
    have hback : rowIsometrySubgroup₀Map eR (norm_ringEquivRealOfIsReal hw) r' = r := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      show eR (eR.symm (((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) = _
      exact eR.apply_symm_apply _
    have hkr : ∀ g' : AdelicGL2 (𝓞 ℚ) ℚ, φ (g' * archRealGLAt hw (r : GL (Fin 2) ℝ)) =
        (archWeightCharℝ k r : ℂ) * φ g' := by
      intro g'
      have := hk r' g'
      rw [MonoidHom.comp_apply, hback] at this
      exact this
    rw [hA, hA, archRealLiftAt_coeGL, archRealLiftAt_coeGL, map_mul, mul_assoc,
      archRealGLAt_mul_comm_of_glArch_eq_one hw (r : GL (Fin 2) ℝ) hg₀, ← mul_assoc]
    exact whittakerCoefficient_mul_right _ (stdAddChar ℚ) φ 1 _ _ _ hkr
  ·
    intro ε hε

    have hg₀' : archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g₀) = 1 := by
      rw [hg₀, map_one]
    have hfun : (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) = fun y : ℝ =>
        whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ)) (stdAddChar ℚ) φ 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) := by
      funext y
      rw [hA, archRealLiftAt_mul_comm_of_glArch_eq_one hw _ hg₀]
    have hAg : ∀ y : ℝ, A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ)) (stdAddChar ℚ) φ 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) :=
      fun y => congrFun hfun y
    have hode := AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
      ℚ D Rat.infinitePlace hw k lam ν hν φ hφc hleftβ hsm (fun d => (hreg [d]).1) (fun d d' => (hreg [d, d']).1) hΩ hk
      g₀ hg₀' ε hε
    refine ⟨by rw [hfun]; exact hode.1, by rw [hfun]; exact hode.2.1,
      fun y hy => by rw [hfun, hAg]; exact hode.2.2 y hy, ?_⟩

    have hprob : @IsProbabilityMeasure _ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).nS
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ)).ν :=
      isProbabilityMeasure_productionPinsOf_ν ℚ D _ _ (adelicBox ℚ) (adelicAddHaar_adelicBox_pos ℚ).ne'
        (adelicAddHaar_adelicBox_lt_top ℚ).ne
    obtain ⟨B, hB⟩ := (hreg []).2 (nu g₀ / 2) (2 * nu g₀) (by have := nu_pos g₀; positivity)
      (by have := nu_pos g₀; linarith)
    refine ⟨B, 0, fun y hy => ?_⟩
    rw [Real.rpow_zero, mul_one, hAg]
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy0).ne'
    have hdet : (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det = ε := by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_assoc, mul_inv_cancel₀ hsq, mul_one]
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have hdet0 : (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
      rw [hdet]; exact hε0
    have hlift : archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) =
        archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet0) := archRealLiftAt_of _ hdet0
    refine norm_whittakerCoefficient_le _ (stdAddChar ℚ) φ 1 _ B hprob norm_stdAddChar fun v => ?_
    apply hB
    show nu (unipotentGL2 v * (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]))) ∈ _
    rw [nu_mul, nu_unipotentGL2, one_mul, nu_mul, hlift, nu_archRealGLAt]
    have habs : |((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet0 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 := by
      show |(!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det| = 1
      rw [hdet]
      rcases hε with rfl | rfl <;> norm_num
    rw [habs, mul_one]
    have := nu_pos g₀
    constructor <;> linarith

end S_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat (solution)
