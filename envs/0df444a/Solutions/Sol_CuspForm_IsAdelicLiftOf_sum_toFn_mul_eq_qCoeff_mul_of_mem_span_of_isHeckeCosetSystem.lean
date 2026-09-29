-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c4df1929-92ef-5f8a-b860-6de087fd00b3

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_PadicHeckeCosetSystem
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem

set_option autoImplicit false

noncomputable section

namespace AdelicEigenRow

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped MatrixGroups ModularForm

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

theorem eq_finEmbed_glFin_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    u = finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) :=
  gl_ext_of_arch_fin (by rw [glArch_finEmbed, hu]) (by rw [glFin_finEmbed])

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finComponent (𝓞 ℚ) ℚ w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem glEq_of_forall_finComponent_eq {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : ∀ w : HeightOneSpectrum (𝓞 ℚ), finComponent (𝓞 ℚ) ℚ w g = finComponent (𝓞 ℚ) ℚ w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

theorem mul_comm_of_finComponent_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    {a b : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (ha : finComponent (𝓞 ℚ) ℚ v a = 1)
    (hb : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → finComponent (𝓞 ℚ) ℚ w b = 1) :
    a * b = b * a := by
  refine glEq_of_forall_finComponent_eq fun w => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [ha, one_mul, mul_one]
  · rw [hb w hw, mul_one, one_mul]

def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

theorem globalPoints_eq_archPart_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archPart γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archPart, inv_mul_cancel_right]

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

theorem padicPlace_ne_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p ≠ q) :
    padicPlace p ≠ padicPlace q := by
  intro heq
  have h' := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) heq
  simp only [padicPlace, Equiv.apply_symm_apply] at h'
  exact h h'

theorem exists_eq_padicPlace_of_ne {ℓ : ℕ} [Fact ℓ.Prime] {w : HeightOneSpectrum (𝓞 ℚ)}
    (hwℓ : w ≠ padicPlace ℓ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ≠ ℓ ∧ w = padicPlace p := by
  refine ⟨_, ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩, ?_, eq_padicPlace_natGenerator w⟩
  intro h
  apply hwℓ
  rw [eq_padicPlace_natGenerator w]
  exact congrArg (fun n : Nat.Primes => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm n)
    (Subtype.ext (by exact h) : (⟨Rat.HeightOneSpectrum.natGenerator w, Rat.HeightOneSpectrum.prime_natGenerator w⟩
      : Nat.Primes) = ⟨ℓ, Fact.out⟩)

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prime ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      Rat.ringOfIntegersEquiv.symm ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (Rat.HeightOneSpectrum.prime_natGenerator v))

theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

theorem absNorm_padicPlace (ℓ : ℕ) [Fact ℓ.Prime] : Ideal.absNorm (padicPlace ℓ).asIdeal = ℓ := by
  rw [asIdeal_eq_span_natGenerator, natGenerator_padicPlace, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
    Module.finrank_self, pow_one]

theorem algebraMap_apply_padicPlace (p : ℕ) [Fact p.Prime] (x : ℚ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) (padicPlace p) = padicRingEquiv p (x : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) (padicPlace p) = (x : (padicPlace p).adicCompletion ℚ) := by
    change ((finAdeleEval (𝓞 ℚ) ℚ (padicPlace p)).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) x = _
    exact eq_ratCast _ x
  rw [hL, map_ratCast]

theorem algebraMap_apply_mem_integers_of_norm_le (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : ‖(x : ℚ_[p])‖ ≤ 1) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) (padicPlace p) ∈ (padicPlace p).adicCompletionIntegers ℚ := by
  rw [algebraMap_apply_padicPlace]
  exact (norm_le_one_iff_mem p _).mp hx

theorem norm_natCast_prime_of_ne (p : ℕ) [hp : Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) :
    ‖(ℓ : ℚ_[p])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hp.out hℓ).mpr hpℓ)

theorem norm_intCast_div_natCast_le (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (n : ℤ) :
    ‖(((n : ℚ) / (ℓ : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  push_cast
  rw [norm_div, norm_natCast_prime_of_ne p hℓ hpℓ, div_one]
  exact Padic.norm_int_le_one n

section IntMat

theorem det_map_intCast {R : Type*} [CommRing R] (B : Matrix (Fin 2) (Fin 2) ℤ) :
    (B.map (Int.cast : ℤ → R)).det = (B.det : R) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply]
  push_cast
  ring

theorem det_map_ratCast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  rw [det_map_intCast, hB]; exact_mod_cast hℓ.ne_zero

theorem det_map_padicCast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ)
    (p : ℕ) [Fact p.Prime] : (B.map (Int.cast : ℤ → ℚ_[p])).det ≠ 0 := by
  rw [det_map_intCast, hB]; exact_mod_cast hℓ.ne_zero

def βQ {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_map_ratCast_ne_zero hℓ B hB)

def βP {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (p : ℕ) [Fact p.Prime] :
    GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_map_padicCast_ne_zero hℓ B hB p)

theorem coe_βQ_apply {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (i j : Fin 2) :
    ((βQ hℓ B hB : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = (B i j : ℚ) := rfl

theorem coe_βQ {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    ((βQ hℓ B hB : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ) := rfl

theorem coe_βP_apply {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (p : ℕ) [Fact p.Prime]
    (i j : Fin 2) : ((βP hℓ B hB p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j = (B i j : ℚ_[p]) := rfl

theorem coe_βP {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (p : ℕ) [Fact p.Prime] :
    ((βP hℓ B hB p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = B.map (Int.cast : ℤ → ℚ_[p]) := rfl

def βinvMat (ℓ : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(B 1 1 : ℚ) / (ℓ : ℚ), -(B 0 1 : ℚ) / (ℓ : ℚ); -(B 1 0 : ℚ) / (ℓ : ℚ), (B 0 0 : ℚ) / (ℓ : ℚ)]

theorem coe_βQ_mul_βinvMat {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    ((βQ hℓ B hB : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * βinvMat ℓ B = 1 := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hℓinv : (ℓ : ℚ)⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ0
  have hdet : (B 0 0 : ℚ) * (B 1 1 : ℚ) - (B 0 1 : ℚ) * (B 1 0 : ℚ) = ℓ := by
    have := congrArg (Int.cast : ℤ → ℚ) hB
    rw [Matrix.det_fin_two] at this
    push_cast at this
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, βinvMat, coe_βQ_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (ℓ : ℚ)⁻¹ * hdet + hℓinv
  · ring
  · ring
  · linear_combination (ℓ : ℚ)⁻¹ * hdet + hℓinv

theorem coe_βQ_inv {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    (((βQ hℓ B hB)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = βinvMat ℓ B := by
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv (coe_βQ_mul_βinvMat hℓ B hB)]

theorem βinvMat_apply_eq (ℓ : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    ∃ n : ℤ, βinvMat ℓ B i j = ((n : ℚ) / (ℓ : ℚ) : ℚ) := by
  fin_cases i <;> fin_cases j
  · exact ⟨B 1 1, by simp [βinvMat]⟩
  · exact ⟨-B 0 1, by simp [βinvMat, neg_div]⟩
  · exact ⟨-B 1 0, by simp [βinvMat, neg_div]⟩
  · exact ⟨B 0 0, by simp [βinvMat]⟩

theorem βinvMat_one_zero_of_eq_zero (ℓ : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) (h10 : B 1 0 = 0) :
    βinvMat ℓ B 1 0 = 0 := by
  simp [βinvMat, h10]

theorem finComponent_glFin_globalPoints_βQ {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ)
    (p : ℕ) [Fact p.Prime] :
    finComponent (𝓞 ℚ) ℚ (padicPlace p) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (βQ hℓ B hB)))
      = padicGL p (βP hℓ B hB p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, glFin_globalPoints_apply, coe_βQ_apply, padicGL_apply, coe_βP_apply,
    algebraMap_apply_padicPlace, Rat.cast_intCast]

theorem det_map_βQ {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓ B hB)).det : ℝ) = (ℓ : ℝ) := by
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply,
    coe_βQ, det_map_intCast, hB, map_intCast, Int.cast_natCast]

theorem map_βQ_inv_mem_GLPos {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓ B hB)⁻¹ ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [map_inv]
  refine Subgroup.inv_mem _ ?_
  rw [Matrix.mem_glpos, det_map_βQ]
  exact_mod_cast hℓ.pos

theorem coe_map_βQ_inv_apply {ℓ : ℕ} (hℓ : ℓ.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓ B hB)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = ((βinvMat ℓ B i j : ℚ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.map_apply, coe_βQ_inv, Rat.coe_castHom]

end IntMat

section Away

variable (ℓ : ℕ) [hℓF : Fact ℓ.Prime]

def GB (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (βQ hℓF.out B hB))

def WB (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  GB ℓ B hB * (padicToFinAdelic ℓ (βP hℓF.out B hB ℓ))⁻¹

theorem WB_def (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    WB ℓ B hB = GB ℓ B hB * (padicToFinAdelic ℓ (βP hℓF.out B hB ℓ))⁻¹ := rfl

theorem finComponent_GB_ℓ (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (GB ℓ B hB) = padicGL ℓ (βP hℓF.out B hB ℓ) :=
  finComponent_glFin_globalPoints_βQ hℓF.out B hB ℓ

theorem finComponent_WB_ℓ (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) :
    finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (WB ℓ B hB) = 1 := by
  rw [WB_def, map_mul, map_inv, finComponent_GB_ℓ, finComponent_padicToFinAdelic_self, mul_inv_cancel]

theorem finComponent_WB_of_ne (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hwℓ : w ≠ padicPlace ℓ) :
    finComponent (𝓞 ℚ) ℚ w (WB ℓ B hB) = finComponent (𝓞 ℚ) ℚ w (GB ℓ B hB) := by
  rw [WB_def, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne ℓ _ hwℓ, inv_one, mul_one]

theorem isLevelZero_entries_one (w : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) :
    (∀ a b : Fin 2, ((1 : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) a b
      ∈ w.adicCompletionIntegers ℚ) ∧
    Valued.v (((1 : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) 1 0)
      ≤ idealBound (𝓞 ℚ) N w := by
  refine ⟨fun a b => ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le'

theorem isLevelZeroMatrix_of_components (N : Ideal (𝓞 ℚ)) (X : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (m : Matrix (Fin 2) (Fin 2) ℚ)
    (hXℓ : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) X = 1)
    (hoff : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace ℓ → ∀ i j : Fin 2,
      ((finComponent (𝓞 ℚ) ℚ w X : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
        = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (m i j)) w)
    (hint : ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → ∀ i j : Fin 2, ‖(m i j : ℚ_[p])‖ ≤ 1)
    (hll : m 1 0 = 0) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ N
      ((X : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hentry : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2),
      ((X : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w
        = ((finComponent (𝓞 ℚ) ℚ w X : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _) i j :=
    fun w i j => (finComponent_apply (𝓞 ℚ) ℚ w X i j).symm
  refine ⟨fun i j w => ?_, fun w => ?_⟩
  · rw [hentry]
    by_cases hwℓ : w = padicPlace ℓ
    · subst hwℓ; rw [hXℓ]; exact (isLevelZero_entries_one _ N).1 i j
    obtain ⟨p, hp, hpℓ, rfl⟩ := exists_eq_padicPlace_of_ne hwℓ
    rw [hoff _ hwℓ]
    exact algebraMap_apply_mem_integers_of_norm_le p (hint p hpℓ i j)
  · rw [hentry]
    by_cases hwℓ : w = padicPlace ℓ
    · subst hwℓ; rw [hXℓ]; exact (isLevelZero_entries_one _ N).2
    rw [hoff _ hwℓ, hll, map_zero]
    change Valued.v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w) ≤ _
    rw [coe_zero_apply, map_zero]
    exact zero_le'

theorem WB_mem_finiteLevelZero (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (h10 : B 1 0 = 0)
    (N : Ideal (𝓞 ℚ)) : WB ℓ B hB ∈ finiteLevelZero (𝓞 ℚ) ℚ N := by
  have hℓ : ℓ.Prime := hℓF.out
  refine mem_finiteLevelZero_iff.mpr ⟨?_, ?_⟩
  · refine isLevelZeroMatrix_of_components ℓ N _ (fun i j => (B i j : ℚ)) (finComponent_WB_ℓ ℓ B hB)
      (fun w hwℓ i j => ?_) (fun p _ _ i j => ?_) (by simp [h10])
    · rw [finComponent_WB_of_ne ℓ B hB hwℓ, GB, finComponent_apply, glFin_globalPoints_apply, coe_βQ_apply]
    · rw [Rat.cast_intCast]; exact Padic.norm_int_le_one _
  · refine isLevelZeroMatrix_of_components ℓ N _ (βinvMat ℓ B) ?_ (fun w hwℓ i j => ?_) (fun p _ hpℓ i j => ?_)
      (βinvMat_one_zero_of_eq_zero ℓ B h10)
    · rw [map_inv, finComponent_WB_ℓ ℓ B hB, inv_one]
    · have hGinv : (GB ℓ B hB)⁻¹ = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (βQ hℓF.out B hB)⁻¹) := by
        rw [GB, map_inv, map_inv]
      rw [map_inv, finComponent_WB_of_ne ℓ B hB hwℓ, ← map_inv, hGinv, finComponent_apply,
        glFin_globalPoints_apply, coe_βQ_inv]
    · obtain ⟨n, hn⟩ := βinvMat_apply_eq ℓ B i j
      rw [hn]
      exact norm_intCast_div_natCast_le p hℓ hpℓ n

end Away

section Invariance

variable {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem padicToFinAdelic_mem_finiteLevelOne_of_mem_integralSubgroup (hN : N ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) {k : GL (Fin 2) ℚ_[ℓ]} (hk : k ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ]) :
    padicToFinAdelic ℓ k ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := by
  obtain ⟨y0, hy0⟩ := hk
  rw [padicToFinAdelic_apply, localEmbed_mem_finiteLevelOne_iff]
  exact padicGL_mem_localLevelOne ℓ hN (by rw [Nat.factorization_eq_zero_of_not_dvd hℓN]) (n := 0)
    ⟨y0, hy0, by simp, by simp⟩

theorem apply_mul_of_mem_levelOne_inf (hΦg : g.IsAdelicLiftOf Φ) (x : AdelicGL2 (𝓞 ℚ) ℚ)
    {u : AdelicGL2 (𝓞 ℚ) ℚ} (hu : u ∈ levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ) :
    Φ (x * u) = Φ x := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  rw [eq_finEmbed_glFin_of_glArch_eq_one ((mem_finiteAdelicGL2Subgroup_iff ℚ u).mp hu2)]
  exact hΦg.level_inv _ (mem_levelOne_iff.mp hu1) x

theorem finEmbed_mem_levelOne_inf {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    finEmbed (𝓞 ℚ) ℚ u ∈ levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ :=
  Subgroup.mem_inf.mpr ⟨(finEmbed_mem_levelOne_iff (𝓞 ℚ) ℚ u).mpr hu,
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_finEmbed (𝓞 ℚ) ℚ u)⟩

end Invariance

section PerCoset

variable {N : ℕ} (ℓ : ℕ) [hℓF : Fact ℓ.Prime]
  {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem apply_mul_padicToAdelic_eq_slash (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) (hΦg : g.IsAdelicLiftOf Φ)
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = ℓ) (h10 : B 1 0 = 0)
    (r : GL (Fin 2) ℚ_[ℓ]) (hr : (βP hℓF.out B hB ℓ)⁻¹ * r ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
    (h : AdelicGL2 (𝓞 ℚ) ℚ) (hh : glFin (𝓞 ℚ) ℚ h = 1) (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    Φ (h * padicToAdelic ℓ r) =
      (((⇑g) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓF.out B hB)⁻¹) ∣[(2 : ℤ)]
        LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by

  set β : GL (Fin 2) ℚ := βQ hℓF.out B hB with hβ
  set bL : GL (Fin 2) ℚ_[ℓ] := βP hℓF.out B hB ℓ with hbL
  obtain ⟨G, hG⟩ : ∃ G : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ), G = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ β) :=
    ⟨_, rfl⟩
  have hGB : GB ℓ B hB = G := by rw [hG]; rfl
  set W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := WB ℓ B hB with hW
  set k : GL (Fin 2) ℚ_[ℓ] := bL⁻¹ * r with hk
  set A : AdelicGL2 (𝓞 ℚ) ℚ := (archPart β)⁻¹ * h with hA
  set T : AdelicGL2 (𝓞 ℚ) ℚ := finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic ℓ k * W⁻¹) with hT
  have hkK : k ∈ LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ] := hr

  have hGℓ : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) G = padicGL ℓ bL := by
    rw [hG]; exact finComponent_glFin_globalPoints_βQ hℓF.out B hB ℓ
  have hWℓ : finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) W = 1 := finComponent_WB_ℓ ℓ B hB
  have hWw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace ℓ →
      finComponent (𝓞 ℚ) ℚ w W = finComponent (𝓞 ℚ) ℚ w G := fun w hwℓ => by
    rw [← hGB]; exact finComponent_WB_of_ne ℓ B hB hwℓ
  have hWlev : W ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := WB_mem_finiteLevelZero ℓ B hB h10 _

  have hfinId : G * (padicToFinAdelic ℓ k * W⁻¹) = padicToFinAdelic ℓ r := by
    refine glEq_of_forall_finComponent_eq fun w => ?_
    by_cases hwℓ : w = padicPlace ℓ
    · subst hwℓ
      simp only [map_mul, map_inv, hGℓ, hWℓ, finComponent_padicToFinAdelic_self, inv_one, mul_one]
      rw [← map_mul, hk, mul_inv_cancel_left]
    · simp only [map_mul, map_inv, finComponent_padicToFinAdelic_of_ne ℓ _ hwℓ, hWw w hwℓ, one_mul,
        mul_inv_cancel]

  have hAfin : glFin (𝓞 ℚ) ℚ A = 1 := by
    rw [hA, map_mul, map_inv, glFin_archPart, inv_one, one_mul, hh]
  have hcomm : finEmbed (𝓞 ℚ) ℚ G * A = A * finEmbed (𝓞 ℚ) ℚ G := finEmbed_mul_comm_of_glFin_eq_one hAfin G
  have hEq : h * padicToAdelic ℓ r = globalPoints (𝓞 ℚ) ℚ β * (A * T) := by
    symm
    calc globalPoints (𝓞 ℚ) ℚ β * (A * T)
        = archPart β * (finEmbed (𝓞 ℚ) ℚ G * A) * T := by
          rw [globalPoints_eq_archPart_mul β, ← hG]; simp only [mul_assoc]
      _ = archPart β * (A * finEmbed (𝓞 ℚ) ℚ G) * T := by rw [hcomm]
      _ = h * (finEmbed (𝓞 ℚ) ℚ G * T) := by rw [hA]; simp only [mul_assoc, mul_inv_cancel_left]
      _ = h * finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic ℓ r) := by
          rw [hT, ← map_mul, hfinId]
      _ = h * padicToAdelic ℓ r := by rw [padicToAdelic_apply]
  have hT' : A * T = A * finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic ℓ k) * finEmbed (𝓞 ℚ) ℚ W⁻¹ := by
    simp only [hT, map_mul, map_inv, mul_assoc]

  have hAarch : LanglandsTunnell.ratArchGL2 A
      = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) β⁻¹ * LanglandsTunnell.ratArchGL2 h := by
    rw [hA, ratArch_mul, ratArch_inv, ratArch_archPart, map_inv]
  have hApos : LanglandsTunnell.ratArchGL2 A ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hAarch]
    exact Subgroup.mul_mem _ (map_βQ_inv_mem_GLPos hℓF.out B hB) hpos

  have hklev : padicToFinAdelic ℓ k ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) :=
    padicToFinAdelic_mem_finiteLevelOne_of_mem_integralSubgroup hN ℓ hℓN hkK
  rw [hEq, hΦg.left_inv, hT', hΦg.levelZero_inv hN _ (Subgroup.inv_mem _ hWlev), hΦg.level_inv _ hklev,
    hΦg.apply_eq A hAfin hApos, hAarch, SlashAction.slash_mul]

end PerCoset

section Reps

open LocalGL2 HeckeIntegralSeam

variable (ℓ : ℕ) [hℓF : Fact ℓ.Prime]

def Bsome (c : ZMod ℓ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), -(((-c).val : ℕ) : ℤ); 0, 1]

def Bnone : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (ℓ : ℤ)]

theorem det_Bsome (c : ZMod ℓ) : (Bsome ℓ c).det = ℓ := by
  simp [Bsome, Matrix.det_fin_two_of]

omit hℓF in
theorem det_Bnone : (Bnone ℓ).det = ℓ := by
  simp [Bnone, Matrix.det_fin_two_of]

theorem Bsome_one_zero (c : ZMod ℓ) : Bsome ℓ c 1 0 = 0 := by simp [Bsome]

omit hℓF in
theorem Bnone_one_zero : Bnone ℓ 1 0 = 0 := by simp [Bnone]

theorem βP_Bsome_inv_mul_padicHeckeRep_mem (c : ZMod ℓ) :
    (βP hℓF.out (Bsome ℓ c) (det_Bsome ℓ c) ℓ)⁻¹ * padicHeckeRep ℓ (some c)
      ∈ integralSubgroup ℤ_[ℓ] ℚ_[ℓ] := by
  obtain ⟨m, hm⟩ : (ℓ : ℤ) ∣ (c.val : ℤ) + ((-c).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_neg_cancel]
  have hrep : padicHeckeRep ℓ (some c) =
      βP hℓF.out (Bsome ℓ c) (det_Bsome ℓ c) ℓ * unipotentInt ℚ_[ℓ] (m : ℤ_[ℓ]) := by
    refine Units.ext ?_
    change ((localRepSome (K := ℚ_[ℓ]) (ℓ : ℤ_[ℓ]) (algebraMap_natCast_p_ne_zero ℓ) ((ZMod.val c : ℕ) : ℤ_[ℓ])
      : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) = _
    rw [Units.val_mul, coe_localRepSome, coe_βP, coe_unipotentInt, Bsome]
    have hm' : ((c.val : ℕ) : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) * (m : ℚ_[ℓ]) + (-(((-c).val : ℕ) : ℤ) : ℚ_[ℓ]) := by
      have := congrArg (Int.cast : ℤ → ℚ_[ℓ]) hm
      push_cast at this ⊢
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, -ZMod.natCast_val]
    · exact hm'
  rw [hrep, inv_mul_cancel_left]
  exact unipotentInt_mem _

theorem βP_Bnone_inv_mul_padicHeckeRep_mem :
    (βP hℓF.out (Bnone ℓ) (det_Bnone ℓ) ℓ)⁻¹ * padicHeckeRep ℓ none ∈ integralSubgroup ℤ_[ℓ] ℚ_[ℓ] := by
  have hrep : padicHeckeRep ℓ none = βP hℓF.out (Bnone ℓ) (det_Bnone ℓ) ℓ := by
    refine Units.ext ?_
    change ((localRepInf (K := ℚ_[ℓ]) (ℓ : ℤ_[ℓ]) (algebraMap_natCast_p_ne_zero ℓ) : GL (Fin 2) ℚ_[ℓ]) :
      Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) = _
    rw [coe_localRepInf, coe_βP, Bnone]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  rw [hrep, inv_mul_cancel]
  exact one_mem _

end Reps

section Slash

open UpperHalfPlane

theorem coe_scalar_mul (u : ℝˣ) (B : GL (Fin 2) ℝ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u * B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (u : ℝ) • (B : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Units.val_mul]
  change Matrix.scalar (Fin 2) (u : ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem slash_two_scalar (u : ℝˣ) (f : ℍ → ℂ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by
  ext τ
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val : ℝ) = (u : ℝ) * u := by
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val, pow_two]
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val : ℝ) := by
    rw [hdet]; exact mul_self_pos.mpr u.ne_zero
  have hu : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  rw [ModularForm.slash_apply, glScalar_smul, denom_scalar, UpperHalfPlane.σ, if_pos hpos, hdet,
    abs_of_pos (mul_self_pos.mpr u.ne_zero)]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_mul]
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg, zpow_two]
  field_simp

theorem slash_two_scalar_mul (u : ℝˣ) (B : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u * B) = f ∣[(2 : ℤ)] B := by
  rw [SlashAction.slash_mul, slash_two_scalar]

theorem slash_two_eq_of_coe_eq_smul {A B : GL (Fin 2) ℝ} {a : ℝ} (ha : a ≠ 0)
    (hAB : (A : Matrix (Fin 2) (Fin 2) ℝ) = a • (B : Matrix (Fin 2) (Fin 2) ℝ)) (f : ℍ → ℂ) :
    f ∣[(2 : ℤ)] A = f ∣[(2 : ℤ)] B := by
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha) * B :=
    Units.ext (by rw [coe_scalar_mul]; exact hAB)
  rw [hA, slash_two_scalar_mul]

variable (ℓ : ℕ) [hℓF : Fact ℓ.Prime]

theorem slash_map_βQ_Bsome_inv (c : ZMod ℓ) (f : ℍ → ℂ) :
    f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓF.out (Bsome ℓ c) (det_Bsome ℓ c))⁻¹
      = f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (-c).val := by
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓF.out.ne_zero
  refine slash_two_eq_of_coe_eq_smul (inv_ne_zero hℓ0) ?_ f
  ext i j
  rw [coe_map_βQ_inv_apply, ModularForm.val_heckeMatrix hℓF.out.ne_zero]
  fin_cases i <;> fin_cases j <;> simp [βinvMat, Bsome, div_eq_mul_inv, mul_comm, hℓ0, -ZMod.natCast_val]

theorem slash_map_βQ_Bnone_inv (f : ℍ → ℂ) :
    f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓF.out (Bnone ℓ) (det_Bnone ℓ))⁻¹
      = f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix ℓ := by
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓF.out.ne_zero
  refine slash_two_eq_of_coe_eq_smul (inv_ne_zero hℓ0) ?_ f
  ext i j
  rw [coe_map_βQ_inv_apply, ModularForm.val_heckeDiagMatrix hℓF.out.ne_zero]
  fin_cases i <;> fin_cases j <;> simp [βinvMat, Bnone, div_eq_mul_inv, mul_comm, hℓ0]

theorem val_finEquiv : ∀ (n : ℕ) [NeZero n] (i : Fin n), (ZMod.finEquiv n i).val = (i : ℕ)
  | 0, h, _ => (h.out rfl).elim
  | _ + 1, _, _ => rfl

theorem sum_slash_map_βQ_inv_eq_heckeT (f : ℍ → ℂ) :
    (∑ c : ZMod ℓ, f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)
        (βQ hℓF.out (Bsome ℓ c) (det_Bsome ℓ c))⁻¹) +
      f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓF.out (Bnone ℓ) (det_Bnone ℓ))⁻¹
      = ModularForm.heckeT 2 ℓ f := by
  rw [ModularForm.heckeT_def, slash_map_βQ_Bnone_inv]
  congr 1
  simp only [slash_map_βQ_Bsome_inv]
  calc ∑ c : ZMod ℓ, f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ (-c).val
      = ∑ c : ZMod ℓ, f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ c.val :=
        Equiv.sum_comp (Equiv.neg (ZMod ℓ)) (fun c => f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ c.val)
    _ = ∑ i : Fin ℓ, f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ i :=
        (Fintype.sum_equiv (ZMod.finEquiv ℓ).toEquiv _ _ (fun i => by
          simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_finEquiv])).symm
    _ = ∑ j ∈ Finset.range ℓ, f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j :=
        (Finset.sum_range fun j => f ∣[(2 : ℤ)] ModularForm.heckeMatrix ℓ j).symm

theorem σ_apply_of_det_pos {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ A z = z := by
  rw [UpperHalfPlane.σ, if_pos hA]
  rfl

def slashHom (k : ℤ) (A : GL (Fin 2) ℝ) : (ℍ → ℂ) →+ (ℍ → ℂ) where
  toFun f := f ∣[k] A
  map_zero' := SlashAction.zero_slash k A
  map_add' f g := SlashAction.add_slash k A f g

theorem sum_slash {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ) :
    (∑ i ∈ s, f i) ∣[k] A = ∑ i ∈ s, f i ∣[k] A :=
  map_sum (slashHom k A) f s

end Slash

section Systems

open HeckeIntegralSeam

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι κ : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps)
    (e : κ ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective (by simpa using hkk'))

theorem isHeckeCosetSystem_mul_left {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) :
    IsHeckeCosetSystem U g (fun i => u * reps i) := by
  refine ⟨fun i => HeckePair.mul_mem_doubleCoset (h.mem_doubleCoset i) hu, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers (u⁻¹ * x) (HeckePair.mul_mem_doubleCoset hx (inv_mem hu))
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
  · apply h.mk_injective
    have hij' : (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (u * reps j) := hij
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [QuotientGroup.eq] at hij' ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hij'

variable (ℓ : ℕ) [hℓF : Fact ℓ.Prime]

def optEquiv : Fin (ℓ + 1) ≃ Option (ZMod ℓ) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_option, ZMod.card])

def stdReps (i : Fin (ℓ + 1)) : AdelicGL2 (𝓞 ℚ) ℚ :=
  padicToAdelic ℓ (padicHeckeRep ℓ (optEquiv ℓ i))

theorem isHeckeCosetSystem_stdReps {N : ℕ} (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) :
    IsHeckeCosetSystem (levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ)
      (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ)) (stdReps ℓ) :=
  NumberField.AdelicLevel.isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup hN ℓ hℓN
    (padicHeckeRep ℓ ∘ optEquiv ℓ) (isHeckeCosetSystem_comp_equiv (isHeckeCosetSystem_padicHeckeRep ℓ) (optEquiv ℓ))

end Systems

section Eigen

open HeckeIntegralSeam UpperHalfPlane

variable {N : ℕ} (ℓ : ℕ) [hℓF : Fact ℓ.Prime]
  {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem sum_apply_mul_stdReps (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) (hg : g.IsNormalizedEigenform) (hΦg : g.IsAdelicLiftOf Φ)
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ i : Fin (ℓ + 1), Φ (z * stdReps ℓ i) = (ModularFormClass.qCoeff g ℓ : ℂ) * Φ z := by
  have hℓ : ℓ.Prime := hℓF.out
  set a : ℂ := (ModularFormClass.qCoeff g ℓ : ℂ) with ha
  have hsys := isHeckeCosetSystem_stdReps ℓ hN hℓN
  have hinv : ∀ (x : AdelicGL2 (𝓞 ℚ) ℚ), ∀ u ∈ levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ,
      Φ (x * u) = Φ x := fun x u hu => apply_mul_of_mem_levelOne_inf hΦg x hu
  have key : (fun w : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i : Fin (ℓ + 1), Φ (w * stdReps ℓ i)) = fun w => a * Φ w := by
    refine AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat (ratLevel_ne_bot hN) ?_ ?_ ?_ ?_ ?_
    · intro γ w
      simp only [mul_assoc, hΦg.left_inv]
    · intro γ w
      simp only [hΦg.left_inv]
    · intro u hu w
      have hsys' := isHeckeCosetSystem_mul_left hsys (finEmbed_mem_levelOne_inf hu)
      have h1 := heckeCosetSum_eq_of_isHeckeCosetSystem hsys hsys' hinv w
      simp only [mul_assoc]
      simpa only [mul_assoc] using h1
    · intro u hu w
      simp only [hΦg.level_inv u hu]
    · intro h hh hpos
      have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos

      have hsum : ∑ i : Fin (ℓ + 1), Φ (h * stdReps ℓ i)
          = ∑ o : Option (ZMod ℓ), Φ (h * padicToAdelic ℓ (padicHeckeRep ℓ o)) :=
        Fintype.sum_equiv (optEquiv ℓ) _ _ (fun i => rfl)
      have hsome : ∀ c : ZMod ℓ, Φ (h * padicToAdelic ℓ (padicHeckeRep ℓ (some c))) =
          (((⇑g) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓ (Bsome ℓ c) (det_Bsome ℓ c))⁻¹)
            ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := fun c =>
        apply_mul_padicToAdelic_eq_slash ℓ hN hℓN hΦg (Bsome ℓ c) (det_Bsome ℓ c) (Bsome_one_zero ℓ c) _
          (βP_Bsome_inv_mul_padicHeckeRep_mem ℓ c) h hh hpos
      have hnone : Φ (h * padicToAdelic ℓ (padicHeckeRep ℓ none)) =
          (((⇑g) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (βQ hℓ (Bnone ℓ) (det_Bnone ℓ))⁻¹)
            ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I :=
        apply_mul_padicToAdelic_eq_slash ℓ hN hℓN hΦg (Bnone ℓ) (det_Bnone ℓ) (Bnone_one_zero ℓ) _
          (βP_Bnone_inv_mul_padicHeckeRep_mem ℓ) h hh hpos
      have hT : ModularForm.heckeT 2 ℓ (⇑g) = a • (⇑g : ℍ → ℂ) := by
        have h1 := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 => (⇑f : ℍ → ℂ))
          (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N g hg ℓ hℓ hℓN)
        simpa only [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul] using h1
      change ∑ i : Fin (ℓ + 1), Φ (h * stdReps ℓ i) = a * Φ h
      rw [hsum, Fintype.sum_option, hnone, Finset.sum_congr rfl fun c _ => hsome c, ← Finset.sum_apply,
        ← sum_slash, ← Pi.add_apply, ← SlashAction.add_slash, add_comm, sum_slash_map_βQ_inv_eq_heckeT, hT,
        ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos hdet, smul_eq_mul, hΦg.apply_eq h hh hpos]
  exact congrFun key z

theorem sum_apply_mul_eq_of_isHeckeCosetSystem (hN : N ≠ 0) (hℓN : ¬ ℓ ∣ N) (hg : g.IsNormalizedEigenform)
    (hΦg : g.IsAdelicLiftOf Φ)
    (reps : Fin (Ideal.absNorm (padicPlace ℓ).asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ)
    (hsys : IsHeckeCosetSystem (levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ)
      (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ)) reps)
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ j, Φ (z * reps j) = (ModularFormClass.qCoeff g ℓ : ℂ) * Φ z := by
  set e : Fin (Ideal.absNorm (padicPlace ℓ).asIdeal + 1) ≃ Fin (ℓ + 1) :=
    finCongr (by rw [absNorm_padicPlace]) with he
  have hsys' : IsHeckeCosetSystem (levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ)
      (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ)) (stdReps ℓ ∘ e) :=
    isHeckeCosetSystem_comp_equiv (isHeckeCosetSystem_stdReps ℓ hN hℓN) e
  have hinv : ∀ (x : AdelicGL2 (𝓞 ℚ) ℚ), ∀ u ∈ levelOne (𝓞 ℚ) ℚ (ratLevel N) ⊓ finiteAdelicGL2Subgroup ℚ,
      Φ (x * u) = Φ x := fun x u hu => apply_mul_of_mem_levelOne_inf hΦg x hu
  rw [heckeCosetSum_eq_of_isHeckeCosetSystem hsys' hsys hinv z, ← sum_apply_mul_stdReps ℓ hN hℓN hg hΦg z]
  exact Fintype.sum_equiv e _ _ (fun j => rfl)

end Eigen

end AdelicEigenRow

end

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector AdelicEigenRow HeckeIntegralSeam in

theorem solution
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNormalizedEigenform)
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')
    (reps : Fin (Ideal.absNorm (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal + 1) → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel (q ^ 2 * M')) ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
      (NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) ((@AdelicDock.padicPlace ℓ ⟨hℓ⟩).adicCompletion ℚ),
      reps j = AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩) m))
    (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∑ j, (LocalNewvector.AdelicSpan.toFn Φ y).toFn (z * reps j) =
      (ModularFormClass.qCoeff g ℓ : ℂ) * (LocalNewvector.AdelicSpan.toFn Φ y).toFn z := by
  haveI hℓF : Fact ℓ.Prime := ⟨hℓ⟩
  have hq' : q.Prime := Fact.out
  have hN : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hq'.ne_zero) (NeZero.ne M')
  have hℓq : ℓ ≠ q := by
    intro h; apply hℓN; rw [h]; exact Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'
  set a : ℂ := (ModularFormClass.qCoeff g ℓ : ℂ) with ha

  have hΦ : ∀ w : AdelicGL2 (𝓞 ℚ) ℚ, ∑ j, Φ (w * reps j) = a * Φ w := fun w =>
    sum_apply_mul_eq_of_isHeckeCosetSystem ℓ hN hℓN hg hΦg reps hsys w

  have hcomm : ∀ (j) (x : GL (Fin 2) ℚ_[q]), reps j * padicToAdelic q x = padicToAdelic q x * reps j := by
    intro j x
    obtain ⟨m, hm⟩ := hpure j
    rw [hm, padicToAdelic_apply, ← map_mul, ← map_mul]
    congr 1
    symm
    refine mul_comm_of_finComponent_eq_one (padicPlace ℓ) ?_ ?_
    · exact finComponent_padicToFinAdelic_of_ne q x (padicPlace_ne_of_ne hℓq)
    · intro w hw
      exact finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ (padicPlace ℓ) m hw

  induction hy using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    show ∑ j, Φ (z * reps j * padicToAdelic q x) = a * Φ (z * padicToAdelic q x)
    simp only [mul_assoc, hcomm, ← hΦ (z * padicToAdelic q x)]
  | zero =>
    show ∑ j, (0 : ℂ) = a * 0
    simp
  | add b c _ _ hb hc =>
    show ∑ j, ((AdelicSpan.toFn Φ b).toFn (z * reps j) + (AdelicSpan.toFn Φ c).toFn (z * reps j))
      = a * ((AdelicSpan.toFn Φ b).toFn z + (AdelicSpan.toFn Φ c).toFn z)
    rw [Finset.sum_add_distrib, hb z, hc z, mul_add]
  | smul t b _ hb =>
    show ∑ j, t • (AdelicSpan.toFn Φ b).toFn (z * reps j) = a * (t • (AdelicSpan.toFn Φ b).toFn z)
    rw [← Finset.smul_sum, hb z, smul_eq_mul, smul_eq_mul]
    ring

end S_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem (solution)
