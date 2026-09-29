-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b1ec9328-284e-5904-9dc0-29becf254e76

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Mathlib
import Theorems.Thm_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
import Theorems.Thm_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
p2m_attr_erase "instance" "HeckeIntegralSeam.finite_padicInt_quotient_span_p"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U"

set_option autoImplicit false

open scoped MatrixGroups

open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

namespace W7E3

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {h k : 𝔸GL} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hk : glArch (𝓞 ℚ) ℚ k = 1) : h * k = k * h := by
  have hfin : (adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, ← glFin_apply, hh, Units.val_one]
  have harch : (adeleArch (𝓞 ℚ) ℚ).mapMatrix (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, ← glArch_apply, hk, Units.val_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply matrix_eq_of_mapMatrix_arch_fin_eq
  · rw [map_mul, map_mul, harch, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem toFn_globalPoints_mul {Φ : 𝔸GL → ℂ}
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (x : 𝔸GL), Φ (globalPoints (𝓞 ℚ) ℚ γ * x) = Φ x)
    (y : AdelicSpan Φ) (γ : GL (Fin 2) ℚ) (x : 𝔸GL) :
    (AdelicSpan.toFn Φ y).toFn (globalPoints (𝓞 ℚ) ℚ γ * x) = (AdelicSpan.toFn Φ y).toFn x := by
  have hy : AdelicSpan.toFn Φ y ∈ AdelicSpanSubmodule Φ := (show AdelicSpanSubmodule Φ from y).2
  suffices h : ∀ ψ ∈ AdelicSpanSubmodule Φ, ∀ x : 𝔸GL,
      ψ.toFn (globalPoints (𝓞 ℚ) ℚ γ * x) = ψ.toFn x from h _ hy x
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem ψ h =>
    obtain ⟨g, rfl⟩ := h
    intro x
    simp only [AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk, mul_assoc]
    exact hleft γ (x * g)
  | zero => intro x; rfl
  | add ψ₁ ψ₂ _ _ h1 h2 => intro x; simp only [AdelicFnCarrier.toFn_add, Pi.add_apply, h1, h2]
  | smul c ψ _ h => intro x; simp only [AdelicFnCarrier.toFn_csmul, Pi.smul_apply, h]

variable (q : ℕ) [Fact q.Prime]

theorem toFn_mul_of_comm {Φ : 𝔸GL → ℂ} {k : 𝔸GL} (hk : ∀ z : 𝔸GL, Φ (z * k) = Φ z)
    (hcomm : ∀ x : GL (Fin 2) ℚ_[q], padicToAdelic q x * k = k * padicToAdelic q x)
    (y : AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (z : 𝔸GL) :
    (AdelicSpan.toFn Φ y).toFn (z * k) = (AdelicSpan.toFn Φ y).toFn z := by
  revert z
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨x, rfl⟩ := h
    intro z
    simp only [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicSpan.toFn_self,
      AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk]
    rw [mul_assoc, ← hcomm x, ← mul_assoc, hk]
  | zero => intro z; rfl
  | add y₁ y₂ _ _ h1 h2 =>
    intro z
    change (AdelicSpan.toFn Φ y₁ + AdelicSpan.toFn Φ y₂).toFn (z * k) = (AdelicSpan.toFn Φ y₁ + AdelicSpan.toFn Φ y₂).toFn z
    simp only [AdelicFnCarrier.toFn_add, Pi.add_apply, h1, h2]
  | smul c y _ h =>
    intro z
    change (c • AdelicSpan.toFn Φ y).toFn (z * k) = (c • AdelicSpan.toFn Φ y).toFn z
    simp only [AdelicFnCarrier.toFn_csmul, Pi.smul_apply, h]

theorem toFn_mul_padicToAdelic_of_mem_fixed {Φ : 𝔸GL → ℂ} (y : AdelicSpan Φ) {U : Subgroup (GL (Fin 2) ℚ_[q])}
    (hfix : y ∈ fixedSubmodule U (AdelicSpan Φ)) {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ U) (z : 𝔸GL) :
    (AdelicSpan.toFn Φ y).toFn (z * padicToAdelic q m) = (AdelicSpan.toFn Φ y).toFn z := by
  have h := hfix m hm
  have := congrArg (fun w => (AdelicSpan.toFn Φ w).toFn z) h
  simpa [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul] using this

theorem exists_eq_padicPlace (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), w = @padicPlace ℓ ⟨hℓ⟩ := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).1, (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2, ?_⟩
  change w = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨_, _⟩
  simp

theorem padicPlace_injective {ℓ ℓ' : ℕ} [hℓ : Fact ℓ.Prime] [hℓ' : Fact ℓ'.Prime]
    (h : padicPlace ℓ = padicPlace ℓ') : ℓ = ℓ' := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h
  exact congrArg Subtype.val this

noncomputable def awayPart (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (localEmbed (𝓞 ℚ) ℚ (padicPlace q) (finComponent (𝓞 ℚ) ℚ (padicPlace q) k))⁻¹ * k

theorem localEmbed_mul_awayPart (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    localEmbed (𝓞 ℚ) ℚ (padicPlace q) (finComponent (𝓞 ℚ) ℚ (padicPlace q) k) * awayPart q k = k := by
  rw [awayPart, mul_inv_cancel_left]

theorem finComponent_awayPart (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finComponent (𝓞 ℚ) ℚ (padicPlace q) (awayPart q k) = 1 := by
  rw [awayPart, map_mul, map_inv, finComponent_localEmbed_self, inv_mul_cancel]

theorem mapMatrix_finComponent (w : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = ((finComponent (𝓞 ℚ) ℚ w k : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, finComponent_apply]

theorem mapMatrix_awayPart_of_ne (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ padicPlace q) :
    (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((awayPart q k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  rw [awayPart, Units.val_mul, map_mul]
  have : (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
      (((localEmbed (𝓞 ℚ) ℚ (padicPlace q) (finComponent (𝓞 ℚ) ℚ (padicPlace q) k))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [← map_inv, coe_localEmbed, mapMatrix_localMat_of_ne _ _ _ _ hw]
  rw [this, one_mul]

theorem localEmbed_mul_comm_of_finComponent_eq_one {a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (ha : finComponent (𝓞 ℚ) ℚ (padicPlace q) a = 1) (x : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) :
    localEmbed (𝓞 ℚ) ℚ (padicPlace q) x * a = a * localEmbed (𝓞 ℚ) ℚ (padicPlace q) x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_localEmbed]
  apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq
  intro w
  by_cases hw : w = padicPlace q
  · subst hw
    rw [map_mul, map_mul, mapMatrix_localMat_self, mapMatrix_finComponent, ha, Units.val_one, mul_one, one_mul]
  · rw [map_mul, map_mul, mapMatrix_localMat_of_ne _ _ _ _ hw, one_mul, mul_one]

theorem padicToAdelic_mul_finEmbed_comm {a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (ha : finComponent (𝓞 ℚ) ℚ (padicPlace q) a = 1) (x : GL (Fin 2) ℚ_[q]) :
    padicToAdelic q x * finEmbed (𝓞 ℚ) ℚ a = finEmbed (𝓞 ℚ) ℚ a * padicToAdelic q x := by
  rw [padicToAdelic_apply, padicToFinAdelic_apply, ← map_mul, ← map_mul,
    localEmbed_mul_comm_of_finComponent_eq_one q ha]

theorem idealBound_ratLevel_eq_of_ne {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0) {ℓ : ℕ} [Fact ℓ.Prime]
    (h : ‖(N : ℚ_[ℓ])‖ = ‖(N' : ℚ_[ℓ])‖) :
    idealBound (𝓞 ℚ) (ratLevel N) (padicPlace ℓ) = idealBound (𝓞 ℚ) (ratLevel N') (padicPlace ℓ) := by
  rw [idealBound_ratLevel ℓ hN, idealBound_ratLevel ℓ hN']
  have hNq : (N : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN
  have hN'q : (N' : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN'
  apply le_antisymm
  · rw [valued_le_valued_iff ℓ _ _ hN'q, h]
  · rw [valued_le_valued_iff ℓ _ _ hNq, h]

theorem padicNorm_mul_eq_of_ne {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (N : ℕ) :
    ‖((q * N : ℕ) : ℚ_[ℓ])‖ = ‖(N : ℚ_[ℓ])‖ := by
  rw [Nat.cast_mul, norm_mul]
  have : ‖(q : ℚ_[ℓ])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Fact.out).mpr hℓq
  rw [this, one_mul]

theorem apply_eq_mapMatrix_apply (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 2)
    (w : HeightOneSpectrum (𝓞 ℚ)) : (A i j) w = ((finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix A) i j := by
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

variable {q}

theorem isLevelZeroMatrix_of_mapMatrix {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (hNN' : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q → ‖(N : ℚ_[ℓ])‖ = ‖(N' : ℚ_[ℓ])‖)
    {m A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : IsLevelOneMatrix (𝓞 ℚ) ℚ (ratLevel N) m)
    (hAq : (finAdeleEval (𝓞 ℚ) ℚ (padicPlace q)).mapMatrix A = 1)
    (hAw : ∀ w, w ≠ padicPlace q → (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix A = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix m) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N') A := by
  refine ⟨fun i j w => ?_, fun w => ?_⟩
  · rw [apply_eq_mapMatrix_apply]
    by_cases hw : w = padicPlace q
    · subst hw
      rw [hAq, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [hAw w hw, ← apply_eq_mapMatrix_apply]
      exact hm.integral i j w
  · rw [apply_eq_mapMatrix_apply]
    by_cases hw : w = padicPlace q
    · subst hw
      rw [hAq, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'
    · rw [hAw w hw, ← apply_eq_mapMatrix_apply]
      obtain ⟨ℓ, hℓ, rfl⟩ := exists_eq_padicPlace w
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      have hℓq : ℓ ≠ q := fun h => hw (by subst h; rfl)
      rw [← idealBound_ratLevel_eq_of_ne hN hN' (hNN' ℓ hℓq)]
      exact hm.lowerLeft (padicPlace ℓ)

theorem awayPart_mem_finiteLevelZero {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (hNN' : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q → ‖(N : ℚ_[ℓ])‖ = ‖(N' : ℚ_[ℓ])‖)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    awayPart q k ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N') := by
  rw [mem_finiteLevelZero_iff]
  obtain ⟨hk1, hk2⟩ := mem_finiteLevelOne_iff.mp hk
  constructor
  · refine isLevelZeroMatrix_of_mapMatrix hN hN' hNN' hk1 ?_ (fun w hw => mapMatrix_awayPart_of_ne q k hw)
    rw [mapMatrix_finComponent, finComponent_awayPart, Units.val_one]
  · refine isLevelZeroMatrix_of_mapMatrix hN hN' hNN' hk2 ?_ (fun w hw => ?_)
    · rw [mapMatrix_finComponent, map_inv, finComponent_awayPart, inv_one, Units.val_one]
    · rw [awayPart, mul_inv_rev, inv_inv, Units.val_mul, map_mul, coe_localEmbed,
        mapMatrix_localMat_of_ne _ _ _ _ hw, mul_one]

variable (q)

theorem toFn_mul_finEmbed_of_mem_finiteLevelZero {M : ℕ} (hM : M ≠ 0)
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {Φ : 𝔸GL → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (ha : a ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (haq : finComponent (𝓞 ℚ) ℚ (padicPlace q) a = 1) (z : 𝔸GL) :
    (AdelicSpan.toFn Φ y).toFn (z * finEmbed (𝓞 ℚ) ℚ a) = (AdelicSpan.toFn Φ y).toFn z := by
  refine toFn_mul_of_comm q (fun z => ?_) (fun x => ?_) y hy z
  · exact hΦg.levelZero_inv hM _ ha z
  · exact padicToAdelic_mul_finEmbed_comm q haq x

noncomputable def qComp (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv q).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace q) k)

theorem padicGL_qComp (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    padicGL q (qComp q k) = finComponent (𝓞 ℚ) ℚ (padicPlace q) k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [padicGL_apply, qComp, Matrix.GeneralLinearGroup.map_apply]
  exact (padicRingEquiv q).apply_symm_apply _

theorem padicRingEquiv_qComp_apply (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 2) :
    padicRingEquiv q ((qComp q k : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j)
      = ((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) (padicPlace q) := by
  rw [← padicGL_apply, padicGL_qComp, finComponent_apply]

theorem padicToFinAdelic_qComp_mul_awayPart (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    padicToFinAdelic q (qComp q k) * awayPart q k = k := by
  rw [padicToFinAdelic_apply, padicGL_qComp, localEmbed_mul_awayPart]

theorem finEmbed_eq_padicToAdelic_qComp_mul (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ k = padicToAdelic q (qComp q k) * finEmbed (𝓞 ℚ) ℚ (awayPart q k) := by
  rw [padicToAdelic_apply, ← map_mul, padicToFinAdelic_qComp_mul_awayPart]

theorem norm_natCast_q_mul {M' : ℕ} (hqM' : ¬ q ∣ M') : ‖((q * M' : ℕ) : ℚ_[q])‖ = (q : ℝ)⁻¹ := by
  rw [Nat.cast_mul, norm_mul, Padic.norm_p]
  have : ‖(M' : ℚ_[q])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'
  rw [this, mul_one]

theorem qComp_level {N : ℕ} (hN0 : N ≠ 0) (hNn : ‖(N : ℚ_[q])‖ = (q : ℝ)⁻¹)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} {c : Matrix (Fin 2) (Fin 2) ℚ_[q]}
    (hm : IsLevelOneMatrix (𝓞 ℚ) ℚ (ratLevel N) m)
    (hc : ∀ i j, padicRingEquiv q (c i j) = (m i j) (padicPlace q)) :
    (∀ i j, ‖c i j‖ ≤ 1) ∧ ‖c 1 0‖ ≤ (q : ℝ)⁻¹ ∧ ‖c 1 1 - 1‖ ≤ (q : ℝ)⁻¹ := by
  have hNq : ((N : ℕ) : ℚ_[q]) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [norm_le_one_iff_mem, hc]
    exact hm.integral i j (padicPlace q)
  · have h := hm.lowerLeft (padicPlace q)
    rw [idealBound_ratLevel q hN0, ← hc, valued_le_valued_iff q _ _ hNq, hNn] at h
    exact h
  · have h := hm.lowerRight (padicPlace q)
    rw [coe_sub_apply, coe_one_apply, idealBound_ratLevel q hN0, ← hc, ← map_one (padicRingEquiv q),
      ← map_sub, valued_le_valued_iff q _ _ hNq, hNn] at h
    exact h

theorem qComp_level' {N : ℕ} (hN0 : N ≠ 0) (hNn : ‖(N : ℚ_[q])‖ = (q : ℝ)⁻¹) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N)) :
    (∀ i j, ‖(qComp q k : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1) ∧
      ‖(qComp q k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0‖ ≤ (q : ℝ)⁻¹ ∧
      ‖(qComp q k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 - 1‖ ≤ (q : ℝ)⁻¹ ∧
      (∀ i j, ‖(((qComp q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1) ∧
      ‖(((qComp q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0‖ ≤ (q : ℝ)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := qComp_level q hN0 hNn (mem_finiteLevelOne_iff.mp hk).1 (padicRingEquiv_qComp_apply q k)
  have hqinv : (qComp q k)⁻¹ = qComp q k⁻¹ := by simp only [qComp, map_inv]
  have hinv : ∀ i j, padicRingEquiv q ((((qComp q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j)
      = (((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
        (padicPlace q) := fun i j => by
    rw [hqinv, padicRingEquiv_qComp_apply]
  obtain ⟨h4, h5, -⟩ := qComp_level q hN0 hNn (mem_finiteLevelOne_iff.mp hk).2 hinv
  exact ⟨h1, h2, h3, h4, h5⟩

theorem padicRingEquiv_algebraMap (r : ℚ) :
    padicRingEquiv q (algebraMap ℚ ℚ_[q] r) = algebraMap ℚ ((padicPlace q).adicCompletion ℚ) r := by
  rw [padicRingEquiv_apply]
  exact AlgHomClass.commutes _ r

theorem qComp_glFin_globalPoints (γ : GL (Fin 2) ℚ) :
    qComp q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => (padicRingEquiv q).injective ?_
  rw [padicRingEquiv_qComp_apply, glFin_apply, globalPoints_apply, Matrix.GeneralLinearGroup.map_apply,
    padicRingEquiv_algebraMap, NumberField.AdeleRing.algebraMap_snd_apply]
  rfl

open LanglandsTunnell in
theorem ratArchGL2_mul (g h : 𝔸GL) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  simp only [ratArchGL2, map_mul]

open LanglandsTunnell in
theorem ratArchGL2_finEmbed (a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : ratArchGL2 (finEmbed (𝓞 ℚ) ℚ a) = 1 := by
  simp only [ratArchGL2, glArch_finEmbed, map_one]

open LanglandsTunnell in
theorem ratArchGL2_eq_of_glFin (g : 𝔸GL) :
    ratArchGL2 (g * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g))⁻¹) = ratArchGL2 g := by
  rw [ratArchGL2_mul, ← map_inv, ratArchGL2_finEmbed, mul_one]

theorem glFin_mul_finEmbed_glFin_inv (g : 𝔸GL) :
    glFin (𝓞 ℚ) ℚ (g * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g))⁻¹) = 1 := by
  rw [map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

open LanglandsTunnell in

theorem ratArchGL2_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = (((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℚ) : ℝ) := by
  rw [ratArchGL2, Matrix.GeneralLinearGroup.map_apply]
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom.comp
        (algebraMap ℚ ((default : InfinitePlace ℚ).Completion))) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  exact eq_ratCast _ _

open LanglandsTunnell in
theorem det_ratArchGL2_globalPoints (γ : GL (Fin 2) ℚ) :
    ((ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det : ℝ) = ((γ.det : ℚ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
    Matrix.det_fin_two]
  simp only [ratArchGL2_globalPoints_apply]
  push_cast
  ring

open LanglandsTunnell in
theorem ratArchGL2_globalPoints_mul_mem_GLPos {γ : GL (Fin 2) ℚ} (hγ : (γ.det : ℚ) = 1) {h : 𝔸GL}
    (hh : ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) : ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos] at hh ⊢
  rw [ratArchGL2_mul, map_mul, Units.val_mul, det_ratArchGL2_globalPoints, hγ]
  simpa using hh

theorem qComp_mul (a b : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : qComp q (a * b) = qComp q a * qComp q b := by
  simp only [qComp, map_mul]

theorem qComp_inv (a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : qComp q a⁻¹ = (qComp q a)⁻¹ := by
  simp only [qComp, map_inv]

theorem qComp_padicToFinAdelic (x : GL (Fin 2) ℚ_[q]) : qComp q (padicToFinAdelic q x) = x := by
  apply padicGL_injective q
  rw [padicGL_qComp, finComponent_padicToFinAdelic_self]

theorem qComp_localEmbed_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace q)
    (m : GL (Fin 2) (w.adicCompletion ℚ)) : qComp q (localEmbed (𝓞 ℚ) ℚ w m) = 1 := by
  apply padicGL_injective q
  rw [padicGL_qComp, map_one, finComponent_localEmbed_of_ne _ _ _ _ (Ne.symm hw)]

open LanglandsTunnell in
theorem ratArchGL2_globalPoints (γ : GL (Fin 2) ℚ) :
    ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [ratArchGL2_globalPoints_apply, Matrix.GeneralLinearGroup.map_apply, Rat.coe_castHom]

noncomputable def archOf (γ : GL (Fin 2) ℚ) : 𝔸GL :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

theorem glFin_archOf (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archOf γ) = 1 := glFin_mul_finEmbed_glFin_inv _

open LanglandsTunnell in
theorem ratArchGL2_archOf_mul (γ : GL (Fin 2) ℚ) (h : 𝔸GL) :
    ratArchGL2 (archOf γ * h) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * ratArchGL2 h := by
  rw [ratArchGL2_mul, archOf, ratArchGL2_eq_of_glFin, ratArchGL2_globalPoints]

theorem globalPoints_eq_archOf_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archOf γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archOf, inv_mul_cancel_right]

theorem toFn_coset_term {M' : ℕ} [NeZero M'] {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : 𝔸GL → ℂ} (hΦg : g.IsAdelicLiftOf Φ) (y : AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (AdelicSpan Φ))
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace q) (m : GL (Fin 2) (w.adicCompletion ℚ))
    (γ : GL (Fin 2) ℚ) (du du' k : GL (Fin 2) ℚ_[q]) (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
    (hq : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ⁻¹ * du = du' * k)
    (ha : awayPart q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) * padicToFinAdelic q du * localEmbed (𝓞 ℚ) ℚ w m)
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')))
    (h : 𝔸GL) (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ w m))
      = (AdelicSpan.toFn Φ y).toFn (archOf γ⁻¹ * h * padicToAdelic q du') := by
  have hM : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')
  set Ff := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) * padicToFinAdelic q du * localEmbed (𝓞 ℚ) ℚ w m with hFf
  have hqc : qComp q Ff = du' * k := by
    rw [hFf, qComp_mul, qComp_mul, qComp_padicToFinAdelic, qComp_localEmbed_of_ne q hw, mul_one,
      qComp_glFin_globalPoints, map_inv, ← map_inv, hq]
  have hdec : finEmbed (𝓞 ℚ) ℚ Ff = padicToAdelic q du' * padicToAdelic q k * finEmbed (𝓞 ℚ) ℚ (awayPart q Ff) := by
    rw [finEmbed_eq_padicToAdelic_qComp_mul q, hqc, map_mul]

  have hcomm : finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹)) * h
      = h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹)) :=
    (mul_comm_of_glFin_eq_one_of_glArch_eq_one hh (glArch_finEmbed _ _ _)).symm
  have key : globalPoints (𝓞 ℚ) ℚ γ⁻¹ * (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ w m))
      = (archOf γ⁻¹ * h * padicToAdelic q du') * padicToAdelic q k * finEmbed (𝓞 ℚ) ℚ (awayPart q Ff) := by
    rw [globalPoints_eq_archOf_mul γ⁻¹]
    calc archOf γ⁻¹ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹))
          * (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ w m))
        = archOf γ⁻¹ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹)) * h)
          * (padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ w m)) := by simp only [mul_assoc]
      _ = archOf γ⁻¹ * h * finEmbed (𝓞 ℚ) ℚ Ff := by
          rw [hcomm, hFf, map_mul, map_mul, padicToAdelic_apply]; simp only [mul_assoc]
      _ = (archOf γ⁻¹ * h * padicToAdelic q du') * padicToAdelic q k * finEmbed (𝓞 ℚ) ℚ (awayPart q Ff) := by
          rw [hdec]; simp only [mul_assoc]
  rw [← toFn_globalPoints_mul hΦg.left_inv y γ⁻¹, key,
    toFn_mul_finEmbed_of_mem_finiteLevelZero q hM hΦg y hy ha (finComponent_awayPart q _),
    toFn_mul_padicToAdelic_of_mem_fixed q y hfix hk]

def IsLocalLevelZero (N : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) (c : GL (Fin 2) (w.adicCompletion ℚ)) : Prop :=
  (∀ i j, (c : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j ∈ w.adicCompletionIntegers ℚ) ∧
  (∀ i j, ((c⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j
    ∈ w.adicCompletionIntegers ℚ) ∧
  Valued.v ((c : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) 1 0) ≤ idealBound (𝓞 ℚ) (ratLevel N) w ∧
  Valued.v (((c⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) 1 0)
    ≤ idealBound (𝓞 ℚ) (ratLevel N) w

theorem mem_finiteLevelZero_of_forall (N : ℕ) (a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (h : ∀ w, IsLocalLevelZero N w (finComponent (𝓞 ℚ) ℚ w a)) :
    a ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [mem_finiteLevelZero_iff]
  refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, ⟨fun i j w => ?_, fun w => ?_⟩⟩
  · have := (h w).1 i j; rwa [finComponent_apply] at this
  · have := (h w).2.2.1; rwa [finComponent_apply] at this
  · have := (h w).2.1 i j; rwa [← map_inv, finComponent_apply] at this
  · have := (h w).2.2.2; rwa [← map_inv, finComponent_apply] at this

theorem isLocalLevelZero_one (N : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) : IsLocalLevelZero N w 1 := by
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  · rw [inv_one, Units.val_one, Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  · rw [Units.val_one, Matrix.one_apply_ne (by decide), map_zero]; exact zero_le'
  · rw [inv_one, Units.val_one, Matrix.one_apply_ne (by decide), map_zero]; exact zero_le'

theorem finComponent_glFin_globalPoints (w : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin 2) ℚ) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (w.adicCompletion ℚ)) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, glFin_apply, globalPoints_apply, Matrix.GeneralLinearGroup.map_apply,
    NumberField.AdeleRing.algebraMap_snd_apply]
  rfl

theorem norm_intCast_le_inv_iff {n : ℤ} : ‖(n : ℚ_[q])‖ ≤ (q : ℝ)⁻¹ ↔ (q : ℤ) ∣ n := by
  rw [← zpow_neg_one, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, Padic.norm_int_le_pow_iff_dvd, pow_one]

theorem coe_unitsMap_padicInt (u : ℤ_[q]ˣ) :
    ((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[q]ˣ) : ℚ_[q]) = ((u : ℤ_[q]) : ℚ_[q]) := rfl

theorem coe_unitsMap_mul_inv {ℓ : ℕ} (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ) (u : ℤ_[q]ˣ) :
    ((Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹) : ℚ_[q]ˣ) : ℚ_[q])
      = ((u : ℤ_[q]) : ℚ_[q]) * (ℓ : ℚ_[q])⁻¹ := by
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, coe_unitsMap_padicInt, coe_unitsMap_padicInt, hℓq]
  norm_cast

theorem diagOne_val {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(a : A), 0; 0, 1] := by
  ext i j; rw [diagOne_coe_apply]; fin_cases i <;> fin_cases j <;> simp

theorem shapeA_q {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq' : ℓ ≠ q) (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ) (t : ℤ) (htq : (q : ℤ) ∣ t)
    (γ : GL (Fin 2) ℚ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) (u : ℤ_[q]ˣ) :
    ∃ k : GL (Fin 2) ℚ_[q], k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 ∧
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ⁻¹ * diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u)
        = diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)) * k := by
  set du := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) with hdu
  set du' := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)) with hdu'
  have hℓq0 : (ℓ : ℚ_[q]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hu0 : ((u : ℤ_[q]) : ℚ_[q]) ≠ 0 := by
    rw [Ne, ← norm_eq_zero, ← PadicInt.norm_def, PadicInt.isUnit_iff.mp u.isUnit]; exact one_ne_zero
  set k : GL (Fin 2) ℚ_[q] := unipotentGL2 (-(t : ℚ_[q]) / ((u : ℤ_[q]) : ℚ_[q])) with hk
  have hk_val : (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![1, -(t : ℚ_[q]) / ((u : ℤ_[q]) : ℚ_[q]); 0, 1] := by
    rw [hk, unipotentGL2_coe]
  have hγ_val : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
      = !![(ℓ : ℚ_[q]), (t : ℚ_[q]); 0, 1] := by
    ext i j; rw [Matrix.GeneralLinearGroup.map_apply, hγ]; fin_cases i <;> fin_cases j <;> simp
  have hdu_val : (du : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![((u : ℤ_[q]) : ℚ_[q]), 0; 0, 1] := by
    rw [hdu, diagOne_val, coe_unitsMap_padicInt]
  have hdu'_val : (du' : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![((u : ℤ_[q]) : ℚ_[q]) * (ℓ : ℚ_[q])⁻¹, 0; 0, 1] := by
    rw [hdu', diagOne_val, coe_unitsMap_mul_inv q ℓq hℓq]
  have hunorm : ‖((u : ℤ_[q]) : ℚ_[q])‖ = 1 := by rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
  refine ⟨k, ?_, ?_⟩
  · rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q le_rfl]
    have e01 : ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) 0 1 = -(t : ℚ_[q]) / ((u : ℤ_[q]) : ℚ_[q]) := by
      rw [hk_val]; simp [Matrix.one_apply]
    have n01 : ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) 0 1‖ ≤ (q : ℝ)⁻¹ := by
      rw [e01, norm_div, norm_neg, hunorm, div_one, norm_intCast_le_inv_iff]; exact htq
    have n00 : ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) 0 0‖ ≤ (q : ℝ)⁻¹ := by
      rw [hk_val]; simp [Matrix.one_apply]
    have n10 : ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) 1 0‖ ≤ (q : ℝ)⁻¹ := by
      rw [hk_val]; simp [Matrix.one_apply]
    have n11 : ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) 1 1‖ ≤ (q : ℝ)⁻¹ := by
      rw [hk_val]; simp [Matrix.one_apply]
    intro i j
    rw [show ((q : ℝ) ^ (-((1 : ℕ) : ℤ))) = (q : ℝ)⁻¹ by simp]
    fin_cases i <;> fin_cases j
    · exact n00
    · exact n01
    · exact n10
    · exact n11
  ·
    have hprod : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ * du' * k = du := by
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Units.val_mul, Units.val_mul, hγ_val, hdu'_val, hk_val, hdu_val]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
    rw [← hprod]
    simp only [map_inv, mul_assoc, inv_mul_cancel_left]

theorem shapeB_q {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq' : ℓ ≠ q) (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ)
    (σ : SL(2, ℤ)) (hσb : (q : ℤ) ∣ σ 0 1) (hσc : (q : ℤ) ∣ σ 1 0) (hσa : ((σ 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q))
    (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
    (u : ℤ_[q]ˣ) :
    ∃ k : GL (Fin 2) ℚ_[q], k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 ∧
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ⁻¹ * diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u)
        = diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)) * k := by
  set du := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) with hdu
  set du' := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)) with hdu'
  set a : ℤ := σ 0 0 with ha
  set b : ℤ := σ 0 1 with hb
  set c : ℤ := σ 1 0 with hc
  set d : ℤ := σ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe σ; rw [Matrix.det_fin_two] at this; exact this
  have hℓq0 : (ℓ : ℚ_[q]) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hu0 : ((u : ℤ_[q]) : ℚ_[q]) ≠ 0 := by
    rw [Ne, ← norm_eq_zero, ← PadicInt.norm_def, PadicInt.isUnit_iff.mp u.isUnit]; exact one_ne_zero
  have hunorm : ‖((u : ℤ_[q]) : ℚ_[q])‖ = 1 := by rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
  have hℓnorm : ‖(ℓ : ℚ_[q])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]; exact (Nat.coprime_primes Fact.out hℓ).mpr (Ne.symm hℓq')

  set uq : ℚ_[q] := ((u : ℤ_[q]) : ℚ_[q]) with huq
  set K : Matrix (Fin 2) (Fin 2) ℚ_[q] := !![(ℓ : ℚ_[q]) * d, -(ℓ : ℚ_[q]) * uq⁻¹ * b; -(ℓ : ℚ_[q])⁻¹ * uq * c, (ℓ : ℚ_[q])⁻¹ * a]
    with hK
  have hKdet : K.det = 1 := by
    rw [hK, Matrix.det_fin_two_of]
    have : (a : ℚ_[q]) * d - b * c = 1 := by exact_mod_cast hdet
    field_simp
    linear_combination this
  set k : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.mkOfDetNeZero K (by rw [hKdet]; exact one_ne_zero) with hk
  have hk_val : (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) = K := rfl
  have hγ_val : ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q])
      = !![(a : ℚ_[q]), (b : ℚ_[q]) * ℓ; (c : ℚ_[q]), (d : ℚ_[q]) * ℓ] := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hγ]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd]
  have hdu_val : (du : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![uq, 0; 0, 1] := by
    rw [hdu, diagOne_val, coe_unitsMap_padicInt]
  have hdu'_val : (du' : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![uq * (ℓ : ℚ_[q])⁻¹, 0; 0, 1] := by
    rw [hdu', diagOne_val, coe_unitsMap_mul_inv q ℓq hℓq]
  refine ⟨k, ?_, ?_⟩
  · rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q le_rfl]
    have e00 : (K - 1) 0 0 = (((ℓ : ℤ) * d - 1 : ℤ) : ℚ_[q]) := by simp [hK, Matrix.one_apply]
    have e01 : (K - 1) 0 1 = -(ℓ : ℚ_[q]) * uq⁻¹ * b := by simp [hK, Matrix.one_apply]
    have e10 : (K - 1) 1 0 = -(ℓ : ℚ_[q])⁻¹ * uq * c := by simp [hK, Matrix.one_apply]
    have e11 : (K - 1) 1 1 = (ℓ : ℚ_[q])⁻¹ * (((a - ℓ : ℤ)) : ℚ_[q]) := by
      simp [hK, Matrix.one_apply]; field_simp
    have hℓd : (q : ℤ) ∣ ℓ * d - 1 := by
      have h1 : ((a : ℤ) : ZMod q) * (d : ZMod q) - (b : ZMod q) * (c : ZMod q) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ZMod q)) hdet
      rw [hσa, (ZMod.intCast_zmod_eq_zero_iff_dvd b q).mpr hσb, zero_mul, sub_zero] at h1
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1, sub_self]
    have haℓ : (q : ℤ) ∣ a - ℓ := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hσa, sub_self]
    have n00 : ‖(K - 1) 0 0‖ ≤ (q : ℝ)⁻¹ := by rw [e00, norm_intCast_le_inv_iff]; exact hℓd
    have n01 : ‖(K - 1) 0 1‖ ≤ (q : ℝ)⁻¹ := by
      rw [e01, norm_mul, norm_mul, norm_neg, hℓnorm, norm_inv, hunorm, inv_one, one_mul, one_mul, norm_intCast_le_inv_iff]
      exact hσb
    have n10 : ‖(K - 1) 1 0‖ ≤ (q : ℝ)⁻¹ := by
      rw [e10, norm_mul, norm_mul, norm_neg, norm_inv, hℓnorm, inv_one, hunorm, one_mul, one_mul, norm_intCast_le_inv_iff]
      exact hσc
    have n11 : ‖(K - 1) 1 1‖ ≤ (q : ℝ)⁻¹ := by
      rw [e11, norm_mul, norm_inv, hℓnorm, inv_one, one_mul, norm_intCast_le_inv_iff]; exact haℓ
    intro i j
    rw [hk_val, show ((q : ℝ) ^ (-((1 : ℕ) : ℤ))) = (q : ℝ)⁻¹ by simp]
    fin_cases i <;> fin_cases j
    · exact n00
    · exact n01
    · exact n10
    · exact n11
  · have hprod : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ * du' * k = du := by
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Units.val_mul, Units.val_mul, hγ_val, hdu'_val, hk_val, hK, hdu_val]
      have : (a : ℚ_[q]) * d - b * c = 1 := by exact_mod_cast hdet
      fin_cases i <;> fin_cases j
      all_goals (simp [Matrix.mul_apply, Fin.sum_univ_two]; try field_simp)
      all_goals (first | linear_combination this | ring1 | linear_combination uq * this)
    rw [← hprod]
    simp only [map_inv, mul_assoc, inv_mul_cancel_left]

theorem valued_algebraMap_le_one_iff {p : ℕ} [Fact p.Prime] (r : ℚ) :
    algebraMap ℚ ((padicPlace p).adicCompletion ℚ) r ∈ (padicPlace p).adicCompletionIntegers ℚ ↔ ‖(r : ℚ_[p])‖ ≤ 1 := by
  rw [← padicRingEquiv_algebraMap, ← norm_le_one_iff_mem]; rfl

theorem valued_algebraMap_le_idealBound_iff {p : ℕ} [Fact p.Prime] {N : ℕ} (hN : N ≠ 0) (r : ℚ) :
    Valued.v (algebraMap ℚ ((padicPlace p).adicCompletion ℚ) r) ≤ idealBound (𝓞 ℚ) (ratLevel N) (padicPlace p)
      ↔ ‖(r : ℚ_[p])‖ ≤ ‖(N : ℚ_[p])‖ := by
  have hNq : (N : ℚ_[p]) ≠ 0 := by exact_mod_cast hN
  rw [← padicRingEquiv_algebraMap, idealBound_ratLevel p hN, valued_le_valued_iff p _ _ hNq]; rfl

theorem isLocalLevelZero_of_rat {p : ℕ} [Fact p.Prime] {N : ℕ} (hN : N ≠ 0)
    (C : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)) (X Y : Matrix (Fin 2) (Fin 2) ℚ)
    (hX : (C : Matrix (Fin 2) (Fin 2) _) = X.map (algebraMap ℚ ((padicPlace p).adicCompletion ℚ)))
    (hY : ((C⁻¹ : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _)
      = Y.map (algebraMap ℚ ((padicPlace p).adicCompletion ℚ)))
    (h1 : ∀ i j, ‖(X i j : ℚ_[p])‖ ≤ 1) (h2 : ∀ i j, ‖(Y i j : ℚ_[p])‖ ≤ 1)
    (h3 : ‖(X 1 0 : ℚ_[p])‖ ≤ ‖(N : ℚ_[p])‖) (h4 : ‖(Y 1 0 : ℚ_[p])‖ ≤ ‖(N : ℚ_[p])‖) :
    IsLocalLevelZero N (padicPlace p) C := by
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [hX, Matrix.map_apply, valued_algebraMap_le_one_iff]; exact h1 i j
  · rw [hY, Matrix.map_apply, valued_algebraMap_le_one_iff]; exact h2 i j
  · rw [hX, Matrix.map_apply, valued_algebraMap_le_idealBound_iff hN]; exact h3
  · rw [hY, Matrix.map_apply, valued_algebraMap_le_idealBound_iff hN]; exact h4

theorem finComponent_awayPart_of_ne' {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace q) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finComponent (𝓞 ℚ) ℚ w (awayPart q k) = finComponent (𝓞 ℚ) ℚ w k := by
  apply Units.ext
  rw [← mapMatrix_finComponent, ← mapMatrix_finComponent, mapMatrix_awayPart_of_ne q k hw]

theorem finComponent_triple_self {w₀ : HeightOneSpectrum (𝓞 ℚ)} (hw₀ : w₀ ≠ padicPlace q)
    (γ : GL (Fin 2) ℚ) (du : GL (Fin 2) ℚ_[q]) (m : GL (Fin 2) (w₀.adicCompletion ℚ)) :
    finComponent (𝓞 ℚ) ℚ w₀ (awayPart q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * padicToFinAdelic q du
        * localEmbed (𝓞 ℚ) ℚ w₀ m))
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (w₀.adicCompletion ℚ)) γ * m := by
  rw [finComponent_awayPart_of_ne' q hw₀, map_mul, map_mul, finComponent_glFin_globalPoints,
    finComponent_padicToFinAdelic_of_ne q du hw₀, mul_one, finComponent_localEmbed_self]

theorem finComponent_triple_of_ne {w₀ w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace q) (hww₀ : w ≠ w₀)
    (γ : GL (Fin 2) ℚ) (du : GL (Fin 2) ℚ_[q]) (m : GL (Fin 2) (w₀.adicCompletion ℚ)) :
    finComponent (𝓞 ℚ) ℚ w (awayPart q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * padicToFinAdelic q du
        * localEmbed (𝓞 ℚ) ℚ w₀ m))
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (w.adicCompletion ℚ)) γ := by
  rw [finComponent_awayPart_of_ne' q hw, map_mul, map_mul, finComponent_glFin_globalPoints,
    finComponent_padicToFinAdelic_of_ne q du hw, mul_one, finComponent_localEmbed_of_ne _ _ _ _ hww₀, mul_one]

theorem coe_inv_of_mul_eq_one {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n R) (Y : Matrix n n R) (h : (g : Matrix n n R) * Y = 1) : ((g⁻¹ : GL n R) : Matrix n n R) = Y := by
  have : (g⁻¹ : GL n R) = ⟨Y, g, mul_eq_one_comm.mp h, h⟩ :=
    inv_eq_of_mul_eq_one_right (Units.ext h)
  rw [this]

theorem map_coe_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) = (g : Matrix (Fin 2) (Fin 2) R).map f := rfl

theorem map_inv_coe_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    (((Matrix.GeneralLinearGroup.map f g)⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      = ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f := by
  rw [← map_inv]; rfl

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem valued_algebraMap_eq_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  simp

theorem valued_algebraMap_intCast_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ)) ≤ 1 := by
  rw [valued_algebraMap_eq_valuation, show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by simp,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem valued_algebraMap_integer_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (s : w.adicCompletionIntegers ℚ) :
    Valued.v (algebraMap (w.adicCompletionIntegers ℚ) (w.adicCompletion ℚ) s) ≤ 1 :=
  (mem_integers_iff w _).mp s.2

theorem ne_zero_of_v_eq_exp {w : HeightOneSpectrum (𝓞 ℚ)} {x : w.adicCompletion ℚ} {n : ℤ}
    (h : Valued.v x = WithZero.exp n) : x ≠ 0 := by
  intro hx; rw [hx, map_zero] at h; exact WithZero.coe_ne_zero h.symm

theorem v_inv_mul_le_one {w : HeightOneSpectrum (𝓞 ℚ)} {x z : w.adicCompletion ℚ} (hx : x ≠ 0)
    (h : Valued.v z ≤ Valued.v x) : Valued.v (x⁻¹ * z) ≤ 1 := by
  have hx' : 0 < Valued.v x := (Valuation.pos_iff _).mpr hx
  rw [map_mul, map_inv₀, ← div_eq_inv_mul, div_le_one₀ hx']
  exact h

section PlaceL
variable {ℓ : ℕ} [hℓF : Fact ℓ.Prime]

theorem coe_gammaA_inv (t : ℤ) (γ : GL (Fin 2) ℚ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) :
    ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ)⁻¹, -(t : ℚ) * (ℓ : ℚ)⁻¹; 0, 1] := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓF.out.ne_zero
  apply coe_inv_of_mul_eq_one
  rw [hγ]; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring1

theorem isLocalLevelZero_shapeA (N : ℕ)
    (ϖ s : (padicPlace ℓ).adicCompletionIntegers ℚ)
    (hϖ0 : algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ ≠ 0)
    (hval : Valued.v (algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ)
      = WithZero.exp (-1))
    (hℓval : Valued.v (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (ℓ : ℚ)) = WithZero.exp (-1))
    (t : ℤ)
    (hst : Valued.v (algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) s
      - algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (t : ℚ)) ≤ WithZero.exp (-1))
    (γ : GL (Fin 2) ℚ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) :
    IsLocalLevelZero N (padicPlace ℓ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ)) γ⁻¹ * LocalGL2.localRepSome ϖ hϖ0 s) := by
  set Kℓ := (padicPlace ℓ).adicCompletion ℚ
  set ℓ' : Kℓ := algebraMap ℚ Kℓ (ℓ : ℚ) with hℓ'
  set t' : Kℓ := algebraMap ℚ Kℓ (t : ℚ) with ht'
  set ϖ' : Kℓ := algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) Kℓ ϖ with hϖ'
  set s' : Kℓ := algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) Kℓ s with hs'
  have hℓ0 : ℓ' ≠ 0 := ne_zero_of_v_eq_exp hℓval
  have hC : (((Matrix.GeneralLinearGroup.map (algebraMap ℚ Kℓ) γ⁻¹ * LocalGL2.localRepSome ϖ hϖ0 s : GL (Fin 2) Kℓ)) :
      Matrix (Fin 2) (Fin 2) Kℓ) = !![ℓ'⁻¹ * ϖ', ℓ'⁻¹ * (s' - t'); 0, 1] := by
    rw [Units.val_mul, map_coe_eq, coe_gammaA_inv t γ hγ, LocalGL2.coe_localRepSome]
    ext i j : 1
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, map_neg, map_mul, map_inv₀, map_one, map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    all_goals (first | rfl | ring1 | skip)
  have hCi : ((((Matrix.GeneralLinearGroup.map (algebraMap ℚ Kℓ) γ⁻¹ * LocalGL2.localRepSome ϖ hϖ0 s)⁻¹ : GL (Fin 2) Kℓ)) :
      Matrix (Fin 2) (Fin 2) Kℓ) = !![ϖ'⁻¹ * ℓ', ϖ'⁻¹ * (t' - s'); 0, 1] := by
    rw [mul_inv_rev, Units.val_mul, ← map_inv, inv_inv, map_coe_eq, hγ,
      show (((LocalGL2.localRepSome ϖ hϖ0 s)⁻¹ : GL (Fin 2) Kℓ) : Matrix (Fin 2) (Fin 2) Kℓ) = _ from
        LocalGL2.coe_localRepSome_inv ϖ hϖ0 s]
    ext i j : 1
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, map_neg, map_mul, map_inv₀, map_one, map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    all_goals (first | rfl | ring1 | skip)
  have hst' : Valued.v (s' - t') ≤ Valued.v ℓ' := hℓval ▸ hst
  have hts' : Valued.v (t' - s') ≤ Valued.v ϖ' := by rw [Valuation.map_sub_swap]; exact hval ▸ hst
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [hC, mem_integers_iff]
    fin_cases i <;> fin_cases j
    · exact v_inv_mul_le_one hℓ0 (by rw [hval, hℓval])
    · exact v_inv_mul_le_one hℓ0 hst'
    · simp
    · simp
  · rw [hCi, mem_integers_iff]
    fin_cases i <;> fin_cases j
    · exact v_inv_mul_le_one hϖ0 (by rw [hval, hℓval])
    · exact v_inv_mul_le_one hϖ0 hts'
    · simp
    · simp
  · rw [hC]; simp
  · rw [hCi]; simp

end PlaceL

section PlaceL2
variable {ℓ : ℕ} [hℓF : Fact ℓ.Prime]

theorem coe_gammaB (σ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(σ 0 0 : ℚ), (σ 0 1 : ℚ) * ℓ; (σ 1 0 : ℚ), (σ 1 1 : ℚ) * ℓ] := by
  rw [hγ]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_gammaB_inv (σ : SL(2, ℤ)) (c₀ : ℤ) (hc : σ 1 0 = ℓ * c₀) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(σ 1 1 : ℚ), -(σ 0 1 : ℚ); -(c₀ : ℚ), (σ 0 0 : ℚ) * (ℓ : ℚ)⁻¹] := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓF.out.ne_zero
  have hdet : (σ 0 0 : ℚ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe σ; rw [Matrix.det_fin_two] at this; exact_mod_cast this
  have hc' : (σ 1 0 : ℚ) = ℓ * c₀ := by exact_mod_cast hc
  have hdet' : (σ 0 0 : ℚ) * σ 1 1 - σ 0 1 * (ℓ * c₀) = 1 := by rw [← hc']; exact hdet
  apply coe_inv_of_mul_eq_one
  rw [coe_gammaB σ γ hγ, hc']; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp)
  all_goals first
    | ring1
    | (linear_combination hdet')
    | (linear_combination (-1 : ℚ) * hdet')
    | (linear_combination (ℓ : ℚ) * hdet')
    | (linear_combination (-(ℓ : ℚ)) * hdet')
    | (linear_combination (2 : ℚ) * hdet')
    | (linear_combination (-2 : ℚ) * hdet')

theorem coe_localRepInf_inv' (ϖ : (padicPlace ℓ).adicCompletionIntegers ℚ)
    (hϖ0 : algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ ≠ 0) :
    (((LocalGL2.localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _)
      = !![1, 0; 0, (algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ)⁻¹] := by
  have hϖ0' : ((ϖ : (padicPlace ℓ).adicCompletionIntegers ℚ) : (padicPlace ℓ).adicCompletion ℚ) ≠ 0 := hϖ0
  apply coe_inv_of_mul_eq_one
  rw [LocalGL2.coe_localRepInf]; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0']
  all_goals first
    | (exact mul_inv_cancel₀ hϖ0')
    | (exact mul_inv_cancel₀ hϖ0)

theorem isLocalLevelZero_shapeB {N : ℕ} (hbound : idealBound (𝓞 ℚ) (ratLevel N) (padicPlace ℓ) = 1)
    (ϖ : (padicPlace ℓ).adicCompletionIntegers ℚ)
    (hϖ0 : algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ ≠ 0)
    (hval : Valued.v (algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ) ϖ)
      = WithZero.exp (-1))
    (hℓval : Valued.v (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (ℓ : ℚ)) = WithZero.exp (-1))
    (σ : SL(2, ℤ)) (c₀ : ℤ) (hc : σ 1 0 = ℓ * c₀) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    IsLocalLevelZero N (padicPlace ℓ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ)) γ⁻¹ * LocalGL2.localRepInf ϖ hϖ0) := by
  set Kℓ := (padicPlace ℓ).adicCompletion ℚ
  set ℓ' : Kℓ := algebraMap ℚ Kℓ (ℓ : ℚ) with hℓ'
  set ϖ' : Kℓ := algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) Kℓ ϖ with hϖ'
  set a' : Kℓ := algebraMap ℚ Kℓ ((σ 0 0 : ℤ) : ℚ)
  set b' : Kℓ := algebraMap ℚ Kℓ ((σ 0 1 : ℤ) : ℚ)
  set c₀' : Kℓ := algebraMap ℚ Kℓ ((c₀ : ℤ) : ℚ)
  set d' : Kℓ := algebraMap ℚ Kℓ ((σ 1 1 : ℤ) : ℚ)
  have hℓ0 : ℓ' ≠ 0 := ne_zero_of_v_eq_exp hℓval
  have ha1 : Valued.v a' ≤ 1 := valued_algebraMap_intCast_le_one _ _
  have hb1 : Valued.v b' ≤ 1 := valued_algebraMap_intCast_le_one _ _
  have hc1 : Valued.v c₀' ≤ 1 := valued_algebraMap_intCast_le_one _ _
  have hd1 : Valued.v d' ≤ 1 := valued_algebraMap_intCast_le_one _ _
  have hℓ1 : Valued.v ℓ' ≤ 1 := by rw [hℓval, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖ1 : Valued.v ϖ' ≤ 1 := by rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hC : (((Matrix.GeneralLinearGroup.map (algebraMap ℚ Kℓ) γ⁻¹ * LocalGL2.localRepInf ϖ hϖ0 : GL (Fin 2) Kℓ)) :
      Matrix (Fin 2) (Fin 2) Kℓ) = !![d', -b' * ϖ'; -c₀', a' * ℓ'⁻¹ * ϖ'] := by
    rw [Units.val_mul, map_coe_eq, coe_gammaB_inv σ c₀ hc γ hγ, LocalGL2.coe_localRepInf]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, map_neg, map_mul, map_inv₀, map_one, map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    all_goals (first | rfl | ring1 | skip)
  have hCi : ((((Matrix.GeneralLinearGroup.map (algebraMap ℚ Kℓ) γ⁻¹ * LocalGL2.localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) Kℓ)) :
      Matrix (Fin 2) (Fin 2) Kℓ) = !![a', b' * ℓ'; ϖ'⁻¹ * (ℓ' * c₀'), ϖ'⁻¹ * (d' * ℓ')] := by
    have hc' : ((σ 1 0 : ℤ) : ℚ) = (ℓ : ℚ) * c₀ := by exact_mod_cast hc
    rw [mul_inv_rev, Units.val_mul, ← map_inv, inv_inv, map_coe_eq, coe_gammaB σ γ hγ, hc', coe_localRepInf_inv' ϖ hϖ0]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, map_neg, map_mul, map_inv₀, map_one, map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    all_goals (first | rfl | ring1 | skip)
  have key1 : Valued.v (ℓ'⁻¹ * ϖ') ≤ 1 := v_inv_mul_le_one hℓ0 (by rw [hval, hℓval])
  have key2 : Valued.v (ϖ'⁻¹ * ℓ') ≤ 1 := v_inv_mul_le_one hϖ0 (by rw [hval, hℓval])
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [hC, mem_integers_iff]
    fin_cases i <;> fin_cases j
    · exact hd1
    · simpa [map_neg, map_mul] using mul_le_one' hb1 hϖ1
    · simpa [map_neg] using hc1
    · show Valued.v (a' * ℓ'⁻¹ * ϖ') ≤ 1
      rw [mul_assoc, map_mul]; exact mul_le_one' ha1 key1
  · rw [hCi, mem_integers_iff]
    fin_cases i <;> fin_cases j
    · exact ha1
    · simpa [map_mul] using mul_le_one' hb1 hℓ1
    · show Valued.v (ϖ'⁻¹ * (ℓ' * c₀')) ≤ 1
      rw [← mul_assoc, map_mul]; exact mul_le_one' key2 hc1
    · show Valued.v (ϖ'⁻¹ * (d' * ℓ')) ≤ 1
      rw [mul_left_comm, map_mul]; exact mul_le_one' hd1 key2
  · rw [hC, hbound]; simpa [map_neg] using hc1
  · rw [hCi, hbound]
    show Valued.v (ϖ'⁻¹ * (ℓ' * c₀')) ≤ 1
    rw [← mul_assoc, map_mul]; exact mul_le_one' key2 hc1

end PlaceL2

end W7E3

set_option autoImplicit false
open scoped MatrixGroups ModularForm

namespace Ws41
namespace E3Classical

open UpperHalfPlane

noncomputable def toGL (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![y, x; 0, 1] (by simp [Matrix.det_fin_two]; exact hy.ne')

@[scoped simp] theorem toGL_coe (x y : ℝ) (hy : 0 < y) :
    ((toGL x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] := rfl

@[scoped simp] theorem toGL_apply (x y : ℝ) (hy : 0 < y) (i j : Fin 2) :
    (toGL x y hy : GL (Fin 2) ℝ) i j = !![y, x; 0, 1] i j := rfl

theorem toGL_det (x y : ℝ) (hy : 0 < y) : (toGL x y hy).det.val = y := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem toGL_mem_glpos (x y : ℝ) (hy : 0 < y) : toGL x y hy ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos, toGL_det]; exact hy

theorem toGL_smul_I (τ : ℍ) : toGL τ.re τ.im τ.im_pos • UpperHalfPlane.I = τ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [toGL_det]; exact τ.im_pos)]
  simp only [num, denom, toGL_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, Complex.ofReal_one, zero_add, div_one]
  apply Complex.ext <;> simp

theorem slash_toGL_apply_I {k : ℤ} (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] toGL τ.re τ.im τ.im_pos) UpperHalfPlane.I = F τ * (τ.im : ℂ) ^ (k - 1) := by
  have hσ : σ (toGL τ.re τ.im τ.im_pos) = .refl ℝ ℂ := if_pos (by rw [toGL_det]; exact τ.im_pos)
  rw [ModularForm.slash_apply, toGL_smul_I, toGL_det, hσ, ContinuousAlgEquiv.refl_apply, abs_of_pos τ.im_pos]
  simp [denom]

theorem eq_of_forall_slash_apply_I {k : ℤ} {F₁ F₂ : ℍ → ℂ}
    (h : ∀ M : GL (Fin 2) ℝ, M ∈ Matrix.GLPos (Fin 2) ℝ →
      (F₁ ∣[k] M) UpperHalfPlane.I = (F₂ ∣[k] M) UpperHalfPlane.I) : F₁ = F₂ := by
  funext τ
  have := h _ (toGL_mem_glpos τ.re τ.im τ.im_pos)
  rw [slash_toGL_apply_I, slash_toGL_apply_I] at this
  exact mul_right_cancel₀ (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr τ.im_pos.ne')) this

theorem σ_eq_refl_of_mem_glpos {A : GL (Fin 2) ℝ} (hA : A ∈ Matrix.GLPos (Fin 2) ℝ) : σ A = .refl ℝ ℂ :=
  if_pos (Matrix.mem_glpos _ |>.mp hA)

end Ws41.E3Classical
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical"
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41"

namespace Ws41
namespace E3Arch

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.AdelicLevel AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

noncomputable def archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
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

noncomputable def archEmbed : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (AdeleRing R K) where
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

end Generic
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical"

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

theorem ratArchGL2_realToArch (M : GL (Fin 2) ℝ) : LanglandsTunnell.ratArchGL2 (realToArch M) = M := by
  rw [ratArchGL2_def, glArch_realToArch]
  ext i j
  simp [archComponent_apply, Matrix.GeneralLinearGroup.map_apply, realToInfAdele_apply]

theorem ext_arch_fin {g h : 𝔸GL} (h₁ : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (h₂ : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ
  · refine Matrix.ext fun i j => ?_
    have e := congrFun (congrFun (congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) h₁) i) j
    simpa [glArch_apply, RingHom.mapMatrix_apply, adeleArch_apply] using e
  · refine Matrix.ext fun i j => ?_
    have e := congrFun (congrFun (congrArg (fun x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) h₂) i) j
    simpa [glFin_apply, RingHom.mapMatrix_apply, adeleFin_apply] using e

theorem archEmbed_glArch_mul_finEmbed_glFin (g : 𝔸GL) :
    archEmbed (𝓞 ℚ) ℚ (glArch (𝓞 ℚ) ℚ g) * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g) = g := by
  apply ext_arch_fin
  · rw [map_mul, glArch_archEmbed, glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_archEmbed, glFin_finEmbed, one_mul]

theorem eq_realToArch_of_glFin_eq_one {h : 𝔸GL} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    h = realToArch (LanglandsTunnell.ratArchGL2 h) := by
  have e : h = archEmbed (𝓞 ℚ) ℚ (glArch (𝓞 ℚ) ℚ h) := by
    conv_lhs => rw [← archEmbed_glArch_mul_finEmbed_glFin h, hh, map_one, mul_one]
  rw [e, realToArch, MonoidHom.comp_apply]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  funext w
  have hw : w = default := Subsingleton.elim _ _
  subst hw
  rw [Matrix.GeneralLinearGroup.map_apply, realToInfAdele_apply, ratArchGL2_def,
    Matrix.GeneralLinearGroup.map_apply, archComponent_apply, glArch_archEmbed]
  simp

theorem eq_of_glFin_eq_one_of_ratArchGL2_eq {h h' : 𝔸GL} (hh : glFin (𝓞 ℚ) ℚ h = 1) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (e : LanglandsTunnell.ratArchGL2 h = LanglandsTunnell.ratArchGL2 h') : h = h' := by
  rw [eq_realToArch_of_glFin_eq_one hh, eq_realToArch_of_glFin_eq_one hh', e]

theorem exists_glFin_eq_one_ratArchGL2_eq (A : GL (Fin 2) ℝ) :
    ∃ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h = A :=
  ⟨realToArch A, glFin_realToArch A, ratArchGL2_realToArch A⟩

end Rat
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical"

end Ws41.E3Arch
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Arch"
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical"

open NumberField IsDedekindDomain AutomorphicForm LocalNewvector
open NumberField.AdelicLevel AdelicDock

namespace W7E3

local notation "𝔸GL" => AdelicGL2 (𝓞 ℚ) ℚ

variable (q : ℕ) [Fact q.Prime]

section Bridge
variable (ℓ : ℕ) [hℓF : Fact ℓ.Prime]

theorem padicPlace_asIdeal : (padicPlace ℓ).asIdeal = Ideal.span {((ℓ : ℕ) : 𝓞 ℚ)} := by
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have hgen : Rat.HeightOneSpectrum.natGenerator (padicPlace ℓ) = ℓ :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨ℓ, hℓF.out⟩)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) (padicPlace ℓ)
  rw [hgen, ← he] at h
  rw [← Ideal.comap_map_of_bijective e e.bijective (I := (padicPlace ℓ).asIdeal), ← h]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · intro hx; have := map_dvd e.symm hx; rwa [map_natCast, RingEquiv.symm_apply_apply] at this
  · intro hx; have := map_dvd e hx; rwa [map_natCast] at this

theorem natCast_mem_padicPlace : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (padicPlace ℓ).asIdeal := by
  rw [padicPlace_asIdeal]; exact Ideal.mem_span_singleton_self _

theorem intCast_mem_padicPlace_iff (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (padicPlace ℓ).asIdeal ↔ (ℓ : ℤ) ∣ n := by
  rw [padicPlace_asIdeal, Ideal.mem_span_singleton]
  constructor
  · intro h
    have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) h
    simpa using this
  · intro h
    have := map_dvd (Int.castRingHom (𝓞 ℚ)) h
    simpa using this

theorem not_asIdeal_dvd_ratLevel {N : ℕ} (hN : ¬ ℓ ∣ N) : ¬ (padicPlace ℓ).asIdeal ∣ ratLevel N := by
  rw [ratLevel, Ideal.dvd_span_singleton, show ((N : ℕ) : 𝓞 ℚ) = ((N : ℤ) : 𝓞 ℚ) by push_cast; rfl,
    intCast_mem_padicPlace_iff]
  exact_mod_cast hN

theorem valued_algebraMap_ell :
    Valued.v (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (ℓ : ℚ)) = WithZero.exp (-1) := by
  rw [valued_algebraMap_eq_valuation, show ((ℓ : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((ℓ : ℕ) : 𝓞 ℚ) by simp,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hℓF.out.ne_zero) (padicPlace_asIdeal ℓ)

theorem valued_algebraMap_ringOfIntegers_le_iff (x : 𝓞 ℚ) :
    Valued.v (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ x)) ≤ WithZero.exp (-1) ↔
      x ∈ (padicPlace ℓ).asIdeal := by
  rw [valued_algebraMap_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap,
    show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]

theorem algebraMap_integers_apply (x : 𝓞 ℚ) :
    algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ)
      (algebraMap (𝓞 ℚ) ((padicPlace ℓ).adicCompletionIntegers ℚ) x)
      = algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ x) := by
  show (((algebraMap (𝓞 ℚ) ((padicPlace ℓ).adicCompletionIntegers ℚ) x :
      (padicPlace ℓ).adicCompletionIntegers ℚ)) : (padicPlace ℓ).adicCompletion ℚ) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]; rfl

theorem algebraMap_rat_intCast (n : ℤ) :
    algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (n : ℚ) =
      algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ)) := by
  simp

noncomputable def quotEquivZMod : 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal ≃+* ZMod ℓ :=
  (Ideal.quotEquivOfEq (padicPlace_asIdeal ℓ)).trans
    ((Ideal.quotientEquiv (Ideal.span {((ℓ : ℕ) : 𝓞 ℚ)}) (Ideal.span {((ℓ : ℕ) : ℤ)})
        (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)
        (by rw [Ideal.map_span, Set.image_singleton]; simp)).trans
      (Int.quotientSpanNatEquivZMod ℓ))

noncomputable scoped instance fintypeQuot : Fintype (𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal) :=
  Fintype.ofEquiv (ZMod ℓ) (quotEquivZMod ℓ).symm.toEquiv

theorem card_quot : Fintype.card (𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal) = ℓ := by
  rw [Fintype.card_congr (quotEquivZMod ℓ).toEquiv, ZMod.card]

theorem absNorm_padicPlace : Ideal.absNorm (padicPlace ℓ).asIdeal = ℓ := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, card_quot]

noncomputable def finEquivQuot : Fin ℓ ≃ 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_quot])

end Bridge
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Arch"

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι κ : Type*} {reps : ι → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (fun k => reps (e k)) where
  mem_doubleCoset k := h.mem_doubleCoset (e k)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by rw [Equiv.apply_symm_apply]; exact hi⟩
  mk_injective a b hab := e.injective (h.mk_injective hab)

theorem exists_sigma (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ σ : SL(2, ℤ), (q : ℤ) ∣ σ 0 1 ∧ σ 1 0 = ((q * M' * ℓ : ℕ) : ℤ) ∧
      ((σ 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q) ∧ 0 < σ 0 0 := by
  have hq : q.Prime := Fact.out
  set m : ℕ := M' * ℓ with hm
  have hm0 : m ≠ 0 := mul_ne_zero (NeZero.ne M') hℓ.ne_zero
  set m₀ : ℕ := m / q ^ m.factorization q with hm₀
  have hm₀0 : m₀ ≠ 0 := (Nat.ordCompl_pos q hm0).ne'
  have hqm₀ : Nat.Coprime q m₀ := (Nat.Prime.coprime_iff_not_dvd hq).mpr (Nat.not_dvd_ordCompl hq hm0)
  haveI : NeZero m₀ := ⟨hm₀0⟩
  set y : ℕ := ((1 - (ℓ : ZMod m₀)) * (q : ZMod m₀)⁻¹).val with hy
  set a : ℕ := ℓ + q * y with ha
  have ha_q : (a : ZMod q) = (ℓ : ZMod q) := by
    rw [ha, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  have ha_m₀ : (a : ZMod m₀) = 1 := by
    have hu : (q : ZMod m₀) * (q : ZMod m₀)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqm₀
    rw [ha, Nat.cast_add, Nat.cast_mul, hy, ZMod.natCast_val, ZMod.cast_id', id]
    linear_combination (1 - (ℓ : ZMod m₀)) * hu
  have hcop_q : Nat.Coprime a q := by
    rw [← ZMod.isUnit_iff_coprime, ha_q, ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_primes hℓ hq).mpr hℓq
  have hcop_m₀ : Nat.Coprime a m₀ := by
    rw [← ZMod.isUnit_iff_coprime, ha_m₀]; exact isUnit_one
  have hcop : Nat.Coprime a (q * (q * M' * ℓ)) := by
    have hdecomp : q ^ m.factorization q * m₀ = m := Nat.ordProj_mul_ordCompl_eq_self m q
    have : q * (q * M' * ℓ) = q ^ (m.factorization q + 2) * m₀ := by
      calc q * (q * M' * ℓ) = q ^ 2 * m := by rw [hm]; ring
        _ = q ^ 2 * (q ^ m.factorization q * m₀) := by rw [hdecomp]
        _ = _ := by ring
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hcop_q) hcop_m₀
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) ((q * (q * M' * ℓ) : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨⟨!![(a : ℤ), -(v * q); ((q * M' * ℓ : ℕ) : ℤ), u], ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; push_cast at huv ⊢; linear_combination huv
  · show (q : ℤ) ∣ -(v * q); exact ⟨-v, by ring⟩
  · rfl
  · show ((a : ℤ) : ZMod q) = _; rw [Int.cast_natCast, ha_q]
  · show (0 : ℤ) < (a : ℤ); have : 0 < a := by rw [ha]; exact Nat.add_pos_left hℓ.pos _
    exact_mod_cast this

theorem map_inv_mem_glpos {γ : GL (Fin 2) ℚ} (hγ : 0 < ((γ.det : ℚˣ) : ℚ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ⁻¹ ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, map_inv, map_inv_coe_eq,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv,
    Units.val_inv_eq_inv_val, map_inv₀, Rat.coe_castHom, inv_pos]
  exact_mod_cast hγ

theorem det_pos_shapeA {ℓ : ℕ} (hℓ : ℓ.Prime) (t : ℤ) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) : 0 < ((γ.det : ℚˣ) : ℚ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hγ, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero]; exact_mod_cast hℓ.pos

theorem det_pos_shapeB {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    0 < ((γ.det : ℚˣ) : ℚ) := by
  have hdet : (σ 0 0 : ℚ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe σ; rw [Matrix.det_fin_two] at this; exact_mod_cast this
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_gammaB σ γ hγ, Matrix.det_fin_two_of]
  have : (σ 0 0 : ℚ) * (σ 1 1 * ℓ) - σ 0 1 * ℓ * σ 1 0 = ℓ := by linear_combination (ℓ : ℚ) * hdet
  rw [this]; exact_mod_cast hℓ.pos

section Away
variable {M' : ℕ} [NeZero M'] {ℓ : ℕ} [hℓF : Fact ℓ.Prime]

theorem norm_level_eq {p : ℕ} [Fact p.Prime] (hpq : p ≠ q) :
    ‖((q ^ 2 * M' : ℕ) : ℚ_[p])‖ = ‖(M' : ℚ_[p])‖ := by
  rw [show q ^ 2 * M' = q * (q * M') by ring, padicNorm_mul_eq_of_ne q hpq, padicNorm_mul_eq_of_ne q hpq]

theorem norm_inv_natCast_of_ne {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) : ‖((ℓ : ℚ) : ℚ_[p])⁻¹‖ = 1 := by
  rw [norm_inv, Rat.cast_natCast, (Padic.norm_natCast_eq_one_iff).mpr ((Nat.coprime_primes Fact.out hℓF.out).mpr hpℓ),
    inv_one]

theorem isLocalLevelZero_shapeA_of_ne {p : ℕ} [Fact p.Prime] (hpq : p ≠ q) (hpℓ : p ≠ ℓ) (t : ℤ)
    (γ : GL (Fin 2) ℚ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t : ℚ); 0, 1]) :
    IsLocalLevelZero (q ^ 2 * M') (padicPlace p)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace p).adicCompletion ℚ)) γ⁻¹) := by
  have hM : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')
  refine isLocalLevelZero_of_rat hM _ ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
    (γ : Matrix (Fin 2) (Fin 2) ℚ) (map_coe_eq _ _) (by rw [map_inv_coe_eq, inv_inv]) ?_ ?_ ?_ ?_
  · intro i j
    rw [coe_gammaA_inv t γ hγ]
    fin_cases i <;> fin_cases j
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.isValue, Rat.cast_inv, norm_inv_natCast_of_ne hpℓ, le_refl]
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.mk_one, Fin.isValue, Fin.zero_eta, Rat.cast_mul, Rat.cast_neg, Rat.cast_inv, Rat.cast_intCast, norm_mul,
        norm_neg, norm_inv_natCast_of_ne hpℓ, mul_one]
      exact Padic.norm_int_le_one t
    · simp
    · simp
  · intro i j
    rw [hγ]
    fin_cases i <;> fin_cases j
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.isValue, Rat.cast_natCast]
      exact_mod_cast Padic.norm_int_le_one (ℓ : ℤ)
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.mk_one, Fin.isValue, Fin.zero_eta, Rat.cast_intCast]
      exact Padic.norm_int_le_one t
    · simp
    · simp
  · rw [coe_gammaA_inv t γ hγ]
    exact (by simp : ‖((!![(ℓ : ℚ)⁻¹, -(t : ℚ) * (ℓ : ℚ)⁻¹; 0, 1] 1 0 : ℚ) : ℚ_[p])‖ = 0).trans_le (norm_nonneg _)
  · rw [hγ]
    exact (by simp : ‖((!![(ℓ : ℚ), (t : ℚ); 0, 1] 1 0 : ℚ) : ℚ_[p])‖ = 0).trans_le (norm_nonneg _)

theorem isLocalLevelZero_shapeB_of_ne {p : ℕ} [Fact p.Prime] (hpq : p ≠ q) (hpℓ : p ≠ ℓ)
    (σ : SL(2, ℤ)) (hc : σ 1 0 = ℓ * (q * M' : ℕ)) (γ : GL (Fin 2) ℚ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℚ) = ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)]) :
    IsLocalLevelZero (q ^ 2 * M') (padicPlace p)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace p).adicCompletion ℚ)) γ⁻¹) := by
  have hM : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')
  have hint : ∀ n : ℤ, ‖((n : ℚ) : ℚ_[p])‖ ≤ 1 := fun n => by rw [Rat.cast_intCast]; exact Padic.norm_int_le_one n
  have hℓ1 : ‖((ℓ : ℚ) : ℚ_[p])‖ ≤ 1 := by rw [Rat.cast_natCast]; exact_mod_cast Padic.norm_int_le_one (ℓ : ℤ)
  have hlev : ‖((((q * M' : ℕ) : ℤ) : ℚ) : ℚ_[p])‖ ≤ ‖((q ^ 2 * M' : ℕ) : ℚ_[p])‖ := by
    rw [norm_level_eq q hpq, Rat.cast_intCast, Int.cast_natCast, padicNorm_mul_eq_of_ne q hpq]
  refine isLocalLevelZero_of_rat hM _ ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
    (γ : Matrix (Fin 2) (Fin 2) ℚ) (map_coe_eq _ _) (by rw [map_inv_coe_eq, inv_inv]) ?_ ?_ ?_ ?_
  · intro i j
    rw [coe_gammaB_inv σ _ hc γ hγ]
    fin_cases i <;> fin_cases j
    · simpa using hint (σ 1 1)
    · simpa using hint (σ 0 1)
    · simpa [Rat.cast_natCast] using hint ((q * M' : ℕ) : ℤ)
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Fin.mk_one, Fin.isValue, Rat.cast_mul, Rat.cast_inv, norm_mul, norm_inv_natCast_of_ne hpℓ, mul_one]
      exact hint (σ 0 0)
  · intro i j
    rw [coe_gammaB σ γ hγ]
    fin_cases i <;> fin_cases j
    · simpa using hint (σ 0 0)
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.mk_one, Fin.isValue, Fin.zero_eta, Rat.cast_mul, norm_mul]
      exact mul_le_one₀ (hint _) (norm_nonneg _) hℓ1
    · simpa using hint (σ 1 0)
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Fin.mk_one, Fin.isValue, Rat.cast_mul, norm_mul]
      exact mul_le_one₀ (hint _) (norm_nonneg _) hℓ1
  · rw [coe_gammaB_inv σ _ hc γ hγ]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.mk_one, Fin.isValue, Fin.zero_eta, Rat.cast_neg, norm_neg]
    exact hlev
  · rw [coe_gammaB σ γ hγ]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.mk_one, Fin.isValue, Fin.zero_eta]
    have hc' : ((σ 1 0 : ℤ) : ℚ) = (ℓ : ℚ) * (((q * M' : ℕ) : ℤ) : ℚ) := by rw [hc]; push_cast; ring
    rw [hc', Rat.cast_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hℓ1).trans hlev

theorem awayPart_mem_of_local (hℓq : ℓ ≠ q) (γ : GL (Fin 2) ℚ) (du : GL (Fin 2) ℚ_[q])
    (m : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ))
    (hℓ : IsLocalLevelZero (q ^ 2 * M') (padicPlace ℓ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ)) γ⁻¹ * m))
    (hp : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → p ≠ ℓ → IsLocalLevelZero (q ^ 2 * M') (padicPlace p)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ((padicPlace p).adicCompletion ℚ)) γ⁻¹)) :
    awayPart q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) * padicToFinAdelic q du *
        localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) m) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')) := by
  have hvq : padicPlace ℓ ≠ padicPlace q := fun h => hℓq (padicPlace_injective h)
  refine mem_finiteLevelZero_of_forall _ _ fun w => ?_
  by_cases hwq : w = padicPlace q
  · subst hwq; rw [finComponent_awayPart]; exact isLocalLevelZero_one _ _
  by_cases hwℓ : w = padicPlace ℓ
  · subst hwℓ; rw [finComponent_triple_self q hvq γ⁻¹ du m]; exact hℓ
  · obtain ⟨p, hpP, rfl⟩ := exists_eq_padicPlace w
    haveI : Fact p.Prime := ⟨hpP⟩
    have hpq : p ≠ q := fun h => hwq (by subst h; rfl)
    have hpℓ : p ≠ ℓ := fun h => hwℓ (by subst h; rfl)
    rw [finComponent_triple_of_ne q hwq hwℓ γ⁻¹ du m]
    exact hp p hpq hpℓ

end Away
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Arch"

section Main
variable {M' : ℕ} [NeZero M']

open LanglandsTunnell in

theorem heckeTLinH_main
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNewform)
    {Φ : 𝔸GL → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (AdelicSpan Φ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M') (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ)
    (u : ℤ_[q]ˣ)
    (F Fu : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        (AdelicSpan.toFn Φ y).toFn
            (h * padicToAdelic q (diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)))) =
          ((⇑F) ∣[(2 : ℤ)] ratArchGL2 h) UpperHalfPlane.I)
    (hFu : ∀ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        (AdelicSpan.toFn Φ y).toFn
            (h * padicToAdelic q (diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
          ((⇑Fu) ∣[(2 : ℤ)] ratArchGL2 h) UpperHalfPlane.I)
    (F' Fu' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
    (hFu' : ⇑Fu' = (⇑Fu) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    CuspForm.heckeTLinH 2 hℓ hℓN F' = (ModularFormClass.qCoeff g ℓ : ℂ) • Fu' := by
  haveI hℓF : Fact ℓ.Prime := ⟨hℓ⟩
  have hq : q.Prime := Fact.out
  have hM : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hq.ne_zero) (NeZero.ne M')
  have hℓq' : ℓ ≠ q := by
    rintro rfl; exact hℓN (dvd_mul_of_dvd_left (dvd_pow_self ℓ two_ne_zero) M')
  have hvq : padicPlace ℓ ≠ padicPlace q := fun h => hℓq' (padicPlace_injective h)
  have hℓQ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  set du : GL (Fin 2) ℚ_[q] := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) with hdu
  set du' : GL (Fin 2) ℚ_[q] := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)) with hdu'

  obtain ⟨ϖ, hϖ0, hval, -, sec, hsec, hsysM⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen ℚ (padicPlace ℓ)
  have hsys0 := hsysM (ratLevel (q ^ 2 * M')) (not_asIdeal_dvd_ratLevel ℓ hℓN)
  clear hsysM
  set E : Fin ℓ ≃ 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal := finEquivQuot ℓ with hE
  set eFin : Fin (Ideal.absNorm (padicPlace ℓ).asIdeal + 1) ≃ Option (𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal) :=
    ((finCongr (by rw [absNorm_padicPlace])).trans (finSuccEquiv ℓ)).trans (Equiv.optionCongr E) with heFin
  set mloc : Option (𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal) → GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ) := fun i =>
    i.elim (LocalGL2.localRepInf ϖ hϖ0)
      (fun c => LocalGL2.localRepSome ϖ hϖ0 (algebraMap (𝓞 ℚ) ((padicPlace ℓ).adicCompletionIntegers ℚ) (sec c)))
    with hmloc
  set reps : Fin (Ideal.absNorm (padicPlace ℓ).asIdeal + 1) → 𝔸GL := fun j =>
    finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc (eFin j))) with hreps
  have hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')) ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ (padicPlace ℓ))
      reps :=
    isHeckeCosetSystem_comp_equiv hsys0 eFin

  have heig : ∀ z : 𝔸GL, ∑ j, (AdelicSpan.toFn Φ y).toFn (z * reps j) =
      (ModularFormClass.qCoeff g ℓ : ℂ) * (AdelicSpan.toFn Φ y).toFn z := fun z =>
    CuspForm.IsAdelicLiftOf.sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
      q hg.isNormalizedEigenform hΦg y hy hℓ hℓN reps hsys (fun j => ⟨mloc (eFin j), rfl⟩) z

  have hqℓcop : Nat.Coprime q ℓ := (Nat.coprime_primes hq hℓ).mpr (Ne.symm hℓq')
  set q' : ℕ := ((q : ZMod ℓ)⁻¹).val with hq'
  have hqq' : ((q * q' : ℕ) : ZMod ℓ) = 1 := by
    rw [Nat.cast_mul, hq', ZMod.natCast_val, ZMod.cast_id', id, ZMod.coe_mul_inv_eq_one q hqℓcop]
  set nz : 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal → ℤ := fun c => Rat.ringOfIntegersEquiv (sec c) with hnz
  set tc : 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal → ℤ := fun c => nz c * (q * q' : ℕ) with htc
  have htq : ∀ c, (q : ℤ) ∣ tc c := fun c => ⟨nz c * q', by simp only [htc]; push_cast; ring⟩
  have hnz_cast : ∀ c, ((nz c : ℤ) : 𝓞 ℚ) = sec c := fun c =>
    (eq_intCast (Rat.ringOfIntegersEquiv.symm.toRingHom) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply _)
  have hℓdvd : (ℓ : ℤ) ∣ 1 - (q * q' : ℕ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
    rw [show ((q : ZMod ℓ) * (q' : ZMod ℓ)) = 1 by exact_mod_cast hqq', sub_self]
  have hmem : ∀ c, sec c - ((tc c : ℤ) : 𝓞 ℚ) ∈ (padicPlace ℓ).asIdeal := fun c => by
    have h2 : sec c - ((tc c : ℤ) : 𝓞 ℚ) = (((nz c * (1 - (q * q' : ℕ)) : ℤ)) : 𝓞 ℚ) := by
      rw [← hnz_cast c, htc]; push_cast; ring
    rw [h2, intCast_mem_padicPlace_iff]
    exact Dvd.dvd.mul_left hℓdvd _
  have hst : ∀ c, Valued.v (algebraMap ((padicPlace ℓ).adicCompletionIntegers ℚ) ((padicPlace ℓ).adicCompletion ℚ)
        (algebraMap (𝓞 ℚ) ((padicPlace ℓ).adicCompletionIntegers ℚ) (sec c))
        - algebraMap ℚ ((padicPlace ℓ).adicCompletion ℚ) ((tc c : ℤ) : ℚ)) ≤ WithZero.exp (-1) := fun c => by
    rw [algebraMap_integers_apply, algebraMap_rat_intCast, ← map_sub, ← map_sub,
      valued_algebraMap_ringOfIntegers_le_iff]
    exact hmem c
  have htinj : Function.Injective fun c => ((tc c : ℤ) : ZMod ℓ) := by
    intro c c' hcc'
    have h3 : ((nz c : ℤ) : ZMod ℓ) = ((nz c' : ℤ) : ZMod ℓ) := by
      have h := hcc'
      simp only [htc, Int.cast_mul, Int.cast_natCast, hqq', mul_one] at h
      exact h
    have h4 : (ℓ : ℤ) ∣ nz c - nz c' := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h3, sub_self]
    have h5 : sec c - sec c' ∈ (padicPlace ℓ).asIdeal := by
      rw [← hnz_cast c, ← hnz_cast c', ← Int.cast_sub, intCast_mem_padicPlace_iff]; exact h4
    rw [← hsec c, ← hsec c']
    exact Ideal.Quotient.eq.mpr h5

  set γA : 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal → GL (Fin 2) ℚ := fun c =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), (tc c : ℚ); 0, 1]
      (by rw [Matrix.det_fin_two_of]; simp [hℓQ0]) with hγA
  have hγA_coe : ∀ c, ((γA c : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (tc c : ℚ); 0, 1] :=
    fun c => rfl
  obtain ⟨σ₀, hσb, hσc, hσa, -⟩ := exists_sigma q M' hℓ hℓq'
  have hdetσ : (((σ₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)).det = 1 := by
    rw [show (Int.cast : ℤ → ℚ) = ⇑(Int.castRingHom ℚ) from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.SpecialLinearGroup.det_coe, map_one]
  set γB : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (((σ₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
      (by rw [Matrix.det_mul, hdetσ, Matrix.det_fin_two_of]; simp [hℓQ0]) with hγB
  have hγB_coe : (γB : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)] := rfl
  have hσc' : σ₀ 1 0 = ℓ * ((q * M' : ℕ) : ℤ) := by rw [hσc]; push_cast; ring
  have hσcq : (q : ℤ) ∣ σ₀ 1 0 := ⟨(M' * ℓ : ℕ), by rw [hσc]; push_cast; ring⟩
  have hposA : ∀ c, Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γA c)⁻¹ ∈ Matrix.GLPos (Fin 2) ℝ :=
    fun c => map_inv_mem_glpos (det_pos_shapeA hℓ _ _ (hγA_coe c))
  have hposB : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γB⁻¹ ∈ Matrix.GLPos (Fin 2) ℝ :=
    map_inv_mem_glpos (det_pos_shapeB hℓ σ₀ _ hγB_coe)

  have hterm : ∀ (γ : GL (Fin 2) ℚ) (m : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)),
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ⁻¹ ∈ Matrix.GLPos (Fin 2) ℝ →
      (∃ k : GL (Fin 2) ℚ_[q], k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 ∧
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[q]) γ⁻¹ * du = du' * k) →
      awayPart q (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) * padicToFinAdelic q du *
          localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) m) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')) →
      ∀ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q du *
            finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) m)) =
          (((⇑F) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ⁻¹) ∣[(2 : ℤ)] ratArchGL2 h)
            UpperHalfPlane.I := by
    intro γ m hpos hk ha h hh hhpos
    obtain ⟨k, hk, hqk⟩ := hk
    rw [toFn_coset_term q hΦg y hy hfix hvq m γ du du' k hk hqk ha h hh]
    have hh' : glFin (𝓞 ℚ) ℚ (archOf γ⁻¹ * h) = 1 := by rw [map_mul, glFin_archOf, hh, one_mul]
    have hpos' : ratArchGL2 (archOf γ⁻¹ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [ratArchGL2_archOf_mul]; exact Subgroup.mul_mem _ hpos hhpos
    rw [hF _ hh' hpos', ratArchGL2_archOf_mul, SlashAction.slash_mul]
  have hA : ∀ c (h : 𝔸GL), glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q du *
          finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc (some c)))) =
        (((⇑F) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γA c)⁻¹) ∣[(2 : ℤ)] ratArchGL2 h)
          UpperHalfPlane.I := fun c =>
    hterm (γA c) (mloc (some c)) (hposA c) (shapeA_q q hℓ hℓq' ℓq hℓq (tc c) (htq c) (γA c) (hγA_coe c) u)
      (awayPart_mem_of_local q hℓq' (γA c) du _
        (isLocalLevelZero_shapeA (q ^ 2 * M') ϖ _ hϖ0 hval (valued_algebraMap_ell ℓ) (tc c) (hst c)
          (γA c) (hγA_coe c))
        (fun p _ hpq hpℓ => isLocalLevelZero_shapeA_of_ne q hpq hpℓ (tc c) (γA c) (hγA_coe c)))
  have hB : ∀ (h : 𝔸GL), glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q du *
          finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc none))) =
        (((⇑F) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γB⁻¹) ∣[(2 : ℤ)] ratArchGL2 h)
          UpperHalfPlane.I :=
    hterm γB (mloc none) hposB (shapeB_q q hℓ hℓq' ℓq hℓq σ₀ hσb hσcq hσa γB hγB_coe u)
      (awayPart_mem_of_local q hℓq' γB du _
        (isLocalLevelZero_shapeB
          (idealBound_eq_one_of_not_dvd (ratLevel_ne_bot hM) (not_asIdeal_dvd_ratLevel ℓ hℓN))
          ϖ hϖ0 hval (valued_algebraMap_ell ℓ) σ₀ _ hσc' γB hγB_coe)
        (fun p _ hpq hpℓ => isLocalLevelZero_shapeB_of_ne q hpq hpℓ σ₀ hσc' γB hγB_coe))

  set aℓ : ℂ := (ModularFormClass.qCoeff g ℓ : ℂ) with haℓ
  set fsum : UpperHalfPlane → ℂ :=
    (∑ i : Fin ℓ, (⇑F) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γA (E i))⁻¹) +
      (⇑F) ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γB⁻¹ with hfsum
  have hval_h : ∀ h : 𝔸GL, glFin (𝓞 ℚ) ℚ h = 1 → ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (fsum ∣[(2 : ℤ)] ratArchGL2 h) UpperHalfPlane.I =
        ((aℓ • ⇑Fu) ∣[(2 : ℤ)] ratArchGL2 h) UpperHalfPlane.I := by
    intro h hh hhpos
    have e1 := heig (h * padicToAdelic q du)
    rw [hFu h hh hhpos] at e1
    have e2 : ∑ j, (AdelicSpan.toFn Φ y).toFn (h * padicToAdelic q du * reps j)
        = ∑ o : Option (𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal), (AdelicSpan.toFn Φ y).toFn
            (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc o))) :=
      Fintype.sum_equiv eFin _ _ (fun j => rfl)
    have e3 : ∑ c : 𝓞 ℚ ⧸ (padicPlace ℓ).asIdeal, (AdelicSpan.toFn Φ y).toFn
            (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc (some c))))
        = ∑ i : Fin ℓ, (AdelicSpan.toFn Φ y).toFn
            (h * padicToAdelic q du * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ (padicPlace ℓ) (mloc (some (E i))))) :=
      (Fintype.sum_equiv E _ _ (fun i => rfl)).symm
    rw [e2, Fintype.sum_option, e3, hB h hh hhpos,
      Finset.sum_congr rfl (fun i _ => hA (E i) h hh hhpos)] at e1
    rw [hfsum, SlashAction.add_slash, Pi.add_apply, SlashAction.sum_slash, Finset.sum_apply,
      ModularForm.smul_slash, Ws41.E3Classical.σ_eq_refl_of_mem_glpos hhpos, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul, ← e1, add_comm]
  have hfun : fsum = aℓ • ⇑Fu :=
    Ws41.E3Classical.eq_of_forall_slash_apply_I (k := 2) fun A hA' => by
      obtain ⟨h, hh, hhA⟩ := Ws41.E3Arch.exists_glFin_eq_one_ratArchGL2_eq A
      subst hhA
      exact hval_h h hh hA'

  have hT := CuspForm.sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH q M' hℓ hℓN
      (fun i => tc (E i)) (fun i => htq (E i)) (htinj.comp E.injective)
      (fun i => γA (E i)) (fun i => hγA_coe (E i)) σ₀ hσb ⟨1, by rw [hσc, mul_one]⟩ hσa γB hγB_coe (⇑F) F' hF'
  change fsum ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q = ⇑(CuspForm.heckeTLinH 2 hℓ hℓN F') at hT
  rw [hfun, ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply, ← hFu'] at hT
  exact DFunLike.coe_injective (hT.symm.trans rfl)

end Main
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Arch"

end W7E3
p2m_reactivate "P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41 P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Classical P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.Ws41.E3Arch P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform.W7E3"

theorem solution
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNewform)
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M') (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ)
    (u : ℤ_[q]ˣ)
    (F Fu : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (u * ℓq⁻¹)))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (hFu : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
              ((⇑Fu) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I)
    (F' Fu' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
    (hFu' : ⇑Fu' = (⇑Fu) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    CuspForm.heckeTLinH 2 hℓ hℓN F' = (ModularFormClass.qCoeff g ℓ : ℂ) • Fu' :=
  W7E3.heckeTLinH_main q hg hΦg y hy hfix hℓ hℓN ℓq hℓq u F Fu hF hFu F' Fu' hF' hFu'

end S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform (solution)
