-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/92dc246a-230e-59e4-9d74-61b4ae98c280

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ComponentEquivariance

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector

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

theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

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

theorem map_castHom_mapGL (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem mapGL_mem_GLPos (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem mapGL_rat_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((γ i j : ℤ) : ℚ) := by
  simp [Matrix.SpecialLinearGroup.mapGL]

section Local

variable (q : ℕ) [hq : Fact q.Prime]

def slQ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ_[q] := Matrix.SpecialLinearGroup.mapGL ℚ_[q] γ

theorem slQ_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((slQ q γ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j = ((γ i j : ℤ) : ℚ_[q]) := by
  simp [slQ, Matrix.SpecialLinearGroup.mapGL]

theorem slQ_inv (γ : SL(2, ℤ)) : (slQ q γ)⁻¹ = slQ q γ⁻¹ := by
  rw [slQ, slQ, map_inv]

theorem slQ_mem (γ : SL(2, ℤ)) : slQ q γ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [mem_gl2CongruenceSubgroup_zero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [slQ_apply]; exact Padic.norm_int_le_one _
  · rw [slQ_inv, slQ_apply]; exact Padic.norm_int_le_one _

def dQ (u : ℤ_[q]ˣ) : GL (Fin 2) ℚ_[q] := diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u)

theorem dQ_apply (u : ℤ_[q]ˣ) (i j : Fin 2) :
    ((dQ q u : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j
      = Matrix.diagonal ![((u : ℤ_[q]) : ℚ_[q]), 1] i j := rfl

theorem dQ_inv (u : ℤ_[q]ˣ) : (dQ q u)⁻¹ = dQ q u⁻¹ := by
  rw [dQ, dQ, ← map_inv, ← map_inv]

theorem norm_dQ_apply_le (u : ℤ_[q]ˣ) (i j : Fin 2) :
    ‖((dQ q u : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1 := by
  rw [dQ_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem dQ_mem (u : ℤ_[q]ˣ) : dQ q u ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [mem_gl2CongruenceSubgroup_zero_iff]
  refine ⟨fun i j => norm_dQ_apply_le q u i j, fun i j => ?_⟩
  rw [dQ_inv]
  exact norm_dQ_apply_le q u⁻¹ i j

theorem dQ_apply_int (u : ℤ_[q]ˣ) (i j : Fin 2) :
    ((dQ q u : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j
      = ((Matrix.diagonal ![(u : ℤ_[q]), 1] i j : ℤ_[q]) : ℚ_[q]) := by
  rw [dQ_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl2ReductionHom_dQ (u : ℤ_[q]ˣ) :
    gl2ReductionHom q ⟨dQ q u, dQ_mem q u⟩ = CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [CuspidalType.diagElem_val,
    gl2ReductionHom_apply_of_coe_eq q ⟨dQ q u, dQ_mem q u⟩ i j (Matrix.diagonal ![(u : ℤ_[q]), 1] i j)
      (dQ_apply_int q u i j).symm]
  fin_cases i <;> fin_cases j <;> simp

theorem gl2ReductionHom_slQ_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((gl2ReductionHom q ⟨slQ q γ, slQ_mem q γ⟩ : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j
      = ((γ i j : ℤ) : ZMod q) := by
  rw [gl2ReductionHom_apply_of_coe_eq q _ i j ((γ i j : ℤ) : ℤ_[q]) (by rw [PadicInt.coe_intCast, slQ_apply]),
    map_intCast]

theorem exists_dQ_mul_eq (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (u : ℤ_[q]ˣ) (γ : SL(2, ℤ))
    (hγq : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) *
          gl2ReductionHom q k *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (u * Matrix.GeneralLinearGroup.det (gl2IntegralLift q k))))⁻¹ : CuspidalType.GL2 q) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j) :
    ∃ κ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1,
      dQ q u * (k : GL (Fin 2) ℚ_[q]) =
        slQ q γ * dQ q (u * Matrix.GeneralLinearGroup.det (gl2IntegralLift q k)) * κ := by
  set u' : ℤ_[q]ˣ := u * Matrix.GeneralLinearGroup.det (gl2IntegralLift q k) with hu'
  set G : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) := ⟨slQ q γ, slQ_mem q γ⟩ with hG
  set Du : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) := ⟨dQ q u, dQ_mem q u⟩ with hDu
  set Du' : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) := ⟨dQ q u', dQ_mem q u'⟩ with hDu'

  have hred : gl2ReductionHom q G = gl2ReductionHom q (Du * k * Du'⁻¹) := by
    rw [map_mul, map_mul, map_inv, hDu, hDu', gl2ReductionHom_dQ, gl2ReductionHom_dQ]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [hG, gl2ReductionHom_slQ_apply]
    exact hγq i j

  have hker : G⁻¹ * (Du * k * Du'⁻¹) ∈ (gl2ReductionHom q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hred, inv_mul_cancel]
  have hκ : (slQ q γ)⁻¹ * (dQ q u * (k : GL (Fin 2) ℚ_[q]) * (dQ q u')⁻¹)
      ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 := by
    have := (mem_ker_gl2ReductionHom_iff q _).1 hker
    simpa [hG, hDu, hDu'] using this

  have hκ' : (dQ q u')⁻¹ * ((slQ q γ)⁻¹ * (dQ q u * (k : GL (Fin 2) ℚ_[q]) * (dQ q u')⁻¹)) * (dQ q u')⁻¹⁻¹
      ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 :=
    FLT.SmoothVectors.conj_mem_gl2CongruenceSubgroup q (Subgroup.inv_mem _ (dQ_mem q u')) hκ
  refine ⟨_, hκ', ?_⟩
  group

end Local

def finPart (γ : SL(2, ℤ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ))

theorem finPart_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((finPart γ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ i j : ℤ) : ℚ) := by
  rw [finPart, glFin_globalPoints_apply, mapGL_rat_apply]

theorem finPart_inv (γ : SL(2, ℤ)) : (finPart γ)⁻¹ = finPart γ⁻¹ := by
  rw [finPart, finPart, map_inv, map_inv, map_inv]

theorem finComponent_finPart_apply (ℓ : ℕ) [Fact ℓ.Prime] (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((finComponent (𝓞 ℚ) ℚ (padicPlace ℓ) (finPart γ) : GL (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) ((padicPlace ℓ).adicCompletion ℚ)) i j
      = padicRingEquiv ℓ (((γ i j : ℤ) : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  rw [finComponent_apply, finPart_apply, algebraMap_intCast_apply_padicPlace_eq]

theorem intCast_mem_span_pow_factorization (q : ℕ) {M' : ℕ} (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hq' : q.Prime)
    {a : ℤ} (ha : (M' : ℤ) ∣ a) :
    (a : ℤ_[ℓ]) ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ (q ^ 2 * M').factorization ℓ} := by
  by_cases hM' : M' = 0
  · subst hM'
    simp only [mul_zero, Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, pow_zero,
      Ideal.span_singleton_one, Submodule.mem_top]
  have hfac : (q ^ 2 * M').factorization ℓ = M'.factorization ℓ := by
    rw [Nat.factorization_mul (pow_ne_zero 2 hq'.ne_zero) hM', Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, hq'.factorization, Finsupp.single_apply, if_neg (Ne.symm hℓq), smul_zero, zero_add]
  rw [hfac]
  have hdvd : ((ℓ : ℤ) ^ M'.factorization ℓ) ∣ a :=
    (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd M' ℓ)).trans (by exact_mod_cast ha)
  obtain ⟨c, hc⟩ := hdvd
  refine Ideal.mem_span_singleton.mpr ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this ⊢
  exact this

theorem dvd_of_mem_Gamma_10 {M' : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma M') :
    (M' : ℤ) ∣ (γ 1 0 : ℤ) :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

theorem dvd_of_mem_Gamma_11 {M' : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma M') :
    (M' : ℤ) ∣ (γ 1 1 : ℤ) - 1 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
  push_cast
  rw [(CongruenceSubgroup.Gamma_mem.mp hγ).2.2.2, sub_self]

section Away

variable (q : ℕ) [hq : Fact q.Prime]

theorem finComponent_finPart_self (γ : SL(2, ℤ)) :
    finComponent (𝓞 ℚ) ℚ (padicPlace q) (finPart γ) = padicGL q (slQ q γ) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_finPart_apply, padicGL_apply, slQ_apply, PadicInt.coe_intCast]

def awayPart (γ : SL(2, ℤ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  finPart γ * (padicToFinAdelic q (slQ q γ))⁻¹

theorem finPart_eq_awayPart_mul (γ : SL(2, ℤ)) :
    finPart γ = awayPart q γ * padicToFinAdelic q (slQ q γ) := by
  rw [awayPart, inv_mul_cancel_right]

theorem finComponent_awayPart_self (γ : SL(2, ℤ)) :
    finComponent (𝓞 ℚ) ℚ (padicPlace q) (awayPart q γ) = 1 := by
  rw [awayPart, map_mul, map_inv, finComponent_finPart_self, finComponent_padicToFinAdelic_self, mul_inv_cancel]

theorem finComponent_awayPart_of_ne (γ : SL(2, ℤ)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace q) :
    finComponent (𝓞 ℚ) ℚ w (awayPart q γ) = finComponent (𝓞 ℚ) ℚ w (finPart γ) := by
  rw [awayPart, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne _ _ hw, inv_one, mul_one]

theorem padicToFinAdelic_mul_comm_of_finComponent_eq_one {W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hW : finComponent (𝓞 ℚ) ℚ (padicPlace q) W = 1) (x : GL (Fin 2) ℚ_[q]) :
    padicToFinAdelic q x * W = W * padicToFinAdelic q x := by
  refine glEq_of_forall_finComponent_eq fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = padicPlace q
  · subst hw
    rw [hW, mul_one, one_mul]
  · rw [finComponent_padicToFinAdelic_of_ne _ _ hw, one_mul, mul_one]

theorem isLevelOneMatrix_of_finComponent {M' : ℕ} [NeZero M'] {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M')
    {W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hWq : finComponent (𝓞 ℚ) ℚ (padicPlace q) W = 1)
    (hW : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ padicPlace q →
      finComponent (𝓞 ℚ) ℚ w W = finComponent (𝓞 ℚ) ℚ w (finPart δ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M'))
      ((W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hq' : q.Prime := Fact.out
  have hN : q ^ 2 * M' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hq'.ne_zero) (NeZero.ne M')

  have hentry : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2),
      ((W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w
        = ((finComponent (𝓞 ℚ) ℚ w W : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _) i j :=
    fun w i j => (finComponent_apply (𝓞 ℚ) ℚ w W i j).symm

  have hq_entry : ∀ i j : Fin 2,
      ((W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j (padicPlace q)
        = (1 : Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) i j := by
    intro i j
    rw [hentry, hWq, Units.val_one]

  have hplace : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), w = padicPlace ℓ := fun w =>
    ⟨_, ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩, eq_padicPlace_natGenerator w⟩
  have haway : ∀ (ℓ : ℕ) [Fact ℓ.Prime], padicPlace ℓ ≠ padicPlace q → ∀ i j : Fin 2,
      ((W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j (padicPlace ℓ)
        = padicRingEquiv ℓ (((δ i j : ℤ) : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    intro ℓ _ hw i j
    rw [hentry, hW _ hw, finComponent_finPart_apply]
  have hne : ∀ (ℓ : ℕ) [Fact ℓ.Prime], padicPlace ℓ ≠ padicPlace q → ℓ ≠ q := by
    intro ℓ _ hw heq
    subst heq
    exact hw rfl
  refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
  ·
    by_cases hw : w = padicPlace q
    · subst hw
      rw [hq_entry, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · obtain ⟨ℓ, hℓ, rfl⟩ := hplace w
      rw [haway ℓ hw i j]
      exact padicRingEquiv_coe_mem ℓ _
  ·
    by_cases hw : w = padicPlace q
    · subst hw
      rw [hq_entry, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'
    · obtain ⟨ℓ, hℓ, rfl⟩ := hplace w
      rw [haway ℓ hw 1 0, valued_coe_le_idealBound_iff ℓ hN]
      exact intCast_mem_span_pow_factorization q ℓ (hne ℓ hw) hq' (dvd_of_mem_Gamma_10 hδ)
  ·
    rw [coe_sub_apply, coe_one_apply]
    by_cases hw : w = padicPlace q
    · subst hw
      rw [hq_entry, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_le'
    · obtain ⟨ℓ, hℓ, rfl⟩ := hplace w
      have hcast : ((δ 1 1 : ℤ) : ℤ_[ℓ]) - 1 = (((δ 1 1 : ℤ) - 1 : ℤ) : ℤ_[ℓ]) := by push_cast; ring
      rw [haway ℓ hw 1 1, ← map_one (padicRingEquiv ℓ), ← map_sub, ← PadicInt.coe_one, ← PadicInt.coe_sub, hcast,
        valued_coe_le_idealBound_iff ℓ hN]
      exact intCast_mem_span_pow_factorization q ℓ (hne ℓ hw) hq' (dvd_of_mem_Gamma_11 hδ)

theorem awayPart_mem_finiteLevelOne {M' : ℕ} [NeZero M'] {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma M') :
    awayPart q γ ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')) := by
  refine mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩
  · exact isLevelOneMatrix_of_finComponent q hγ (finComponent_awayPart_self q γ)
      (fun w hw => finComponent_awayPart_of_ne q γ hw)
  · refine isLevelOneMatrix_of_finComponent q (Subgroup.inv_mem _ hγ) ?_ (fun w hw => ?_)
    · rw [map_inv, finComponent_awayPart_self, inv_one]
    · rw [map_inv, finComponent_awayPart_of_ne q γ hw, ← map_inv, finPart_inv]

end Away

section Invariance

variable {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (q : ℕ) [hq : Fact q.Prime]

theorem toFn_globalPoints_mul (hΦg : g.IsAdelicLiftOf Φ) {y : AdelicSpan Φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (δ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn Φ y).toFn (globalPoints (𝓞 ℚ) ℚ δ * z) = (AdelicSpan.toFn Φ y).toFn z := by
  induction hy using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    show Φ (globalPoints (𝓞 ℚ) ℚ δ * z * padicToAdelic q x) = Φ (z * padicToAdelic q x)
    rw [mul_assoc, hΦg.left_inv]
  | zero => rfl
  | add a b _ _ ha hb =>
    show (AdelicSpan.toFn Φ a).toFn (globalPoints (𝓞 ℚ) ℚ δ * z) + (AdelicSpan.toFn Φ b).toFn (globalPoints (𝓞 ℚ) ℚ δ * z)
      = (AdelicSpan.toFn Φ a).toFn z + (AdelicSpan.toFn Φ b).toFn z
    rw [ha, hb]
  | smul c a _ ha =>
    show c • (AdelicSpan.toFn Φ a).toFn (globalPoints (𝓞 ℚ) ℚ δ * z) = c • (AdelicSpan.toFn Φ a).toFn z
    rw [ha]

theorem toFn_mul_finEmbed (hΦg : g.IsAdelicLiftOf Φ) {y : AdelicSpan Φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    {W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hW : W ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    (hWq : finComponent (𝓞 ℚ) ℚ (padicPlace q) W = 1) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn Φ y).toFn (z * finEmbed (𝓞 ℚ) ℚ W) = (AdelicSpan.toFn Φ y).toFn z := by
  induction hy using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    show Φ (z * finEmbed (𝓞 ℚ) ℚ W * padicToAdelic q x) = Φ (z * padicToAdelic q x)
    have hcomm : finEmbed (𝓞 ℚ) ℚ W * padicToAdelic q x = padicToAdelic q x * finEmbed (𝓞 ℚ) ℚ W := by
      rw [padicToAdelic_apply, ← map_mul, ← map_mul, padicToFinAdelic_mul_comm_of_finComponent_eq_one q hWq]
    rw [mul_assoc, hcomm, ← mul_assoc, hΦg.level_inv _ hW]
  | zero => rfl
  | add a b _ _ ha hb =>
    show (AdelicSpan.toFn Φ a).toFn (z * finEmbed (𝓞 ℚ) ℚ W) + (AdelicSpan.toFn Φ b).toFn (z * finEmbed (𝓞 ℚ) ℚ W)
      = (AdelicSpan.toFn Φ a).toFn z + (AdelicSpan.toFn Φ b).toFn z
    rw [ha, hb]
  | smul c a _ ha =>
    show c • (AdelicSpan.toFn Φ a).toFn (z * finEmbed (𝓞 ℚ) ℚ W) = c • (AdelicSpan.toFn Φ a).toFn z
    rw [ha]

theorem toFn_mul_padicToAdelic_of_mem_fixedSubmodule {y : AdelicSpan Φ}
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (AdelicSpan Φ))
    {κ : GL (Fin 2) ℚ_[q]} (hκ : κ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn Φ y).toFn (z * padicToAdelic q κ) = (AdelicSpan.toFn Φ y).toFn z := by
  have h := (mem_fixedSubmodule_iff.mp hfix) κ hκ
  have h' := congrArg (fun w : AdelicSpan Φ => (AdelicSpan.toFn Φ w).toFn z) h
  exact h'

end Invariance

end ComponentEquivariance

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector ComponentEquivariance in

theorem solution
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (u : ℤ_[q]ˣ)
    (γ : SL(2, ℤ)) (hγM : γ ∈ CongruenceSubgroup.Gamma M')
    (hγq : ∀ i j : Fin 2, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod q) =
      ((CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u) *
          LocalNewvector.gl2ReductionHom q k *
          (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom
            (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))⁻¹ : CuspidalType.GL2 q) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j)
    (F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2)
    (hF : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom
                    (u * Matrix.GeneralLinearGroup.det (LocalNewvector.gl2IntegralLift q k))))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          (LocalNewvector.AdelicSpan.toFn Φ y).toFn
              (h * AdelicDock.padicToAdelic q
                (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) *
                  (k : GL (Fin 2) ℚ_[q]))) =
            (((⇑F) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h)
              UpperHalfPlane.I := by
  intro h hfin hpos
  set u' : ℤ_[q]ˣ := u * Matrix.GeneralLinearGroup.det (gl2IntegralLift q k) with hu'

  obtain ⟨κ, hκ, hloc⟩ := exists_dQ_mul_eq q k u γ hγq
  have hDu : diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) * (k : GL (Fin 2) ℚ_[q])
      = slQ q γ * dQ q u' * κ := hloc

  set γQ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hγQ
  set W : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := awayPart q γ with hWdef
  set fW : AdelicGL2 (𝓞 ℚ) ℚ := finEmbed (𝓞 ℚ) ℚ W with hfW
  set ιs : AdelicGL2 (𝓞 ℚ) ℚ := padicToAdelic q (slQ q γ) with hιs
  set ιd : AdelicGL2 (𝓞 ℚ) ℚ := padicToAdelic q (dQ q u') with hιd
  set A : AdelicGL2 (𝓞 ℚ) ℚ := (archPart γQ)⁻¹ * h with hA
  have hWq : finComponent (𝓞 ℚ) ℚ (padicPlace q) W = 1 := finComponent_awayPart_self q γ
  have hWlev : W ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel (q ^ 2 * M')) := awayPart_mem_finiteLevelOne q hγM

  have hG : globalPoints (𝓞 ℚ) ℚ γQ = archPart γQ * fW * ιs := by
    rw [globalPoints_eq_archPart_mul γQ, mul_assoc]
    congr 1
    rw [hfW, hιs, padicToAdelic_apply, ← map_mul, hWdef, ← finPart_eq_awayPart_mul]
    rfl

  have hAfin : glFin (𝓞 ℚ) ℚ A = 1 := by
    rw [hA, map_mul, map_inv, glFin_archPart, inv_one, one_mul, hfin]
  have hcW : ∀ x : GL (Fin 2) ℚ_[q], padicToAdelic q x * fW = fW * padicToAdelic q x := fun x => by
    rw [hfW, padicToAdelic_apply, ← map_mul, padicToFinAdelic_mul_comm_of_finComponent_eq_one q hWq, map_mul]
  have e1 : fW⁻¹ * A = A * fW⁻¹ := by
    rw [hfW, ← map_inv]; exact finEmbed_mul_comm_of_glFin_eq_one hAfin _
  have e2 : ιs⁻¹ * A = A * ιs⁻¹ := by
    rw [hιs, padicToAdelic_apply, ← map_inv]; exact finEmbed_mul_comm_of_glFin_eq_one hAfin _
  have e3 : fW⁻¹ * ιs = ιs * fW⁻¹ := ((show Commute ιs fW from hcW (slQ q γ)).inv_right).eq.symm
  have e4 : fW⁻¹ * ιd = ιd * fW⁻¹ := ((show Commute ιd fW from hcW (dQ q u')).inv_right).eq.symm

  have hconj : (globalPoints (𝓞 ℚ) ℚ γQ)⁻¹ * (h * ιs * ιd) = A * ιd * fW⁻¹ := by
    rw [hG, mul_inv_rev, mul_inv_rev]
    calc ιs⁻¹ * (fW⁻¹ * (archPart γQ)⁻¹) * (h * ιs * ιd)
        = ιs⁻¹ * (fW⁻¹ * A) * ιs * ιd := by rw [hA]; group
      _ = A * (ιs⁻¹ * (fW⁻¹ * ιs)) * ιd := by rw [e1, ← mul_assoc, e2]; group
      _ = A * (fW⁻¹ * ιd) := by rw [e3, inv_mul_cancel_left, mul_assoc]
      _ = A * ιd * fW⁻¹ := by rw [e4, ← mul_assoc]
  have hstep : h * padicToAdelic q (diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u) * (k : GL (Fin 2) ℚ_[q]))
      = globalPoints (𝓞 ℚ) ℚ γQ * (A * ιd * fW⁻¹) * padicToAdelic q κ := by
    rw [hDu, map_mul, map_mul, ← hιs, ← hιd, ← hconj]
    group

  have hAarch : LanglandsTunnell.ratArchGL2 A
      = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ * LanglandsTunnell.ratArchGL2 h := by
    rw [hA, ratArch_mul, ratArch_inv, ratArch_archPart, hγQ, map_castHom_mapGL]
  have hApos : LanglandsTunnell.ratArchGL2 A ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hAarch]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mapGL_mem_GLPos γ)) hpos
  have hWinv_q : finComponent (𝓞 ℚ) ℚ (padicPlace q) W⁻¹ = 1 := by
    rw [map_inv, hWq, inv_one]
  rw [hstep, toFn_mul_padicToAdelic_of_mem_fixedSubmodule q hfix hκ, toFn_globalPoints_mul q hΦg hy,
    hfW, ← map_inv (finEmbed (𝓞 ℚ) ℚ) W, toFn_mul_finEmbed q hΦg hy (Subgroup.inv_mem _ hWlev) hWinv_q, hιd, dQ,
    hF A hAfin hApos,
    hAarch, SlashAction.slash_mul, ← map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) γ]
  rfl

end
end S_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_apply_mul_padicToAdelic_diagOne_mul_eq_slash_inv_slash_of_component (solution)
