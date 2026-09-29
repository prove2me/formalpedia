-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5f61238b-a3b4-5e4f-81eb-364cc27ff8b1

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Theorems.Thm_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1
import Theorems.Thm_CuspForm_IsPrimitiveForm_factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1
import Theorems.Thm_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
import Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable
import Theorems.Thm_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace PSLevelNebentypus

variable (q : ℕ) [Fact q.Prime]

abbrev unitsCoe : ℤ_[q]ˣ →* ℚ_[q]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom

@[scoped simp] theorem val_unitsCoe (u : ℤ_[q]ˣ) : ((unitsCoe q u : ℚ_[q]ˣ) : ℚ_[q]) = ((u : ℤ_[q]) : ℚ_[q]) := rfl

theorem norm_unitsCoe (u : ℤ_[q]ˣ) : ‖((unitsCoe q u : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
  rw [val_unitsCoe]
  exact PadicInt.isUnit_iff.mp u.isUnit

theorem unitsCoe_mkUnits {z : ℚ_[q]ˣ} (hz : ‖(z : ℚ_[q])‖ = 1) :
    unitsCoe q (PadicInt.mkUnits hz) = z :=
  Units.ext (by rw [val_unitsCoe, PadicInt.mkUnits_eq])

section Adelic

theorem coe_glArch (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ((AdelicLevel.glArch (𝓞 ℚ) ℚ g : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := rfl

theorem coe_finComponent_glFin (w : HeightOneSpectrum (𝓞 ℚ)) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ g) : GL (Fin 2) (w.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) := rfl

theorem adelicGL2_ext {g h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (harch : AdelicLevel.glArch (𝓞 ℚ) ℚ g = AdelicLevel.glArch (𝓞 ℚ) ℚ h)
    (hfin : ∀ w, AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ g) =
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ h)) : g = h := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [← coe_glArch, ← coe_glArch, harch]
  · refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [← coe_finComponent_glFin, ← coe_finComponent_glFin, hfin w]

def qComponent (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom
    (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g))

theorem padicGL_qComponent (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicGL q (qComponent q g) =
      AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, qComponent, Matrix.GeneralLinearGroup.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

def awayPart (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ :=
  (AdelicDock.padicToAdelic q (qComponent q g))⁻¹ * g

theorem finComponent_awayPart_self (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ (awayPart q g)) = 1 := by
  rw [awayPart, map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
    AdelicDock.finComponent_padicToFinAdelic_self, padicGL_qComponent, inv_mul_cancel]

theorem padicToAdelic_mul_awayPart (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicToAdelic q (qComponent q g) * awayPart q g = g := by
  rw [awayPart, mul_inv_cancel_left]

theorem padicToAdelic_mul_comm_of_finComponent_eq_one {g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g) = 1)
    (x : GL (Fin 2) ℚ_[q]) :
    AdelicDock.padicToAdelic q x * g = g * AdelicDock.padicToAdelic q x := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.glArch_padicToAdelic, one_mul, mul_one]
  · intro w
    rw [map_mul, map_mul, map_mul, map_mul, AdelicDock.glFin_padicToAdelic]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw; rw [hg, mul_one, one_mul]
    · rw [AdelicDock.finComponent_padicToFinAdelic_of_ne _ _ hw, one_mul, mul_one]

end Adelic

section SpanFacts

open LocalNewvector

variable {φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem mk_smul_mk (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (h : g • AdelicFnCarrier.mk φ ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (g • AdelicFnCarrier.mk φ) h = g • AdelicSpan.self φ :=
  AdelicSpan.ext φ rfl

theorem mk_zero (h : (0 : AdelicFnCarrier ℚ) ∈ AdelicSpanSubmodule φ) : AdelicSpan.mk φ 0 h = 0 :=
  AdelicSpan.ext φ rfl

theorem mk_add (x y : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule φ) (hy : y ∈ AdelicSpanSubmodule φ)
    (hxy : x + y ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (x + y) hxy = AdelicSpan.mk φ x hx + AdelicSpan.mk φ y hy :=
  AdelicSpan.ext φ rfl

theorem mk_csmul (a : ℂ) (x : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule φ)
    (hax : a • x ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (a • x) hax = a • AdelicSpan.mk φ x hx :=
  AdelicSpan.ext φ rfl

theorem mk_toFn (v : AdelicSpan φ) :
    AdelicSpan.mk φ (AdelicSpan.toFn φ v) (v : AdelicSpanSubmodule φ).2 = v :=
  AdelicSpan.ext φ rfl

theorem linearMap_eq_zero_of_forall_translate {N : Type*} [AddCommGroup N] [Module ℂ N]
    (L : AdelicSpan φ →ₗ[ℂ] N)
    (hL : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, L (g • AdelicSpan.self φ) = 0) : L = 0 := by
  have key : ∀ (ψ : AdelicFnCarrier ℚ) (hψ : ψ ∈ AdelicSpanSubmodule φ), L (AdelicSpan.mk φ ψ hψ) = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [mk_smul_mk]; exact hL g
    | zero => rw [mk_zero, map_zero]
    | add x y hx hy ihx ihy => rw [mk_add x y hx hy, map_add, ihx, ihy, add_zero]
    | smul a x hx ih => rw [mk_csmul a x hx, map_smul, ih, smul_zero]
  ext v
  rw [LinearMap.zero_apply, ← mk_toFn v]
  exact key _ _

def qSpan (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ (AdelicSpan φ) :=
  Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)

theorem self_mem_qSpan : AdelicSpan.self φ ∈ qSpan q φ :=
  Submodule.subset_span ⟨1, one_smul _ _⟩

theorem smul_mem_qSpan (x : GL (Fin 2) ℚ_[q]) : ∀ w ∈ qSpan q φ, x • w ∈ qSpan q φ := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', rfl⟩ := hw
    exact Submodule.subset_span ⟨x * x', by simp only [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ ih₁ ih₂ => rw [smul_add]; exact add_mem ih₁ ih₂
  | smul a w _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih

theorem qSpan_smooth (K : Subgroup (GL (Fin 2) ℚ_[q])) (hKopen : IsOpen (K : Set (GL (Fin 2) ℚ_[q])))
    (hKfix : ∀ k ∈ K, k • AdelicSpan.self φ = AdelicSpan.self φ) :
    ∀ w ∈ qSpan q φ, ∃ U : Subgroup (GL (Fin 2) ℚ_[q]),
      IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    refine ⟨K.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hKopen.preimage ?_
      show Continuous fun u : GL (Fin 2) ℚ_[q] => x⁻¹ * u * x⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · intro u hu
      rw [Subgroup.mem_comap] at hu
      have hk := hKfix _ hu
      show u • x • AdelicSpan.self φ = x • AdelicSpan.self φ
      have hux : u * x = x * (x⁻¹ * u * x⁻¹⁻¹) := by group
      rw [← mul_smul, hux, mul_smul]
      exact congrArg (fun v => x • v) hk
  | zero => exact ⟨⊤, isOpen_univ, fun u _ => smul_zero u⟩
  | add w₁ w₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, ?_, fun u hu => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · rw [smul_add, h₁ u hu.1, h₂ u hu.2]
  | smul a w _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    exact ⟨U, hU, fun u hu => by rw [smul_comm, h u hu]⟩

end SpanFacts

section Generator

open LocalNewvector

variable (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

theorem toFn_toFn_smul_self (g x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (x • AdelicSpan.self Φ)).toFn g = Φ (g * x) := rfl

theorem toFn_toFn_self (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (AdelicSpan.self Φ)).toFn g = Φ g := rfl

theorem toFn_toFn_csmul (a : ℂ) (v : AdelicSpan Φ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (a • v)).toFn g = a * (AdelicSpan.toFn _ v).toFn g := rfl

theorem smul_self_eq_self_of {k : GL (Fin 2) ℚ_[q]}
    (hΦk : ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x) :
    k • AdelicSpan.self Φ = AdelicSpan.self Φ := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun g => ?_)
  rw [AdelicSpan.padic_smul_def, toFn_toFn_smul_self, toFn_toFn_self, hΦk]

theorem centralGL_smul_self_of {z : ℚ_[q]ˣ} {c : ℂ}
    (hΦz : ∀ x, Φ (x * AdelicDock.padicToAdelic q (centralGL q z)) = c * Φ x) :
    centralGL q z • AdelicSpan.self Φ = c • AdelicSpan.self Φ := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun g => ?_)
  rw [AdelicSpan.padic_smul_def, toFn_toFn_smul_self, toFn_toFn_csmul, toFn_toFn_self, hΦz]

theorem centralGL_mul_comm (z : ℚ_[q]ˣ) (x : GL (Fin 2) ℚ_[q]) : centralGL q z * x = x * centralGL q z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact Algebra.commutes (z : ℚ_[q]) (x : Matrix (Fin 2) (Fin 2) ℚ_[q])

end Generator

section PSCentre

open LocalNewvector

variable {ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ}

theorem borelElem_self_eq_centralGL (z : ℚ_[q]ˣ) : borelElem q z z 0 = centralGL q z := by
  apply Units.ext
  rw [coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralGL, Matrix.algebraMap_matrix_apply]

theorem halfModulus_self (z : ℚ_[q]ˣ) : halfModulus q z z = 1 := by
  have hz : ‖(z : ℚ_[q])‖ ≠ 0 := norm_ne_zero_iff.mpr z.ne_zero
  simp only [halfModulus, div_self hz, Real.sqrt_one, Complex.ofReal_one]

theorem centralGL_smul_ps (z : ℚ_[q]ˣ) (F : PSCarrier q ν₁ ν₂) :
    centralGL q z • F = ((ν₁ z : ℂ) * (ν₂ z : ℂ)) • F := by
  refine PSCarrier.ext q ν₁ ν₂ fun y => ?_
  rw [PSCarrier.toFn_smul, PSCarrier.toFn_csmul, ← centralGL_mul_comm, ← borelElem_self_eq_centralGL,
    apply_borelElem_mul_of_mem_principalSeries q (PSCarrier.toFn_mem q ν₁ ν₂ F), halfModulus_self, mul_one]

end PSCentre

section LocalLevel

open LocalNewvector

variable {ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ}

theorem fixedSubmodule_padicK1_mono {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[q]) V] [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    {a b : ℕ} (hab : a ≤ b) :
    fixedSubmodule (padicK1 q a) V ≤ fixedSubmodule (padicK1 q b) V := by
  intro v hv
  rw [mem_fixedSubmodule_iff] at hv ⊢
  exact fun g hg => hv g (congruenceK1_antitone hab hg)

theorem norm_det_eq_one_of_mem_padicK1 {m : ℕ} {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ padicK1 q m) :
    ‖((Matrix.GeneralLinearGroup.det k : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
  obtain ⟨y, rfl, -, -⟩ := hk
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  show ‖(algebraMap ℤ_[q] ℚ_[q]) ((Matrix.GeneralLinearGroup.det y : ℤ_[q]ˣ) : ℤ_[q])‖ = 1
  rw [PadicInt.algebraMap_apply]
  exact PadicInt.isUnit_iff.mp (Matrix.GeneralLinearGroup.det y).isUnit

theorem exists_ne_zero_mem_fixedSubmodule_of_stable {n₂ : ℕ}
    (h₁ : HasCharConductor q ν₁ 0) (h₂ : HasCharConductor q ν₂ n₂)
    (W : Submodule ℂ (PSCarrier q ν₁ ν₂)) (hW : ∀ g : GL (Fin 2) ℚ_[q], ∀ v ∈ W, g • v ∈ W)
    (hb : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ w ∈ fixedSubmodule (padicK1 q (max n₂ 1)) (PSCarrier q ν₁ ν₂) := by
  classical

  have htop : W = ⊤ → ∃ w ∈ W, w ≠ 0 ∧ w ∈ fixedSubmodule (padicK1 q (max n₂ 1)) (PSCarrier q ν₁ ν₂) := by
    intro hWtop
    have hfin := PSCarrier.finrank_fixedSubmodule_padicK1 q h₁ h₂ (max n₂ 1)
    have hpos : 0 < Module.finrank ℂ ↥(fixedSubmodule (padicK1 q (max n₂ 1)) (PSCarrier q ν₁ ν₂)) := by
      rw [hfin]; omega
    haveI := Module.nontrivial_of_finrank_pos (R := ℂ) hpos
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : ↥(fixedSubmodule (padicK1 q (max n₂ 1)) (PSCarrier q ν₁ ν₂)))
    refine ⟨w₀, by rw [hWtop]; exact Submodule.mem_top, fun h => hw₀ (Subtype.ext h), w₀.2⟩
  set ϖ : ℚ_[q]ˣ := Units.mk0 (q : ℚ_[q]) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) with hϖ_def
  by_cases hgen : IsUnramified q (ν₁⁻¹ * ν₂) →
      (ν₁ ϖ : ℂ) * ((ν₂ ϖ : ℂ))⁻¹ ≠ (q : ℂ) ∧ (ν₁ ϖ : ℂ) * ((ν₂ ϖ : ℂ))⁻¹ ≠ ((q : ℂ))⁻¹
  ·
    have hirr := PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio q h₁ h₂ hgen
    rcases hirr.2 W hW with hbot | hWtop
    · exact absurd hbot hb
    · exact htop hWtop
  ·
    push Not at hgen
    obtain ⟨hun, hspecial⟩ := hgen
    have hν₂un : IsUnramified q ν₂ := by
      intro z hz
      have h1 : ν₁ z = 1 := (hasCharConductor_zero_iff_isUnramified q).mp h₁ z hz
      have h2 : (ν₁⁻¹ * ν₂) z = 1 := hun z hz
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, inv_one, one_mul] at h2
      exact h2
    have h₂' : HasCharConductor q ν₂ 0 := (hasCharConductor_zero_iff_isUnramified q).mpr hν₂un
    have hn₂ : n₂ = 0 := hasCharConductor_unique q h₂ h₂'
    subst hn₂
    by_cases hWtop : W = ⊤
    · exact htop hWtop
    rw [Nat.zero_max]
    by_cases hr : (ν₁ ϖ : ℂ) * ((ν₂ ϖ : ℂ))⁻¹ = (q : ℂ)
    ·
      obtain ⟨T₀, hT₀, hclass⟩ :=
        PSCarrier.exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast q h₁ hun hr
      rcases (hclass W).mp hW with hbot | hWT | hWtop'
      · exact absurd hbot hb
      · have hT₀W : T₀ ∈ W := by rw [hWT]; exact Submodule.mem_span_singleton_self T₀
        have hT₀ne : T₀ ≠ 0 := by
          intro h0
          apply hb
          rw [hWT, h0, Submodule.span_singleton_eq_bot]
        refine ⟨T₀, hT₀W, hT₀ne, ?_⟩
        rw [mem_fixedSubmodule_iff]
        intro k hk
        have hdk := norm_det_eq_one_of_mem_padicK1 q hk
        refine PSCarrier.ext q ν₁ ν₂ fun g => ?_
        rw [PSCarrier.toFn_smul, hT₀, hT₀, map_mul, map_mul, Units.val_mul,
          h₁.1 _ ((mem_higherUnits_zero_iff q).mpr hdk), Units.val_one, mul_one]
        congr 1
        refine halfModulus_congr q ?_ rfl
        rw [Units.val_mul, norm_mul, hdk, mul_one]
      · exact absurd hWtop' hWtop
    ·
      have hr' := hspecial hr
      have hfin := PSCarrier.finrank_inf_fixedSubmodule_padicK1_of_stable q h₁ h₂' hr' W hW hb hWtop 1
      have hpos : 0 < Module.finrank ℂ ↥(W ⊓ fixedSubmodule (padicK1 q 1) (PSCarrier q ν₁ ν₂)) := by
        rw [hfin]; norm_num
      haveI := Module.nontrivial_of_finrank_pos (R := ℂ) hpos
      obtain ⟨w₀, hw₀⟩ := exists_ne (0 : ↥(W ⊓ fixedSubmodule (padicK1 q 1) (PSCarrier q ν₁ ν₂)))
      exact ⟨w₀, w₀.2.1, fun h => hw₀ (Subtype.ext h), w₀.2.2⟩

end LocalLevel

end PSLevelNebentypus
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified.PSLevelNebentypus"

open NumberField LocalNewvector PSLevelNebentypus in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hν₁ : LocalNewvector.IsUnramified q ν₁) :
    M.factorization q = ε.conductor.factorization q ∨
      (q ∣ M ∧ ¬ q ^ 2 ∣ M ∧ ¬ q ∣ ε.conductor) := by
  classical
  have hq : q.Prime := Fact.out
  have hM0 : M ≠ 0 := NeZero.ne M
  set n : ℕ := M.factorization q with hn_def
  set c₀ : ℕ := ε.conductor.factorization q with hc₀_def
  have hcond0 : ε.conductor ≠ 0 := ε.conductor_ne_zero
  have hcondM : ε.conductor ∣ M := ε.conductor_dvd_level
  have hc₀n : c₀ ≤ n := (Nat.factorization_le_iff_dvd hcond0 hM0).mpr hcondM q

  suffices hmain : ∃ n₂ : ℕ, n₂ ≤ c₀ ∧ n ≤ max n₂ 1 by
    obtain ⟨n₂, hn₂c₀, hnle⟩ := hmain
    rcases Nat.eq_zero_or_pos n₂ with h0 | hpos
    · rw [h0, Nat.zero_max] at hnle
      rcases Nat.lt_or_ge n 1 with hn0 | hn1
      · left; omega
      · rcases Nat.lt_or_ge c₀ 1 with hc0 | hc1
        · right
          refine ⟨(hq.dvd_iff_one_le_factorization hM0).mpr hn1, fun h2 => ?_, fun hd => ?_⟩
          · have := (hq.pow_dvd_iff_le_factorization hM0).mp h2
            omega
          · have := (hq.dvd_iff_one_le_factorization hcond0).mp hd
            omega
        · left; omega
    · left
      have : n ≤ n₂ := hnle.trans (max_le le_rfl hpos)
      omega

  have hΦK : ∀ k ∈ padicK1 q n, ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x := by
    intro k hk x
    have hmem := AdelicDock.padicToAdelic_mem_levelOne q hM0 le_rfl hk
    rw [AdelicDock.padicToAdelic_apply] at hmem ⊢
    exact hΦh.level_inv _ ((AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mp hmem) x

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, f (g₀ • AdelicSpan.self Φ) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (linearMap_eq_zero_of_forall_translate f hall)
  set gq := awayPart q g₀ with hgq_def
  have hgq1 := finComponent_awayPart_self q g₀
  have hcomm : ∀ x : GL (Fin 2) ℚ_[q], AdelicDock.padicToAdelic q x * gq = gq * AdelicDock.padicToAdelic q x :=
    fun x => padicToAdelic_mul_comm_of_finComponent_eq_one q hgq1 x
  have hgqself : f (gq • AdelicSpan.self Φ) ≠ 0 := by
    intro h0
    apply hg₀
    rw [← padicToAdelic_mul_awayPart q g₀, mul_smul, ← AdelicSpan.padic_smul_def, hfequiv, ← hgq_def, h0,
      smul_zero]
  set T : AdelicSpan Φ →ₗ[ℂ] PSCarrier q ν₁ ν₂ := f ∘ₗ DistribSMul.toLinearMap ℂ (AdelicSpan Φ) gq with hT_def
  have hT_apply : ∀ v, T v = f (gq • v) := fun v => rfl
  have hT : ∀ (x : GL (Fin 2) ℚ_[q]) (v : AdelicSpan Φ), T (x • v) = x • T v := by
    intro x v
    rw [hT_apply, hT_apply, AdelicSpan.padic_smul_def, ← mul_smul, ← hcomm x, mul_smul,
      ← AdelicSpan.padic_smul_def, hfequiv]
  have hTself : T (AdelicSpan.self Φ) ≠ 0 := hgqself

  set W : Submodule ℂ (AdelicSpan Φ) := qSpan q Φ with hW_def
  have hW : ∀ x : GL (Fin 2) ℚ_[q], ∀ w ∈ W, x • w ∈ W := smul_mem_qSpan q
  have hKfix : ∀ k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n, k • AdelicSpan.self Φ = AdelicSpan.self Φ :=
    fun k hk => smul_self_eq_self_of q Φ (hΦK k (gl2CongruenceSubgroup_le_padicK1 q n hk))
  have hsmooth := qSpan_smooth q (FLT.SmoothVectors.gl2CongruenceSubgroup q n)
    (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q n) hKfix

  set M' : ℕ := M / q ^ n with hM'_def
  have hMfac : q ^ n * M' = M := Nat.ordProj_mul_ordCompl_eq_self M q
  have hcop : Nat.Coprime (q ^ n) M' := (Nat.coprime_ordCompl hq hM0).pow_left n
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hdex : ∀ u : ℤ_[q]ˣ, ∃ d : ℕ, ((d : ℤ_[q]) * u - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ n}) ∧
      ((M' : ℤ) ∣ (d : ℤ) - 1) ∧ d.Coprime M := by
    intro u
    set r : ZMod (q ^ n) := PadicInt.toZModPow n ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) with hr
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop r.val 1
    have hkr : (k : ZMod (q ^ n)) = r := by
      rw [← ZMod.natCast_zmod_val r]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hk1
    refine ⟨k, ?_, hk2.symm.dvd, ?_⟩
    · rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, map_mul, map_natCast, hkr, hr,
        ← map_mul, Units.inv_mul, map_one, sub_self]
    · rw [← hMfac]
      refine Nat.Coprime.mul_right ?_ ?_
      · have hu : IsUnit ((k : ZMod (q ^ n))) := by
          rw [hkr, hr]
          exact (Units.map (PadicInt.toZModPow n).toMonoidHom u⁻¹).isUnit
        exact (ZMod.isUnit_iff_coprime k (q ^ n)).mp hu
      · rw [Nat.Coprime, hk2.gcd_eq, Nat.gcd_one_left]
  choose d hdq hdM hdcop using hdex
  have hε : CuspForm.HasNebentypus ε h := hh.isEigenformWith.hasNebentypus
  have hcentΦ : ∀ (u : ℤ_[q]ˣ) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (x * AdelicDock.padicToAdelic q (centralGL q (unitsCoe q u))) = ε ((d u : ℕ) : ZMod M) * Φ x := by
    intro u x
    have := hε.apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1 Φ hΦh q u ((d u : ℕ) : ℤ)
      (by rw [Int.cast_natCast]; exact hdq u) (hdM u) x
    rw [Int.cast_natCast] at this
    exact this

  have hcentW : ∀ (u : ℤ_[q]ˣ), ∀ w ∈ W,
      centralGL q (unitsCoe q u) • w = (ε ((d u : ℕ) : ZMod M)) • w := by
    intro u w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, rfl⟩ := hw
      show centralGL q (unitsCoe q u) • x • AdelicSpan.self Φ = _
      rw [← mul_smul, centralGL_mul_comm, mul_smul, centralGL_smul_self_of q Φ (hcentΦ u), smul_comm]
    | zero => rw [smul_zero, smul_zero]
    | add w₁ w₂ _ _ ih₁ ih₂ => rw [smul_add, smul_add, ih₁, ih₂]
    | smul a w _ ih => rw [smul_comm, ih, smul_comm]

  have hprod : ∀ u : ℤ_[q]ˣ, (ν₁ (unitsCoe q u) : ℂ) * (ν₂ (unitsCoe q u) : ℂ) = ε ((d u : ℕ) : ZMod M) := by
    intro u
    have h1 : T (centralGL q (unitsCoe q u) • AdelicSpan.self Φ) =
        ((ν₁ (unitsCoe q u) : ℂ) * (ν₂ (unitsCoe q u) : ℂ)) • T (AdelicSpan.self Φ) := by
      rw [hT, centralGL_smul_ps]
    have h2 : T (centralGL q (unitsCoe q u) • AdelicSpan.self Φ) =
        (ε ((d u : ℕ) : ZMod M)) • T (AdelicSpan.self Φ) := by
      rw [hcentW u _ (self_mem_qSpan q), map_smul]
    by_contra hne
    apply hTself
    have h3 : (((ν₁ (unitsCoe q u) : ℂ) * (ν₂ (unitsCoe q u) : ℂ)) - ε ((d u : ℕ) : ZMod M)) •
        T (AdelicSpan.self Φ) = 0 := by
      rw [sub_smul, ← h1, h2, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)
  have hν₂θ : ∀ u : ℤ_[q]ˣ, (ν₂ (unitsCoe q u) : ℂ) = ε ((d u : ℕ) : ZMod M) := by
    intro u
    rw [← hprod u, hν₁ _ (norm_unitsCoe q u), Units.val_one, one_mul]

  have hθ1 : ∀ u : ℤ_[q]ˣ, (u : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ c₀} →
      ε ((d u : ℕ) : ZMod M) = 1 := by
    intro u hu

    have h1 : ((d u : ℕ) : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ c₀} := by
      have hsplit : ((d u : ℕ) : ℤ_[q]) - 1 =
          (d u : ℤ_[q]) * (-((u : ℤ_[q]) - 1)) + ((d u : ℤ_[q]) * u - 1) := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Submodule.neg_mem _ hu))
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₀n) (hdq u))
    have h2 : ((q : ℤ) ^ c₀) ∣ ((d u : ℕ) : ℤ) - 1 := by
      have hcast : ((((d u : ℕ) : ℤ) - 1 : ℤ) : ℤ_[q]) = ((d u : ℕ) : ℤ_[q]) - 1 := by push_cast; ring
      rw [← PadicInt.norm_int_le_pow_iff_dvd, hcast, PadicInt.norm_le_pow_iff_mem_span_pow]
      exact h1

    have h3 : ((ε.conductor / q ^ c₀ : ℕ) : ℤ) ∣ ((d u : ℕ) : ℤ) - 1 :=
      (Int.natCast_dvd_natCast.mpr (Nat.ordCompl_dvd_ordCompl_of_dvd hcondM q)).trans (hdM u)

    have h4 : (ε.conductor : ℤ) ∣ ((d u : ℕ) : ℤ) - 1 := by
      have hfac : (ε.conductor : ℤ) = ((q : ℤ) ^ c₀) * ((ε.conductor / q ^ c₀ : ℕ) : ℤ) := by
        have := (Nat.ordProj_mul_ordCompl_eq_self ε.conductor q).symm
        exact_mod_cast this
      rw [hfac]
      refine IsCoprime.mul_dvd ?_ h2 h3
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hcopc : Nat.Coprime (q ^ c₀) (ε.conductor / q ^ c₀) := (Nat.coprime_ordCompl hq hcond0).pow_left c₀
      have : Int.gcd ((q : ℤ) ^ c₀) ((ε.conductor / q ^ c₀ : ℕ) : ℤ) = Nat.gcd (q ^ c₀) (ε.conductor / q ^ c₀) := by
        rw [show ((q : ℤ) ^ c₀) = ((q ^ c₀ : ℕ) : ℤ) by push_cast; rfl, Int.gcd_natCast_natCast]
      rw [this]
      exact hcopc

    obtain ⟨hdvd, χ₀, hεχ⟩ := ε.factorsThrough_conductor
    have hunit : IsUnit ((d u : ℕ) : ZMod M) := (ZMod.isUnit_iff_coprime _ _).mpr (hdcop u)
    have h5 : ((d u : ℕ) : ZMod ε.conductor) = 1 := by
      have h5' : (((d u : ℕ) : ℤ) : ZMod ε.conductor) = ((1 : ℤ) : ZMod ε.conductor) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact (dvd_sub_comm.mp h4)
      rwa [Int.cast_natCast, Int.cast_one] at h5'
    have hεd := congrArg (fun χ : DirichletCharacter ℂ M => χ ((d u : ℕ) : ZMod M)) hεχ
    rw [hεd, ← hunit.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd, IsUnit.unit_spec,
      ZMod.cast_natCast hdvd, h5, map_one]

  have hc₀ok : ∀ z ∈ higherUnits q c₀, ν₂ z = 1 := by
    intro z hz
    have hz1 : ‖(z : ℚ_[q])‖ = 1 := hz.1
    have hu : unitsCoe q (PadicInt.mkUnits hz1) = z := unitsCoe_mkUnits q hz1
    apply Units.ext
    rw [← hu, hν₂θ, Units.val_one]
    apply hθ1
    rcases hz.2 with h0 | hle
    · rw [h0, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    · rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      have : ‖((PadicInt.mkUnits hz1 : ℤ_[q]ˣ) : ℤ_[q]) - 1‖ = ‖(z : ℚ_[q]) - 1‖ := by
        rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.mkUnits_eq]
      rw [this]
      exact hle
  have hex : ∃ c, ∀ z ∈ higherUnits q c, ν₂ z = 1 := ⟨c₀, hc₀ok⟩
  set n₂ : ℕ := Nat.find hex with hn₂_def
  have hν₂c : HasCharConductor q ν₂ n₂ := by
    refine ⟨Nat.find_spec hex, fun m hm => ?_⟩
    have hmin := Nat.find_min hex hm
    push Not at hmin
    exact hmin
  have hn₂c₀ : n₂ ≤ c₀ := Nat.find_min' hex hc₀ok
  have hν₁c : HasCharConductor q ν₁ 0 := (hasCharConductor_zero_iff_isUnramified q).mpr hν₁

  have hWT : ∀ x : GL (Fin 2) ℚ_[q], ∀ v ∈ W.map T, x • v ∈ W.map T := by
    rintro x _ ⟨w', hw', rfl⟩
    exact ⟨x • w', hW x w' hw', hT x w'⟩
  have hWTb : W.map T ≠ ⊥ := by
    intro hbot
    apply hTself
    have : T (AdelicSpan.self Φ) ∈ W.map T := ⟨_, self_mem_qSpan q, rfl⟩
    rw [hbot] at this
    exact (Submodule.mem_bot ℂ).mp this
  obtain ⟨w₀, hw₀W, hw₀ne, hw₀fix⟩ :=
    exists_ne_zero_mem_fixedSubmodule_of_stable q hν₁c hν₂c (W.map T) hWT hWTb
  obtain ⟨v, hvW, hTv⟩ := hw₀W
  obtain ⟨y, hyW, hyfix, hTy⟩ :=
    exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule q ν₁ ν₂ T hT W hW hsmooth (max n₂ 1) hvW
      (by rw [hTv]; exact hw₀fix)
  have hy0 : y ≠ 0 := by
    intro h0
    apply hw₀ne
    rw [← hTv, ← hTy, h0, map_zero]

  have hle := hh.factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1 q Φ hΦh (le_max_right n₂ 1)
    y hyW hyfix hy0
  exact ⟨n₂, hn₂c₀, hle⟩

end
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified.PSLevelNebentypus"

end S_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified (solution)
