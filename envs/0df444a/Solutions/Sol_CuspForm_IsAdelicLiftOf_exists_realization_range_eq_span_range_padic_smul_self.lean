-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.exists_realization_range_eq_span_range_padic_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2752da00-5075-5255-abbc-764df8857ced

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier

import Theorems.Thm_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_exists_realization_range_eq_span_range_padic_smul_self
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv"

set_option autoImplicit false

theorem solution
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) V)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V)
      (_ : FiniteDimensional ℂ
        ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))
      (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) ∧ Function.Injective f ∧
      LinearMap.range f =
        Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) := by
  classical

  set S : Submodule ℂ (LocalNewvector.AdelicSpan Φ) :=
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) with hS

  have hstab : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), v ∈ S → x • v ∈ S := by
    intro x v hv
    have hle : S.map (DistribSMul.toLinearMap ℂ (LocalNewvector.AdelicSpan Φ) x) ≤ S := by
      rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨x * y, mul_smul x y (LocalNewvector.AdelicSpan.self Φ)⟩
    exact hle (Submodule.mem_map_of_mem hv)

  letI instDMA : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥S :=
    { smul := fun x v => ⟨x • (v : LocalNewvector.AdelicSpan Φ), hstab x v.1 v.2⟩
      one_smul := fun v => Subtype.ext (one_smul (GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ))
      mul_smul := fun x y v => Subtype.ext (mul_smul x y (v : LocalNewvector.AdelicSpan Φ))
      smul_zero := fun x => Subtype.ext (smul_zero (A := LocalNewvector.AdelicSpan Φ) x)
      smul_add := fun x v w =>
        Subtype.ext (smul_add (A := LocalNewvector.AdelicSpan Φ) x (v : LocalNewvector.AdelicSpan Φ) w) }
  have hcoe : ∀ (x : GL (Fin 2) ℚ_[q]) (v : ↥S), ((x • v : ↥S) : LocalNewvector.AdelicSpan Φ) = x • (v : _) :=
    fun _ _ => rfl
  letI instSCC : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥S :=
    ⟨fun x c v => Subtype.ext (by
      rw [hcoe, Submodule.coe_smul, Submodule.coe_smul, hcoe, smul_comm])⟩

  haveI hfin := CuspForm.IsAdelicLiftOf.finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
    g q Φ hgΦ 1
  let T : Submodule ℂ (LocalNewvector.AdelicSpan Φ) :=
    LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (LocalNewvector.AdelicSpan Φ) ⊓ S
  let ι : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) ↥S) →ₗ[ℂ] ↥T :=
    LinearMap.codRestrict T
      (S.subtype ∘ₗ (LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) ↥S).subtype)
      (fun v => by
        refine ⟨?_, (v : ↥S).2⟩
        show ((v : ↥S) : LocalNewvector.AdelicSpan Φ) ∈
          LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) (LocalNewvector.AdelicSpan Φ)
        rw [LocalNewvector.mem_fixedSubmodule_iff]
        intro k hk
        have hv := (LocalNewvector.mem_fixedSubmodule_iff.1 v.2) k hk
        rw [← hcoe]
        exact congrArg Subtype.val hv)
  have hι : Function.Injective ι := by
    intro v w h
    have h' := congrArg Subtype.val h
    simp only [ι, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype] at h'
    exact Subtype.ext (Subtype.ext h')
  haveI : FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) ↥S) :=
    Module.Finite.of_injective ι hι
  refine ⟨↥S, inferInstance, inferInstance, instDMA, instSCC, inferInstance, S.subtype, fun _ _ => rfl,
    S.injective_subtype, ?_⟩
  rw [Submodule.range_subtype]

end S_CuspForm_IsAdelicLiftOf_exists_realization_range_eq_span_range_padic_smul_self
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_exists_realization_range_eq_span_range_padic_smul_self (solution)
