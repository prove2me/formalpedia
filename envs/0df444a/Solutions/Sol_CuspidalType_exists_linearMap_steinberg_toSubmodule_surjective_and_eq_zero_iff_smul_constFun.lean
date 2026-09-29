-- Prove2me | solution 1 for CuspidalType.exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f04d0356-d206-5f1a-8474-a16cb605a24d

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun

set_option autoImplicit false

namespace CuspidalTypeBlockExists

noncomputable section

open CuspidalType

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ]

private theorem ind_constFun (g : GL2 q) : ind q κ g (constFun q κ) = constFun q κ := by
  rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
  ext x
  have h := Finsupp.mapDomain_apply (MulAction.injective g) (constFun q κ) (g⁻¹ • x)
  rw [smul_inv_smul] at h
  exact h.trans (by simp [constFun])

private def StCar : Type := ↥(steinberg q κ).toSubmodule

private scoped instance : AddCommGroup (StCar q κ) := inferInstanceAs (AddCommGroup ↥(steinberg q κ).toSubmodule)

private scoped instance : Module κ (StCar q κ) := inferInstanceAs (Module κ ↥(steinberg q κ).toSubmodule)

private def svLin : StCar q κ →ₗ[κ] (ProjLine q →₀ κ) := (steinberg q κ).toSubmodule.subtype

private theorem svLin_injective : Function.Injective (svLin q κ) := fun _ _ h => Subtype.ext h

private scoped instance : FiniteDimensional κ (StCar q κ) := Module.Finite.of_injective (svLin q κ) (svLin_injective q κ)

private def stEnd (g : GL2 q) : StCar q κ →ₗ[κ] StCar q κ := steinbergRep q κ g

private theorem svLin_stEnd (g : GL2 q) (x : StCar q κ) : svLin q κ (stEnd q κ g x) = ind q κ g (svLin q κ x) := rfl

private theorem stEnd_one : stEnd q κ 1 = LinearMap.id := by
  ext x
  apply svLin_injective
  rw [svLin_stEnd, map_one]
  rfl

private theorem stEnd_mul (g h : GL2 q) : stEnd q κ (g * h) = stEnd q κ g ∘ₗ stEnd q κ h := by
  ext x
  apply svLin_injective
  rw [LinearMap.comp_apply, svLin_stEnd, svLin_stEnd, svLin_stEnd, map_mul]
  rfl

private def constLine : Submodule κ (StCar q κ) := (Submodule.span κ {constFun q κ}).comap (svLin q κ)

private theorem mem_constLine (x : StCar q κ) : x ∈ constLine q κ ↔ ∃ c : κ, svLin q κ x = c • constFun q κ := by
  rw [constLine, Submodule.mem_comap, Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

private theorem constLine_stable (g : GL2 q) : ∀ x ∈ constLine q κ, stEnd q κ g x ∈ constLine q κ := by
  intro x hx
  rw [mem_constLine] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, by rw [svLin_stEnd, hc, map_smul, ind_constFun]⟩

private def quotRep : Representation κ (GL2 q) (StCar q κ ⧸ constLine q κ) where
  toFun g := (constLine q κ).mapQ (constLine q κ) (stEnd q κ g) fun x hx => constLine_stable q κ g x hx
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp [stEnd_one]
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp [Submodule.mapQ_apply, stEnd_mul]

private theorem quotRep_apply (g : GL2 q) :
    quotRep q κ g = (constLine q κ).mapQ (constLine q κ) (stEnd q κ g) fun x hx => constLine_stable q κ g x hx := rfl

private theorem quotRep_mk (g : GL2 q) (x : StCar q κ) :
    quotRep q κ g ((constLine q κ).mkQ x) = (constLine q κ).mkQ (stEnd q κ g x) := by
  rw [quotRep_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
  rfl

private def toStLin : ↥(steinberg q κ).toSubmodule →ₗ[κ] StCar q κ where
  toFun v := (v : StCar q κ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem toStLin_ind (g : GL2 q) (v : ↥(steinberg q κ).toSubmodule) :
    toStLin q κ ⟨ind q κ g v, (steinberg q κ).apply_mem_toSubmodule g v.2⟩ = stEnd q κ g (toStLin q κ v) := rfl

private theorem svLin_toStLin (v : ↥(steinberg q κ).toSubmodule) : svLin q κ (toStLin q κ v) = (v : ProjLine q →₀ κ) :=
  rfl

private theorem toStLin_surjective : Function.Surjective (toStLin q κ) := fun x => ⟨x, rfl⟩

end

end CuspidalTypeBlockExists
p2m_reactivate "P2MW.S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun.CuspidalTypeBlockExists"

open CuspidalTypeBlockExists in
theorem solution
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module κ V) (_ : FiniteDimensional κ V)
      (ρ : Representation κ (CuspidalType.GL2 q) V)
      (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V),
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      (∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) := by
  refine ⟨StCar q κ ⧸ constLine q κ, inferInstance, inferInstance, inferInstance, quotRep q κ,
    (constLine q κ).mkQ ∘ₗ toStLin q κ, fun g v => ?_, (constLine q κ).mkQ_surjective.comp (toStLin_surjective q κ),
    fun v => ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [toStLin_ind, quotRep_mk]
  · rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_constLine, svLin_toStLin]

end S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
end P2MW
export P2MW.S_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun (solution)
